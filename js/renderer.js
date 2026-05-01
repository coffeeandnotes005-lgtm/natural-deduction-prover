function createFitchEmitState() {
  return {
    lines: [],
    naturalScope: new Map(),
    emittedNaturalLine: new Map(),
    emittedAtScope: new Map(),
    repetitionCache: new Map(),
  };
}

function scopeDepth(scope) {
  return scope.length;
}

function scopeKey(scope) {
  return scope.join("/");
}

function unarySubScope(scope, node) {
  return [...scope, node.id];
}

function leftSubScope(scope, node) {
  return [...scope, `${node.id}:0`];
}

function rightSubScope(scope, node) {
  return [...scope, `${node.id}:1`];
}

function isScopePrefix(prefix, full) {
  if (prefix.length > full.length) return false;

  for (let i = 0; i < prefix.length; i++) {
    if (prefix[i] !== full[i]) return false;
  }

  return true;
}

function appendFitchLine(st, scope, formula, reason, refs = [], ranges = []) {
  const line = {
    number: st.lines.length + 1,
    depth: scopeDepth(scope),
    scope: [...scope],
    formula,
    reason,
    refs: [...refs],
    ranges: ranges.map(([a, b]) => [a, b]),
  };

  st.lines.push(line);

  return line.number;
}

function getLineScope(st, lineNumber) {
  if (lineNumber <= 0 || lineNumber > st.lines.length) return [];

  return st.lines[lineNumber - 1].scope;
}

function collectNaturalScopes(node, scope, naturalScope) {
  if (!node) return;

  const actualScope = node.reason === "Premise" ? [] : scope;

  const oldScope = naturalScope.get(node.id);
  if (oldScope && scopeDepth(oldScope) <= scopeDepth(actualScope)) {
    return;
  }

  naturalScope.set(node.id, [...actualScope]);

  if (node.reason === "∨E") {
    collectNaturalScopes(node.parent1, actualScope, naturalScope);

    const leftScope = leftSubScope(actualScope, node);
    const rightScope = rightSubScope(actualScope, node);

    collectNaturalScopes(node.subAssumption1, leftScope, naturalScope);
    collectNaturalScopes(node.subEnd1, leftScope, naturalScope);
    collectNaturalScopes(node.subAssumption2, rightScope, naturalScope);
    collectNaturalScopes(node.subEnd2, rightScope, naturalScope);

    return;
  }

  if (node.reason === "∃E") {
    collectNaturalScopes(node.parent1, actualScope, naturalScope);

    const subScope = unarySubScope(actualScope, node);

    collectNaturalScopes(node.subAssumption1, subScope, naturalScope);
    collectNaturalScopes(node.subEnd1, subScope, naturalScope);

    return;
  }

  if (["->I", "~I", "RAA"].includes(node.reason)) {
    const subScope = unarySubScope(actualScope, node);

    collectNaturalScopes(node.subAssumption1, subScope, naturalScope);
    collectNaturalScopes(node.subEnd1, subScope, naturalScope);

    return;
  }

  collectNaturalScopes(node.parent1, actualScope, naturalScope);
  collectNaturalScopes(node.parent2, actualScope, naturalScope);
}

function ensureLineAtScope(st, sourceLine, targetScope) {
  if (sourceLine <= 0) return sourceLine;

  const sourceScope = getLineScope(st, sourceLine);

  if (scopeKey(sourceScope) === scopeKey(targetScope)) return sourceLine;

  if (isScopePrefix(sourceScope, targetScope)) {
    const key = `${sourceLine}|${scopeKey(targetScope)}`;

    if (st.repetitionCache.has(key)) {
      return st.repetitionCache.get(key);
    }

    const sameFormula = st.lines[sourceLine - 1].formula;

    const newLine = appendFitchLine(st, targetScope, sameFormula, "R", [sourceLine], []);

    st.repetitionCache.set(key, newLine);

    return newLine;
  }

  throw new Error(`불법 scope 참조: source_scope=${scopeKey(sourceScope)}, target_scope=${scopeKey(targetScope)}, line=${sourceLine}`);
}

function emitSubproofRange(st, assumptionNode, endNode, scope) {
  const a = emitNode(assumptionNode, st, scope);

  if (assumptionNode === endNode) {
    const formula = st.lines[a - 1].formula;
    const e = appendFitchLine(st, scope, formula, "R", [a], []);

    return [a, e];
  }

  let e = emitNode(endNode, st, scope);

  if (a === e) {
    const formula = st.lines[a - 1].formula;
    e = appendFitchLine(st, scope, formula, "R", [a], []);
  }

  return [a, e];
}

function emitActualNode(node, st) {
  const scope = st.naturalScope.get(node.id);

  if (["Premise", "Assumption"].includes(node.reason)) {
    return appendFitchLine(st, scope, node.formula, node.reason, [], []);
  }

  if (["->I", "~I", "RAA"].includes(node.reason)) {
    const subScope = unarySubScope(scope, node);
    const [a1, e1] = emitSubproofRange(st, node.subAssumption1, node.subEnd1, subScope);

    return appendFitchLine(st, scope, node.formula, node.reason, [], [[a1, e1]]);
  }

  if (node.reason === "∨E") {
    const disj = emitNode(node.parent1, st, scope);

    const leftScope = leftSubScope(scope, node);
    const rightScope = rightSubScope(scope, node);

    const [a1, e1] = emitSubproofRange(st, node.subAssumption1, node.subEnd1, leftScope);
    const [a2, e2] = emitSubproofRange(st, node.subAssumption2, node.subEnd2, rightScope);

    return appendFitchLine(st, scope, node.formula, node.reason, [disj], [[a1, e1], [a2, e2]]);
  }

  if (node.reason === "∃E") {
    const existsLine = emitNode(node.parent1, st, scope);

    const subScope = unarySubScope(scope, node);
    const [a1, e1] = emitSubproofRange(st, node.subAssumption1, node.subEnd1, subScope);

    return appendFitchLine(st, scope, node.formula, node.reason, [existsLine], [[a1, e1]]);
  }

  if (node.parent1 && !node.parent2) {
    const p1 = emitNode(node.parent1, st, scope);

    return appendFitchLine(st, scope, node.formula, node.reason, [p1], []);
  }

  if (node.parent1 && node.parent2) {
    if (node.reason === "->E") {
      const antecedentLine = emitNode(node.parent2, st, scope);
      const implicationLine = emitNode(node.parent1, st, scope);

      return appendFitchLine(st, scope, node.formula, node.reason, [antecedentLine, implicationLine], []);
    }

    const p1 = emitNode(node.parent1, st, scope);
    const p2 = emitNode(node.parent2, st, scope);

    return appendFitchLine(st, scope, node.formula, node.reason, [p1, p2], []);
  }

  return appendFitchLine(st, scope, node.formula, node.reason, [], []);
}

function emitNode(node, st, currentScope) {
  if (!node) return 0;

  const scopedKey = `${node.id}|${scopeKey(currentScope)}`;

  if (st.emittedAtScope.has(scopedKey)) {
    return st.emittedAtScope.get(scopedKey);
  }

  const naturalScope = st.naturalScope.get(node.id) || [];

  if (scopeKey(naturalScope) !== scopeKey(currentScope)) {
    if (!isScopePrefix(naturalScope, currentScope)) {
      throw new Error(`ND node를 현재 scope에서 사용할 수 없음: natural_scope=${scopeKey(naturalScope)}, current_scope=${scopeKey(currentScope)}`);
    }

    const baseLine = emitNode(node, st, naturalScope);

    const result = ensureLineAtScope(st, baseLine, currentScope);

    st.emittedAtScope.set(scopedKey, result);

    return result;
  }

  if (st.emittedNaturalLine.has(node.id)) {
    const result = st.emittedNaturalLine.get(node.id);

    st.emittedAtScope.set(scopedKey, result);

    return result;
  }

  const result = emitActualNode(node, st);

  st.emittedNaturalLine.set(node.id, result);
  st.emittedAtScope.set(scopedKey, result);

  return result;
}

function reasonToDisplay(reason) {
  return reason
    .replace(/∨I 1/g, "∨I")
    .replace(/∨I 2/g, "∨I")
    .replace(/∨E/g, "∨E")

    .replace(/\\\/I 1/g, "∨I")
    .replace(/\\\/I 2/g, "∨I")
    .replace(/\\\/I1/g, "∨I")
    .replace(/\\\/I2/g, "∨I")
    .replace(/\\\//g, "∨")

    .replace(/RAA/g, "__TEMP_RAA__")
    .replace(/~E/g, "RAA")
    .replace(/__TEMP_RAA__/g, "~E")

    .replace(/->/g, "→")
    .replace(/~/g, "¬")
    .replace(/&/g, "∧");
}

function formatFitchReason(line) {
  let out = reasonToDisplay(line.reason);

  const hasRefs = line.refs.length > 0;
  const hasRanges = line.ranges.length > 0;

  if (!hasRefs && !hasRanges) return out;

  const items = [];

  for (const ref of line.refs) items.push(String(ref));

  for (const [start, end] of line.ranges) items.push(`${start}-${end}`);

  return out + " " + items.join(", ");
}

function buildFitchLines(root, premiseNodes = []) {
  const st = createFitchEmitState();

  for (const premiseNode of premiseNodes) {
    collectNaturalScopes(premiseNode, [], st.naturalScope);
  }

  collectNaturalScopes(root, [], st.naturalScope);

  for (const premiseNode of premiseNodes) {
    emitNode(premiseNode, st, []);
  }

  emitNode(root, st, []);

  return st.lines;
}

function fitchLinesToString(lines) {
  if (!lines || lines.length === 0) return "";

  const numberWidth = String(lines.length).length;

  const formulaTexts = lines.map((line) => " ".repeat(line.depth * 12) + formulaToDisplayString(line.formula));

  const formulaColumnWidth = Math.max(...formulaTexts.map((s) => s.length), 0);

  const ruleGap = 4;

  const outLines = [];

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];

    const formulaText = formulaTexts[i];

    const numberText = String(line.number).padStart(numberWidth, " ");

    const formulaPadded = formulaText.padEnd(formulaColumnWidth + ruleGap, " ");

    outLines.push(`${numberText}  ${formulaPadded}${formatFitchReason(line)}`);
  }

  return outLines.join("\n");
}

function escapeHtml(text) {
  return String(text)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function renderFitchHTML(lines, zebraOn = true) {
  if (!lines || lines.length === 0) return "";

  const orElimBranchStartLines = new Set();
  const orElimBranchEndLines = new Set();

  lines.forEach((line) => {
    if (line.reason === "∨E" && Array.isArray(line.ranges)) {
      line.ranges.forEach((range) => {
        if (Array.isArray(range) && range.length >= 2) {
          const start = Number(range[0]);
          const end = Number(range[1]);

          if (Number.isFinite(start) && start > 0) orElimBranchStartLines.add(start);
          if (Number.isFinite(end) && end > 0) orElimBranchEndLines.add(end);
        }
      });
    }
  });

  function scopePrefixKey(scope, level) {
    return scope.slice(0, level).join("/");
  }

  function isOrElimScope(scope, level) {
    const token = scope[level - 1];

    return typeof token === "string" && token.includes(":");
  }

  function scopeClosesHere(lines, index, level) {
    const line = lines[index];

    if (!line || level > line.depth) return false;

    if (isOrElimScope(line.scope, level)) return false;

    if (index === lines.length - 1) return true;

    const next = lines[index + 1];

    if (!next || level > next.depth) return true;

    return scopePrefixKey(next.scope, level) !== scopePrefixKey(line.scope, level);
  }

  return `
    <div class="fitch-proof ${zebraOn ? "zebra-on" : "zebra-off"}">
      ${lines.map((line, index) => {
        const baseScopeClasses = ["fitch-scope", "fitch-scope-base"];

        if (line.depth === 0) baseScopeClasses.push("scope-last");

        const baseScope = `<span class="${baseScopeClasses.join(" ")}"></span>`;

        const scopes = baseScope + Array.from({ length: line.depth }, (_, scopeIndex) => {
          const level = scopeIndex + 1;

          const classes = ["fitch-scope"];

          if (line.reason === "Assumption" && level === line.depth) {
            classes.push("scope-open");
            classes.push("scope-start");
          }

          if (scopeClosesHere(lines, index, level)) classes.push("scope-close");

          if (level === line.depth) classes.push("scope-last");

          if (level === line.depth && orElimBranchEndLines.has(line.number)) {
            classes.push("scope-branch-end");
          }

          return `<span class="${classes.join(" ")}"></span>`;
        }).join("");

        const lineClasses = ["fitch-line"];

        if (line.reason === "Premise") {
          lineClasses.push("premise-line");

          const nextLine = lines[index + 1];

          if (!nextLine || nextLine.reason !== "Premise") {
            lineClasses.push("premise-divider");
          }
        }

        return `
          <div class="${lineClasses.join(" ")}">
            <div class="fitch-num">${line.number}</div>
            <div class="fitch-main">
              ${scopes}
              <div class="fitch-content">
                <div class="fitch-formula-body">
                  <span class="fitch-expr-chip">
                    <span class="fitch-expr">${escapeHtml(formulaToDisplayString(line.formula))}</span>
                  </span>
                </div>
                <div class="fitch-reason">
                  <span class="fitch-reason-chip">${escapeHtml(formatFitchReason(line))}</span>
                </div>
              </div>
            </div>
          </div>
        `;
      }).join("")}
    </div>
  `;
}

function renderProofResult(result) {
  if (result.timedOut) {
    return `<div class="plain-result">제한시간 안에 증명을 생성하지 못했습니다.</div>`;
  }

  if (!result.fitchLines) {
    return `<div class="plain-result">증명을 찾지 못했습니다.</div>`;
  }

  return renderFitchHTML(result.fitchLines, window.zebraStripingEnabled);
}
