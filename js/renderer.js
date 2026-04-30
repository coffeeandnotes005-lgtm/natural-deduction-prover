// 피치 증명을 출력할 때 필요한 상태 객체를 만듭니다.
function createFitchEmitState() {
  return {
    // 최종적으로 화면에 출력될 피치 증명 줄 목록입니다.
    lines: [],

    // 각 ND proof node가 자연스럽게 위치해야 하는 scope를 저장합니다.
    naturalScope: new Map(),

    // 각 proof node가 원래 scope에서 이미 몇 번 줄로 출력됐는지 저장합니다.
    emittedNaturalLine: new Map(),

    // 특정 proof node를 특정 scope에서 출력했을 때의 줄 번호를 저장합니다.
    emittedAtScope: new Map(),

    // 바깥 scope의 식을 안쪽 scope에서 반복 사용할 때 만든 R 줄을 재사용하기 위한 캐시입니다.
    repetitionCache: new Map(),
  };
}

// scope 깊이를 계산합니다.
// scope 배열이 길수록 더 안쪽 가정 박스에 있다는 뜻입니다.
function scopeDepth(scope) {
  return scope.length;
}

// scope 배열을 문자열 key로 바꿉니다.
// Map 캐시 키로 쓰기 편하게 하기 위한 함수입니다.
function scopeKey(scope) {
  return scope.join("/");
}

// 단일 하위증명용 scope를 만듭니다.
// 예: →I, ¬I, RAA, ∃E 같은 한 갈래짜리 subproof에 사용합니다.
function unarySubScope(scope, node) {
  return [...scope, node.id];
}

// ∨E의 왼쪽 가지 scope를 만듭니다.
function leftSubScope(scope, node) {
  return [...scope, `${node.id}:0`];
}

// ∨E의 오른쪽 가지 scope를 만듭니다.
function rightSubScope(scope, node) {
  return [...scope, `${node.id}:1`];
}

// prefix가 full의 앞부분 scope인지 확인합니다.
// 바깥 scope의 식은 안쪽 scope에서 반복해서 사용할 수 있습니다.
function isScopePrefix(prefix, full) {
  if (prefix.length > full.length) return false;

  for (let i = 0; i < prefix.length; i++) {
    if (prefix[i] !== full[i]) return false;
  }

  return true;
}

// 피치 증명 한 줄을 추가합니다.
function appendFitchLine(st, scope, formula, reason, refs = [], ranges = []) {
  const line = {
    // 줄 번호는 현재 줄 개수 + 1입니다.
    number: st.lines.length + 1,

    // 가정 박스 깊이입니다.
    depth: scopeDepth(scope),

    // 이 줄이 속한 scope입니다.
    scope: [...scope],

    // 출력할 논리식입니다.
    formula,

    // 규칙 이름입니다. 예: Premise, Assumption, ->I, ∧E
    reason,

    // 참조하는 줄 번호들입니다.
    refs: [...refs],

    // 하위증명 범위입니다. 예: 2-4
    ranges: ranges.map(([a, b]) => [a, b]),
  };

  st.lines.push(line);

  return line.number;
}

// 특정 줄 번호의 scope를 가져옵니다.
function getLineScope(st, lineNumber) {
  if (lineNumber <= 0 || lineNumber > st.lines.length) return [];

  return st.lines[lineNumber - 1].scope;
}

// proof node들이 각각 어느 scope에 놓여야 자연스러운지 미리 수집합니다.
function collectNaturalScopes(node, scope, naturalScope) {
  if (!node) return;

  // 전제는 항상 최상위 scope에 둡니다.
  const actualScope = node.reason === "Premise" ? [] : scope;

  // 이미 더 바깥쪽 scope로 등록되어 있으면 그대로 둡니다.
  const oldScope = naturalScope.get(node.id);
  if (oldScope && scopeDepth(oldScope) <= scopeDepth(actualScope)) {
    return;
  }

  naturalScope.set(node.id, [...actualScope]);

  // ∨E는 왼쪽 가지와 오른쪽 가지가 서로 다른 scope를 가집니다.
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

  // ∃E는 하나의 임시 가정 subproof를 엽니다.
  if (node.reason === "∃E") {
    collectNaturalScopes(node.parent1, actualScope, naturalScope);

    const subScope = unarySubScope(actualScope, node);

    collectNaturalScopes(node.subAssumption1, subScope, naturalScope);
    collectNaturalScopes(node.subEnd1, subScope, naturalScope);

    return;
  }

  // →I, ¬I, RAA도 하나의 subproof를 엽니다.
  if (["->I", "~I", "RAA"].includes(node.reason)) {
    const subScope = unarySubScope(actualScope, node);

    collectNaturalScopes(node.subAssumption1, subScope, naturalScope);
    collectNaturalScopes(node.subEnd1, subScope, naturalScope);

    return;
  }

  // 일반 규칙은 부모 노드들을 같은 scope에서 추적합니다.
  collectNaturalScopes(node.parent1, actualScope, naturalScope);
  collectNaturalScopes(node.parent2, actualScope, naturalScope);
}

// sourceLine을 targetScope 안에서 쓸 수 있게 보장합니다.
// 바깥 줄을 안쪽에서 쓰는 경우 R 줄을 새로 추가합니다.
function ensureLineAtScope(st, sourceLine, targetScope) {
  if (sourceLine <= 0) return sourceLine;

  const sourceScope = getLineScope(st, sourceLine);

  // 이미 같은 scope면 그대로 사용합니다.
  if (scopeKey(sourceScope) === scopeKey(targetScope)) return sourceLine;

  // 바깥 scope의 줄은 안쪽 scope에서 반복 사용 가능합니다.
  if (isScopePrefix(sourceScope, targetScope)) {
    const key = `${sourceLine}|${scopeKey(targetScope)}`;

    // 이미 같은 반복 줄을 만든 적 있으면 재사용합니다.
    if (st.repetitionCache.has(key)) {
      return st.repetitionCache.get(key);
    }

    const sameFormula = st.lines[sourceLine - 1].formula;

    // R은 반복을 뜻합니다.
    const newLine = appendFitchLine(st, targetScope, sameFormula, "R", [sourceLine], []);

    st.repetitionCache.set(key, newLine);

    return newLine;
  }

  // 안쪽 scope의 식을 바깥 scope에서 쓰는 것은 불법입니다.
  throw new Error(`불법 scope 참조: source_scope=${scopeKey(sourceScope)}, target_scope=${scopeKey(targetScope)}, line=${sourceLine}`);
}

// 하위증명의 시작 줄과 끝 줄 번호를 만듭니다.
function emitSubproofRange(st, assumptionNode, endNode, scope) {
  // 하위증명의 첫 줄은 가정입니다.
  const a = emitNode(assumptionNode, st, scope);

  // 가정 자체가 곧 결론이면, 범위를 만들기 위해 반복 줄을 하나 추가합니다.
  if (assumptionNode === endNode) {
    const formula = st.lines[a - 1].formula;
    const e = appendFitchLine(st, scope, formula, "R", [a], []);

    return [a, e];
  }

  let e = emitNode(endNode, st, scope);

  // 시작과 끝이 같은 줄이면 범위 표시가 애매하므로 반복 줄을 추가합니다.
  if (a === e) {
    const formula = st.lines[a - 1].formula;
    e = appendFitchLine(st, scope, formula, "R", [a], []);
  }

  return [a, e];
}

// 실제로 proof node 하나를 피치 줄로 출력합니다.
function emitActualNode(node, st) {
  const scope = st.naturalScope.get(node.id);

  // 전제와 가정은 바로 한 줄로 출력합니다.
  if (["Premise", "Assumption"].includes(node.reason)) {
    return appendFitchLine(st, scope, node.formula, node.reason, [], []);
  }

  // →I, ¬I, RAA는 하위증명 범위를 참조합니다.
  if (["->I", "~I", "RAA"].includes(node.reason)) {
    const subScope = unarySubScope(scope, node);
    const [a1, e1] = emitSubproofRange(st, node.subAssumption1, node.subEnd1, subScope);

    return appendFitchLine(st, scope, node.formula, node.reason, [], [[a1, e1]]);
  }

  // ∨E는 선언식 한 줄과 두 개의 하위증명 범위를 참조합니다.
  if (node.reason === "∨E") {
    const disj = emitNode(node.parent1, st, scope);

    const leftScope = leftSubScope(scope, node);
    const rightScope = rightSubScope(scope, node);

    const [a1, e1] = emitSubproofRange(st, node.subAssumption1, node.subEnd1, leftScope);
    const [a2, e2] = emitSubproofRange(st, node.subAssumption2, node.subEnd2, rightScope);

    return appendFitchLine(st, scope, node.formula, node.reason, [disj], [[a1, e1], [a2, e2]]);
  }

  // ∃E는 존재식 한 줄과 하나의 하위증명 범위를 참조합니다.
  if (node.reason === "∃E") {
    const existsLine = emitNode(node.parent1, st, scope);

    const subScope = unarySubScope(scope, node);
    const [a1, e1] = emitSubproofRange(st, node.subAssumption1, node.subEnd1, subScope);

    return appendFitchLine(st, scope, node.formula, node.reason, [existsLine], [[a1, e1]]);
  }

  // 부모가 하나인 규칙입니다. 예: ∧E, ∨I, ∀I, ∃I
  if (node.parent1 && !node.parent2) {
    const p1 = emitNode(node.parent1, st, scope);

    return appendFitchLine(st, scope, node.formula, node.reason, [p1], []);
  }

  // 부모가 둘인 규칙입니다. 예: ∧I, →E, ¬E
  if (node.parent1 && node.parent2) {
    // →E는 보통 antecedent 줄을 먼저, implication 줄을 나중에 표시하기 위해 순서를 조정합니다.
    if (node.reason === "->E") {
      const antecedentLine = emitNode(node.parent2, st, scope);
      const implicationLine = emitNode(node.parent1, st, scope);

      return appendFitchLine(st, scope, node.formula, node.reason, [antecedentLine, implicationLine], []);
    }

    const p1 = emitNode(node.parent1, st, scope);
    const p2 = emitNode(node.parent2, st, scope);

    return appendFitchLine(st, scope, node.formula, node.reason, [p1, p2], []);
  }

  // 예외적인 경우에도 최소한 한 줄은 출력합니다.
  return appendFitchLine(st, scope, node.formula, node.reason, [], []);
}

// proof node를 필요한 scope에서 출력합니다.
// 이미 출력된 node는 재사용하고, scope가 다르면 R 줄을 만듭니다.
function emitNode(node, st, currentScope) {
  if (!node) return 0;

  const scopedKey = `${node.id}|${scopeKey(currentScope)}`;

  // 이 node를 이 scope에서 이미 출력했다면 줄 번호를 재사용합니다.
  if (st.emittedAtScope.has(scopedKey)) {
    return st.emittedAtScope.get(scopedKey);
  }

  const naturalScope = st.naturalScope.get(node.id) || [];

  // node의 자연 scope와 현재 scope가 다르면 scope 이동 처리를 합니다.
  if (scopeKey(naturalScope) !== scopeKey(currentScope)) {
    // 안쪽 scope의 줄을 바깥 scope에서 쓰는 것은 허용하지 않습니다.
    if (!isScopePrefix(naturalScope, currentScope)) {
      throw new Error(`ND node를 현재 scope에서 사용할 수 없음: natural_scope=${scopeKey(naturalScope)}, current_scope=${scopeKey(currentScope)}`);
    }

    // 먼저 자연 scope에서 출력합니다.
    const baseLine = emitNode(node, st, naturalScope);

    // 그 줄을 현재 scope에서 쓸 수 있게 R 줄을 만들거나 재사용합니다.
    const result = ensureLineAtScope(st, baseLine, currentScope);

    st.emittedAtScope.set(scopedKey, result);

    return result;
  }

  // 자연 scope에서 이미 출력된 node면 그 줄 번호를 재사용합니다.
  if (st.emittedNaturalLine.has(node.id)) {
    const result = st.emittedNaturalLine.get(node.id);

    st.emittedAtScope.set(scopedKey, result);

    return result;
  }

  // 아직 출력된 적 없으면 실제 줄을 생성합니다.
  const result = emitActualNode(node, st);

  st.emittedNaturalLine.set(node.id, result);
  st.emittedAtScope.set(scopedKey, result);

  return result;
}

// 내부 규칙 이름을 화면 표시용 규칙 이름으로 바꿉니다.
function reasonToDisplay(reason) {
  return reason
    // ∨I 1, ∨I 2는 화면에서는 그냥 ∨I로 표시합니다.
    .replace(/∨I 1/g, "∨I")
    .replace(/∨I 2/g, "∨I")
    .replace(/∨E/g, "∨E")

    // 예전 표기 호환용 변환입니다.
    .replace(/\\\/I 1/g, "∨I")
    .replace(/\\\/I 2/g, "∨I")
    .replace(/\\\/I1/g, "∨I")
    .replace(/\\\/I2/g, "∨I")
    .replace(/\\\//g, "∨")

    // RAA와 ~E 표시를 서로 바꾸기 위한 임시 치환입니다.
    .replace(/RAA/g, "__TEMP_RAA__")
    .replace(/~E/g, "RAA")
    .replace(/__TEMP_RAA__/g, "~E")

    // ASCII식 기호를 논리 기호로 바꿉니다.
    .replace(/->/g, "→")
    .replace(/~/g, "¬")
    .replace(/&/g, "∧");
}

// 한 줄의 규칙 표시 문자열을 만듭니다.
// 예: →I 2-4, ∧E 1, →E 2, 1
function formatFitchReason(line) {
  let out = reasonToDisplay(line.reason);

  const hasRefs = line.refs.length > 0;
  const hasRanges = line.ranges.length > 0;

  if (!hasRefs && !hasRanges) return out;

  const items = [];

  // 일반 참조 줄 번호
  for (const ref of line.refs) items.push(String(ref));

  // 하위증명 범위
  for (const [start, end] of line.ranges) items.push(`${start}-${end}`);

  return out + " " + items.join(", ");
}

// ND proof tree를 피치 줄 배열로 변환합니다.
function buildFitchLines(root, premiseNodes = []) {
  const st = createFitchEmitState();

  // 전제들의 자연 scope를 먼저 수집합니다.
  for (const premiseNode of premiseNodes) {
    collectNaturalScopes(premiseNode, [], st.naturalScope);
  }

  // 결론 proof tree의 자연 scope를 수집합니다.
  collectNaturalScopes(root, [], st.naturalScope);

  // 전제를 먼저 출력합니다.
  for (const premiseNode of premiseNodes) {
    emitNode(premiseNode, st, []);
  }

  // 그 다음 결론 proof tree를 출력합니다.
  emitNode(root, st, []);

  return st.lines;
}

// 피치 줄 배열을 plain text 문자열로 바꿉니다.
// 현재 HTML 렌더링을 쓰는 경우에는 보조용입니다.
function fitchLinesToString(lines) {
  if (!lines || lines.length === 0) return "";

  const numberWidth = String(lines.length).length;

  // depth에 따라 식 앞에 공백을 넣습니다.
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

// HTML에 직접 넣으면 위험한 문자를 안전한 문자로 바꿉니다.
// 사용자가 입력한 식을 HTML로 출력하므로 필수입니다.
function escapeHtml(text) {
  return String(text)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

// 피치 줄 배열을 HTML 문자열로 렌더링합니다.
function renderFitchHTML(lines, zebraOn = true) {
  if (!lines || lines.length === 0) return "";

  // ∨E 가지 끝 줄 번호를 저장합니다.
  // 가지 끝에서는 scope 선 모양을 다르게 그려야 합니다.
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

  // scope의 앞부분만 key로 바꿉니다.
  function scopePrefixKey(scope, level) {
    return scope.slice(0, level).join("/");
  }

  // 현재 level의 scope가 ∨E의 왼쪽/오른쪽 가지인지 확인합니다.
  function isOrElimScope(scope, level) {
    const token = scope[level - 1];

    return typeof token === "string" && token.includes(":");
  }

  // 특정 줄에서 특정 level의 scope가 닫히는지 판단합니다.
  function scopeClosesHere(lines, index, level) {
    const line = lines[index];

    if (!line || level > line.depth) return false;

    // ∨E 가지 scope는 여기서 닫힘 표시를 따로 하지 않습니다.
    if (isOrElimScope(line.scope, level)) return false;

    // 마지막 줄이면 닫힙니다.
    if (index === lines.length - 1) return true;

    const next = lines[index + 1];

    // 다음 줄이 없거나 더 얕은 scope면 닫힙니다.
    if (!next || level > next.depth) return true;

    // 다음 줄의 같은 level scope가 달라지면 현재 scope가 닫힌 것입니다.
    return scopePrefixKey(next.scope, level) !== scopePrefixKey(line.scope, level);
  }

  return `
    <div class="fitch-proof ${zebraOn ? "zebra-on" : "zebra-off"}">
      ${lines.map((line, index) => {
        // 최상위 scope 선입니다.
        const baseScopeClasses = ["fitch-scope", "fitch-scope-base"];

        if (line.depth === 0) baseScopeClasses.push("scope-last");

        const baseScope = `<span class="${baseScopeClasses.join(" ")}"></span>`;

        // 현재 줄의 depth만큼 scope 선을 만듭니다.
        const scopes = baseScope + Array.from({ length: line.depth }, (_, scopeIndex) => {
          const level = scopeIndex + 1;

          const classes = ["fitch-scope"];

          // 가정 줄이면 박스가 시작되는 표시를 붙입니다.
          if (line.reason === "Assumption" && level === line.depth) {
            classes.push("scope-open");
            classes.push("scope-start");
          }

          // 이 줄에서 scope가 닫히면 닫힘 표시를 붙입니다.
          if (scopeClosesHere(lines, index, level)) classes.push("scope-close");

          // 가장 안쪽 scope면 폭을 줄이는 클래스입니다.
          if (level === line.depth) classes.push("scope-last");

          // ∨E 가지 끝 줄이면 가지 끝 전용 클래스를 붙입니다.
          if (level === line.depth && orElimBranchEndLines.has(line.number)) {
            classes.push("scope-branch-end");
          }

          return `<span class="${classes.join(" ")}"></span>`;
        }).join("");

        // 한 줄 전체 클래스입니다.
        const lineClasses = ["fitch-line"];

        // 전제 줄이면 premise-line을 붙입니다.
        if (line.reason === "Premise") {
          lineClasses.push("premise-line");

          const nextLine = lines[index + 1];

          // 마지막 전제 줄에는 아래 가로선을 붙입니다.
          if (!nextLine || nextLine.reason !== "Premise") {
            lineClasses.push("premise-divider");
          }
        }

        // 실제 한 줄 HTML입니다.
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

// 증명 결과 객체를 최종 출력 HTML로 바꿉니다.
function renderProofResult(result) {
  // 시간 제한으로 중단된 경우
  if (result.timedOut) {
    return `<div class="plain-result">제한시간 안에 증명을 생성하지 못했습니다.</div>`;
  }

  // 증명 줄이 없으면 실패 메시지를 출력합니다.
  if (!result.fitchLines) {
    return `<div class="plain-result">증명을 찾지 못했습니다.</div>`;
  }

  // 성공하면 피치 증명을 HTML로 출력합니다.
  return renderFitchHTML(result.fitchLines, window.zebraStripingEnabled);
}
