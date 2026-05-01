const ICRule = {
  Leaf: "Leaf",
  Clash: "Clash",
  ContradSearch: "ContradSearch",
  AndDown1: "AndDown1",
  AndDown2: "AndDown2",
  OrDown: "OrDown",
  ImpDown: "ImpDown",
  AndUp: "AndUp",
  OrUp1: "OrUp1",
  OrUp2: "OrUp2",
  ImpUp: "ImpUp",
  NegUp: "NegUp",
  ClassicalUp: "ClassicalUp",
  ForallDown: "ForallDown",
  ExistsDown: "ExistsDown",
  ForallUp: "ForallUp",
  ExistsUp: "ExistsUp",
  Fail: "Fail",
};

let nextNodeId = 1;

function negateFormula(f) {
  return Formula.createNegation(f);
}

function collectSubformulas(f, out) {
  if (!f) return;

  if (containsFormula(out, f)) return;

  out.push(f);

  if (f.type === FormulaType.Negation) {
    collectSubformulas(f.left, out);

  } else if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(f.type)) {
    collectSubformulas(f.left, out);
    collectSubformulas(f.right, out);

  } else if ([FormulaType.Universal, FormulaType.Existential].includes(f.type)) {
    collectSubformulas(f.left, out);
  }
}

function cloneTerm(term) {
  if (!term) return null;

  if (term.type === TermType.Variable) return Term.createVariable(term.symbol);

  if (term.type === TermType.Constant) return Term.createConstant(term.symbol);

  return Term.createConstant(term.symbol);
}

function cloneFormula(formula) {
  if (!formula) return null;

  if (formula.type === FormulaType.SentenceLetter) {
    return Formula.createSentenceLetter(formula.symbol);
  }

  if (formula.type === FormulaType.Predicate) {
    return Formula.createPredicate(formula.symbol, (formula.args || []).map(cloneTerm));
  }

  if (formula.type === FormulaType.Contradiction) {
    return Formula.createContradiction();
  }

  if (formula.type === FormulaType.Negation) {
    return Formula.createNegation(cloneFormula(formula.left));
  }

  if (formula.type === FormulaType.Universal) {
    return Formula.createUniversal(formula.variable, cloneFormula(formula.left));
  }

  if (formula.type === FormulaType.Existential) {
    return Formula.createExistential(formula.variable, cloneFormula(formula.left));
  }

  return Formula.createBinary(
    formula.type,
    cloneFormula(formula.left),
    cloneFormula(formula.right)
  );
}

function collectTermsFromTerm(term, out) {
  if (!term) return;

  out.push(cloneTerm(term));

  for (const arg of term.args || []) {
    collectTermsFromTerm(arg, out);
  }
}

function collectTermsFromFormula(formula, out) {
  if (!formula) return;

  if (formula.type === FormulaType.Predicate) {
    for (const arg of formula.args || []) {
      collectTermsFromTerm(arg, out);
    }
    return;
  }

  if (formula.type === FormulaType.Negation) {
    collectTermsFromFormula(formula.left, out);
    return;
  }

  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    collectTermsFromFormula(formula.left, out);
    collectTermsFromFormula(formula.right, out);
    return;
  }

  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    collectTermsFromFormula(formula.left, out);
  }
}

function uniqueTermsPreserveOrder(terms) {
  const seen = new Set();
  const out = [];

  for (const term of terms) {
    const key = termToString(term);

    if (seen.has(key)) continue;

    seen.add(key);
    out.push(term);
  }

  return out;
}

function collectQuestionTerms(q, extraFormula = null, extraTerm = null) {
  const raw = [];

  for (const f of q.alpha) {
    collectTermsFromFormula(f, raw);
  }

  for (const f of q.beta) {
    collectTermsFromFormula(f, raw);
  }

  collectTermsFromFormula(q.goal, raw);

  collectTermsFromFormula(extraFormula, raw);

  if (
    extraFormula &&
    [FormulaType.Universal, FormulaType.Existential].includes(extraFormula.type) &&
    extraFormula.variable
  ) {
    raw.push(Term.createVariable(extraFormula.variable));
  }

  if (extraTerm) {
    raw.push(cloneTerm(extraTerm));
  }

  return uniqueTermsPreserveOrder(raw);
}

function collectOpenFreeVariableSymbols(q) {
  const blocked = new Set();

  for (const formula of q.alpha || []) {
    for (const v of freeVariablesOfFormula(formula)) {
      blocked.add(v);
    }
  }

  for (const formula of q.beta || []) {
    for (const v of freeVariablesOfFormula(formula)) {
      blocked.add(v);
    }
  }

  return blocked;
}

function collectSafeInstantiationTerms(q, extraFormula = null, extraTerm = null) {
  const terms = collectQuestionTerms(q, extraFormula, extraTerm);
  const blockedVars = collectOpenFreeVariableSymbols(q);

  return terms.filter((term) => {
    if (!term) return false;

    if (term.type === TermType.Constant) return true;

    if (term.type === TermType.Variable) {
      return !blockedVars.has(term.symbol);
    }

    return false;
  });
}

function collectVariableSymbolsFromTerm(term, out) {
  if (!term) return;

  if (term.type === TermType.Variable) {
    out.add(term.symbol);
  }

  for (const arg of term.args || []) {
    collectVariableSymbolsFromTerm(arg, out);
  }
}

function collectVariableSymbolsFromFormula(formula, out) {
  if (!formula) return;

  if (formula.variable) out.add(formula.variable);

  if (formula.type === FormulaType.Predicate) {
    for (const arg of formula.args || []) {
      collectVariableSymbolsFromTerm(arg, out);
    }
    return;
  }

  collectVariableSymbolsFromFormula(formula.left, out);
  collectVariableSymbolsFromFormula(formula.right, out);
}

function collectFreeVariablesTerm(term, out) {
  if (!term) return;

  if (term.type === TermType.Variable) {
    out.add(term.symbol);
    return;
  }

  for (const arg of term.args || []) {
    collectFreeVariablesTerm(arg, out);
  }
}

function collectFreeVariablesFormula(formula, out, bound = new Set()) {
  if (!formula) return;

  if (formula.type === FormulaType.Predicate) {
    for (const arg of formula.args || []) {
      const tmp = new Set();
      collectFreeVariablesTerm(arg, tmp);

      for (const v of tmp) {
        if (!bound.has(v)) out.add(v);
      }
    }
    return;
  }

  if (formula.type === FormulaType.Negation) {
    collectFreeVariablesFormula(formula.left, out, bound);
    return;
  }

  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    collectFreeVariablesFormula(formula.left, out, bound);
    collectFreeVariablesFormula(formula.right, out, bound);
    return;
  }

  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    const nextBound = new Set(bound);

    nextBound.add(formula.variable);

    collectFreeVariablesFormula(formula.left, out, nextBound);
  }
}

function freeVariablesOfTerm(term) {
  const out = new Set();
  collectFreeVariablesTerm(term, out);
  return out;
}

function freeVariablesOfFormula(formula) {
  const out = new Set();
  collectFreeVariablesFormula(formula, out);
  return out;
}

function formulaHasFreeVariable(formula, variable) {
  return freeVariablesOfFormula(formula).has(variable);
}

function chooseFreshVariableSymbol(...items) {
  const used = new Set();

  for (const item of items) {
    if (!item) continue;

    if (item instanceof Term) {
      collectVariableSymbolsFromTerm(item, used);

    } else if (item instanceof Formula) {
      collectVariableSymbolsFromFormula(item, used);

    } else if (Array.isArray(item)) {
      for (const sub of item) {
        if (sub instanceof Term) collectVariableSymbolsFromTerm(sub, used);
        else if (sub instanceof Formula) collectVariableSymbolsFromFormula(sub, used);
        else if (typeof sub === "string") used.add(sub);
      }

    } else if (item instanceof Set) {
      for (const v of item) used.add(v);

    } else if (typeof item === "string") {
      used.add(item);
    }
  }

  const bases = ["u", "v", "w", "x", "y", "z"];
  for (const base of bases) {
    if (!used.has(base)) return base;
  }

  for (let suffix = 1; suffix < 10000; suffix++) {
    for (const base of bases) {
      const candidate = `${base}${suffix}`;
      if (!used.has(candidate)) return candidate;
    }
  }

  throw new Error("새 변항기호를 더 만들 수 없습니다.");
}

function renameBoundOccurrencesInTerm(term, oldVar, newVar) {
  if (!term) return null;

  if (term.type === TermType.Variable) {
    return Term.createVariable(term.symbol === oldVar ? newVar : term.symbol);
  }

  if (term.type === TermType.Constant) return Term.createConstant(term.symbol);

  return Term.createConstant(term.symbol);
}

function renameBoundOccurrencesInFormula(formula, oldVar, newVar) {
  if (!formula) return null;

  if (formula.type === FormulaType.SentenceLetter) {
    return Formula.createSentenceLetter(formula.symbol);
  }

  if (formula.type === FormulaType.Predicate) {
    return Formula.createPredicate(
      formula.symbol,
      (formula.args || []).map((arg) => renameBoundOccurrencesInTerm(arg, oldVar, newVar))
    );
  }

  if (formula.type === FormulaType.Contradiction) {
    return Formula.createContradiction();
  }

  if (formula.type === FormulaType.Negation) {
    return Formula.createNegation(renameBoundOccurrencesInFormula(formula.left, oldVar, newVar));
  }

  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    return Formula.createBinary(
      formula.type,
      renameBoundOccurrencesInFormula(formula.left, oldVar, newVar),
      renameBoundOccurrencesInFormula(formula.right, oldVar, newVar)
    );
  }

  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    if (formula.variable === oldVar) {
      return formula.type === FormulaType.Universal
        ? Formula.createUniversal(formula.variable, cloneFormula(formula.left))
        : Formula.createExistential(formula.variable, cloneFormula(formula.left));
    }

    return formula.type === FormulaType.Universal
      ? Formula.createUniversal(formula.variable, renameBoundOccurrencesInFormula(formula.left, oldVar, newVar))
      : Formula.createExistential(formula.variable, renameBoundOccurrencesInFormula(formula.left, oldVar, newVar));
  }

  return null;
}

function substituteTermInTerm(term, variable, replacement) {
  if (!term) return null;

  if (term.type === TermType.Variable) {
    return term.symbol === variable ? cloneTerm(replacement) : Term.createVariable(term.symbol);
  }

  if (term.type === TermType.Constant) return Term.createConstant(term.symbol);

  return Term.createConstant(term.symbol);
}

function substituteTermInFormula(formula, variable, replacement) {
  if (!formula) return null;

  if (formula.type === FormulaType.SentenceLetter) {
    return Formula.createSentenceLetter(formula.symbol);
  }

  if (formula.type === FormulaType.Predicate) {
    return Formula.createPredicate(
      formula.symbol,
      (formula.args || []).map((arg) => substituteTermInTerm(arg, variable, replacement))
    );
  }

  if (formula.type === FormulaType.Contradiction) {
    return Formula.createContradiction();
  }

  if (formula.type === FormulaType.Negation) {
    return Formula.createNegation(substituteTermInFormula(formula.left, variable, replacement));
  }

  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    return Formula.createBinary(
      formula.type,
      substituteTermInFormula(formula.left, variable, replacement),
      substituteTermInFormula(formula.right, variable, replacement)
    );
  }

  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    if (formula.variable === variable) {
      return formula.type === FormulaType.Universal
        ? Formula.createUniversal(formula.variable, cloneFormula(formula.left))
        : Formula.createExistential(formula.variable, cloneFormula(formula.left));
    }

    const replacementFree = freeVariablesOfTerm(replacement);

    let nextVariable = formula.variable;
    let nextBody = formula.left;

    if (replacementFree.has(formula.variable) && formulaHasFreeVariable(formula.left, variable)) {
      const fresh = chooseFreshVariableSymbol(formula.left, replacement, variable, formula.variable);

      nextBody = renameBoundOccurrencesInFormula(formula.left, formula.variable, fresh);
      nextVariable = fresh;
    }

    const substitutedBody = substituteTermInFormula(nextBody, variable, replacement);

    return formula.type === FormulaType.Universal
      ? Formula.createUniversal(nextVariable, substitutedBody)
      : Formula.createExistential(nextVariable, substitutedBody);
  }

  return null;
}

function instantiateQuantifiedFormula(quantifiedFormula, term) {
  if (
    !quantifiedFormula ||
    ![FormulaType.Universal, FormulaType.Existential].includes(quantifiedFormula.type)
  ) {
    return null;
  }

  return substituteTermInFormula(
    quantifiedFormula.left,
    quantifiedFormula.variable,
    term
  );
}

function pickFreshWitnessVariable(q, formula, goal) {
  const preferred = formula && formula.variable ? formula.variable : null;

  const openFormulas = [
    ...(q.alpha || []),
    ...(q.beta || []),
  ];

  if (preferred) {
    let blocked = false;

    for (const openFormula of openFormulas) {
      if (formulaHasFreeVariable(openFormula, preferred)) {
        blocked = true;
        break;
      }
    }

    if (!blocked && goal && formulaHasFreeVariable(goal, preferred)) {
      blocked = true;
    }

    if (!blocked) return preferred;
  }

  try {
    return chooseFreshVariableSymbol(q.alpha, q.beta, formula, goal);
  } catch (err) {
    return null;
  }
}

function alphaHasExistentialWitness(q, existentialFormula) {
  const seen = new Set();

  const variableTerms = [];

  for (const formula of q.alpha || []) {
    const terms = [];

    collectTermsFromFormula(formula, terms);

    for (const term of terms) {
      if (term.type !== TermType.Variable) continue;

      const key = term.symbol;

      if (seen.has(key)) continue;

      seen.add(key);
      variableTerms.push(term);
    }
  }

  for (const term of variableTerms) {
    const instance = instantiateQuantifiedFormula(existentialFormula, term);

    if (instance && containsFormula(q.alpha, instance)) return true;
  }

  return false;
}

function icRuleDisplayName(rule) {
  const names = {
    Leaf: "Leaf",
    Clash: "Clash",
    ContradSearch: "⊥Search",
    AndDown1: "∧↓1",
    AndDown2: "∧↓2",
    OrDown: "∨↓",
    ImpDown: "→↓",
    AndUp: "∧↑",
    OrUp1: "∨↑1",
    OrUp2: "∨↑2",
    ImpUp: "→↑",
    NegUp: "¬↑",
    ClassicalUp: "RAA",
    ForallDown: "∀↓",
    ExistsDown: "∃↓",
    ForallUp: "∀↑",
    ExistsUp: "∃↑",
    Fail: "Fail",
  };

  return names[rule] || rule;
}

function renderICTreeText(node, indent = "") {
  if (!node) return "";

  const mark = node.success ? "Y" : "N";

  const lines = [
    `${indent}${mark} [${icRuleDisplayName(node.rule)}] ${questionToString(node.question)}`
  ];

  for (const child of node.children || []) {
    lines.push(renderICTreeText(child, indent + "  "));
  }

  return lines.join("\n");
}

function renderFullICTreeText(node, indent = "") {
  if (!node) return "";

  if (node.kind === "question") {
    const lines = [
      `${indent}${node.status} [?] ${questionToString(node.question)}`
    ];

    for (const ruleNode of node.ruleNodes || []) {
      lines.push(renderFullICTreeText(ruleNode, indent + "  "));
    }

    return lines.join("\n");
  }

  if (node.kind === "rule") {
    const lines = [
      `${indent}${node.status} [${icRuleDisplayName(node.rule)}]`
    ];

    for (const childQuestion of node.children || []) {
      lines.push(renderFullICTreeText(childQuestion, indent + "  "));
    }

    return lines.join("\n");
  }

  return "";
}

function createQuestion(alpha = [], beta = [], goal = null) {
  return { alpha, beta, goal };
}

function containsFormula(xs, f) {
  if (!f) return false;

  return xs.some((x) => equalFormula(x, f));
}

function containsInAlphaBeta(q, f) {
  return containsFormula(q.alpha, f) || containsFormula(q.beta, f);
}

function addUnique(xs, f) {
  if (!containsFormula(xs, f)) xs.push(f);
}

function sequenceToString(xs) {
  return "{" + xs.map((x) => formulaToString(x)).join(", ") + "}";
}

function questionToString(q) {
  return `${sequenceToString(q.alpha)}; ${sequenceToString(q.beta)} ? ${formulaToString(q.goal)}`;
}

function questionKey(q) {
  const a = [...q.alpha].map(formulaToString).sort();

  const b = [...q.beta].map(formulaToString).sort();

  let key = "A[";

  for (const s of a) key += `(${s})`;

  key += "]B[";

  for (const s of b) key += `(${s})`;

  key += `]G[${formulaToString(q.goal)}]`;

  return key;
}

function hasClashInAlphaBeta(q) {
  const allFormulas = [...q.alpha, ...q.beta];

  for (const f of allFormulas) {
    if (!f || f.type === FormulaType.Contradiction) continue;

    if (f.type === FormulaType.Negation) {
      if (f.left && containsFormula(allFormulas, f.left)) return true;

    } else {
      if (containsFormula(allFormulas, negateFormula(f))) return true;
    }
  }

  return false;
}
function alphaBetaOrder(q) {
  const result = [];

  q.alpha.forEach((formula, index) => result.push({
    formula,
    fromAlpha: true,
    index
  }));

  q.beta.forEach((formula, index) => result.push({
    formula,
    fromAlpha: false,
    index
  }));

  return result;
}

function collectNegationBodiesFromFormula(formula, out) {
  if (!formula) return;

  if (formula.type === FormulaType.Negation) {
    if (formula.left && formula.left.type !== FormulaType.Contradiction) {
      addUnique(out, formula.left);
    }

    collectNegationBodiesFromFormula(formula.left, out);
    return;
  }

  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    collectNegationBodiesFromFormula(formula.left, out);
    collectNegationBodiesFromFormula(formula.right, out);
    return;
  }

  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    collectNegationBodiesFromFormula(formula.left, out);
  }
}

function collectContradictionCandidates(q) {
  const out = [];

  for (const f of q.alpha || []) {
    collectNegationBodiesFromFormula(f, out);
  }

  for (const f of q.beta || []) {
    collectNegationBodiesFromFormula(f, out);
  }

  if (q.goal) {
    collectNegationBodiesFromFormula(negateFormula(q.goal), out);
  }

  out.sort((a, b) => formulaToString(a).localeCompare(formulaToString(b)));
  return out;
}

function createICTreeNode(
  question,
  rule = ICRule.Fail,
  success = false,
  children = [],
  focusFormula = null,
  focusTerm = null,
  meta = {}
) {
  return { question, rule, success, children, focusFormula, focusTerm, meta };
}

function createICQuestionNode(question, status = "open", ruleNodes = [], meta = {}) {
  return {
    kind: "question",
    question,
    status,
    ruleNodes,
    meta,
  };
}

function createICRuleNode(rule, status = "open", children = [], focusFormula = null, focusTerm = null, meta = {}) {
  return {
    kind: "rule",
    rule,
    status,
    children,
    focusFormula,
    focusTerm,
    meta,
  };
}

function isICSuccess(node) {
  return node && node.status === "Y";
}

function isICFailure(node) {
  return node && node.status === "N";
}

const icTreeMetricCache = new WeakMap();

const MAX_ROOT_ATTEMPTS = 800;

const PROOF_TIME_LIMIT_MS = 10000;

const PROOF_TIMEOUT_ERROR = "PROOF_TIMEOUT";

function createProofTimeoutError() {
  const error = new Error(PROOF_TIMEOUT_ERROR);

  error.code = PROOF_TIMEOUT_ERROR;

  return error;
}

function ensureSearchNotTimedOut(options = {}) {
  if (Number.isFinite(options.deadlineMs) && performance.now() >= options.deadlineMs) {
    throw createProofTimeoutError();
  }
}

function assumptionOpeningsForRule(rule) {
  if (rule === ICRule.OrDown) return 2;

  if ([ICRule.ExistsDown, ICRule.ImpUp, ICRule.NegUp, ICRule.ClassicalUp].includes(rule)) {
    return 1;
  }

  return 0;
}

function getICTreeMetrics(node) {
  if (!node) {
    return {
      repeatedAssumptions: 0,
      contradictionSearches: 0,
      nodes: 0,
      maxDepth: 0,
      assumptionOpenings: 0,
    };
  }

  if (icTreeMetricCache.has(node)) return icTreeMetricCache.get(node);

  const metrics = {
    repeatedAssumptions: node.meta?.repeatedAssumptions || 0,
    contradictionSearches: node.rule === ICRule.ContradSearch ? 1 : 0,
    nodes: 1,
    maxDepth: 1,
    assumptionOpenings: assumptionOpeningsForRule(node.rule),
  };

  for (const child of node.children || []) {
    const childMetrics = getICTreeMetrics(child);

    metrics.repeatedAssumptions += childMetrics.repeatedAssumptions;
    metrics.contradictionSearches += childMetrics.contradictionSearches;
    metrics.nodes += childMetrics.nodes;
    metrics.assumptionOpenings += childMetrics.assumptionOpenings;
    metrics.maxDepth = Math.max(metrics.maxDepth, childMetrics.maxDepth + 1);
  }

  icTreeMetricCache.set(node, metrics);

  return metrics;
}

function compareICTreeMetrics(a, b) {
  const orderedKeys = [
    'repeatedAssumptions',
    'contradictionSearches',
    'nodes',
    'maxDepth',
    'assumptionOpenings',
  ];

  for (const key of orderedKeys) {
    const diff = a[key] - b[key];

    if (diff !== 0) return diff;
  }

  return 0;
}

function chooseBetterICTreeNode(currentBest, candidate) {
  if (!candidate || !candidate.success) return currentBest;

  if (!currentBest) return candidate;

  const currentMetrics = getICTreeMetrics(currentBest);

  const candidateMetrics = getICTreeMetrics(candidate);

  return compareICTreeMetrics(candidateMetrics, currentMetrics) < 0 ? candidate : currentBest;
}

function buildICTree(q, activeStates, failedStates, successStates = new Map(), options = {}) {
  return buildFairICTreeBasic(q, options);
}

function expandICNodeOneStep(q) {
  const results = [];

  if (containsInAlphaBeta(q, q.goal)) {
    results.push(createICTreeNode(q, ICRule.Leaf, true));
    return results;
  }

  if (q.goal && q.goal.type === FormulaType.Contradiction && hasClashInAlphaBeta(q)) {
    results.push(createICTreeNode(q, ICRule.Clash, true));
    return results;
  }

  if (q.goal && q.goal.type === FormulaType.Conjunction && q.goal.left && q.goal.right) {
    const leftQ = createQuestion(q.alpha, q.beta, q.goal.left);
    const rightQ = createQuestion(q.alpha, q.beta, q.goal.right);

    results.push(
      createICTreeNode(q, ICRule.AndUp, false, [
        createICTreeNode(leftQ),
        createICTreeNode(rightQ)
      ])
    );
  }

  if (q.goal && q.goal.type === FormulaType.Implication && q.goal.left && q.goal.right) {
    const newAlpha = [...q.alpha, q.goal.left];
    const subQ = createQuestion(newAlpha, q.beta, q.goal.right);

    results.push(
      createICTreeNode(q, ICRule.ImpUp, false, [
        createICTreeNode(subQ)
      ])
    );
  }

  if (q.goal && q.goal.type === FormulaType.Disjunction && q.goal.left && q.goal.right) {
    const leftQ = createQuestion(q.alpha, q.beta, q.goal.left);
    const rightQ = createQuestion(q.alpha, q.beta, q.goal.right);

    results.push(
      createICTreeNode(q, ICRule.OrUp1, false, [
        createICTreeNode(leftQ)
      ])
    );

    results.push(
      createICTreeNode(q, ICRule.OrUp2, false, [
        createICTreeNode(rightQ)
      ])
    );
  }

  if (q.goal && q.goal.type === FormulaType.Existential && q.goal.left) {
    const terms = collectQuestionTerms(q, q.goal);

    for (const term of terms) {
      const instance = instantiateQuantifiedFormula(q.goal, term);
      if (!instance) continue;

      const subQ = createQuestion(q.alpha, q.beta, instance);

      results.push(
        createICTreeNode(q, ICRule.ExistsUp, false, [
          createICTreeNode(subQ)
        ], q.goal, term)
      );
    }
  }

  if (q.goal && q.goal.type === FormulaType.Negation && q.goal.left) {
    const newAlpha = [...q.alpha, q.goal.left];
    const subQ = createQuestion(newAlpha, q.beta, Formula.createContradiction());

    results.push(
      createICTreeNode(q, ICRule.NegUp, false, [
        createICTreeNode(subQ)
      ])
    );
  }

  if (
    q.goal &&
    q.goal.type !== FormulaType.Contradiction &&
    q.goal.type !== FormulaType.Negation
  ) {
    const negGoal = negateFormula(q.goal);
    const newAlpha = [...q.alpha];
    addUnique(newAlpha, negGoal);

    const subQ = createQuestion(newAlpha, q.beta, Formula.createContradiction());

    const repeatedAssumptions = containsInAlphaBeta(q, negGoal) ? 1 : 0;

    results.push(
      createICTreeNode(q, ICRule.ClassicalUp, false, [
        createICTreeNode(subQ)
      ], null, null, { repeatedAssumptions })
    );
  }

  if (q.goal && q.goal.type === FormulaType.Universal && q.goal.left) {
    const blockedVars = collectOpenFreeVariableSymbols(q);

    const freshVar = chooseFreshVariableSymbol(q.alpha, q.beta, q.goal);

    if (blockedVars.has(freshVar)) {
    } else {
      const witnessTerm = Term.createVariable(freshVar);
      const instance = instantiateQuantifiedFormula(q.goal, witnessTerm);

      if (instance) {
        const subQ = createQuestion(q.alpha, q.beta, instance);

        results.push(
          createICTreeNode(q, ICRule.ForallUp, false, [
            createICTreeNode(subQ)
          ], q.goal, witnessTerm)
        );
      }
    }
  }

  for (const f of q.alpha) {
    if (f.type !== FormulaType.Conjunction) continue;

    if (!containsFormula(q.alpha, f.left)) {
      const newAlpha = [...q.alpha];
      addUnique(newAlpha, f.left);

      const subQ = createQuestion(newAlpha, q.beta, q.goal);

      results.push(
        createICTreeNode(q, ICRule.AndDown1, false, [
          createICTreeNode(subQ)
        ], f)
      );
    }

    if (!containsFormula(q.alpha, f.right)) {
      const newAlpha = [...q.alpha];
      addUnique(newAlpha, f.right);

      const subQ = createQuestion(newAlpha, q.beta, q.goal);

      results.push(
        createICTreeNode(q, ICRule.AndDown2, false, [
          createICTreeNode(subQ)
        ], f)
      );
    }
  }

  for (const f of q.alpha) {
    if (f.type !== FormulaType.Implication) continue;

    const antecedent = f.left;
    const consequent = f.right;

    if (!antecedent || !consequent) continue;
    if (containsFormula(q.alpha, consequent)) continue;

    const antecedentQ = createQuestion(q.alpha, q.beta, antecedent);

    const newAlpha = [...q.alpha];
    addUnique(newAlpha, consequent);

    const goalQ = createQuestion(newAlpha, q.beta, q.goal);

    results.push(
      createICTreeNode(q, ICRule.ImpDown, false, [
        createICTreeNode(antecedentQ),
        createICTreeNode(goalQ)
      ], f)
    );
  }

  for (const f of q.alpha) {
    if (f.type !== FormulaType.Disjunction) continue;

    const left = f.left;
    const right = f.right;

    if (!left || !right) continue;

    const leftAlpha = [...q.alpha, left];
    const rightAlpha = [...q.alpha, right];

    const leftQ = createQuestion(leftAlpha, q.beta, q.goal);
    const rightQ = createQuestion(rightAlpha, q.beta, q.goal);

    results.push(
      createICTreeNode(q, ICRule.OrDown, false, [
        createICTreeNode(leftQ),
        createICTreeNode(rightQ)
      ], f)
    );
  }

  for (const f of q.alpha) {
    if (f.type !== FormulaType.Universal) continue;

    const terms = collectQuestionTerms(q, f);

    for (const term of terms) {
      const instance = instantiateQuantifiedFormula(f, term);
      if (!instance) continue;
      if (containsFormula(q.alpha, instance)) continue;

      const newAlpha = [...q.alpha];
      addUnique(newAlpha, instance);

      const subQ = createQuestion(newAlpha, q.beta, q.goal);

      results.push(
        createICTreeNode(q, ICRule.ForallDown, false, [
          createICTreeNode(subQ)
        ], f, term)
      );
    }
  }

  for (const f of q.alpha) {
    if (f.type !== FormulaType.Existential) continue;

    if (alphaHasExistentialWitness(q, f)) continue;

    const witnessVar = pickFreshWitnessVariable(q, f, q.goal);
    if (!witnessVar) continue;

    const witnessTerm = Term.createVariable(witnessVar);
    const instance = instantiateQuantifiedFormula(f, witnessTerm);
    if (!instance) continue;

    const newAlpha = [...q.alpha, instance];
    const subQ = createQuestion(newAlpha, q.beta, q.goal);

    results.push(
      createICTreeNode(q, ICRule.ExistsDown, false, [
        createICTreeNode(subQ)
      ], f, witnessTerm)
    );
  }

  if (q.goal && q.goal.type === FormulaType.Contradiction) {
    const candidates = collectContradictionCandidates(q);

    for (const phi of candidates) {
      if (containsInAlphaBeta(q, phi) && containsInAlphaBeta(q, negateFormula(phi))) continue;

      const leftQ = createQuestion(q.alpha, q.beta, phi);
      const rightQ = createQuestion(q.alpha, q.beta, negateFormula(phi));

      results.push(
        createICTreeNode(q, ICRule.ContradSearch, false, [
          createICTreeNode(leftQ),
          createICTreeNode(rightQ)
        ], phi)
      );
    }
  }

  return results;
}

function expandICQuestionOneStep(q) {
  const oldCandidates = expandICNodeOneStep(q);
  const ruleNodes = [];

  for (const candidate of oldCandidates) {
    const childQuestionNodes = (candidate.children || []).map((child) =>
      createICQuestionNode(child.question, "open", [], {
        sourceRule: candidate.rule,
      })
    );

    const status = candidate.success ? "Y" : "open";

    ruleNodes.push(
      createICRuleNode(
        candidate.rule,
        status,
        childQuestionNodes,
        candidate.focusFormula,
        candidate.focusTerm,
        candidate.meta || {}
      )
    );
  }

  let questionStatus = "open";

  if (ruleNodes.some((ruleNode) => ruleNode.status === "Y")) {
    questionStatus = "Y";
  } else if (ruleNodes.length === 0) {
    questionStatus = "N";
  }

  return createICQuestionNode(q, questionStatus, ruleNodes);
}

function closeICRuleNodeAtDepth(ruleNode, depth, path, options = {}) {
  ensureSearchNotTimedOut(options);

  if (!ruleNode) return createICRuleNode(ICRule.Fail, "N");

  if (ruleNode.status === "Y") return ruleNode;

  if (depth <= 0) {
    return createICRuleNode(
      ruleNode.rule,
      "N",
      ruleNode.children || [],
      ruleNode.focusFormula,
      ruleNode.focusTerm,
      ruleNode.meta || {}
    );
  }

  const closedChildren = [];

  for (const childQuestion of ruleNode.children || []) {
    const closedChild = closeICQuestionAtDepth(
      childQuestion.question,
      depth - 1,
      path,
      options
    );

    closedChildren.push(closedChild);
  }

  const allChildrenSuccess =
    closedChildren.length > 0 &&
    closedChildren.every((child) => child.status === "Y");

  return createICRuleNode(
    ruleNode.rule,
    allChildrenSuccess ? "Y" : "N",
    closedChildren,
    ruleNode.focusFormula,
    ruleNode.focusTerm,
    ruleNode.meta || {}
  );
}

function closeICQuestionAtDepth(q, depth, path, options = {}) {
  ensureSearchNotTimedOut(options);

  const key = questionKey(q);

  if (path.has(key)) {
    return createICQuestionNode(q, "N", [], {
      closedBy: "repeat",
    });
  }

  if (depth < 0) {
    return createICQuestionNode(q, "N", [], {
      closedBy: "depth",
    });
  }

  path.add(key);

  const expanded = expandICQuestionOneStep(q);
  const closedRuleNodes = [];

  for (const ruleNode of expanded.ruleNodes || []) {
    const closedRuleNode = closeICRuleNodeAtDepth(
      ruleNode,
      depth,
      path,
      options
    );

    closedRuleNodes.push(closedRuleNode);
  }

  path.delete(key);

  let status = "N";

  if (closedRuleNodes.some((ruleNode) => ruleNode.status === "Y")) {
    status = "Y";
  }

  return createICQuestionNode(q, status, closedRuleNodes);
}

function extractSuccessfulICDerivation(questionNode) {
  if (!questionNode || questionNode.kind !== "question") return null;
  if (questionNode.status !== "Y") return null;

  const successfulRule = (questionNode.ruleNodes || []).find((ruleNode) => ruleNode.status === "Y");
  if (!successfulRule) return null;

  const oldChildren = [];

  for (const childQuestion of successfulRule.children || []) {
    const childDerivation = extractSuccessfulICDerivation(childQuestion);
    if (!childDerivation) return null;
    oldChildren.push(childDerivation);
  }

  return createICTreeNode(
    questionNode.question,
    successfulRule.rule,
    true,
    oldChildren,
    successfulRule.focusFormula,
    successfulRule.focusTerm,
    successfulRule.meta || {}
  );
}

function solveICTreeCandidateAtDepth(node, depth, path, options = {}) {
  ensureSearchNotTimedOut(options);

  if (!node) return null;
  if (node.success) return node;
  if (depth <= 0) return createICTreeNode(node.question, node.rule, false, node.children, node.focusFormula, node.focusTerm, node.meta);

  const solvedChildren = [];

  for (const child of node.children || []) {
    const solvedChild = solveICTreeAtDepth(child.question, depth - 1, path, options);
    solvedChildren.push(solvedChild);
  }

  let success = false;

  switch (node.rule) {
    case ICRule.AndUp:
      success = solvedChildren.length === 2 && solvedChildren[0].success && solvedChildren[1].success;
      break;

    case ICRule.ImpDown:
    case ICRule.OrDown:
      success = solvedChildren.length === 2 && solvedChildren[0].success && solvedChildren[1].success;
      break;

    case ICRule.ImpUp:
    case ICRule.OrUp1:
    case ICRule.OrUp2:
    case ICRule.NegUp:
    case ICRule.ClassicalUp:  
    case ICRule.AndDown1:
    case ICRule.AndDown2:
    case ICRule.ForallDown:
    case ICRule.ExistsDown:
    case ICRule.ForallUp:
    case ICRule.ExistsUp:  
      success = solvedChildren.length === 1 && solvedChildren[0].success;
      break;

    default:
      success = false;
  }

  return createICTreeNode(
    node.question,
    node.rule,
    success,
    solvedChildren,
    node.focusFormula,
    node.focusTerm,
    node.meta
  );
}

function solveICTreeAtDepth(q, depth, path, options = {}) {
  ensureSearchNotTimedOut(options);

  const key = questionKey(q);

  if (path.has(key)) {
    return createICTreeNode(q, ICRule.Fail, false);
  }

  path.add(key);

  const candidates = expandICNodeOneStep(q);
  let best = null;

  for (const candidate of candidates) {
    const solved = solveICTreeCandidateAtDepth(candidate, depth, path, options);

    if (solved && solved.success) {
      best = chooseBetterICTreeNode(best, solved);
    }
  }

  path.delete(key);

  return best || createICTreeNode(q, ICRule.Fail, false);
}
function buildFairICTreeBasic(q, options = {}) {
  ensureSearchNotTimedOut(options);

  const maxDepth = Number.isFinite(options.maxDepth)
    ? Math.max(1, Math.floor(options.maxDepth))
    : 1000;

  for (let depth = 0; depth <= maxDepth; depth++) {
    const fullTree = closeICQuestionAtDepth(q, depth, new Set(), options);

    if (fullTree.status === "Y") {
      const derivation = extractSuccessfulICDerivation(fullTree);

    if (derivation && derivation.success) {
      derivation.meta = {
     ...(derivation.meta || {}),
     fullTree,
     };

  return derivation;
}
    }
  }

  return createICTreeNode(q, ICRule.Fail, false);
}

function createNDProofNode({
  formula = null,
  reason = "",
  parent1 = null,
  parent2 = null,
  subAssumption1 = null,
  subEnd1 = null,
  subAssumption2 = null,
  subEnd2 = null
} = {}) {
  return {
    id: nextNodeId++,
    formula,
    reason,
    parent1,
    parent2,
    subAssumption1,
    subEnd1,
    subAssumption2,
    subEnd2,
  };
}

function findProofWithFormula(ctx, target) {
  for (let i = ctx.length - 1; i >= 0; i--) {
    if (equalFormula(ctx[i].formula, target)) return ctx[i];
  }
  return null;
}

function findClashWitnessInContext(ctx) {
  for (let i = ctx.length - 1; i >= 0; i--) {
    const node = ctx[i];
    const f = node.formula;

    if (!f || f.type === FormulaType.Contradiction) continue;

    if (f.type === FormulaType.Negation) {
      const pos = findProofWithFormula(ctx, f.left);
      if (pos) return [pos, node];

    } else {
      const negNode = findProofWithFormula(ctx, negateFormula(f));
      if (negNode) return [node, negNode];
    }
  }

  return [null, null];
}

function makeSimpleNode(formula, reason) {
  return createNDProofNode({ formula, reason });
}

function makeUnaryNode(formula, reason, p1) {
  return createNDProofNode({ formula, reason, parent1: p1 });
}

function makeBinaryNode(formula, reason, p1, p2) {
  return createNDProofNode({ formula, reason, parent1: p1, parent2: p2 });
}

function makeContradictionNode(positive, negative) {
  return makeBinaryNode(Formula.createContradiction(), "~E", positive, negative);
}

function addProofNodeUniqueByFormula(xs, node) {
  if (!node || !node.formula) return false;

  if (findProofWithFormula(xs, node.formula)) return false;

  xs.push(node);
  return true;
}

function extractNDProof(icNode, ctx) {
  if (!icNode || !icNode.success) return null;

  switch (icNode.rule) {
    case ICRule.Leaf:
      return findProofWithFormula(ctx, icNode.question.goal);

    case ICRule.Clash: {
      const [pos, neg] = findClashWitnessInContext(ctx);
      if (!pos || !neg) return null;
      return makeContradictionNode(pos, neg);
    }

    case ICRule.ContradSearch: {
      const leftProof = extractNDProof(icNode.children[0], ctx);
      if (!leftProof) return null;

      const rightProof = extractNDProof(icNode.children[1], ctx);
      if (!rightProof) return null;

      return makeContradictionNode(leftProof, rightProof);
    }

    case ICRule.AndDown1: {
      const source = findProofWithFormula(ctx, icNode.focusFormula);

      if (!source || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Conjunction) return null;

      const derivedFormula = icNode.focusFormula.left;
      if (!derivedFormula) return null;

      const derived = makeUnaryNode(derivedFormula, "&E", source);
      const nextCtx = [...ctx, derived];

      return extractNDProof(icNode.children[0], nextCtx);
    }

    case ICRule.AndDown2: {
      const source = findProofWithFormula(ctx, icNode.focusFormula);

      if (!source || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Conjunction) return null;

      const derivedFormula = icNode.focusFormula.right;
      if (!derivedFormula) return null;

      const derived = makeUnaryNode(derivedFormula, "&E", source);
      const nextCtx = [...ctx, derived];

      return extractNDProof(icNode.children[0], nextCtx);
    }

    case ICRule.ForallDown: {
      const source = findProofWithFormula(ctx, icNode.focusFormula);

      if (
        !source ||
        !icNode.focusFormula ||
        icNode.focusFormula.type !== FormulaType.Universal ||
        !icNode.focusTerm
      ) {
        return null;
      }

      const derivedFormula = instantiateQuantifiedFormula(icNode.focusFormula, icNode.focusTerm);
      if (!derivedFormula) return null;

      const derived = makeUnaryNode(derivedFormula, "∀E", source);
      const nextCtx = [...ctx, derived];

      return extractNDProof(icNode.children[0], nextCtx);
    }

    case ICRule.ImpDown: {
      const implicationNode = findProofWithFormula(ctx, icNode.focusFormula);

      if (!implicationNode || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Implication) return null;

      const antecedentProof = extractNDProof(icNode.children[0], ctx);
      if (!antecedentProof) return null;

      const consequent = icNode.focusFormula.right;
      if (!consequent) return null;

      const consequentNode = makeBinaryNode(consequent, "->E", implicationNode, antecedentProof);
      const nextCtx = [...ctx, consequentNode];

      return extractNDProof(icNode.children[1], nextCtx);
    }

    case ICRule.OrDown: {
      const disjunctionNode = findProofWithFormula(ctx, icNode.focusFormula);

      if (!disjunctionNode || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Disjunction) return null;

      const leftAssumptionFormula = icNode.focusFormula.left;
      const rightAssumptionFormula = icNode.focusFormula.right;

      if (!leftAssumptionFormula || !rightAssumptionFormula) return null;

      const leftAssumption = makeSimpleNode(leftAssumptionFormula, "Assumption");
      const leftCtx = [...ctx, leftAssumption];
      const leftEnd = extractNDProof(icNode.children[0], leftCtx);
      if (!leftEnd) return null;

      const rightAssumption = makeSimpleNode(rightAssumptionFormula, "Assumption");
      const rightCtx = [...ctx, rightAssumption];
      const rightEnd = extractNDProof(icNode.children[1], rightCtx);
      if (!rightEnd) return null;

      return createNDProofNode({
        formula: icNode.question.goal,
        reason: "∨E",
        parent1: disjunctionNode,
        subAssumption1: leftAssumption,
        subEnd1: leftEnd,
        subAssumption2: rightAssumption,
        subEnd2: rightEnd,
      });
    }

    case ICRule.ExistsDown: {
      const source = findProofWithFormula(ctx, icNode.focusFormula);

      if (
        !source ||
        !icNode.focusFormula ||
        icNode.focusFormula.type !== FormulaType.Existential ||
        !icNode.focusTerm
      ) {
        return null;
      }

      const assumptionFormula = instantiateQuantifiedFormula(icNode.focusFormula, icNode.focusTerm);
      if (!assumptionFormula) return null;

      const assumption = makeSimpleNode(assumptionFormula, "Assumption");
      const nextCtx = [...ctx, assumption];

      const body = extractNDProof(icNode.children[0], nextCtx);
      if (!body) return null;

      return createNDProofNode({
        formula: icNode.question.goal,
        reason: "∃E",
        parent1: source,
        subAssumption1: assumption,
        subEnd1: body,
      });
    }

    case ICRule.AndUp: {
      const leftProof = extractNDProof(icNode.children[0], ctx);
      if (!leftProof) return null;

      const rightProof = extractNDProof(icNode.children[1], ctx);
      if (!rightProof || !icNode.question.goal) return null;

      return makeBinaryNode(icNode.question.goal, "&I", leftProof, rightProof);
    }

    case ICRule.OrUp1: {
      const leftProof = extractNDProof(icNode.children[0], ctx);
      if (!leftProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∨I 1", leftProof);
    }

    case ICRule.OrUp2: {
      const rightProof = extractNDProof(icNode.children[0], ctx);
      if (!rightProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∨I 2", rightProof);
    }

    case ICRule.ImpUp: {
      if (!icNode.question.goal || icNode.question.goal.type !== FormulaType.Implication || !icNode.question.goal.left) {
        return null;
      }

      const assumption = makeSimpleNode(icNode.question.goal.left, "Assumption");
      const nextCtx = [...ctx, assumption];

      const body = extractNDProof(icNode.children[0], nextCtx);
      if (!body) return null;

      return createNDProofNode({
        formula: icNode.question.goal,
        reason: "->I",
        subAssumption1: assumption,
        subEnd1: body,
      });
    }

    case ICRule.ForallUp: {
      const bodyProof = extractNDProof(icNode.children[0], ctx);
      if (!bodyProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∀I", bodyProof);
    }

    case ICRule.ExistsUp: {
      const witnessProof = extractNDProof(icNode.children[0], ctx);
      if (!witnessProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∃I", witnessProof);
    }

    case ICRule.NegUp: {
      if (!icNode.question.goal || icNode.question.goal.type !== FormulaType.Negation || !icNode.question.goal.left) {
        return null;
      }

      const assumption = makeSimpleNode(icNode.question.goal.left, "Assumption");
      const nextCtx = [...ctx, assumption];

      const contradiction =
       extractNDProof(icNode.children[0], nextCtx);

      if (!contradiction) return null;

      return createNDProofNode({
        formula: icNode.question.goal,
        reason: "~I",
        subAssumption1: assumption,
        subEnd1: contradiction,
      });
    }

    case ICRule.ClassicalUp: {
      if (!icNode.question.goal) return null;

      const negGoal = negateFormula(icNode.question.goal);
      const assumption = makeSimpleNode(negGoal, "Assumption");
      const nextCtx = [...ctx, assumption];

     const contradiction =
      extractNDProof(icNode.children[0], nextCtx);

      if (!contradiction) return null;

      return createNDProofNode({
        formula: icNode.question.goal,
        reason: "RAA",
        subAssumption1: assumption,
        subEnd1: contradiction,
      });
    }

    default:
      return null;
  }
}

function solveProofData(premisesInput, conclusionInput, signature) {
  premisesInput = premisesInput.trim();

  conclusionInput = conclusionInput.trim();

  const parsedPremises = parsePremises(premisesInput, signature);

  const conclusion = parseSingleFormula(conclusionInput, signature);

  const premises = parsedPremises;

  const rootCtx = [];

  for (const premise of premises) {
    rootCtx.push(createNDProofNode({ formula: premise, reason: "Premise" }));
  }

  const root = createQuestion([...premises], [], conclusion);

  const activeStates = new Set();

  const failedStates = new Set();

  let tree;

  try {
    tree = buildICTree(root, activeStates, failedStates, new Map(), {
      maxRootAttempts: MAX_ROOT_ATTEMPTS,
      deadlineMs: performance.now() + PROOF_TIME_LIMIT_MS,
    });
  } catch (err) {
    if (err && err.code === PROOF_TIMEOUT_ERROR) {
      const timeoutParts = [];

      timeoutParts.push("=== 구문 확인 ===");

      timeoutParts.push(`전제: ${parsedPremises.length > 0 ? parsedPremises.map(formulaToDisplayString).join(", ") : "(없음)"}`);

      timeoutParts.push(`결론: ${formulaToDisplayString(conclusion)}`);

      timeoutParts.push("");

      timeoutParts.push("=== 결과 ===");

      timeoutParts.push(`제한시간 안에 증명을 생성하지 못했습니다. (${PROOF_TIME_LIMIT_MS / 1000}초)`);

      timeoutParts.push("");

      return {
        text: timeoutParts.join("\n"),
        fitchLines: null,
        tree: null,
        timedOut: true
      };
    }

    throw err;
  }

  const parts = [];

  parts.push("=== 구문 확인 ===");

  parts.push(`전제: ${parsedPremises.length > 0 ? parsedPremises.map(formulaToDisplayString).join(", ") : "(없음)"}`);

  parts.push(`결론: ${formulaToDisplayString(conclusion)}`);

  parts.push("");

  parts.push("=== IC Tree ===");

   if (tree.meta && tree.meta.fullTree) {
  parts.push(renderFullICTreeText(tree.meta.fullTree));
     } else {
     parts.push(renderICTreeText(tree));
}

  parts.push("");

  parts.push("=== 결과 ===");

  parts.push(tree.success ? "Y" : "N");

  parts.push("");

  if (!tree.success) {
    return { text: parts.join("\n"), fitchLines: null, tree };
  }

  const ndRoot = extractNDProof(tree, rootCtx);

  if (!ndRoot) {
    parts.push("추출 실패");
    return { text: parts.join("\n"), fitchLines: null, tree };
  }

  const fitchLines = buildFitchLines(ndRoot, rootCtx);

  return { text: parts.join("\n"), fitchLines, tree };
}

const premisesEl = document.getElementById("premises");

const conclusionEl = document.getElementById("conclusion");

const outputEl = document.getElementById("output");

const proofBtn = document.getElementById("proofBtn");

const clearBtn = document.getElementById("clearBtn");

const stripeToggleBtn = document.getElementById("stripeToggleBtn");

const themeToggleBtn = document.getElementById("themeToggleBtn");

const symbolButtons = document.querySelectorAll("[data-symbol]");

let lastFocused = premisesEl;

let zebraStripingEnabled = true;

window.zebraStripingEnabled = zebraStripingEnabled;

let lightThemeEnabled = true;

premisesEl.addEventListener("focus", () => {
  lastFocused = premisesEl;
});

conclusionEl.addEventListener("focus", () => {
  lastFocused = conclusionEl;
});

symbolButtons.forEach((button) => {
  button.addEventListener("click", () => {
    const symbol = button.getAttribute("data-symbol");

    const target = lastFocused || premisesEl;

    target.focus();

    const start = target.selectionStart ?? target.value.length;

    const end = target.selectionEnd ?? target.value.length;

    const value = target.value;

    target.value = value.slice(0, start) + symbol + value.slice(end);

    target.selectionStart = target.selectionEnd = start + symbol.length;
  });
});

function readCurrentSignature() {
  return buildSignature();
}

proofBtn.addEventListener("click", () => {
  try {
    const premiseText = premisesEl.value.trim();

    const conclusionText = conclusionEl.value.trim();

    if (!conclusionText) {
      outputEl.className = "output error";
      outputEl.textContent = "결론을 입력해 주세요.";
      return;
    }

    const signature = readCurrentSignature();

    const result = solveProofData(premiseText, conclusionText, signature);

    outputEl.className = "output";

    outputEl.innerHTML = renderProofResult(result);
  } catch (err) {
    outputEl.className = "output error";
    outputEl.textContent = "식 입력이 잘못됐습니다 or 현재 버전에서 증명을 찾지 못했습니다";
  }
});

stripeToggleBtn.addEventListener("click", () => {
  zebraStripingEnabled = !zebraStripingEnabled;

  window.zebraStripingEnabled = zebraStripingEnabled;

  stripeToggleBtn.textContent = `줄 구분: ${zebraStripingEnabled ? "켜짐" : "꺼짐"}`;

  const proofEl = outputEl.querySelector(".fitch-proof");

  if (proofEl) {
    proofEl.classList.toggle("zebra-on", zebraStripingEnabled);
    proofEl.classList.toggle("zebra-off", !zebraStripingEnabled);
  }
});

themeToggleBtn.addEventListener("click", () => {
  lightThemeEnabled = !lightThemeEnabled;

  document.body.classList.toggle("light-theme", lightThemeEnabled);

  themeToggleBtn.textContent = `화면 테마: ${lightThemeEnabled ? "라이트" : "다크"}`;
});

clearBtn.addEventListener("click", () => {
  premisesEl.value = "";

  conclusionEl.value = "";

  outputEl.className = "output";

  outputEl.innerHTML = "이곳에 결과가 표시됩니다.";

  premisesEl.focus();

  lastFocused = premisesEl;
});
