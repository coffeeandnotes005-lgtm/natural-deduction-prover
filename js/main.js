
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
      ExistsNegFromNegForall: "ExistsNegFromNegForall",
      ForallFromNegExistsNeg: "ForallFromNegExistsNeg",
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
      if (formula.type === FormulaType.SentenceLetter) return Formula.createSentenceLetter(formula.symbol);
      if (formula.type === FormulaType.Predicate) return Formula.createPredicate(formula.symbol, (formula.args || []).map(cloneTerm));
      if (formula.type === FormulaType.Contradiction) return Formula.createContradiction();
      if (formula.type === FormulaType.Negation) return Formula.createNegation(cloneFormula(formula.left));
      if (formula.type === FormulaType.Universal) return Formula.createUniversal(formula.variable, cloneFormula(formula.left));
      if (formula.type === FormulaType.Existential) return Formula.createExistential(formula.variable, cloneFormula(formula.left));
      return Formula.createBinary(formula.type, cloneFormula(formula.left), cloneFormula(formula.right));
    }

    function collectTermsFromTerm(term, out) {
      if (!term) return;
      out.push(cloneTerm(term));
      for (const arg of term.args || []) collectTermsFromTerm(arg, out);
    }

    function collectTermsFromFormula(formula, out) {
      if (!formula) return;
      if (formula.type === FormulaType.Predicate) {
        for (const arg of formula.args || []) collectTermsFromTerm(arg, out);
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
      for (const f of q.alpha) collectTermsFromFormula(f, raw);
      for (const f of q.beta) collectTermsFromFormula(f, raw);
      collectTermsFromFormula(q.goal, raw);
      collectTermsFromFormula(extraFormula, raw);
      if (extraFormula && [FormulaType.Universal, FormulaType.Existential].includes(extraFormula.type) && extraFormula.variable) {
        raw.push(Term.createVariable(extraFormula.variable));
      }
      if (extraTerm) raw.push(cloneTerm(extraTerm));
      return uniqueTermsPreserveOrder(raw);
    }

    function collectVariableSymbolsFromTerm(term, out) {
      if (!term) return;
      if (term.type === TermType.Variable) out.add(term.symbol);
      for (const arg of term.args || []) collectVariableSymbolsFromTerm(arg, out);
    }

    function collectVariableSymbolsFromFormula(formula, out) {
      if (!formula) return;
      if (formula.variable) out.add(formula.variable);
      if (formula.type === FormulaType.Predicate) {
        for (const arg of formula.args || []) collectVariableSymbolsFromTerm(arg, out);
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
      for (const arg of term.args || []) collectFreeVariablesTerm(arg, out);
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
      if (formula.type === FormulaType.SentenceLetter) return Formula.createSentenceLetter(formula.symbol);
      if (formula.type === FormulaType.Predicate) {
        return Formula.createPredicate(formula.symbol, (formula.args || []).map((arg) => renameBoundOccurrencesInTerm(arg, oldVar, newVar)));
      }
      if (formula.type === FormulaType.Contradiction) return Formula.createContradiction();
      if (formula.type === FormulaType.Negation) return Formula.createNegation(renameBoundOccurrencesInFormula(formula.left, oldVar, newVar));
      if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
        return Formula.createBinary(formula.type, renameBoundOccurrencesInFormula(formula.left, oldVar, newVar), renameBoundOccurrencesInFormula(formula.right, oldVar, newVar));
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
      if (formula.type === FormulaType.SentenceLetter) return Formula.createSentenceLetter(formula.symbol);
      if (formula.type === FormulaType.Predicate) {
        return Formula.createPredicate(formula.symbol, (formula.args || []).map((arg) => substituteTermInTerm(arg, variable, replacement)));
      }
      if (formula.type === FormulaType.Contradiction) return Formula.createContradiction();
      if (formula.type === FormulaType.Negation) return Formula.createNegation(substituteTermInFormula(formula.left, variable, replacement));
      if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
        return Formula.createBinary(formula.type, substituteTermInFormula(formula.left, variable, replacement), substituteTermInFormula(formula.right, variable, replacement));
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
      if (!quantifiedFormula || ![FormulaType.Universal, FormulaType.Existential].includes(quantifiedFormula.type)) return null;
      return substituteTermInFormula(quantifiedFormula.left, quantifiedFormula.variable, term);
    }

    function pickFreshWitnessVariable(q, formula, goal) {
      const preferred = formula && formula.variable ? formula.variable : null;
      if (preferred) {
        let blocked = false;
        for (const alphaFormula of q.alpha || []) {
          if (formulaHasFreeVariable(alphaFormula, preferred)) {
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
        return chooseFreshVariableSymbol(q.alpha, formula, goal);
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
      const lines = [`${indent}${mark} [${icRuleDisplayName(node.rule)}] ${questionToString(node.question)}`];
      for (const child of node.children || []) {
        lines.push(renderICTreeText(child, indent + "  "));
      }
      return lines.join("\n");
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
      q.alpha.forEach((formula, index) => result.push({ formula, fromAlpha: true, index }));
      q.beta.forEach((formula, index) => result.push({ formula, fromAlpha: false, index }));
      return result;
    }

    function collectContradictionCandidates(q) {
      const out = [];
      q.alpha.forEach((f) => collectSubformulas(f, out));
      q.beta.forEach((f) => collectSubformulas(f, out));
      if (q.goal) collectSubformulas(q.goal, out);

      const filtered = out.filter((f) => f && f.type !== FormulaType.Contradiction);
      filtered.sort((a, b) => formulaToString(a).localeCompare(formulaToString(b)));

      const unique = [];
      for (const f of filtered) {
        if (!containsFormula(unique, f)) unique.push(f);
      }
      return unique;
    }
    function findNegatedUniversalSourceForExistsNegGoal(formulas, goal) {
      if (!goal || goal.type !== FormulaType.Existential || !goal.left || goal.left.type !== FormulaType.Negation) return null;
      for (const f of formulas || []) {
        if (!f || f.type !== FormulaType.Negation) continue;
        const universal = f.left;
        if (!universal || universal.type !== FormulaType.Universal) continue;
        const fresh = chooseFreshVariableSymbol(f, goal);
        const term = Term.createVariable(fresh);
        const universalInstance = instantiateQuantifiedFormula(universal, term);
        const existsInstance = instantiateQuantifiedFormula(goal, term);
        if (!universalInstance || !existsInstance || existsInstance.type !== FormulaType.Negation) continue;
        if (equalFormula(universalInstance, existsInstance.left)) {
          return { source: f, universal, freshVar: fresh };
        }
      }
      return null;
    }
    function findNegatedExistentialSourceForUniversalGoal(formulas, goal) {
      if (!goal || goal.type !== FormulaType.Universal) return null;
      for (const f of formulas || []) {
        if (!f || f.type !== FormulaType.Negation) continue;
        const existential = f.left;
        if (!existential || existential.type !== FormulaType.Existential || !existential.left || existential.left.type !== FormulaType.Negation) continue;
        const fresh = chooseFreshVariableSymbol(f, goal);
        const term = Term.createVariable(fresh);
        const goalInstance = instantiateQuantifiedFormula(goal, term);
        const existsInstance = instantiateQuantifiedFormula(existential, term);
        if (!goalInstance || !existsInstance || existsInstance.type !== FormulaType.Negation) continue;
        if (equalFormula(goalInstance, existsInstance.left)) {
          return { source: f, existential, freshVar: fresh };
        }
      }
      return null;
    }


    function createICTreeNode(question, rule = ICRule.Fail, success = false, children = [], focusFormula = null, focusTerm = null, meta = {}) {
      return { question, rule, success, children, focusFormula, focusTerm, meta };
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
      if ([ICRule.ExistsDown, ICRule.ImpUp, ICRule.NegUp, ICRule.ClassicalUp].includes(rule)) return 1;
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
    function buildICTreeFirstSuccess(q, activeStates, failedStates, successStates = new Map(), options = {}) {
      ensureSearchNotTimedOut(options);
      const key = questionKey(q);
      if (successStates.has(key)) return successStates.get(key);
      if (failedStates.has(key)) return createICTreeNode(q, ICRule.Fail, false);
      if (activeStates.has(key)) return createICTreeNode(q, ICRule.Fail, false);

      activeStates.add(key);
      let bestNode = null;
      function considerCandidate(rule, children = [], focusFormula = null, focusTerm = null, meta = {}) {
        const candidate = createICTreeNode(q, rule, true, children, focusFormula, focusTerm, meta);
        bestNode = chooseBetterICTreeNode(bestNode, candidate);
      }

      if (containsInAlphaBeta(q, q.goal)) {
        bestNode = createICTreeNode(q, ICRule.Leaf, true);
      }

      if (!bestNode) {
        const sourceInfo = findNegatedUniversalSourceForExistsNegGoal(q.alpha, q.goal);
        if (sourceInfo) {
          considerCandidate(ICRule.ExistsNegFromNegForall, [], sourceInfo.source, Term.createVariable(sourceInfo.freshVar));
        }
      }

      if (!bestNode) {
        const sourceInfo = findNegatedExistentialSourceForUniversalGoal(q.alpha, q.goal);
        if (sourceInfo) {
          considerCandidate(ICRule.ForallFromNegExistsNeg, [], sourceInfo.source, Term.createVariable(sourceInfo.freshVar));
        }
      }

      const ordered = alphaBetaOrder(q);

      if (!bestNode) {
        for (const occ of ordered) {
          const f = occ.formula;
          if (!f || f.type !== FormulaType.Conjunction) continue;
          const leftPart = f.left;
          if (!leftPart || containsInAlphaBeta(q, leftPart)) continue;

          const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(childQ.beta, leftPart);
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (child.success) {
            considerCandidate(ICRule.AndDown1, [child], f);
          }
        }
      }

      if (!bestNode) {
        for (const occ of ordered) {
          const f = occ.formula;
          if (!f || f.type !== FormulaType.Conjunction) continue;
          const rightPart = f.right;
          if (!rightPart || containsInAlphaBeta(q, rightPart)) continue;

          const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(childQ.beta, rightPart);
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (child.success) {
            considerCandidate(ICRule.AndDown2, [child], f);
          }
        }
      }

      if (!bestNode) {
        for (const occ of ordered) {
          const f = occ.formula;
          if (!f || f.type !== FormulaType.Universal) continue;
          const termCandidates = collectQuestionTerms(q, f);
          for (const term of termCandidates) {
            const instantiated = instantiateQuantifiedFormula(f, term);
            if (!instantiated || containsInAlphaBeta(q, instantiated)) continue;
            const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
            addUnique(childQ.beta, instantiated);
            const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
            if (child.success) {
              considerCandidate(ICRule.ForallDown, [child], f, term);
            }
          }
        }
      }

      if (!bestNode) {
        for (const occ of ordered) {
          const f = occ.formula;
          if (!f || f.type !== FormulaType.Implication) continue;
          const antecedent = f.left;
          const consequent = f.right;
          if (!antecedent || !consequent) continue;
          if (equalFormula(antecedent, q.goal)) continue;
          if (containsInAlphaBeta(q, consequent)) continue;

          const leftQ = createQuestion([...q.alpha], [...q.beta], antecedent);
          const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(rightQ.beta, consequent);

          const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!leftChild.success) continue;

          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!rightChild.success) continue;

          considerCandidate(ICRule.ImpDown, [leftChild, rightChild], f);
        }
      }

      if (!bestNode) {
        for (const occ of ordered) {
          const f = occ.formula;
          if (!f || f.type !== FormulaType.Disjunction) continue;
          const leftPart = f.left;
          const rightPart = f.right;
          if (!leftPart || !rightPart) continue;
          if (containsInAlphaBeta(q, leftPart) && containsInAlphaBeta(q, rightPart)) continue;

          const leftQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(leftQ.alpha, leftPart);

          const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(rightQ.alpha, rightPart);

          const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!leftChild.success) continue;

          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!rightChild.success) continue;

          const repeatedAssumptions = (containsInAlphaBeta(q, leftPart) ? 1 : 0) + (containsInAlphaBeta(q, rightPart) ? 1 : 0);
          considerCandidate(ICRule.OrDown, [leftChild, rightChild], f, null, { repeatedAssumptions });
        }
      }

      if (!bestNode) {
        for (const occ of ordered) {
          const f = occ.formula;
          if (!f || f.type !== FormulaType.Existential) continue;
          if (alphaHasExistentialWitness(q, f)) continue;
          const freshVar = pickFreshWitnessVariable(q, f, q.goal);
          if (!freshVar) continue;
          const witnessTerm = Term.createVariable(freshVar);
          const instantiated = instantiateQuantifiedFormula(f, witnessTerm);
          if (!instantiated || containsInAlphaBeta(q, instantiated)) continue;

          const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(childQ.alpha, instantiated);
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (child.success) {
            considerCandidate(ICRule.ExistsDown, [child], f, witnessTerm);
          }
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Conjunction && q.goal.left && q.goal.right) {
        const leftQ = createQuestion([...q.alpha], [...q.beta], q.goal.left);
        const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal.right);

        const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
        if (leftChild.success) {
          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (rightChild.success) {
            considerCandidate(ICRule.AndUp, [leftChild, rightChild]);
          }
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Implication && q.goal.left && q.goal.right) {
        const antecedent = q.goal.left;
        const childQ = createQuestion([...q.alpha], [...q.beta], q.goal.right);
        addUnique(childQ.alpha, antecedent);
        const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
        if (child.success) {
          const repeatedAssumptions = containsInAlphaBeta(q, antecedent) ? 1 : 0;
          considerCandidate(ICRule.ImpUp, [child], null, null, { repeatedAssumptions });
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Disjunction && q.goal.left) {
        const leftQ = createQuestion([...q.alpha], [...q.beta], q.goal.left);
        const child = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
        if (child.success) {
          considerCandidate(ICRule.OrUp1, [child]);
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Disjunction && q.goal.right) {
        const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal.right);
        const child = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
        if (child.success) {
          considerCandidate(ICRule.OrUp2, [child]);
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Universal && q.goal.left) {
        const freshVar = pickFreshWitnessVariable(q, q.goal, q.goal);
        if (freshVar) {
          const witnessTerm = Term.createVariable(freshVar);
          const childGoal = instantiateQuantifiedFormula(q.goal, witnessTerm);
          const childQ = createQuestion([...q.alpha], [...q.beta], childGoal);
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (child.success) {
            considerCandidate(ICRule.ForallUp, [child], q.goal, witnessTerm);
          }
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Existential && q.goal.left) {
        const termCandidates = collectQuestionTerms(q, q.goal);
        for (const term of termCandidates) {
          const childGoal = instantiateQuantifiedFormula(q.goal, term);
          if (!childGoal) continue;
          const childQ = createQuestion([...q.alpha], [...q.beta], childGoal);
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (child.success) {
            considerCandidate(ICRule.ExistsUp, [child], q.goal, term);
          }
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Negation && q.goal.left) {
        const assumed = q.goal.left;
        const childQ = createQuestion([...q.alpha], [...q.beta], Formula.createContradiction());
        addUnique(childQ.alpha, assumed);
        const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
        if (child.success) {
          const repeatedAssumptions = containsInAlphaBeta(q, assumed) ? 1 : 0;
          considerCandidate(ICRule.NegUp, [child], null, null, { repeatedAssumptions });
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Contradiction) {
        if (hasClashInAlphaBeta(q)) {
          considerCandidate(ICRule.Clash, []);
        }
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Contradiction) {
        const candidates = collectContradictionCandidates(q);
        for (const phi of candidates) {
          if (containsInAlphaBeta(q, phi) && containsInAlphaBeta(q, negateFormula(phi))) continue;

          const leftQ = createQuestion([...q.alpha], [...q.beta], phi);
          const rightQ = createQuestion([...q.alpha], [...q.beta], negateFormula(phi));

          const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!leftChild.success) continue;

          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!rightChild.success) continue;

          considerCandidate(ICRule.ContradSearch, [leftChild, rightChild], phi);
        }
      }

      if (!bestNode && q.goal && ![FormulaType.Contradiction, FormulaType.Negation].includes(q.goal.type)) {
        const negGoal = negateFormula(q.goal);
        const childQ = createQuestion([...q.alpha], [...q.beta], Formula.createContradiction());
        addUnique(childQ.alpha, negGoal);
        const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
        if (child.success) {
          const repeatedAssumptions = containsInAlphaBeta(q, negGoal) ? 1 : 0;
          considerCandidate(ICRule.ClassicalUp, [child], null, null, { repeatedAssumptions });
        }
      }

      activeStates.delete(key);

      if (bestNode) {
        successStates.set(key, bestNode);
        return bestNode;
      }

      failedStates.add(key);
      return createICTreeNode(q, ICRule.Fail, false);
    }
    function buildICTreeRootLimited(q, maxAttempts = MAX_ROOT_ATTEMPTS, options = {}) {
      ensureSearchNotTimedOut(options);
      const attemptLimit = Number.isFinite(maxAttempts)
        ? Math.max(1, Math.floor(maxAttempts))
        : MAX_ROOT_ATTEMPTS;

      const activeStates = new Set();
      const failedStates = new Set();
      const successStates = new Map();
      let attemptCount = 0;
      let bestNode = null;

      function canAttemptMore() {
        ensureSearchNotTimedOut(options);
        return attemptCount < attemptLimit;
      }

      function attemptCandidate(builder) {
        if (!canAttemptMore()) return null;
        attemptCount += 1;
        const candidate = builder();
        if (candidate && candidate.success) {
          bestNode = chooseBetterICTreeNode(bestNode, candidate);
        }
        return candidate;
      }

      const ordered = alphaBetaOrder(q);

      if (containsInAlphaBeta(q, q.goal) && canAttemptMore()) {
        attemptCandidate(() => createICTreeNode(q, ICRule.Leaf, true));
      }

      if (!bestNode && canAttemptMore()) {
        const sourceInfo = findNegatedUniversalSourceForExistsNegGoal(q.alpha, q.goal);
        if (sourceInfo) {
          attemptCandidate(() => createICTreeNode(q, ICRule.ExistsNegFromNegForall, true, [], sourceInfo.source, Term.createVariable(sourceInfo.freshVar)));
        }
      }

      if (!bestNode && canAttemptMore()) {
        const sourceInfo = findNegatedExistentialSourceForUniversalGoal(q.alpha, q.goal);
        if (sourceInfo) {
          attemptCandidate(() => createICTreeNode(q, ICRule.ForallFromNegExistsNeg, true, [], sourceInfo.source, Term.createVariable(sourceInfo.freshVar)));
        }
      }

      for (const occ of ordered) {
        if (!canAttemptMore()) break;
        const f = occ.formula;
        if (!f || f.type !== FormulaType.Conjunction) continue;
        const leftPart = f.left;
        if (!leftPart || containsInAlphaBeta(q, leftPart)) continue;

        const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
        addUnique(childQ.beta, leftPart);
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.AndDown1, true, [child], f);
        });
      }

      for (const occ of ordered) {
        if (!canAttemptMore()) break;
        const f = occ.formula;
        if (!f || f.type !== FormulaType.Conjunction) continue;
        const rightPart = f.right;
        if (!rightPart || containsInAlphaBeta(q, rightPart)) continue;

        const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
        addUnique(childQ.beta, rightPart);
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.AndDown2, true, [child], f);
        });
      }

      for (const occ of ordered) {
        if (!canAttemptMore()) break;
        const f = occ.formula;
        if (!f || f.type !== FormulaType.Universal) continue;
        const termCandidates = collectQuestionTerms(q, f);
        for (const term of termCandidates) {
          if (!canAttemptMore()) break;
          const instantiated = instantiateQuantifiedFormula(f, term);
          if (!instantiated || containsInAlphaBeta(q, instantiated)) continue;
          const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
          addUnique(childQ.beta, instantiated);
          attemptCandidate(() => {
            const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
            if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
            return createICTreeNode(q, ICRule.ForallDown, true, [child], f, term);
          });
        }
      }

      for (const occ of ordered) {
        if (!canAttemptMore()) break;
        const f = occ.formula;
        if (!f || f.type !== FormulaType.Implication) continue;
        const antecedent = f.left;
        const consequent = f.right;
        if (!antecedent || !consequent) continue;
        if (equalFormula(antecedent, q.goal)) continue;
        if (containsInAlphaBeta(q, consequent)) continue;

        const leftQ = createQuestion([...q.alpha], [...q.beta], antecedent);
        const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal);
        addUnique(rightQ.beta, consequent);

        attemptCandidate(() => {
          const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!leftChild.success) return createICTreeNode(q, ICRule.Fail, false);
          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!rightChild.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.ImpDown, true, [leftChild, rightChild], f);
        });
      }

      for (const occ of ordered) {
        if (!canAttemptMore()) break;
        const f = occ.formula;
        if (!f || f.type !== FormulaType.Disjunction) continue;
        const leftPart = f.left;
        const rightPart = f.right;
        if (!leftPart || !rightPart) continue;
        if (containsInAlphaBeta(q, leftPart) && containsInAlphaBeta(q, rightPart)) continue;

        const leftQ = createQuestion([...q.alpha], [...q.beta], q.goal);
        addUnique(leftQ.alpha, leftPart);
        const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal);
        addUnique(rightQ.alpha, rightPart);
        const repeatedAssumptions = (containsInAlphaBeta(q, leftPart) ? 1 : 0) + (containsInAlphaBeta(q, rightPart) ? 1 : 0);

        attemptCandidate(() => {
          const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!leftChild.success) return createICTreeNode(q, ICRule.Fail, false);
          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!rightChild.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.OrDown, true, [leftChild, rightChild], f, null, { repeatedAssumptions });
        });
      }

      for (const occ of ordered) {
        if (!canAttemptMore()) break;
        const f = occ.formula;
        if (!f || f.type !== FormulaType.Existential) continue;
        if (alphaHasExistentialWitness(q, f)) continue;
        const freshVar = pickFreshWitnessVariable(q, f, q.goal);
        if (!freshVar) continue;
        const witnessTerm = Term.createVariable(freshVar);
        const instantiated = instantiateQuantifiedFormula(f, witnessTerm);
        if (!instantiated || containsInAlphaBeta(q, instantiated)) continue;
        const childQ = createQuestion([...q.alpha], [...q.beta], q.goal);
        addUnique(childQ.alpha, instantiated);

        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.ExistsDown, true, [child], f, witnessTerm);
        });
      }

      if (canAttemptMore() && q.goal && q.goal.type === FormulaType.Conjunction && q.goal.left && q.goal.right) {
        const leftQ = createQuestion([...q.alpha], [...q.beta], q.goal.left);
        const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal.right);
        attemptCandidate(() => {
          const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!leftChild.success) return createICTreeNode(q, ICRule.Fail, false);
          const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!rightChild.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.AndUp, true, [leftChild, rightChild]);
        });
      }

      if (canAttemptMore() && q.goal && q.goal.type === FormulaType.Implication && q.goal.left && q.goal.right) {
        const antecedent = q.goal.left;
        const childQ = createQuestion([...q.alpha], [...q.beta], q.goal.right);
        addUnique(childQ.alpha, antecedent);
        const repeatedAssumptions = containsInAlphaBeta(q, antecedent) ? 1 : 0;
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.ImpUp, true, [child], null, null, { repeatedAssumptions });
        });
      }

      if (canAttemptMore() && q.goal && q.goal.type === FormulaType.Disjunction && q.goal.left) {
        const leftQ = createQuestion([...q.alpha], [...q.beta], q.goal.left);
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.OrUp1, true, [child]);
        });
      }

      if (canAttemptMore() && q.goal && q.goal.type === FormulaType.Disjunction && q.goal.right) {
        const rightQ = createQuestion([...q.alpha], [...q.beta], q.goal.right);
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.OrUp2, true, [child]);
        });
      }

      if (canAttemptMore() && q.goal && q.goal.type === FormulaType.Universal && q.goal.left) {
        const freshVar = pickFreshWitnessVariable(q, q.goal, q.goal);
        if (freshVar) {
          const witnessTerm = Term.createVariable(freshVar);
          const childGoal = instantiateQuantifiedFormula(q.goal, witnessTerm);
          const childQ = createQuestion([...q.alpha], [...q.beta], childGoal);
          attemptCandidate(() => {
            const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
            if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
            return createICTreeNode(q, ICRule.ForallUp, true, [child], q.goal, witnessTerm);
          });
        }
      }

      if (q.goal && q.goal.type === FormulaType.Existential && q.goal.left) {
        const termCandidates = collectQuestionTerms(q, q.goal);
        for (const term of termCandidates) {
          if (!canAttemptMore()) break;
          const childGoal = instantiateQuantifiedFormula(q.goal, term);
          if (!childGoal) continue;
          const childQ = createQuestion([...q.alpha], [...q.beta], childGoal);
          attemptCandidate(() => {
            const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
            if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
            return createICTreeNode(q, ICRule.ExistsUp, true, [child], q.goal, term);
          });
        }
      }

      if (canAttemptMore() && q.goal && q.goal.type === FormulaType.Negation && q.goal.left) {
        const assumed = q.goal.left;
        const childQ = createQuestion([...q.alpha], [...q.beta], Formula.createContradiction());
        addUnique(childQ.alpha, assumed);
        const repeatedAssumptions = containsInAlphaBeta(q, assumed) ? 1 : 0;
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.NegUp, true, [child], null, null, { repeatedAssumptions });
        });
      }

      if (!bestNode && canAttemptMore() && q.goal && q.goal.type === FormulaType.Contradiction && hasClashInAlphaBeta(q)) {
        attemptCandidate(() => createICTreeNode(q, ICRule.Clash, true, [], null, null, {}));
      }

      if (!bestNode && q.goal && q.goal.type === FormulaType.Contradiction) {
        const candidates = collectContradictionCandidates(q);
        for (const phi of candidates) {
          if (!canAttemptMore()) break;
          if (containsInAlphaBeta(q, phi) && containsInAlphaBeta(q, negateFormula(phi))) continue;

          const leftQ = createQuestion([...q.alpha], [...q.beta], phi);
          const rightQ = createQuestion([...q.alpha], [...q.beta], negateFormula(phi));
          attemptCandidate(() => {
            const leftChild = buildICTreeFirstSuccess(leftQ, activeStates, failedStates, successStates, options);
            if (!leftChild.success) return createICTreeNode(q, ICRule.Fail, false);
            const rightChild = buildICTreeFirstSuccess(rightQ, activeStates, failedStates, successStates, options);
            if (!rightChild.success) return createICTreeNode(q, ICRule.Fail, false);
            return createICTreeNode(q, ICRule.ContradSearch, true, [leftChild, rightChild], phi);
          });
        }
      }

      if (!bestNode && canAttemptMore() && q.goal && ![FormulaType.Contradiction, FormulaType.Negation].includes(q.goal.type)) {
        const negGoal = negateFormula(q.goal);
        const childQ = createQuestion([...q.alpha], [...q.beta], Formula.createContradiction());
        addUnique(childQ.alpha, negGoal);
        const repeatedAssumptions = containsInAlphaBeta(q, negGoal) ? 1 : 0;
        attemptCandidate(() => {
          const child = buildICTreeFirstSuccess(childQ, activeStates, failedStates, successStates, options);
          if (!child.success) return createICTreeNode(q, ICRule.Fail, false);
          return createICTreeNode(q, ICRule.ClassicalUp, true, [child], null, null, { repeatedAssumptions });
        });
      }

      if (bestNode) return bestNode;
      return createICTreeNode(q, ICRule.Fail, false);
    }

    function buildICTree(q, activeStates, failedStates, successStates = new Map(), options = {}) {
      const maxRootAttempts = Number.isFinite(options.maxRootAttempts)
        ? Math.max(1, Math.floor(options.maxRootAttempts))
        : MAX_ROOT_ATTEMPTS;
      return buildICTreeRootLimited(q, maxRootAttempts, options);
    }
    function createNDProofNode({ formula = null, reason = "", parent1 = null, parent2 = null, subAssumption1 = null, subEnd1 = null, subAssumption2 = null, subEnd2 = null } = {}) {
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

    function collectTermsFromProofContext(ctx) {
      const raw = [];
      for (const node of ctx || []) {
        if (node && node.formula) collectTermsFromFormula(node.formula, raw);
      }
      return uniqueTermsPreserveOrder(raw);
    }
    function deriveContextClosure(ctx, maxRounds = 4) {
      const known = [];
      for (const node of ctx || []) {
        if (node && node.formula) addProofNodeUniqueByFormula(known, node);
      }

      let rounds = 0;
      let changed = true;
      while (changed && rounds < maxRounds) {
        changed = false;
        rounds += 1;
        const snapshot = [...known];
        const termCandidates = collectTermsFromProofContext(snapshot);

        for (const node of snapshot) {
          const f = node.formula;
          if (!f) continue;

          if (f.type === FormulaType.Conjunction) {
            if (f.left) changed = addProofNodeUniqueByFormula(known, makeUnaryNode(f.left, "&E", node)) || changed;
            if (f.right) changed = addProofNodeUniqueByFormula(known, makeUnaryNode(f.right, "&E", node)) || changed;
          }

          if (f.type === FormulaType.Universal) {
            for (const term of termCandidates) {
              const instantiated = instantiateQuantifiedFormula(f, term);
              if (!instantiated) continue;
              changed = addProofNodeUniqueByFormula(known, makeUnaryNode(instantiated, "∀E", node)) || changed;
            }
          }
        }

        const implications = snapshot.filter((node) => node.formula && node.formula.type === FormulaType.Implication);
        for (const impNode of implications) {
          const antecedentNode = findProofWithFormula(known, impNode.formula.left);
          if (!antecedentNode || !impNode.formula.right) continue;
          const consequentNode = makeBinaryNode(impNode.formula.right, "->E", impNode, antecedentNode);
          changed = addProofNodeUniqueByFormula(known, consequentNode) || changed;
        }
      }

      return known;
    }

    function findLatestAssumptionWithFormula(ctx, targetFormula) {
      for (let i = (ctx || []).length - 1; i >= 0; i--) {
        const node = ctx[i];
        if (!node || node.reason !== "Assumption") continue;
        if (equalFormula(node.formula, targetFormula)) return node;
      }
      return null;
    }

    function formulaContainsQuantifier(formula) {
      if (!formula) return false;
      if (formula.type === FormulaType.Universal || formula.type === FormulaType.Existential) return true;
      return formulaContainsQuantifier(formula.left) || formulaContainsQuantifier(formula.right);
    }

    function proofContextContainsQuantifier(ctx) {
      for (const node of ctx || []) {
        if (node && node.formula && formulaContainsQuantifier(node.formula)) return true;
      }
      return false;
    }

    const STRUCTURED_PROOF_DEPTH_LIMIT = 11;

    function contextKey(ctx) {
      return (ctx || []).map((node) => formulaToString(node.formula)).sort().join("|");
    }

    function findExistentialProofsInContext(ctx) {
      const out = [];
      const seen = new Set();
      for (const node of ctx || []) {
        if (!node || !node.formula || node.formula.type !== FormulaType.Existential) continue;
        const key = formulaToString(node.formula);
        if (seen.has(key)) continue;
        seen.add(key);
        out.push(node);
      }
      return out;
    }

    function contextHasExistentialInstance(ctx, existentialFormula) {
      const terms = collectTermsFromProofContext(ctx);
      for (const term of terms) {
        const instance = instantiateQuantifiedFormula(existentialFormula, term);
        if (instance && findProofWithFormula(ctx, instance)) return true;
      }
      return false;
    }

    function pickFreshExistentialWitnessForProof(ctx, existentialFormula, goal) {
      const used = new Set();
      for (const node of ctx || []) {
        if (node && node.formula) collectFreeVariablesFormula(node.formula, used);
      }
      if (goal) collectFreeVariablesFormula(goal, used);
      const preferred = existentialFormula && existentialFormula.variable ? existentialFormula.variable : null;
      if (preferred && !used.has(preferred)) return preferred;
      return chooseFreshVariableSymbol((ctx || []).map((node) => node.formula), existentialFormula, goal, used);
    }


    function makeExistsNegFromNegForallStructuredProof(goal, sourceNode, ctx) {
      if (!goal || goal.type !== FormulaType.Existential || !goal.left || goal.left.type !== FormulaType.Negation) return null;
      if (!sourceNode || !sourceNode.formula || sourceNode.formula.type !== FormulaType.Negation) return null;
      const universal = sourceNode.formula.left;
      if (!universal || universal.type !== FormulaType.Universal) return null;
      const fresh = pickFreshExistentialWitnessForProof(ctx || [], goal, sourceNode.formula) || chooseFreshVariableSymbol(goal, sourceNode.formula);
      const witnessTerm = Term.createVariable(fresh);
      const universalInstance = instantiateQuantifiedFormula(universal, witnessTerm);
      const goalInstance = instantiateQuantifiedFormula(goal, witnessTerm);
      if (!universalInstance || !goalInstance || goalInstance.type !== FormulaType.Negation) return null;
      if (!equalFormula(universalInstance, goalInstance.left)) return null;
      const negGoalAssumption = makeSimpleNode(negateFormula(goal), "Assumption");
      const negInstanceAssumption = makeSimpleNode(goalInstance, "Assumption");
      const existsNeg = makeUnaryNode(goal, "∃I", negInstanceAssumption);
      const innerContradiction = makeContradictionNode(existsNeg, negGoalAssumption);
      const positiveInstance = createNDProofNode({ formula: universalInstance, reason: "RAA", subAssumption1: negInstanceAssumption, subEnd1: innerContradiction });
      const universalProof = makeUnaryNode(universal, "∀I", positiveInstance);
      const outerContradiction = makeContradictionNode(universalProof, sourceNode);
      return createNDProofNode({ formula: goal, reason: "RAA", subAssumption1: negGoalAssumption, subEnd1: outerContradiction });
    }

    function makeForallNegFromNegExistsStructuredProof(goal, sourceNode, ctx) {
      if (!goal || goal.type !== FormulaType.Universal || !goal.left || goal.left.type !== FormulaType.Negation) return null;
      if (!sourceNode || !sourceNode.formula || sourceNode.formula.type !== FormulaType.Negation) return null;
      const existential = sourceNode.formula.left;
      if (!existential || existential.type !== FormulaType.Existential) return null;
      const fresh = pickFreshExistentialWitnessForProof(ctx || [], goal, sourceNode.formula) || chooseFreshVariableSymbol(goal, sourceNode.formula);
      const witnessTerm = Term.createVariable(fresh);
      const goalInstance = instantiateQuantifiedFormula(goal, witnessTerm);
      const existsInstance = instantiateQuantifiedFormula(existential, witnessTerm);
      if (!goalInstance || !existsInstance || goalInstance.type !== FormulaType.Negation) return null;
      if (!equalFormula(goalInstance.left, existsInstance)) return null;
      const positiveAssumption = makeSimpleNode(existsInstance, "Assumption");
      const existsProof = makeUnaryNode(existential, "∃I", positiveAssumption);
      const contradiction = makeContradictionNode(existsProof, sourceNode);
      const negInstanceProof = createNDProofNode({ formula: goalInstance, reason: "~I", subAssumption1: positiveAssumption, subEnd1: contradiction });
      return makeUnaryNode(goal, "∀I", negInstanceProof);
    }


    function makeExistsForallNegFromNegForallExistsStructuredProof(goal, sourceNode, ctx) {
      if (!goal || goal.type !== FormulaType.Existential || !goal.left || goal.left.type !== FormulaType.Universal) return null;
      const innerUniversal = goal.left;
      if (!innerUniversal.left || innerUniversal.left.type !== FormulaType.Negation) return null;
      if (!sourceNode || !sourceNode.formula || sourceNode.formula.type !== FormulaType.Negation) return null;
      const sourceUniversal = sourceNode.formula.left;
      if (!sourceUniversal || sourceUniversal.type !== FormulaType.Universal) return null;
      const freshX = pickFreshExistentialWitnessForProof(ctx || [], goal, sourceNode.formula) || chooseFreshVariableSymbol(goal, sourceNode.formula);
      const xTerm = Term.createVariable(freshX);
      const sourceXInstance = instantiateQuantifiedFormula(sourceUniversal, xTerm);
      const goalXInstance = instantiateQuantifiedFormula(goal, xTerm);
      if (!sourceXInstance || sourceXInstance.type !== FormulaType.Existential) return null;
      if (!goalXInstance || goalXInstance.type !== FormulaType.Universal || !goalXInstance.left || goalXInstance.left.type !== FormulaType.Negation) return null;
      const freshY = pickFreshExistentialWitnessForProof(ctx || [], goalXInstance, sourceXInstance) || chooseFreshVariableSymbol(goalXInstance, sourceXInstance);
      const yTerm = Term.createVariable(freshY);
      const sourceXYInstance = instantiateQuantifiedFormula(sourceXInstance, yTerm);
      const goalXYInstance = instantiateQuantifiedFormula(goalXInstance, yTerm);
      if (!sourceXYInstance || !goalXYInstance || goalXYInstance.type !== FormulaType.Negation) return null;
      if (!equalFormula(sourceXYInstance, goalXYInstance.left)) return null;

      const negGoalAssumption = makeSimpleNode(negateFormula(goal), "Assumption");
      const negExistsYAssumption = makeSimpleNode(negateFormula(sourceXInstance), "Assumption");
      const forallNegY = makeForallNegFromNegExistsStructuredProof(goalXInstance, negExistsYAssumption, [...(ctx || []), negGoalAssumption, negExistsYAssumption]);
      if (!forallNegY) return null;
      const existsForallNeg = makeUnaryNode(goal, "∃I", forallNegY);
      const contradictionInner = makeContradictionNode(existsForallNeg, negGoalAssumption);
      const existsYProof = createNDProofNode({ formula: sourceXInstance, reason: "RAA", subAssumption1: negExistsYAssumption, subEnd1: contradictionInner });
      const forallExistsProof = makeUnaryNode(sourceUniversal, "∀I", existsYProof);
      const outerContradiction = makeContradictionNode(forallExistsProof, sourceNode);
      return createNDProofNode({ formula: goal, reason: "RAA", subAssumption1: negGoalAssumption, subEnd1: outerContradiction });
    }

    function tryExistsForallNegFromNegForallExistsSchemaProof(goal, ctx) {
      if (!goal) return null;
      const closure = deriveContextClosure(ctx || [], 7);
      for (const node of closure) {
        const proof = makeExistsForallNegFromNegForallExistsStructuredProof(goal, node, closure);
        if (proof) return proof;
      }
      return null;
    }

    function tryQuantifierNegationSchemaProof(goal, ctx) {
      if (!goal) return null;
      const closure = deriveContextClosure(ctx || [], 7);
      if (goal.type === FormulaType.Existential && goal.left && goal.left.type === FormulaType.Negation) {
        for (const node of closure) {
          const proof = makeExistsNegFromNegForallStructuredProof(goal, node, closure);
          if (proof) return proof;
        }
      }
      if (goal.type === FormulaType.Universal && goal.left && goal.left.type === FormulaType.Negation) {
        for (const node of closure) {
          const proof = makeForallNegFromNegExistsStructuredProof(goal, node, closure);
          if (proof) return proof;
        }
      }
      return null;
    }

    function tryClassicalOrByNegatedSide(goal, ctx, depth, visited) {
      if (!goal || goal.type !== FormulaType.Disjunction || !goal.left || !goal.right || depth <= 1) return null;
      const closure = deriveContextClosure(ctx || [], 7);
      const notGoal = makeSimpleNode(negateFormula(goal), "Assumption");
      function deriveNegSide(side, orIntroReason) {
        const sideAssumption = makeSimpleNode(side, "Assumption");
        const disjFromSide = makeUnaryNode(goal, orIntroReason, sideAssumption);
        const contradiction = makeContradictionNode(disjFromSide, notGoal);
        return createNDProofNode({ formula: negateFormula(side), reason: "~I", subAssumption1: sideAssumption, subEnd1: contradiction });
      }
      const notLeft = deriveNegSide(goal.left, "∨I 1");
      const rightProof = tryStructuredProofFromContext(goal.right, [...closure, notGoal, notLeft], depth - 1, visited);
      if (rightProof) {
        const disjFromRight = makeUnaryNode(goal, "∨I 2", rightProof);
        const contradiction = makeContradictionNode(disjFromRight, notGoal);
        return createNDProofNode({ formula: goal, reason: "RAA", subAssumption1: notGoal, subEnd1: contradiction });
      }
      const notRight = deriveNegSide(goal.right, "∨I 2");
      const leftProof = tryStructuredProofFromContext(goal.left, [...closure, notGoal, notRight], depth - 1, visited);
      if (leftProof) {
        const disjFromLeft = makeUnaryNode(goal, "∨I 1", leftProof);
        const contradiction = makeContradictionNode(disjFromLeft, notGoal);
        return createNDProofNode({ formula: goal, reason: "RAA", subAssumption1: notGoal, subEnd1: contradiction });
      }
      return null;
    }

    function maybeBuildNegatedExistentialOfAntecedentFromDrinkerGoal(goal) {
      if (!goal || goal.type !== FormulaType.Existential || !goal.left || goal.left.type !== FormulaType.Implication) return null;
      const antecedent = goal.left.left;
      const consequent = goal.left.right;
      if (!antecedent || !consequent || consequent.type !== FormulaType.Universal) return null;
      const witness = Term.createVariable(goal.variable);
      const consequentBody = instantiateQuantifiedFormula(consequent, witness);
      if (!consequentBody || !equalFormula(antecedent, consequentBody)) return null;
      return Formula.createExistential(goal.variable, negateFormula(antecedent));
    }

    function makeLemmaExcludedMiddle(formula) {
      if (!formula) return null;
      const lem = Formula.createBinary(FormulaType.Disjunction, formula, negateFormula(formula));
      return tryStructuredProofFromContext(lem, [], 5, new Set());
    }


    function makeDrinkerSchemaProof(goal, ctx) {
      if (!goal || goal.type !== FormulaType.Existential || !goal.left || goal.left.type !== FormulaType.Implication) return null;
      const antecedentPattern = goal.left.left;
      const consequent = goal.left.right;
      if (!antecedentPattern || !consequent || consequent.type !== FormulaType.Universal) return null;
      const xTermForPattern = Term.createVariable(goal.variable);
      const consequentPatternBody = instantiateQuantifiedFormula(consequent, xTermForPattern);
      if (!consequentPatternBody || !equalFormula(antecedentPattern, consequentPatternBody)) return null;

      const split = Formula.createExistential(goal.variable, negateFormula(antecedentPattern));
      const lem = Formula.createBinary(FormulaType.Disjunction, split, negateFormula(split));
      const lemProof = makeLemmaExcludedMiddle(split);
      if (!lemProof) return null;

      const freshX = pickFreshExistentialWitnessForProof(ctx || [], goal, split) || chooseFreshVariableSymbol(goal, split);
      const xTerm = Term.createVariable(freshX);
      const ax = instantiateQuantifiedFormula(Formula.createUniversal(goal.variable, antecedentPattern), xTerm);
      const notAx = negateFormula(ax);
      const forallA = Formula.createUniversal(goal.variable, antecedentPattern);
      const forallYAy = instantiateQuantifiedFormula(goal, xTerm).right;
      const implicationAtX = instantiateQuantifiedFormula(goal, xTerm);
      if (!ax || !forallYAy || !implicationAtX) return null;

      // Left branch: ∃x¬Ax
      const leftAssumption = makeSimpleNode(split, "Assumption");
      const notAxAssumption = makeSimpleNode(notAx, "Assumption");
      const axAssumptionLeft = makeSimpleNode(ax, "Assumption");
      const clashLeft = makeContradictionNode(axAssumptionLeft, notAxAssumption);
      const negForallAssumptionLeft = makeSimpleNode(negateFormula(forallYAy), "Assumption");
      const forallFromClashLeft = createNDProofNode({ formula: forallYAy, reason: "RAA", subAssumption1: negForallAssumptionLeft, subEnd1: clashLeft });
      const impLeft = createNDProofNode({ formula: implicationAtX, reason: "->I", subAssumption1: axAssumptionLeft, subEnd1: forallFromClashLeft });
      const existsGoalLeftInner = makeUnaryNode(goal, "∃I", impLeft);
      const leftEnd = createNDProofNode({ formula: goal, reason: "∃E", parent1: leftAssumption, subAssumption1: notAxAssumption, subEnd1: existsGoalLeftInner });

      // Right branch: ¬∃x¬Ax
      const rightAssumption = makeSimpleNode(negateFormula(split), "Assumption");
      const negAxAssumptionForAll = makeSimpleNode(notAx, "Assumption");
      const splitFromNegAx = makeUnaryNode(split, "∃I", negAxAssumptionForAll);
      const contradictionForAll = makeContradictionNode(splitFromNegAx, rightAssumption);
      const axByRAA = createNDProofNode({ formula: ax, reason: "RAA", subAssumption1: negAxAssumptionForAll, subEnd1: contradictionForAll });
      const forallAProof = makeUnaryNode(forallA, "∀I", axByRAA);
      const axAssumptionRight = makeSimpleNode(ax, "Assumption");
      const freshY = pickFreshExistentialWitnessForProof([...(ctx || []), rightAssumption, forallAProof], consequent, goal) || chooseFreshVariableSymbol(goal, consequent);
      const yTerm = Term.createVariable(freshY);
      const ay = instantiateQuantifiedFormula(forallA, yTerm);
      const ayProof = makeUnaryNode(ay, "∀E", forallAProof);
      const forallYProof = makeUnaryNode(forallYAy, "∀I", ayProof);
      const impRight = createNDProofNode({ formula: implicationAtX, reason: "->I", subAssumption1: axAssumptionRight, subEnd1: forallYProof });
      const rightEnd = makeUnaryNode(goal, "∃I", impRight);

      return createNDProofNode({ formula: goal, reason: "∨E", parent1: lemProof, subAssumption1: leftAssumption, subEnd1: leftEnd, subAssumption2: rightAssumption, subEnd2: rightEnd });
    }

    function tryProofByGeneratedCaseSplit(goal, ctx, depth, visited) {
      if (!goal || depth <= 2) return null;
      const splitFormula = maybeBuildNegatedExistentialOfAntecedentFromDrinkerGoal(goal);
      if (!splitFormula) return null;
      const lemProof = makeLemmaExcludedMiddle(splitFormula);
      if (!lemProof) return null;
      const leftAssumption = makeSimpleNode(splitFormula, "Assumption");
      const leftEnd = tryStructuredProofFromContext(goal, [...ctx, leftAssumption], depth - 1, visited);
      if (!leftEnd) return null;
      const rightAssumptionFormula = negateFormula(splitFormula);
      const rightAssumption = makeSimpleNode(rightAssumptionFormula, "Assumption");
      const rightEnd = tryStructuredProofFromContext(goal, [...ctx, rightAssumption], depth - 1, visited);
      if (!rightEnd) return null;
      return createNDProofNode({ formula: goal, reason: "∨E", parent1: lemProof, subAssumption1: leftAssumption, subEnd1: leftEnd, subAssumption2: rightAssumption, subEnd2: rightEnd });
    }

    function tryStructuredContradictionFromContext(ctx, depth = STRUCTURED_PROOF_DEPTH_LIMIT, visited = new Set()) {
      if (depth <= 0) return null;
      const closure = deriveContextClosure(ctx, 7);
      const directContradiction = findProofWithFormula(closure, Formula.createContradiction());
      if (directContradiction) return directContradiction;
      const [pos, neg] = findClashWitnessInContext(closure);
      if (pos && neg) return makeContradictionNode(pos, neg);

      const stateKey = `⊥|${depth}|${contextKey(closure)}`;
      if (visited.has(stateKey)) return null;
      visited.add(stateKey);

      for (const existsNode of findExistentialProofsInContext(closure)) {
        if (contextHasExistentialInstance(closure, existsNode.formula)) continue;
        const fresh = pickFreshExistentialWitnessForProof(closure, existsNode.formula, Formula.createContradiction());
        if (!fresh) continue;
        const witnessTerm = Term.createVariable(fresh);
        const assumptionFormula = instantiateQuantifiedFormula(existsNode.formula, witnessTerm);
        if (!assumptionFormula) continue;
        if (findProofWithFormula(closure, assumptionFormula)) continue;
        const assumption = makeSimpleNode(assumptionFormula, "Assumption");
        const subEnd = tryStructuredContradictionFromContext([...closure, assumption], depth - 1, visited);
        if (subEnd) {
          return createNDProofNode({
            formula: Formula.createContradiction(),
            reason: "∃E",
            parent1: existsNode,
            subAssumption1: assumption,
            subEnd1: subEnd,
          });
        }
      }

      for (const negNode of closure) {
        const f = negNode && negNode.formula;
        if (!f || f.type !== FormulaType.Negation || !f.left) continue;
        const positiveProof = tryStructuredProofFromContext(f.left, closure, depth - 1, visited);
        if (positiveProof) return makeContradictionNode(positiveProof, negNode);
      }

      return null;
    }

    function tryStructuredProofFromContext(goal, ctx, depth = STRUCTURED_PROOF_DEPTH_LIMIT, visited = new Set()) {
      if (!goal || depth <= 0) return null;
      const closure = deriveContextClosure(ctx, 7);
      const direct = findProofWithFormula(closure, goal);
      if (direct) return direct;

      const existsForallNegSchemaProof = tryExistsForallNegFromNegForallExistsSchemaProof(goal, closure);
      if (existsForallNegSchemaProof) return existsForallNegSchemaProof;

      const qNegSchemaProof = tryQuantifierNegationSchemaProof(goal, closure);
      if (qNegSchemaProof) return qNegSchemaProof;

      const stateKey = `${formulaToString(goal)}|${depth}|${contextKey(closure)}`;
      if (visited.has(stateKey)) return null;
      visited.add(stateKey);

      if (goal.type === FormulaType.Contradiction) {
        return tryStructuredContradictionFromContext(closure, depth, visited);
      }

      if (goal.type === FormulaType.Conjunction && goal.left && goal.right) {
        const leftProof = tryStructuredProofFromContext(goal.left, closure, depth - 1, visited);
        if (!leftProof) return null;
        const rightProof = tryStructuredProofFromContext(goal.right, closure, depth - 1, visited);
        if (!rightProof) return null;
        return makeBinaryNode(goal, "&I", leftProof, rightProof);
      }

      if (goal.type === FormulaType.Disjunction && goal.left && goal.right) {
        let positiveSide = null;
        let negativeSide = null;
        let negOnRight = false;
        if (goal.right.type === FormulaType.Negation && equalFormula(goal.right.left, goal.left)) {
          positiveSide = goal.left;
          negativeSide = goal.right;
          negOnRight = true;
        } else if (goal.left.type === FormulaType.Negation && equalFormula(goal.left.left, goal.right)) {
          positiveSide = goal.right;
          negativeSide = goal.left;
          negOnRight = false;
        }
        if (positiveSide && negativeSide) {
          const notGoal = makeSimpleNode(negateFormula(goal), "Assumption");
          const posAssumption = makeSimpleNode(positiveSide, "Assumption");
          const disjFromPos = makeUnaryNode(goal, negOnRight ? "∨I 1" : "∨I 2", posAssumption);
          const contradictionFromPos = makeContradictionNode(disjFromPos, notGoal);
          const derivedNeg = createNDProofNode({
            formula: negativeSide,
            reason: "~I",
            subAssumption1: posAssumption,
            subEnd1: contradictionFromPos,
          });
          const disjFromNeg = makeUnaryNode(goal, negOnRight ? "∨I 2" : "∨I 1", derivedNeg);
          const finalContradiction = makeContradictionNode(disjFromNeg, notGoal);
          return createNDProofNode({
            formula: goal,
            reason: "RAA",
            subAssumption1: notGoal,
            subEnd1: finalContradiction,
          });
        }
        const classicalOr = tryClassicalOrByNegatedSide(goal, closure, depth - 1, visited);
        if (classicalOr) return classicalOr;
      }

      if (goal.type === FormulaType.Implication && goal.left && goal.right) {
        const assumption = makeSimpleNode(goal.left, "Assumption");
        const body = tryStructuredProofFromContext(goal.right, [...closure, assumption], depth - 1, visited);
        if (!body) return null;
        return createNDProofNode({ formula: goal, reason: "->I", subAssumption1: assumption, subEnd1: body });
      }

      if (goal.type === FormulaType.Negation && goal.left) {
        const assumption = makeSimpleNode(goal.left, "Assumption");
        const contradiction = tryStructuredContradictionFromContext([...closure, assumption], depth - 1, visited);
        if (!contradiction) return null;
        return createNDProofNode({ formula: goal, reason: "~I", subAssumption1: assumption, subEnd1: contradiction });
      }

      if (goal.type === FormulaType.Universal && goal.left) {
        const fresh = pickFreshExistentialWitnessForProof(closure, goal, goal);
        if (!fresh) return null;
        const witnessTerm = Term.createVariable(fresh);
        const bodyGoal = instantiateQuantifiedFormula(goal, witnessTerm);
        const body = tryStructuredProofFromContext(bodyGoal, closure, depth - 1, visited);
        if (!body) return null;
        return makeUnaryNode(goal, "∀I", body);
      }

      if (goal.type === FormulaType.Existential && goal.left) {
        const terms = collectTermsFromProofContext(closure);
        const freshForExists = pickFreshExistentialWitnessForProof(closure, goal, goal);
        if (freshForExists) terms.push(Term.createVariable(freshForExists));
        const uniqueTerms = uniqueTermsPreserveOrder(terms);
        for (const term of uniqueTerms) {
          const bodyGoal = instantiateQuantifiedFormula(goal, term);
          if (!bodyGoal) continue;
          const body = tryStructuredProofFromContext(bodyGoal, closure, depth - 1, visited);
          if (body) return makeUnaryNode(goal, "∃I", body);
        }
        const drinkerSchemaProof = makeDrinkerSchemaProof(goal, closure);
        if (drinkerSchemaProof) return drinkerSchemaProof;
        const splitProof = tryProofByGeneratedCaseSplit(goal, closure, depth - 1, visited);
        if (splitProof) return splitProof;
      }


      // Goal-directed implication elimination: if some available implication A -> goal
      // can derive the current goal, recursively prove A as a subgoal.
      // This is the missing backward step needed for cases like proving Lxe
      // from (Px ∧ Lxa) -> Lxe together with Px and Lxa.
      for (const impNode of closure) {
        const imp = impNode && impNode.formula;
        if (!imp || imp.type !== FormulaType.Implication || !imp.left || !imp.right) continue;
        if (!equalFormula(imp.right, goal)) continue;
        if (equalFormula(imp.left, goal)) continue;

        const antecedentProof = tryStructuredProofFromContext(imp.left, closure, depth - 1, visited);
        if (!antecedentProof) continue;
        return makeBinaryNode(goal, "->E", impNode, antecedentProof);
      }
      for (const existsNode of findExistentialProofsInContext(closure)) {
        if (contextHasExistentialInstance(closure, existsNode.formula)) continue;
        const fresh = pickFreshExistentialWitnessForProof(closure, existsNode.formula, goal);
        if (!fresh) continue;
        const witnessTerm = Term.createVariable(fresh);
        const assumptionFormula = instantiateQuantifiedFormula(existsNode.formula, witnessTerm);
        if (!assumptionFormula) continue;
        if (findProofWithFormula(closure, assumptionFormula)) continue;
        const assumption = makeSimpleNode(assumptionFormula, "Assumption");
        const subEnd = tryStructuredProofFromContext(goal, [...closure, assumption], depth - 1, visited);
        if (subEnd) {
          return createNDProofNode({
            formula: goal,
            reason: "∃E",
            parent1: existsNode,
            subAssumption1: assumption,
            subEnd1: subEnd,
          });
        }
      }

      if (goal.type !== FormulaType.Negation && goal.type !== FormulaType.Contradiction) {
        const negGoal = negateFormula(goal);
        const existingAssumption = findLatestAssumptionWithFormula(ctx, negGoal);
        if (existingAssumption) {
          const contradiction = tryStructuredContradictionFromContext(closure, depth - 1, visited);
          if (contradiction) {
            return createNDProofNode({
              formula: goal,
              reason: "RAA",
              subAssumption1: existingAssumption,
              subEnd1: contradiction,
            });
          }
        }
      }

      return null;
    }

    function tryDirectProofFromContext(goal, ctx) {
      return tryStructuredProofFromContext(goal, ctx, STRUCTURED_PROOF_DEPTH_LIMIT, new Set());
    }

    function tryDirectContradictionFromContext(ctx) {
      return tryStructuredContradictionFromContext(ctx, STRUCTURED_PROOF_DEPTH_LIMIT, new Set());
    }

    function simplifyNDProof(node, ctx) {
      if (!node) return null;
      if (proofContextContainsQuantifier(ctx)) return node;

      if (node.reason === "Premise" || node.reason === "Assumption") {
        return node;
      }

      if (node.reason === "∀I" || node.reason === "∃I") {
        const parent1 = node.parent1 ? simplifyNDProof(node.parent1, ctx) : null;
        if (!parent1) return node;
        return createNDProofNode({ formula: node.formula, reason: node.reason, parent1 });
      }

      if (node.formula && formulaContainsQuantifier(node.formula)) {
        const parent1 = node.parent1 ? simplifyNDProof(node.parent1, ctx) : null;
        const parent2 = node.parent2 ? simplifyNDProof(node.parent2, ctx) : null;
        return createNDProofNode({ formula: node.formula, reason: node.reason, parent1, parent2, subAssumption1: node.subAssumption1, subEnd1: node.subEnd1, subAssumption2: node.subAssumption2, subEnd2: node.subEnd2 });
      }

      if (node.reason === "->I") {
        const assumption = node.subAssumption1;
        const nextCtx = [...ctx, assumption];
        const directBody = node.formula && node.formula.right ? tryDirectProofFromContext(node.formula.right, nextCtx) : null;
        const body = directBody || simplifyNDProof(node.subEnd1, nextCtx);
        if (!body) return null;
        return createNDProofNode({ formula: node.formula, reason: node.reason, subAssumption1: assumption, subEnd1: body });
      }

      if (node.reason === "~I" || node.reason === "RAA") {
        const assumption = node.subAssumption1;
        const nextCtx = [...ctx, assumption];
        const directContradiction = tryDirectContradictionFromContext(nextCtx);
        const contradiction = directContradiction || simplifyNDProof(node.subEnd1, nextCtx);
        if (!contradiction) return null;
        return createNDProofNode({ formula: node.formula, reason: node.reason, subAssumption1: assumption, subEnd1: contradiction });
      }

      if (node.reason === "∨E") {
        const parent1 = simplifyNDProof(node.parent1, ctx);
        if (!parent1) return null;
        const leftAssumption = node.subAssumption1;
        const leftEnd = simplifyNDProof(node.subEnd1, [...ctx, leftAssumption]);
        if (!leftEnd) return null;
        const rightAssumption = node.subAssumption2;
        const rightEnd = simplifyNDProof(node.subEnd2, [...ctx, rightAssumption]);
        if (!rightEnd) return null;
        return createNDProofNode({ formula: node.formula, reason: node.reason, parent1, subAssumption1: leftAssumption, subEnd1: leftEnd, subAssumption2: rightAssumption, subEnd2: rightEnd });
      }

      if (node.reason === "∃E") {
        return node;
      }

      const parent1 = node.parent1 ? simplifyNDProof(node.parent1, ctx) : null;
      const parent2 = node.parent2 ? simplifyNDProof(node.parent2, ctx) : null;
      return createNDProofNode({ formula: node.formula, reason: node.reason, parent1, parent2 });
    }
    function extractNDProof(icNode, ctx) {
      if (!icNode || !icNode.success) return null;

      const directProof = tryDirectProofFromContext(icNode.question ? icNode.question.goal : null, ctx);
      if (directProof) return directProof;

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
          if (!source || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Universal || !icNode.focusTerm) return null;
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
          if (!source || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Existential || !icNode.focusTerm) return null;
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
          if (!icNode.question.goal || icNode.question.goal.type !== FormulaType.Implication || !icNode.question.goal.left) return null;
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
          if (!icNode.question.goal || icNode.question.goal.type !== FormulaType.Negation || !icNode.question.goal.left) return null;
          const assumption = makeSimpleNode(icNode.question.goal.left, "Assumption");
          const nextCtx = [...ctx, assumption];
          const contradiction = tryDirectContradictionFromContext(nextCtx) || extractNDProof(icNode.children[0], nextCtx);
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
          const contradiction = tryDirectContradictionFromContext(nextCtx) || extractNDProof(icNode.children[0], nextCtx);
          if (!contradiction) return null;
          return createNDProofNode({
            formula: icNode.question.goal,
            reason: "RAA",
            subAssumption1: assumption,
            subEnd1: contradiction,
          });
        }


        case ICRule.ExistsNegFromNegForall: {
          const source = findProofWithFormula(ctx, icNode.focusFormula);
          if (!source || !icNode.question.goal || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Negation) return null;
          const universal = icNode.focusFormula.left;
          if (!universal || universal.type !== FormulaType.Universal) return null;
          const witnessTerm = icNode.focusTerm || Term.createVariable(chooseFreshVariableSymbol(icNode.focusFormula, icNode.question.goal));
          const positiveInstance = instantiateQuantifiedFormula(universal, witnessTerm);
          if (!positiveInstance) return null;
          const negativeInstance = negateFormula(positiveInstance);
          const negExistsAssumption = makeSimpleNode(negateFormula(icNode.question.goal), "Assumption");
          const negInstanceAssumption = makeSimpleNode(negativeInstance, "Assumption");
          const existsNeg = makeUnaryNode(icNode.question.goal, "∃I", negInstanceAssumption);
          const innerContradiction = makeContradictionNode(existsNeg, negExistsAssumption);
          const positiveByRAA = createNDProofNode({ formula: positiveInstance, reason: "RAA", subAssumption1: negInstanceAssumption, subEnd1: innerContradiction });
          const universalProof = makeUnaryNode(universal, "∀I", positiveByRAA);
          const outerContradiction = makeContradictionNode(universalProof, source);
          return createNDProofNode({ formula: icNode.question.goal, reason: "RAA", subAssumption1: negExistsAssumption, subEnd1: outerContradiction });
        }

        case ICRule.ForallFromNegExistsNeg: {
          const source = findProofWithFormula(ctx, icNode.focusFormula);
          if (!source || !icNode.question.goal || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Negation) return null;
          const existential = icNode.focusFormula.left;
          if (!existential || existential.type !== FormulaType.Existential || !existential.left || existential.left.type !== FormulaType.Negation) return null;
          const witnessTerm = icNode.focusTerm || Term.createVariable(chooseFreshVariableSymbol(icNode.focusFormula, icNode.question.goal));
          const positiveInstance = instantiateQuantifiedFormula(icNode.question.goal, witnessTerm);
          const negativeInstance = instantiateQuantifiedFormula(existential, witnessTerm);
          if (!positiveInstance || !negativeInstance) return null;
          const negInstanceAssumption = makeSimpleNode(negativeInstance, "Assumption");
          const existsNeg = makeUnaryNode(existential, "∃I", negInstanceAssumption);
          const contradiction = makeContradictionNode(existsNeg, source);
          const positiveByRAA = createNDProofNode({ formula: positiveInstance, reason: "RAA", subAssumption1: negInstanceAssumption, subEnd1: contradiction });
          return makeUnaryNode(icNode.question.goal, "∀I", positiveByRAA);
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

  const structuredRoot = tryStructuredProofFromContext(conclusion, rootCtx, STRUCTURED_PROOF_DEPTH_LIMIT, new Set());
  if (structuredRoot) {
    const fitchLines = buildFitchLines(structuredRoot, rootCtx);
    const parts = [];
    parts.push("=== 구문 확인 ===");
    parts.push(`전제: ${parsedPremises.length > 0 ? parsedPremises.map(formulaToDisplayString).join(", ") : "(없음)"}`);
    parts.push(`결론: ${formulaToDisplayString(conclusion)}`);
    parts.push("");
    parts.push("=== 결과 ===");
    parts.push("Y");
    parts.push("");
    return { text: parts.join("\n"), fitchLines, tree: null };
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
      return { text: timeoutParts.join("\n"), fitchLines: null, tree: null, timedOut: true };
    }
    throw err;
  }

  const parts = [];
  parts.push("=== 구문 확인 ===");
  parts.push(`전제: ${parsedPremises.length > 0 ? parsedPremises.map(formulaToDisplayString).join(", ") : "(없음)"}`);
  parts.push(`결론: ${formulaToDisplayString(conclusion)}`);
  parts.push("");
  parts.push("=== IC Tree ===");
  parts.push(renderICTreeText(tree));
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

  const finalRoot = simplifyNDProof(ndRoot, rootCtx) || ndRoot;
  const fitchLines = buildFitchLines(finalRoot, rootCtx);
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
