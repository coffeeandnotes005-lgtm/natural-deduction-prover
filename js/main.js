// IC Tree에서 사용할 규칙 이름들을 한곳에 모아둔 객체.
// 문자열을 직접 여러 번 쓰면 오타가 나기 쉬우므로,
// ICRule.AndUp 같은 식으로 참조하기 위해 만든다.
const ICRule = {
  // 더 이상 분해할 필요 없이 목표가 이미 확보된 경우.
  Leaf: "Leaf",

  // α/β 안에 A와 ¬A가 같이 있어서 모순이 생긴 경우.
  Clash: "Clash",

  // 직접 모순이 없을 때, 어떤 φ와 ¬φ를 각각 증명해서 ⊥를 만들려는 탐색 규칙.
  ContradSearch: "ContradSearch",

  // 아래 방향 규칙: 이미 가진 conjunction A∧B에서 왼쪽 A를 꺼내는 규칙.
  AndDown1: "AndDown1",

  // 아래 방향 규칙: 이미 가진 conjunction A∧B에서 오른쪽 B를 꺼내는 규칙.
  AndDown2: "AndDown2",

  // 아래 방향 규칙: 이미 가진 disjunction A∨B를 경우분석하는 규칙.
  OrDown: "OrDown",

  // 아래 방향 규칙: 이미 가진 implication A→B와 A 증명을 이용해 B를 얻는 규칙.
  ImpDown: "ImpDown",

  // 위 방향 규칙: 목표가 A∧B일 때 A와 B를 각각 증명하는 규칙.
  AndUp: "AndUp",

  // 위 방향 규칙: 목표가 A∨B일 때 왼쪽 A를 증명해서 A∨B를 얻는 규칙.
  OrUp1: "OrUp1",

  // 위 방향 규칙: 목표가 A∨B일 때 오른쪽 B를 증명해서 A∨B를 얻는 규칙.
  OrUp2: "OrUp2",

  // 위 방향 규칙: 목표가 A→B일 때 A를 가정하고 B를 증명하는 규칙.
  ImpUp: "ImpUp",

  // 위 방향 규칙: 목표가 ¬A일 때 A를 가정하고 모순을 증명하는 규칙.
  NegUp: "NegUp",

  // 고전논리 규칙: 목표 G를 증명하기 위해 ¬G를 가정하고 모순을 만드는 규칙.
  ClassicalUp: "ClassicalUp",

  // 아래 방향 규칙: ∀xA에서 특정 항 t를 넣어 A[t/x]를 얻는 규칙.
  ForallDown: "ForallDown",

  // 아래 방향 규칙: ∃xA에서 새 증인 변수를 가정해 A[w/x]로 진행하는 규칙.
  ExistsDown: "ExistsDown",

  // 위 방향 규칙: 목표가 ∀xA일 때 새 변수 w에 대해 A[w/x]를 증명하는 규칙.
  ForallUp: "ForallUp",

  // 위 방향 규칙: 목표가 ∃xA일 때 어떤 항 t에 대해 A[t/x]를 증명하는 규칙.
  ExistsUp: "ExistsUp",

  // 해당 질문에서 증명 탐색이 실패했음을 표시하는 규칙.
  Fail: "Fail",
};

// 자연연역 proof node마다 고유 id를 붙이기 위한 전역 카운터.
// createNDProofNode가 호출될 때마다 하나씩 증가한다.
let nextNodeId = 1;

// 주어진 공식 f의 부정 ¬f를 만든다.
function negateFormula(f) {
  return Formula.createNegation(f);
}

// 공식 f 안에 들어 있는 모든 부분공식을 out 배열에 모은다.
// 이미 들어간 공식은 중복해서 넣지 않는다.
function collectSubformulas(f, out) {
  // 공식이 없으면 처리하지 않는다.
  if (!f) return;

  // 같은 공식이 이미 out에 있으면 중복 수집을 막는다.
  if (containsFormula(out, f)) return;

  // 현재 공식 자체도 부분공식으로 포함한다.
  out.push(f);

  // ¬A이면 A 내부를 계속 탐색한다.
  if (f.type === FormulaType.Negation) {
    collectSubformulas(f.left, out);

  // A∧B, A∨B, A→B이면 왼쪽과 오른쪽을 모두 탐색한다.
  } else if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(f.type)) {
    collectSubformulas(f.left, out);
    collectSubformulas(f.right, out);

  // ∀xA, ∃xA이면 몸통 A를 탐색한다.
  } else if ([FormulaType.Universal, FormulaType.Existential].includes(f.type)) {
    collectSubformulas(f.left, out);
  }
}

// 항 term을 복사해서 새 객체로 만든다.
// 원본 객체를 그대로 공유하지 않게 하려는 용도다.
function cloneTerm(term) {
  // 항이 없으면 null 반환.
  if (!term) return null;

  // 변수항이면 같은 symbol을 가진 새 변수항 생성.
  if (term.type === TermType.Variable) return Term.createVariable(term.symbol);

  // 상항이면 같은 symbol을 가진 새 상항 생성.
  if (term.type === TermType.Constant) return Term.createConstant(term.symbol);

  // 현재 구조에서는 변수/상항만 쓰므로, 예외적 경우는 상항처럼 복사한다.
  return Term.createConstant(term.symbol);
}

// 공식 formula를 깊은 복사한다.
// 내부의 항과 하위 공식까지 새 객체로 다시 만든다.
function cloneFormula(formula) {
  // 공식이 없으면 null 반환.
  if (!formula) return null;

  // 명제문자 A, B, C 같은 경우.
  if (formula.type === FormulaType.SentenceLetter) {
    return Formula.createSentenceLetter(formula.symbol);
  }

  // 술어식 Px, Rab 같은 경우.
  // args도 각각 cloneTerm으로 복사한다.
  if (formula.type === FormulaType.Predicate) {
    return Formula.createPredicate(formula.symbol, (formula.args || []).map(cloneTerm));
  }

  // 모순기호 ⊥.
  if (formula.type === FormulaType.Contradiction) {
    return Formula.createContradiction();
  }

  // 부정 ¬A.
  if (formula.type === FormulaType.Negation) {
    return Formula.createNegation(cloneFormula(formula.left));
  }

  // 보편양화 ∀xA.
  if (formula.type === FormulaType.Universal) {
    return Formula.createUniversal(formula.variable, cloneFormula(formula.left));
  }

  // 존재양화 ∃xA.
  if (formula.type === FormulaType.Existential) {
    return Formula.createExistential(formula.variable, cloneFormula(formula.left));
  }

  // 나머지는 이항연결사 A∧B, A∨B, A→B로 보고 복사한다.
  return Formula.createBinary(
    formula.type,
    cloneFormula(formula.left),
    cloneFormula(formula.right)
  );
}

// 하나의 항 term 안에 등장하는 항들을 out에 모은다.
// 현재는 함수기호를 거의 쓰지 않지만, args가 있을 경우까지 대비해 재귀 처리한다.
function collectTermsFromTerm(term, out) {
  // 항이 없으면 처리하지 않는다.
  if (!term) return;

  // 현재 항 자체를 복사해서 넣는다.
  out.push(cloneTerm(term));

  // 항 안에 하위 항들이 있으면 그것들도 수집한다.
  for (const arg of term.args || []) {
    collectTermsFromTerm(arg, out);
  }
}

// 공식 formula 안에 등장하는 항들을 out에 모은다.
// 예: Pxa 안에서는 x, a를 모은다.
function collectTermsFromFormula(formula, out) {
  // 공식이 없으면 처리하지 않는다.
  if (!formula) return;

  // 술어식이면 그 인자항들을 수집한다.
  if (formula.type === FormulaType.Predicate) {
    for (const arg of formula.args || []) {
      collectTermsFromTerm(arg, out);
    }
    return;
  }

  // 부정식이면 내부 공식만 보면 된다.
  if (formula.type === FormulaType.Negation) {
    collectTermsFromFormula(formula.left, out);
    return;
  }

  // 이항연결사이면 왼쪽/오른쪽 모두 확인한다.
  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    collectTermsFromFormula(formula.left, out);
    collectTermsFromFormula(formula.right, out);
    return;
  }

  // 양화식이면 몸통 공식 안의 항들을 확인한다.
  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    collectTermsFromFormula(formula.left, out);
  }
}

// 항 배열에서 중복을 제거하되, 처음 등장한 순서는 유지한다.
// termToString(term)을 기준으로 같은 항인지 판단한다.
function uniqueTermsPreserveOrder(terms) {
  const seen = new Set();
  const out = [];

  for (const term of terms) {
    // 항을 문자열 key로 바꿔 중복 여부를 확인한다.
    const key = termToString(term);

    // 이미 본 항이면 건너뛴다.
    if (seen.has(key)) continue;

    // 처음 보는 항이면 기록하고 결과에 추가한다.
    seen.add(key);
    out.push(term);
  }

  return out;
}

// 현재 질문 q에서 사용할 수 있는 항 후보들을 모은다.
// 주로 ∀ 제거, ∃ 도입에서 어떤 항을 넣어볼지 정할 때 사용된다.
function collectQuestionTerms(q, extraFormula = null, extraTerm = null) {
  const raw = [];

  // alpha 쪽 공식들에서 항 수집.
  for (const f of q.alpha) {
    collectTermsFromFormula(f, raw);
  }

  // beta 쪽 공식들에서 항 수집.
  for (const f of q.beta) {
    collectTermsFromFormula(f, raw);
  }

  // 현재 목표 공식에서도 항 수집.
  collectTermsFromFormula(q.goal, raw);

  // 추가로 넘겨받은 공식에서도 항 수집.
  collectTermsFromFormula(extraFormula, raw);

  // 추가 공식이 양화식이면 그 바인딩 변수도 후보항으로 넣는다.
  // 예: ∀xFx라면 x를 후보로 넣어 Fx를 시도할 수 있게 한다.
  if (
    extraFormula &&
    [FormulaType.Universal, FormulaType.Existential].includes(extraFormula.type) &&
    extraFormula.variable
  ) {
    raw.push(Term.createVariable(extraFormula.variable));
  }

  // 별도로 추가 항이 주어졌으면 그것도 후보에 넣는다.
  if (extraTerm) {
    raw.push(cloneTerm(extraTerm));
  }

  // 중복을 제거하고 순서를 유지해서 반환한다.
  return uniqueTermsPreserveOrder(raw);
}

// 열린 전제/가정에 자유롭게 등장하는 변수항을 모은다.
// ∀ 제거, ∃ 도입에서 이런 변수항을 함부로 쓰면
// 전제에 의존한 특수한 변수를 일반 항처럼 사용하게 되어 잘못된 증명이 생길 수 있다.
function collectOpenFreeVariableSymbols(q) {
  const blocked = new Set();

  // alpha는 현재 열린 가정/전제 쪽 공식들이다.
  for (const formula of q.alpha || []) {
    for (const v of freeVariablesOfFormula(formula)) {
      blocked.add(v);
    }
  }

  // beta도 현재 사용 가능한 공식들이므로 같이 막는다.
  for (const formula of q.beta || []) {
    for (const v of freeVariablesOfFormula(formula)) {
      blocked.add(v);
    }
  }

  return blocked;
}

// ∀ 제거, ∃ 도입에서 사용할 안전한 항 후보만 남긴다.
// 상항은 허용하고, 열린 전제/가정에 자유롭게 등장한 변수항은 제외한다.
function collectSafeInstantiationTerms(q, extraFormula = null, extraTerm = null) {
  const terms = collectQuestionTerms(q, extraFormula, extraTerm);
  const blockedVars = collectOpenFreeVariableSymbols(q);

  return terms.filter((term) => {
    if (!term) return false;

    // 상항 a, b, c ... 는 안전하게 허용한다.
    if (term.type === TermType.Constant) return true;

    // 변수항 u, v, w, x, y, z ... 는 열린 전제/가정의 자유변수이면 제외한다.
    if (term.type === TermType.Variable) {
      return !blockedVars.has(term.symbol);
    }

    return false;
  });
}

// 하나의 항 term 안에 등장하는 변수 symbol들을 out Set에 모은다.
function collectVariableSymbolsFromTerm(term, out) {
  // 항이 없으면 처리하지 않는다.
  if (!term) return;

  // 변수항이면 그 변수 이름을 Set에 추가한다.
  if (term.type === TermType.Variable) {
    out.add(term.symbol);
  }

  // 하위 항들이 있으면 그 안의 변수들도 수집한다.
  for (const arg of term.args || []) {
    collectVariableSymbolsFromTerm(arg, out);
  }
}

// 공식 formula 안에 등장하는 모든 변수 기호를 out Set에 모은다.
// 여기서는 자유변수/속박변수를 구분하지 않고, 그냥 등장한 변수 이름을 전부 모은다.
function collectVariableSymbolsFromFormula(formula, out) {
  // 공식이 없으면 아무것도 하지 않는다.
  if (!formula) return;

  // 양화식이면 formula.variable에 바인딩 변수가 들어 있다.
  // 예: ∀xFx 에서는 x를 기록한다.
  if (formula.variable) out.add(formula.variable);

  // 술어식이면 그 안의 항들을 확인한다.
  // 예: Pxy 안에서는 x, y 같은 항 변수를 찾아야 한다.
  if (formula.type === FormulaType.Predicate) {
    for (const arg of formula.args || []) {
      collectVariableSymbolsFromTerm(arg, out);
    }
    return;
  }

  // 나머지 공식은 left/right를 재귀적으로 확인한다.
  // 부정식은 left만 있고, 이항연결사는 left/right가 있다.
  // 없는 쪽은 함수 첫 줄의 if (!formula) return;에서 걸러진다.
  collectVariableSymbolsFromFormula(formula.left, out);
  collectVariableSymbolsFromFormula(formula.right, out);
}

// 항 term 안에 자유롭게 등장하는 변수들을 out Set에 모은다.
// 현재 항 구조에서는 변수항 자체가 나오면 곧 자유변수로 본다.
function collectFreeVariablesTerm(term, out) {
  // 항이 없으면 아무것도 하지 않는다.
  if (!term) return;

  // 변수항이면 그 변수 이름을 자유변수로 추가한다.
  if (term.type === TermType.Variable) {
    out.add(term.symbol);
    return;
  }

  // 함수항 같은 확장 구조가 있을 경우를 대비해 하위 항도 확인한다.
  for (const arg of term.args || []) {
    collectFreeVariablesTerm(arg, out);
  }
}

// 공식 formula 안에 자유롭게 등장하는 변수들을 out Set에 모은다.
// bound는 현재 위치에서 이미 양화사에 의해 묶인 변수들의 집합이다.
function collectFreeVariablesFormula(formula, out, bound = new Set()) {
  // 공식이 없으면 아무것도 하지 않는다.
  if (!formula) return;

  // 술어식이면 그 인자항들 안의 변수들을 확인한다.
  if (formula.type === FormulaType.Predicate) {
    for (const arg of formula.args || []) {
      // 항 하나에서 변수들을 임시로 모은다.
      const tmp = new Set();
      collectFreeVariablesTerm(arg, tmp);

      // 임시로 모은 변수 중 bound에 없는 것만 자유변수다.
      for (const v of tmp) {
        if (!bound.has(v)) out.add(v);
      }
    }
    return;
  }

  // 부정식 ¬A이면 A 안의 자유변수를 그대로 확인한다.
  if (formula.type === FormulaType.Negation) {
    collectFreeVariablesFormula(formula.left, out, bound);
    return;
  }

  // 이항연결사 A∧B, A∨B, A→B이면 양쪽을 모두 확인한다.
  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    collectFreeVariablesFormula(formula.left, out, bound);
    collectFreeVariablesFormula(formula.right, out, bound);
    return;
  }

  // 양화식 ∀xA, ∃xA이면 x는 몸통 A 안에서 속박변수가 된다.
  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    // 기존 bound를 직접 바꾸지 않기 위해 새 Set을 만든다.
    const nextBound = new Set(bound);

    // 현재 양화사가 묶는 변수를 bound에 추가한다.
    nextBound.add(formula.variable);

    // 몸통 공식 안에서는 nextBound를 기준으로 자유변수를 찾는다.
    collectFreeVariablesFormula(formula.left, out, nextBound);
  }
}

// 항 term의 자유변수 집합을 반환한다.
function freeVariablesOfTerm(term) {
  const out = new Set();
  collectFreeVariablesTerm(term, out);
  return out;
}

// 공식 formula의 자유변수 집합을 반환한다.
function freeVariablesOfFormula(formula) {
  const out = new Set();
  collectFreeVariablesFormula(formula, out);
  return out;
}

// 공식 formula 안에 variable이 자유변수로 등장하는지 확인한다.
function formulaHasFreeVariable(formula, variable) {
  return freeVariablesOfFormula(formula).has(variable);
}

// 여러 대상 items를 보고, 거기에 아직 쓰이지 않은 새 변수기호를 고른다.
// 주로 ∀I, ∃E, 변수 치환 시 변수충돌을 피하려고 사용한다.
function chooseFreshVariableSymbol(...items) {
  // 이미 사용된 변수기호들을 모을 Set.
  const used = new Set();

  // 인자로 들어온 모든 대상을 검사한다.
  for (const item of items) {
    // null, undefined 등은 건너뛴다.
    if (!item) continue;

    // Term 객체면 그 항 안의 변수기호를 모은다.
    if (item instanceof Term) {
      collectVariableSymbolsFromTerm(item, used);

    // Formula 객체면 그 공식 안의 변수기호를 모은다.
    } else if (item instanceof Formula) {
      collectVariableSymbolsFromFormula(item, used);

    // 배열이면 배열 안의 원소들을 하나씩 확인한다.
    } else if (Array.isArray(item)) {
      for (const sub of item) {
        if (sub instanceof Term) collectVariableSymbolsFromTerm(sub, used);
        else if (sub instanceof Formula) collectVariableSymbolsFromFormula(sub, used);
        else if (typeof sub === "string") used.add(sub);
      }

    // Set이면 그 안의 값을 이미 사용된 이름으로 본다.
    } else if (item instanceof Set) {
      for (const v of item) used.add(v);

    // 문자열이면 그 문자열 자체를 사용된 변수기호로 본다.
    } else if (typeof item === "string") {
      used.add(item);
    }
  }

  // 먼저 기본 변수기호 u, v, w, x, y, z 중 안 쓰인 것을 찾는다.
  const bases = ["u", "v", "w", "x", "y", "z"];
  for (const base of bases) {
    if (!used.has(base)) return base;
  }

  // 기본 기호가 모두 쓰였으면 u1, v1, ..., z1, u2, ... 순서로 찾는다.
  for (let suffix = 1; suffix < 10000; suffix++) {
    for (const base of bases) {
      const candidate = `${base}${suffix}`;
      if (!used.has(candidate)) return candidate;
    }
  }

  // 10000까지도 못 찾으면 사실상 변수기호를 만들 수 없다고 보고 에러를 낸다.
  throw new Error("새 변항기호를 더 만들 수 없습니다.");
}

// 항 term 안에서 oldVar로 된 변수 출현을 newVar로 바꾼다.
// 이름은 BoundOccurrences지만, 항 자체에서는 속박 여부를 판단하지 않는다.
// 속박 여부는 공식 쪽 재귀 함수에서 제어한다.
function renameBoundOccurrencesInTerm(term, oldVar, newVar) {
  // 항이 없으면 null.
  if (!term) return null;

  // 변수항이면 oldVar인지 확인하고, 맞으면 newVar로 바꾼다.
  if (term.type === TermType.Variable) {
    return Term.createVariable(term.symbol === oldVar ? newVar : term.symbol);
  }

  // 상항은 변수 이름 변경 대상이 아니므로 그대로 복사한다.
  if (term.type === TermType.Constant) return Term.createConstant(term.symbol);

  // 현재 구조에서는 예외적 항도 상항처럼 처리한다.
  return Term.createConstant(term.symbol);
}

// 공식 formula 안에서 특정 bound variable의 출현을 새 변수명으로 바꾼다.
// 변수 포획을 피하기 위한 alpha-renaming에 사용된다.
function renameBoundOccurrencesInFormula(formula, oldVar, newVar) {
  // 공식이 없으면 null.
  if (!formula) return null;

  // 명제문자는 변수가 없으므로 그대로 복사한다.
  if (formula.type === FormulaType.SentenceLetter) {
    return Formula.createSentenceLetter(formula.symbol);
  }

  // 술어식이면 인자항들 안에서 oldVar를 newVar로 바꾼다.
  if (formula.type === FormulaType.Predicate) {
    return Formula.createPredicate(
      formula.symbol,
      (formula.args || []).map((arg) => renameBoundOccurrencesInTerm(arg, oldVar, newVar))
    );
  }

  // 모순기호 ⊥는 그대로 복사한다.
  if (formula.type === FormulaType.Contradiction) {
    return Formula.createContradiction();
  }

  // 부정식이면 내부 공식에 대해 계속 rename한다.
  if (formula.type === FormulaType.Negation) {
    return Formula.createNegation(renameBoundOccurrencesInFormula(formula.left, oldVar, newVar));
  }

  // 이항연결사이면 왼쪽과 오른쪽 모두 rename한다.
  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    return Formula.createBinary(
      formula.type,
      renameBoundOccurrencesInFormula(formula.left, oldVar, newVar),
      renameBoundOccurrencesInFormula(formula.right, oldVar, newVar)
    );
  }

  // 양화식이면 조심해야 한다.
  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    // 내부에 같은 이름의 양화사가 다시 나오면,
    // 그 안쪽 변수는 바깥 oldVar와 다른 바인딩으로 봐야 한다.
    // 그래서 여기서는 더 깊이 rename하지 않고 몸통을 그대로 복사한다.
    if (formula.variable === oldVar) {
      return formula.type === FormulaType.Universal
        ? Formula.createUniversal(formula.variable, cloneFormula(formula.left))
        : Formula.createExistential(formula.variable, cloneFormula(formula.left));
    }

    // 현재 양화사가 oldVar를 가로막지 않으면 몸통 안으로 계속 들어간다.
    return formula.type === FormulaType.Universal
      ? Formula.createUniversal(formula.variable, renameBoundOccurrencesInFormula(formula.left, oldVar, newVar))
      : Formula.createExistential(formula.variable, renameBoundOccurrencesInFormula(formula.left, oldVar, newVar));
  }

  // 알 수 없는 공식 타입이면 null.
  return null;
}

// 항 term 안에서 variable을 replacement 항으로 치환한다.
// 예: term이 x이고 variable이 x, replacement가 a이면 a가 된다.
function substituteTermInTerm(term, variable, replacement) {
  // 항이 없으면 null.
  if (!term) return null;

  // 변수항이면 치환 대상인지 확인한다.
  if (term.type === TermType.Variable) {
    // 대상 변수이면 replacement를 복사해서 넣고,
    // 아니면 원래 변수항을 새로 만들어 반환한다.
    return term.symbol === variable ? cloneTerm(replacement) : Term.createVariable(term.symbol);
  }

  // 상항은 치환 대상이 아니므로 그대로 복사한다.
  if (term.type === TermType.Constant) return Term.createConstant(term.symbol);

  // 현재 구조에서는 예외적 항도 상항처럼 처리한다.
  return Term.createConstant(term.symbol);
}

// 공식 formula 안에서 자유롭게 등장하는 variable을 replacement 항으로 치환한다.
// 양화사 내부에서는 변수 포획을 피하기 위해 필요하면 bound variable을 새 이름으로 바꾼다.
function substituteTermInFormula(formula, variable, replacement) {
  // 공식이 없으면 null.
  if (!formula) return null;

  // 명제문자는 항이 없으므로 그대로 복사한다.
  if (formula.type === FormulaType.SentenceLetter) {
    return Formula.createSentenceLetter(formula.symbol);
  }

  // 술어식이면 인자항들에 치환을 적용한다.
  if (formula.type === FormulaType.Predicate) {
    return Formula.createPredicate(
      formula.symbol,
      (formula.args || []).map((arg) => substituteTermInTerm(arg, variable, replacement))
    );
  }

  // 모순기호 ⊥는 그대로 복사한다.
  if (formula.type === FormulaType.Contradiction) {
    return Formula.createContradiction();
  }

  // 부정식이면 내부 공식에 치환을 적용한다.
  if (formula.type === FormulaType.Negation) {
    return Formula.createNegation(substituteTermInFormula(formula.left, variable, replacement));
  }

  // 이항연결사이면 왼쪽과 오른쪽 모두 치환한다.
  if ([FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(formula.type)) {
    return Formula.createBinary(
      formula.type,
      substituteTermInFormula(formula.left, variable, replacement),
      substituteTermInFormula(formula.right, variable, replacement)
    );
  }

  // 양화식에서는 치환 대상 변수와 양화사가 묶는 변수가 같은지 확인해야 한다.
  if ([FormulaType.Universal, FormulaType.Existential].includes(formula.type)) {
    // 예: ∀xFx에서 x를 a로 치환하려고 해도,
    // x는 이 양화사에 묶여 있으므로 몸통 안으로 들어가면 안 된다.
    if (formula.variable === variable) {
      return formula.type === FormulaType.Universal
        ? Formula.createUniversal(formula.variable, cloneFormula(formula.left))
        : Formula.createExistential(formula.variable, cloneFormula(formula.left));
    }

    // replacement 안에 자유롭게 등장하는 변수들을 구한다.
    const replacementFree = freeVariablesOfTerm(replacement);

    // 기본적으로는 기존 양화변수와 몸통을 그대로 쓴다.
    let nextVariable = formula.variable;
    let nextBody = formula.left;

    // 변수 포획 방지 조건.
    // replacement 안에 현재 양화변수가 자유롭게 들어 있고,
    // 동시에 몸통 안에 치환 대상 variable이 자유롭게 들어 있으면,
    // 그대로 치환할 경우 replacement의 자유변수가 양화사에 잡힐 수 있다.
    if (replacementFree.has(formula.variable) && formulaHasFreeVariable(formula.left, variable)) {
      // 충돌하지 않는 새 변수명을 고른다.
      const fresh = chooseFreshVariableSymbol(formula.left, replacement, variable, formula.variable);

      // 기존 bound variable을 fresh로 바꾼다.
      nextBody = renameBoundOccurrencesInFormula(formula.left, formula.variable, fresh);
      nextVariable = fresh;
    }

    // 안전하게 조정된 몸통에 실제 치환을 적용한다.
    const substitutedBody = substituteTermInFormula(nextBody, variable, replacement);

    // 원래 양화사 종류를 유지해서 반환한다.
    return formula.type === FormulaType.Universal
      ? Formula.createUniversal(nextVariable, substitutedBody)
      : Formula.createExistential(nextVariable, substitutedBody);
  }

  // 알 수 없는 공식 타입이면 null.
  return null;
}

// 양화식 ∀xA 또는 ∃xA에 항 term을 넣어 A[term/x]를 만든다.
// 예: ∀xFx와 a가 들어오면 Fa를 반환한다.
function instantiateQuantifiedFormula(quantifiedFormula, term) {
  // 양화식이 아니면 인스턴스화할 수 없으므로 null.
  if (
    !quantifiedFormula ||
    ![FormulaType.Universal, FormulaType.Existential].includes(quantifiedFormula.type)
  ) {
    return null;
  }

  // 양화식의 몸통에서 양화변수를 term으로 치환한다.
  return substituteTermInFormula(
    quantifiedFormula.left,
    quantifiedFormula.variable,
    term
  );
}

// ∃E나 ∀I처럼 “새 변수”가 필요한 규칙에서 사용할 증인 변수를 고른다.
// q는 현재 증명 질문이고, formula는 기준이 되는 양화식, goal은 현재 목표 공식이다.
function pickFreshWitnessVariable(q, formula, goal) {
  // 가능하면 양화식 자체의 변수명을 우선 후보로 쓴다.
  // 예: ∃xFx라면 먼저 x를 써볼 수 있는지 확인한다.
  const preferred = formula && formula.variable ? formula.variable : null;

  // 현재 열려 있는 공식들을 모은다.
  // alpha와 beta 양쪽 모두에서 자유롭게 등장하는 변수와 충돌하면 안 된다.
  const openFormulas = [
    ...(q.alpha || []),
    ...(q.beta || []),
  ];

  // 우선 후보 변수가 있으면, 그 변수를 안전하게 쓸 수 있는지 검사한다.
  if (preferred) {
    let blocked = false;

    // 현재 열려 있는 공식들 안에 preferred가 자유변수로 등장하면 사용할 수 없다.
    for (const openFormula of openFormulas) {
      if (formulaHasFreeVariable(openFormula, preferred)) {
        blocked = true;
        break;
      }
    }

    // 목표 공식 안에도 preferred가 자유변수로 등장하면 사용할 수 없다.
    if (!blocked && goal && formulaHasFreeVariable(goal, preferred)) {
      blocked = true;
    }

    // 막히지 않았다면 preferred를 새 증인 변수로 사용한다.
    if (!blocked) return preferred;
  }

  try {
    // preferred를 못 쓰면 alpha, beta, formula, goal 전체를 보고
    // 아직 쓰이지 않은 새 변수명을 고른다.
    return chooseFreshVariableSymbol(q.alpha, q.beta, formula, goal);
  } catch (err) {
    // 새 변수명을 만들 수 없으면 null을 반환한다.
    return null;
  }
}

// alpha 안에 이미 어떤 존재식의 증인 인스턴스가 들어 있는지 확인한다.
// 예: ∃xFx가 있고 alpha 안에 Fa 또는 Fu 같은 인스턴스가 이미 있으면 true.
function alphaHasExistentialWitness(q, existentialFormula) {
  // 이미 본 변수 이름 중복을 막기 위한 Set.
  const seen = new Set();

  // alpha 안에서 발견한 변수항들을 모은다.
  const variableTerms = [];

  // alpha 공식들을 하나씩 검사한다.
  for (const formula of q.alpha || []) {
    const terms = [];

    // 현재 공식 안의 모든 항을 모은다.
    collectTermsFromFormula(formula, terms);

    // 모은 항들 중 변수항만 추린다.
    for (const term of terms) {
      // 상항은 여기서 관심 없다.
      if (term.type !== TermType.Variable) continue;

      // 변수 이름을 key로 중복을 확인한다.
      const key = term.symbol;

      // 이미 본 변수면 건너뛴다.
      if (seen.has(key)) continue;

      // 처음 본 변수면 기록하고 후보에 넣는다.
      seen.add(key);
      variableTerms.push(term);
    }
  }

  // alpha에서 발견한 변수항들을 존재식에 넣어본다.
  for (const term of variableTerms) {
    // ∃xA의 몸통 A에 term을 넣어 A[term/x]를 만든다.
    const instance = instantiateQuantifiedFormula(existentialFormula, term);

    // 그 인스턴스가 alpha 안에 이미 있으면,
    // 이 존재식은 이미 한 번 증인 처리된 것으로 본다.
    if (instance && containsFormula(q.alpha, instance)) return true;
  }

  // 어떤 변수항으로도 기존 인스턴스를 찾지 못하면 false.
  return false;
}

// 내부 IC 규칙 이름을 화면에 보기 좋은 이름으로 바꾼다.
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

  // 등록된 이름이 있으면 그것을 쓰고, 없으면 원래 rule 문자열을 그대로 쓴다.
  return names[rule] || rule;
}

// IC Tree를 텍스트로 출력한다.
// node 하나를 한 줄로 쓰고, 자식 노드는 들여쓰기해서 재귀적으로 출력한다.
function renderICTreeText(node, indent = "") {
  // 노드가 없으면 빈 문자열.
  if (!node) return "";

  // 성공 노드는 Y, 실패 노드는 N으로 표시한다.
  const mark = node.success ? "Y" : "N";

  // 현재 노드 한 줄을 만든다.
  const lines = [
    `${indent}${mark} [${icRuleDisplayName(node.rule)}] ${questionToString(node.question)}`
  ];

  // 자식 노드들을 한 단계 더 들여써서 출력한다.
  for (const child of node.children || []) {
    lines.push(renderICTreeText(child, indent + "  "));
  }

  // 여러 줄을 줄바꿈으로 합친다.
  return lines.join("\n");
}

// 전체 IC Tree의 질문/규칙 노드 구조를 텍스트로 출력한다.
// 논문식 전체 탐색 공간을 확인할 때 사용한다.
function renderFullICTreeText(node, indent = "") {
  if (!node) return "";

  // 질문 노드: α; β ? G 자체를 표시한다.
  if (node.kind === "question") {
    const lines = [
      `${indent}${node.status} [?] ${questionToString(node.question)}`
    ];

    for (const ruleNode of node.ruleNodes || []) {
      lines.push(renderFullICTreeText(ruleNode, indent + "  "));
    }

    return lines.join("\n");
  }

  // 규칙 노드: 해당 질문에 적용된 규칙 후보를 표시한다.
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

// IC Tree에서 사용하는 질문 객체를 만든다.
// alpha: 현재 사용할 수 있는 가정 쪽 공식들.
// beta: 보조적으로 사용할 수 있는 공식들.
// goal: 증명하려는 목표 공식.
function createQuestion(alpha = [], beta = [], goal = null) {
  return { alpha, beta, goal };
}

// 배열 xs 안에 공식 f와 같은 공식이 있는지 확인한다.
function containsFormula(xs, f) {
  // 찾을 공식이 없으면 false.
  if (!f) return false;

  // equalFormula로 구조적으로 같은 공식인지 확인한다.
  return xs.some((x) => equalFormula(x, f));
}

// q의 alpha 또는 beta 안에 공식 f가 들어 있는지 확인한다.
function containsInAlphaBeta(q, f) {
  return containsFormula(q.alpha, f) || containsFormula(q.beta, f);
}

// 배열 xs에 공식 f가 아직 없으면 추가한다.
// 이미 있으면 중복 추가하지 않는다.
function addUnique(xs, f) {
  if (!containsFormula(xs, f)) xs.push(f);
}

// 공식 배열 xs를 {A, B, C} 같은 문자열로 바꾼다.
function sequenceToString(xs) {
  return "{" + xs.map((x) => formulaToString(x)).join(", ") + "}";
}

// 질문 q를 "{alpha}; {beta} ? goal" 형태의 문자열로 바꾼다.
function questionToString(q) {
  return `${sequenceToString(q.alpha)}; ${sequenceToString(q.beta)} ? ${formulaToString(q.goal)}`;
}

// 질문 q를 탐색 캐시용 문자열 key로 바꾼다.
// alpha/beta의 순서 차이 때문에 다른 질문으로 취급되지 않도록 정렬해서 만든다.
function questionKey(q) {
  // alpha 공식들을 문자열로 바꾼 뒤 정렬한다.
  const a = [...q.alpha].map(formulaToString).sort();

  // beta 공식들도 문자열로 바꾼 뒤 정렬한다.
  const b = [...q.beta].map(formulaToString).sort();

  // alpha 부분 key 시작.
  let key = "A[";

  // alpha 공식들을 key에 넣는다.
  for (const s of a) key += `(${s})`;

  // beta 부분 key 시작.
  key += "]B[";

  // beta 공식들을 key에 넣는다.
  for (const s of b) key += `(${s})`;

  // goal까지 포함해서 최종 key를 완성한다.
  key += `]G[${formulaToString(q.goal)}]`;

  return key;
}

// q의 alpha/beta 전체 안에 A와 ¬A가 동시에 있는지 확인한다.
// 있으면 모순 Clash가 가능하다.
function hasClashInAlphaBeta(q) {
  // alpha와 beta를 하나의 배열로 합친다.
  const allFormulas = [...q.alpha, ...q.beta];

  // 모든 공식을 검사한다.
  for (const f of allFormulas) {
    // 공식이 없거나 ⊥ 자체면 여기서는 건너뛴다.
    if (!f || f.type === FormulaType.Contradiction) continue;

    // f가 ¬A이면 A가 같이 있는지 확인한다.
    if (f.type === FormulaType.Negation) {
      if (f.left && containsFormula(allFormulas, f.left)) return true;

    // f가 A이면 ¬A가 같이 있는지 확인한다.
    } else {
      if (containsFormula(allFormulas, negateFormula(f))) return true;
    }
  }

  // 어떤 충돌도 없으면 false.
  return false;
}

// alpha와 beta의 공식들을 원래 순서를 유지하면서 하나의 목록으로 만든다.
// 각 항목에는 공식, alpha에서 왔는지 여부, 원래 index가 들어간다.
function alphaBetaOrder(q) {
  const result = [];

  // alpha 공식들 기록.
  q.alpha.forEach((formula, index) => result.push({
    formula,
    fromAlpha: true,
    index
  }));

  // beta 공식들 기록.
  q.beta.forEach((formula, index) => result.push({
    formula,
    fromAlpha: false,
    index
  }));

  return result;
}

// 공식 안에 등장하는 모든 부정식 ¬φ를 찾고,
// 그 안쪽 φ만 ContradSearch 후보로 모은다.
// 이것이 N(γ) 방식이다.
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

// N(γ): γ 안에 등장하는 부정식 ¬φ들의 내부 φ만 후보로 삼는다.
// 여기서 γ는 현재 α, β, 그리고 ¬G로 잡는다.
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

// IC Tree의 노드 객체를 만든다.
// question: 현재 질문.
// rule: 이 질문에 적용된 규칙.
// success: 이 노드가 성공했는지 여부.
// children: 하위 질문 노드들.
// focusFormula: 이 규칙이 적용된 주요 공식.
// focusTerm: 양화 규칙 등에서 사용한 항.
// meta: 노드 평가용 부가 정보.
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

// 전체 IC Tree에서 “질문 노드”를 만든다.
// 질문 노드는 α; β ? G 같은 하나의 탐색 상태를 나타낸다.
function createICQuestionNode(question, status = "open", ruleNodes = [], meta = {}) {
  return {
    kind: "question",
    question,
    status,      // "open", "Y", "N"
    ruleNodes,   // 이 질문에서 적용 가능한 규칙 후보들
    meta,
  };
}

// 전체 IC Tree에서 “규칙 노드”를 만든다.
// 규칙 노드는 특정 질문에 어떤 IC 규칙을 적용했는지를 나타낸다.
function createICRuleNode(rule, status = "open", children = [], focusFormula = null, focusTerm = null, meta = {}) {
  return {
    kind: "rule",
    rule,
    status,       // "open", "Y", "N"
    children,     // 이 규칙 적용으로 생기는 하위 질문 노드들
    focusFormula,
    focusTerm,
    meta,
  };
}

// status를 기존 success boolean처럼 쓰기 위한 보조 함수.
function isICSuccess(node) {
  return node && node.status === "Y";
}

function isICFailure(node) {
  return node && node.status === "N";
}

// IC Tree metric 계산 결과를 캐시하기 위한 WeakMap.
// 같은 노드의 metric을 여러 번 다시 계산하지 않기 위해 쓴다.
const icTreeMetricCache = new WeakMap();

// 루트에서 시도할 최대 후보 수.
// 너무 많은 탐색을 막기 위한 제한값이다.
const MAX_ROOT_ATTEMPTS = 800;

// 증명 탐색 제한 시간. 10000ms = 10초.
const PROOF_TIME_LIMIT_MS = 10000;

// 시간초과를 식별하기 위한 에러 코드 문자열.
const PROOF_TIMEOUT_ERROR = "PROOF_TIMEOUT";

// 증명 탐색 시간초과 에러 객체를 만든다.
function createProofTimeoutError() {
  const error = new Error(PROOF_TIMEOUT_ERROR);

  // catch에서 일반 에러와 구분하기 위해 code를 붙인다.
  error.code = PROOF_TIMEOUT_ERROR;

  return error;
}

// 현재 시간이 deadlineMs를 넘었는지 확인한다.
// 넘었으면 시간초과 에러를 던져서 탐색을 중단한다.
function ensureSearchNotTimedOut(options = {}) {
  if (Number.isFinite(options.deadlineMs) && performance.now() >= options.deadlineMs) {
    throw createProofTimeoutError();
  }
}

// 어떤 IC 규칙이 새로운 가정 박스를 몇 개 여는지 계산한다.
// 증명 후보를 비교할 때, 불필요하게 가정이 많이 열린 증명을 낮게 평가하려는 용도다.
function assumptionOpeningsForRule(rule) {
  // ∨ 제거는 두 경우분석이므로 가정 박스 2개를 연다.
  if (rule === ICRule.OrDown) return 2;

  // ∃ 제거, → 도입, ¬ 도입, RAA는 가정 박스 1개를 연다.
  if ([ICRule.ExistsDown, ICRule.ImpUp, ICRule.NegUp, ICRule.ClassicalUp].includes(rule)) {
    return 1;
  }

  // 나머지 규칙은 새 가정을 열지 않는다.
  return 0;
}

// IC Tree 노드의 복잡도 metric을 계산한다.
// 더 짧고, 반복 가정이 적고, 모순 탐색이 적은 증명을 고르기 위한 기준이다.
function getICTreeMetrics(node) {
  // 노드가 없으면 모든 metric을 0으로 둔다.
  if (!node) {
    return {
      repeatedAssumptions: 0,
      contradictionSearches: 0,
      nodes: 0,
      maxDepth: 0,
      assumptionOpenings: 0,
    };
  }

  // 이미 계산한 노드면 캐시된 값을 반환한다.
  if (icTreeMetricCache.has(node)) return icTreeMetricCache.get(node);

  // 현재 노드 하나에 대한 기본 metric.
  const metrics = {
    // 같은 가정을 반복해서 연 횟수.
    repeatedAssumptions: node.meta?.repeatedAssumptions || 0,

    // ContradSearch 규칙을 사용했는지 여부.
    contradictionSearches: node.rule === ICRule.ContradSearch ? 1 : 0,

    // 현재 노드 하나를 센다.
    nodes: 1,

    // 현재 노드만 보면 깊이는 1.
    maxDepth: 1,

    // 현재 규칙이 여는 가정 박스 수.
    assumptionOpenings: assumptionOpeningsForRule(node.rule),
  };

  // 자식 노드들의 metric을 합산한다.
  for (const child of node.children || []) {
    const childMetrics = getICTreeMetrics(child);

    // 반복 가정 수 합산.
    metrics.repeatedAssumptions += childMetrics.repeatedAssumptions;

    // 모순 탐색 수 합산.
    metrics.contradictionSearches += childMetrics.contradictionSearches;

    // 전체 노드 수 합산.
    metrics.nodes += childMetrics.nodes;

    // 열린 가정 박스 수 합산.
    metrics.assumptionOpenings += childMetrics.assumptionOpenings;

    // 최대 깊이는 자식 깊이에 현재 노드 1단계를 더한 값과 비교한다.
    metrics.maxDepth = Math.max(metrics.maxDepth, childMetrics.maxDepth + 1);
  }

  // 계산 결과를 캐시에 저장한다.
  icTreeMetricCache.set(node, metrics);

  return metrics;
}

// 두 IC Tree metric을 비교한다.
// 음수이면 a가 b보다 더 좋은 증명 후보라는 뜻이다.
function compareICTreeMetrics(a, b) {
  // 앞쪽 기준이 더 우선된다.
  const orderedKeys = [
    'repeatedAssumptions',
    'contradictionSearches',
    'nodes',
    'maxDepth',
    'assumptionOpenings',
  ];

  // 기준들을 순서대로 비교한다.
  for (const key of orderedKeys) {
    const diff = a[key] - b[key];

    // 차이가 있으면 그 기준으로 승부가 난다.
    if (diff !== 0) return diff;
  }

  // 모든 기준이 같으면 동급으로 본다.
  return 0;
}

// 현재까지 찾은 최선의 IC Tree 노드(currentBest)와 새 후보(candidate)를 비교해서
// 더 좋은 쪽을 반환한다.
function chooseBetterICTreeNode(currentBest, candidate) {
  // 후보가 없거나 실패 노드이면 기존 최선값을 그대로 유지한다.
  if (!candidate || !candidate.success) return currentBest;

  // 아직 최선값이 없으면 후보가 곧 최선값이다.
  if (!currentBest) return candidate;

  // 기존 최선 노드의 복잡도 정보를 계산한다.
  const currentMetrics = getICTreeMetrics(currentBest);

  // 새 후보 노드의 복잡도 정보를 계산한다.
  const candidateMetrics = getICTreeMetrics(candidate);

  // 후보가 기존 최선보다 더 작고 단순하면 후보를 선택하고,
  // 아니면 기존 최선값을 유지한다.
  return compareICTreeMetrics(candidateMetrics, currentMetrics) < 0 ? candidate : currentBest;
}


// 외부에서 IC Tree 탐색을 호출하는 래퍼 함수.
// 기존 DFS 탐색 대신 공정 IC Tree 탐색으로 보낸다.
function buildICTree(q, activeStates, failedStates, successStates = new Map(), options = {}) {
  return buildFairICTreeBasic(q, options);
}

// q 하나에서 적용 가능한 IC 규칙 후보들을 한 단계만 만든다.
// 여기서는 재귀 탐색하지 않고, 다음 질문 노드만 만든다.
function expandICNodeOneStep(q) {
  const results = [];

  // Leaf
  if (containsInAlphaBeta(q, q.goal)) {
    results.push(createICTreeNode(q, ICRule.Leaf, true));
    return results;
  }

  // Clash
  if (q.goal && q.goal.type === FormulaType.Contradiction && hasClashInAlphaBeta(q)) {
    results.push(createICTreeNode(q, ICRule.Clash, true));
    return results;
  }

  // ∧↑
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

  // →↑
  if (q.goal && q.goal.type === FormulaType.Implication && q.goal.left && q.goal.right) {
    const newAlpha = [...q.alpha, q.goal.left];
    const subQ = createQuestion(newAlpha, q.beta, q.goal.right);

    results.push(
      createICTreeNode(q, ICRule.ImpUp, false, [
        createICTreeNode(subQ)
      ])
    );
  }

  // ∨↑1 / ∨↑2
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

  // ∃↑
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

  // ¬↑
  if (q.goal && q.goal.type === FormulaType.Negation && q.goal.left) {
    const newAlpha = [...q.alpha, q.goal.left];
    const subQ = createQuestion(newAlpha, q.beta, Formula.createContradiction());

    results.push(
      createICTreeNode(q, ICRule.NegUp, false, [
        createICTreeNode(subQ)
      ])
    );
  }

  // ClassicalUp / ⊥c
  // 목표 G가 ⊥도 아니고 ¬A도 아니면,
  // ¬G를 가정하고 ⊥를 증명해 G를 얻으려고 한다.
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

  // ∀↑
  if (q.goal && q.goal.type === FormulaType.Universal && q.goal.left) {
    const blockedVars = collectOpenFreeVariableSymbols(q);

    const freshVar = chooseFreshVariableSymbol(q.alpha, q.beta, q.goal);

    if (blockedVars.has(freshVar)) {
      // 안전하지 않으면 스킵
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

  // ∧↓1 / ∧↓2
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

  // →↓
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

    // ∨↓
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

  // ∀↓
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

  // ∃↓
  for (const f of q.alpha) {
    if (f.type !== FormulaType.Existential) continue;

    // 이미 한 번 증인 사용했으면 스킵
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

  // ContradSearch / N(γ)
  // 목표가 ⊥인데 직접 Clash가 없으면,
  // N(γ) 후보 φ에 대해 φ와 ¬φ를 각각 증명해 ⊥를 만들려고 한다.
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

// 전체 IC Tree용으로, 질문 q에서 가능한 모든 규칙 후보를 한 단계 펼친다.
// 기존 expandICNodeOneStep(q)가 만든 후보들을 새 QuestionNode / RuleNode 구조로 변환한다.
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

// 전체 IC Tree에서 규칙 노드 하나를 depth 제한 안에서 닫는다.
// 규칙 노드는 모든 자식 질문이 Y일 때만 Y가 된다.
function closeICRuleNodeAtDepth(ruleNode, depth, path, options = {}) {
  ensureSearchNotTimedOut(options);

  if (!ruleNode) return createICRuleNode(ICRule.Fail, "N");

  // Leaf, Clash처럼 이미 Y인 규칙은 그대로 닫힌 성공 규칙이다.
  if (ruleNode.status === "Y") return ruleNode;

  // 더 내려갈 수 없으면 아직 성공을 확인하지 못한 것이므로 N으로 닫는다.
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

// 전체 IC Tree에서 질문 노드 하나를 depth 제한 안에서 닫는다.
// 질문 노드는 성공한 규칙 후보가 하나라도 있으면 Y, 전부 실패하면 N이 된다.
function closeICQuestionAtDepth(q, depth, path, options = {}) {
  ensureSearchNotTimedOut(options);

  const key = questionKey(q);

  // 같은 가지 안에서 같은 질문이 반복되면 그 가지는 N으로 닫는다.
  if (path.has(key)) {
    return createICQuestionNode(q, "N", [], {
      closedBy: "repeat",
    });
  }

  // depth가 끝났으면 더 탐색하지 않고 N으로 닫는다.
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

// 전체 IC Tree 질문 노드에서 성공한 규칙 하나를 골라,
// 기존 extractNDProof가 읽을 수 있는 옛 IC derivation 형식으로 변환한다.
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

// 후보 IC 노드의 자식들을 depth 제한 안에서 평가한다.
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

// 주어진 depth 안에서 q를 증명할 수 있는 IC 후보를 찾는다.
// 한 규칙만 깊게 파는 게 아니라, q에서 가능한 후보들을 모두 만든 뒤 평가한다.
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

// 공정 IC Tree 탐색.
// depth를 0, 1, 2, ... 순서로 늘리면서 전체 IC Tree를 만들고,
// 모든 가지를 Y/N으로 닫은 뒤, 성공한 ic-derivation 하나를 기존 형식으로 추출한다.
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

// 자연연역 증명 노드 하나를 만든다.
// parent1/parent2는 일반 추론의 부모 줄이고,
// subAssumption/subEnd는 부분증명 박스의 시작/끝 노드다.
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
    // 각 노드에 고유 id를 붙인다.
    id: nextNodeId++,

    // 이 노드가 증명하는 공식.
    formula,

    // 추론 규칙 이름. 예: Premise, Assumption, ->E, ∀I 등.
    reason,

    // 첫 번째 부모 증명 노드.
    parent1,

    // 두 번째 부모 증명 노드.
    parent2,

    // 첫 번째 부분증명의 가정 노드.
    subAssumption1,

    // 첫 번째 부분증명의 끝 노드.
    subEnd1,

    // 두 번째 부분증명의 가정 노드.
    subAssumption2,

    // 두 번째 부분증명의 끝 노드.
    subEnd2,
  };
}

// 증명 문맥 ctx 안에서 target 공식과 같은 공식을 증명한 노드를 찾는다.
// 뒤에서부터 찾으므로, 가장 최근에 추가된 증명 노드를 우선 반환한다.
function findProofWithFormula(ctx, target) {
  for (let i = ctx.length - 1; i >= 0; i--) {
    if (equalFormula(ctx[i].formula, target)) return ctx[i];
  }
  return null;
}

// 문맥 ctx 안에서 A와 ¬A의 충돌 쌍을 찾는다.
// 찾으면 [positiveNode, negativeNode] 형태로 반환한다.
function findClashWitnessInContext(ctx) {
  // 최신 노드부터 거꾸로 확인한다.
  for (let i = ctx.length - 1; i >= 0; i--) {
    const node = ctx[i];
    const f = node.formula;

    // 공식이 없거나 ⊥이면 건너뛴다.
    if (!f || f.type === FormulaType.Contradiction) continue;

    // f가 ¬A이면 A가 있는지 찾는다.
    if (f.type === FormulaType.Negation) {
      const pos = findProofWithFormula(ctx, f.left);
      if (pos) return [pos, node];

    // f가 A이면 ¬A가 있는지 찾는다.
    } else {
      const negNode = findProofWithFormula(ctx, negateFormula(f));
      if (negNode) return [node, negNode];
    }
  }

  // 충돌 쌍이 없으면 null 쌍.
  return [null, null];
}

// 부모가 없는 단순 증명 노드를 만든다.
// 주로 Premise, Assumption 같은 노드에 사용된다.
function makeSimpleNode(formula, reason) {
  return createNDProofNode({ formula, reason });
}

// 부모가 하나인 증명 노드를 만든다.
// 예: ∧E, ∀E, ∃I, ∨I 같은 규칙에 사용된다.
function makeUnaryNode(formula, reason, p1) {
  return createNDProofNode({ formula, reason, parent1: p1 });
}

// 부모가 둘인 증명 노드를 만든다.
// 예: →E, ∧I, ¬E 같은 규칙에 사용된다.
function makeBinaryNode(formula, reason, p1, p2) {
  return createNDProofNode({ formula, reason, parent1: p1, parent2: p2 });
}

// A와 ¬A로부터 ⊥를 만드는 노드를 만든다.
function makeContradictionNode(positive, negative) {
  return makeBinaryNode(Formula.createContradiction(), "~E", positive, negative);
}

// 증명 노드 배열 xs에 node를 추가하되,
// 같은 공식을 증명한 노드가 이미 있으면 추가하지 않는다.
// 추가했으면 true, 추가하지 않았으면 false.
function addProofNodeUniqueByFormula(xs, node) {
  // 노드나 공식이 없으면 추가 실패.
  if (!node || !node.formula) return false;

  // 같은 공식이 이미 있으면 추가하지 않는다.
  if (findProofWithFormula(xs, node.formula)) return false;

  // 새 공식이면 추가한다.
  xs.push(node);
  return true;
}

// IC Tree 노드를 실제 자연연역 proof node로 변환한다.
// IC Tree는 “어떤 규칙으로 성공했는지”의 탐색 기록이고,
// 이 함수는 그것을 실제 Fitch 출력 가능한 증명 노드 구조로 바꾼다.
function extractNDProof(icNode, ctx) {
  // IC 노드가 없거나 실패 노드이면 변환할 수 없다.
  if (!icNode || !icNode.success) return null;

  // IC 규칙 종류에 따라 자연연역 노드를 구성한다.
  switch (icNode.rule) {
    // Leaf는 목표가 이미 ctx 안에 있다는 뜻이므로 해당 증명 노드를 찾는다.
    case ICRule.Leaf:
      return findProofWithFormula(ctx, icNode.question.goal);

    // Clash는 ctx 안에 A와 ¬A가 있다는 뜻이므로 ⊥ 노드를 만든다.
    case ICRule.Clash: {
      const [pos, neg] = findClashWitnessInContext(ctx);
      if (!pos || !neg) return null;
      return makeContradictionNode(pos, neg);
    }

    // ContradSearch는 φ와 ¬φ를 각각 증명한 뒤 ⊥를 만든다.
    case ICRule.ContradSearch: {
      const leftProof = extractNDProof(icNode.children[0], ctx);
      if (!leftProof) return null;

      const rightProof = extractNDProof(icNode.children[1], ctx);
      if (!rightProof) return null;

      return makeContradictionNode(leftProof, rightProof);
    }

    // AndDown1은 A∧B에서 A를 꺼낸 뒤 자식 증명을 이어간다.
    case ICRule.AndDown1: {
      const source = findProofWithFormula(ctx, icNode.focusFormula);

      if (!source || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Conjunction) return null;

      const derivedFormula = icNode.focusFormula.left;
      if (!derivedFormula) return null;

      const derived = makeUnaryNode(derivedFormula, "&E", source);
      const nextCtx = [...ctx, derived];

      return extractNDProof(icNode.children[0], nextCtx);
    }

    // AndDown2는 A∧B에서 B를 꺼낸 뒤 자식 증명을 이어간다.
    case ICRule.AndDown2: {
      const source = findProofWithFormula(ctx, icNode.focusFormula);

      if (!source || !icNode.focusFormula || icNode.focusFormula.type !== FormulaType.Conjunction) return null;

      const derivedFormula = icNode.focusFormula.right;
      if (!derivedFormula) return null;

      const derived = makeUnaryNode(derivedFormula, "&E", source);
      const nextCtx = [...ctx, derived];

      return extractNDProof(icNode.children[0], nextCtx);
    }

    // ForallDown은 ∀xA에서 특정 항 t를 넣어 A[t/x]를 얻은 뒤 자식 증명을 이어간다.
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

    // ImpDown은 A→B와 A 증명으로 B를 얻은 뒤 자식 증명을 이어간다.
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

    // OrDown은 A∨B를 가지고 A 가정 분기, B 가정 분기를 각각 만들어 ∨E를 구성한다.
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

    // ExistsDown은 ∃xA에서 새 증인 인스턴스 A[w/x]를 가정하고 ∃E를 구성한다.
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

    // AndUp은 왼쪽 목표와 오른쪽 목표를 각각 증명해 ∧I로 합친다.
    case ICRule.AndUp: {
      const leftProof = extractNDProof(icNode.children[0], ctx);
      if (!leftProof) return null;

      const rightProof = extractNDProof(icNode.children[1], ctx);
      if (!rightProof || !icNode.question.goal) return null;

      return makeBinaryNode(icNode.question.goal, "&I", leftProof, rightProof);
    }

    // OrUp1은 왼쪽 항을 증명해 ∨I 1로 목표 disjunction을 얻는다.
    case ICRule.OrUp1: {
      const leftProof = extractNDProof(icNode.children[0], ctx);
      if (!leftProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∨I 1", leftProof);
    }

    // OrUp2는 오른쪽 항을 증명해 ∨I 2로 목표 disjunction을 얻는다.
    case ICRule.OrUp2: {
      const rightProof = extractNDProof(icNode.children[0], ctx);
      if (!rightProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∨I 2", rightProof);
    }

    // ImpUp은 A를 가정하고 B를 증명해서 A→B를 만든다.
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

    // ForallUp은 몸통 인스턴스 증명에서 ∀I로 목표 보편식을 만든다.
    case ICRule.ForallUp: {
      const bodyProof = extractNDProof(icNode.children[0], ctx);
      if (!bodyProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∀I", bodyProof);
    }

    // ExistsUp은 witness 인스턴스 증명에서 ∃I로 목표 존재식을 만든다.
    case ICRule.ExistsUp: {
      const witnessProof = extractNDProof(icNode.children[0], ctx);
      if (!witnessProof || !icNode.question.goal) return null;

      return makeUnaryNode(icNode.question.goal, "∃I", witnessProof);
    }

    // NegUp은 A를 가정하고 ⊥를 얻어 ¬A를 만든다.
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

    // ClassicalUp은 ¬G를 가정하고 ⊥를 얻어 RAA로 G를 만든다.
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

    // 처리하지 않는 IC 규칙이면 실패.
    default:
      return null;
  }
}

// 입력된 전제/결론 문자열을 파싱하고, 증명 탐색을 실행한 뒤,
// 화면 출력에 필요한 결과 객체를 반환한다.
function solveProofData(premisesInput, conclusionInput, signature) {
  // 전제 입력 앞뒤 공백 제거.
  premisesInput = premisesInput.trim();

  // 결론 입력 앞뒤 공백 제거.
  conclusionInput = conclusionInput.trim();

  // 전제 문자열을 공식 배열로 파싱한다.
  const parsedPremises = parsePremises(premisesInput, signature);

  // 결론 문자열을 하나의 공식으로 파싱한다.
  const conclusion = parseSingleFormula(conclusionInput, signature);

  // 파싱된 전제를 premises라는 이름으로 둔다.
  const premises = parsedPremises;

  // 자연연역 증명 문맥의 시작점.
  const rootCtx = [];

  // 각 전제를 Premise 노드로 만들어 rootCtx에 넣는다.
  for (const premise of premises) {
    rootCtx.push(createNDProofNode({ formula: premise, reason: "Premise" }));
  }

  // IC Tree 방식으로 탐색한다.
  const root = createQuestion([...premises], [], conclusion);

  // 현재 재귀 경로에서 활성화된 질문 상태.
  const activeStates = new Set();

  // 이미 실패한 질문 상태.
  const failedStates = new Set();

  // IC Tree 결과를 담을 변수.
  let tree;

  try {
    // IC Tree 탐색 실행.
    tree = buildICTree(root, activeStates, failedStates, new Map(), {
      maxRootAttempts: MAX_ROOT_ATTEMPTS,
      deadlineMs: performance.now() + PROOF_TIME_LIMIT_MS,
    });
  } catch (err) {
    // 탐색 중 시간초과가 발생한 경우.
    if (err && err.code === PROOF_TIMEOUT_ERROR) {
      const timeoutParts = [];

      // 구문 확인 영역.
      timeoutParts.push("=== 구문 확인 ===");

      // 전제 표시.
      timeoutParts.push(`전제: ${parsedPremises.length > 0 ? parsedPremises.map(formulaToDisplayString).join(", ") : "(없음)"}`);

      // 결론 표시.
      timeoutParts.push(`결론: ${formulaToDisplayString(conclusion)}`);

      // 빈 줄.
      timeoutParts.push("");

      // 결과 영역.
      timeoutParts.push("=== 결과 ===");

      // 시간초과 메시지.
      timeoutParts.push(`제한시간 안에 증명을 생성하지 못했습니다. (${PROOF_TIME_LIMIT_MS / 1000}초)`);

      // 빈 줄.
      timeoutParts.push("");

      // 시간초과 결과 객체 반환.
      return {
        text: timeoutParts.join("\n"),
        fitchLines: null,
        tree: null,
        timedOut: true
      };
    }

    // 시간초과가 아닌 다른 에러는 다시 던진다.
    throw err;
  }

  // IC Tree 출력용 텍스트 배열.
  const parts = [];

  // 구문 확인 영역.
  parts.push("=== 구문 확인 ===");

  // 전제 표시.
  parts.push(`전제: ${parsedPremises.length > 0 ? parsedPremises.map(formulaToDisplayString).join(", ") : "(없음)"}`);

  // 결론 표시.
  parts.push(`결론: ${formulaToDisplayString(conclusion)}`);

  // 빈 줄.
  parts.push("");

  // IC Tree를 텍스트로 변환해 넣는다.
  parts.push("=== IC Tree ===");

   if (tree.meta && tree.meta.fullTree) {
  parts.push(renderFullICTreeText(tree.meta.fullTree));
     } else {
     parts.push(renderICTreeText(tree));
}

  // 빈 줄.
  parts.push("");

  // 결과 영역.
  parts.push("=== 결과 ===");

  // tree.success에 따라 Y 또는 N을 출력한다.
  parts.push(tree.success ? "Y" : "N");

  // 빈 줄.
  parts.push("");

  // IC Tree 탐색이 실패한 경우.
  if (!tree.success) {
    return { text: parts.join("\n"), fitchLines: null, tree };
  }

  // IC Tree 성공 결과를 자연연역 proof node로 변환한다.
  const ndRoot = extractNDProof(tree, rootCtx);

  // 변환에 실패한 경우.
  if (!ndRoot) {
    parts.push("추출 실패");
    return { text: parts.join("\n"), fitchLines: null, tree };
  }

  // 최종 proof node를 Fitch 출력 줄들로 변환한다.
  const fitchLines = buildFitchLines(ndRoot, rootCtx);

  // 최종 결과 객체 반환.
  return { text: parts.join("\n"), fitchLines, tree };
}

// 전제 입력 textarea 요소.
const premisesEl = document.getElementById("premises");

// 결론 입력 textarea 요소.
const conclusionEl = document.getElementById("conclusion");

// 출력 영역 요소.
const outputEl = document.getElementById("output");

// Proof 버튼 요소.
const proofBtn = document.getElementById("proofBtn");

// 모두 지우기 버튼 요소.
const clearBtn = document.getElementById("clearBtn");

// 줄 구분 켜기/끄기 버튼 요소.
const stripeToggleBtn = document.getElementById("stripeToggleBtn");

// 테마 전환 버튼 요소.
const themeToggleBtn = document.getElementById("themeToggleBtn");

// 논리기호 입력 버튼들.
const symbolButtons = document.querySelectorAll("[data-symbol]");

// 마지막으로 포커스된 입력칸.
// 기호 버튼을 눌렀을 때 어디에 삽입할지 정하는 데 쓴다.
let lastFocused = premisesEl;

// Fitch 출력의 줄무늬 표시 여부.
let zebraStripingEnabled = true;

// renderer 쪽에서도 접근할 수 있게 window에 저장한다.
window.zebraStripingEnabled = zebraStripingEnabled;

// 현재 라이트 테마 사용 여부.
let lightThemeEnabled = true;

// 전제 입력칸에 포커스가 가면 마지막 포커스 대상을 전제칸으로 기록한다.
premisesEl.addEventListener("focus", () => {
  lastFocused = premisesEl;
});

// 결론 입력칸에 포커스가 가면 마지막 포커스 대상을 결론칸으로 기록한다.
conclusionEl.addEventListener("focus", () => {
  lastFocused = conclusionEl;
});

// 모든 기호 버튼에 클릭 이벤트를 붙인다.
symbolButtons.forEach((button) => {
  button.addEventListener("click", () => {
    // 버튼의 data-symbol 값을 읽는다.
    const symbol = button.getAttribute("data-symbol");

    // 마지막으로 포커스된 입력칸에 넣는다.
    // 기록이 없으면 전제 입력칸에 넣는다.
    const target = lastFocused || premisesEl;

    // 대상 입력칸에 포커스를 준다.
    target.focus();

    // 현재 선택 시작 위치.
    const start = target.selectionStart ?? target.value.length;

    // 현재 선택 끝 위치.
    const end = target.selectionEnd ?? target.value.length;

    // 기존 입력값.
    const value = target.value;

    // 선택된 부분을 symbol로 교체한다.
    target.value = value.slice(0, start) + symbol + value.slice(end);

    // 커서를 삽입된 symbol 뒤로 이동한다.
    target.selectionStart = target.selectionEnd = start + symbol.length;
  });
});

// 현재 사용하는 signature를 만든다.
// 지금 버전에서는 기본 signature만 사용한다.
function readCurrentSignature() {
  return buildSignature();
}

// Proof 버튼을 눌렀을 때 실행된다.
proofBtn.addEventListener("click", () => {
  try {
    // 전제 입력값.
    const premiseText = premisesEl.value.trim();

    // 결론 입력값.
    const conclusionText = conclusionEl.value.trim();

    // 결론이 비어 있으면 에러 메시지를 출력하고 중단한다.
    if (!conclusionText) {
      outputEl.className = "output error";
      outputEl.textContent = "결론을 입력해 주세요.";
      return;
    }

    // 현재 signature 생성.
    const signature = readCurrentSignature();

    // 증명 탐색 실행.
    const result = solveProofData(premiseText, conclusionText, signature);

    // 출력 영역을 일반 상태로 바꾼다.
    outputEl.className = "output";

    // 결과를 HTML로 렌더링한다.
    outputEl.innerHTML = renderProofResult(result);
  } catch (err) {
    // 파싱 실패나 증명 생성 중 예외가 나면 에러 메시지를 출력한다.
    outputEl.className = "output error";
    outputEl.textContent = "식 입력이 잘못됐습니다 or 현재 버전에서 증명을 찾지 못했습니다";
  }
});

// 줄 구분 켜기/끄기 버튼 클릭 처리.
stripeToggleBtn.addEventListener("click", () => {
  // 현재 상태를 반대로 바꾼다.
  zebraStripingEnabled = !zebraStripingEnabled;

  // 전역 상태도 갱신한다.
  window.zebraStripingEnabled = zebraStripingEnabled;

  // 버튼 문구를 갱신한다.
  stripeToggleBtn.textContent = `줄 구분: ${zebraStripingEnabled ? "켜짐" : "꺼짐"}`;

  // 현재 출력된 Fitch proof 요소를 찾는다.
  const proofEl = outputEl.querySelector(".fitch-proof");

  // 이미 출력된 proof가 있으면 class를 즉시 바꿔 화면에 반영한다.
  if (proofEl) {
    proofEl.classList.toggle("zebra-on", zebraStripingEnabled);
    proofEl.classList.toggle("zebra-off", !zebraStripingEnabled);
  }
});

// 테마 버튼 클릭 처리.
themeToggleBtn.addEventListener("click", () => {
  // 라이트/다크 상태를 반대로 바꾼다.
  lightThemeEnabled = !lightThemeEnabled;

  // body에 light-theme 클래스를 켜거나 끈다.
  document.body.classList.toggle("light-theme", lightThemeEnabled);

  // 버튼 문구를 갱신한다.
  themeToggleBtn.textContent = `화면 테마: ${lightThemeEnabled ? "라이트" : "다크"}`;
});

// 모두 지우기 버튼 클릭 처리.
clearBtn.addEventListener("click", () => {
  // 전제 입력칸 비우기.
  premisesEl.value = "";

  // 결론 입력칸 비우기.
  conclusionEl.value = "";

  // 출력 영역을 일반 상태로 되돌린다.
  outputEl.className = "output";

  // 출력 영역 기본 문구 복원.
  outputEl.innerHTML = "이곳에 결과가 표시됩니다.";

  // 전제 입력칸에 포커스를 둔다.
  premisesEl.focus();

  // 마지막 포커스 대상도 전제 입력칸으로 기록한다.
  lastFocused = premisesEl;
});
