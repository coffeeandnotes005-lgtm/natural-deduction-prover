// 항(term)의 종류입니다.
// 현재는 변항과 상항만 사용합니다.
const TermType = {
  Variable: "Variable",
  Constant: "Constant",
};

// 식(formula)의 종류입니다.
// 명제문자, 술어식, 모순, 부정, 이항 연결사, 양화사를 구분합니다.
const FormulaType = {
  SentenceLetter: "SentenceLetter",
  Predicate: "Predicate",
  Contradiction: "Contradiction",
  Negation: "Negation",
  Conjunction: "Conjunction",
  Disjunction: "Disjunction",
  Implication: "Implication",
  Universal: "Universal",
  Existential: "Existential",
};

// 기본 변항 기호입니다.
// u-z만 변항으로 허용합니다.
const BUILTIN_VARIABLE_BASES = ["u", "v", "w", "x", "y", "z"];

// 항을 표현하는 클래스입니다.
// 예: x, y, a, b 같은 것들을 Term 객체로 저장합니다.
class Term {
  constructor(type, { symbol = "", args = [] } = {}) {
    // Variable 또는 Constant
    this.type = type;

    // 실제 기호 이름입니다. 예: x, y1, a, b2
    this.symbol = symbol;

    // 현재 구조에서는 사실상 사용하지 않지만,
    // 나중에 함수기호를 넣을 경우를 대비한 자리입니다.
    this.args = args;
  }

  // 변항 Term을 만듭니다.
  static createVariable(symbol) {
    return new Term(TermType.Variable, { symbol });
  }

  // 상항 Term을 만듭니다.
  static createConstant(symbol) {
    return new Term(TermType.Constant, { symbol });
  }
}

// 논리식을 표현하는 클래스입니다.
// 예: A, Px, ¬A, A∧B, ∀xFx 등을 모두 Formula로 저장합니다.
class Formula {
  constructor(type, { symbol = "", args = [], variable = "", left = null, right = null } = {}) {
    // 식의 종류입니다.
    this.type = type;

    // 명제기호 또는 술어기호입니다. 예: A, P, Q
    this.symbol = symbol;

    // 술어식의 항 목록입니다. 예: Pxy라면 [x, y]
    this.args = args;

    // 양화사의 변수입니다. 예: ∀xFx에서 x
    this.variable = variable;

    // 단항식의 하위식 또는 이항식의 왼쪽 식입니다.
    this.left = left;

    // 이항식의 오른쪽 식입니다.
    this.right = right;
  }

  // 명제문자를 만듭니다. 예: A
  static createSentenceLetter(symbol) {
    return new Formula(FormulaType.SentenceLetter, { symbol });
  }

  // 술어식을 만듭니다. 예: Pxy
  static createPredicate(symbol, args = []) {
    return new Formula(FormulaType.Predicate, { symbol, args });
  }

  // 모순 기호 ⊥를 만듭니다.
  static createContradiction() {
    return new Formula(FormulaType.Contradiction);
  }

  // 부정식을 만듭니다. 예: ¬A
  static createNegation(child) {
    return new Formula(FormulaType.Negation, { left: child });
  }

  // 이항 연결사 식을 만듭니다. 예: A∧B, A∨B, A→B
  static createBinary(type, lhs, rhs) {
    return new Formula(type, { left: lhs, right: rhs });
  }

  // 보편양화식을 만듭니다. 예: ∀xFx
  static createUniversal(variable, body) {
    return new Formula(FormulaType.Universal, { variable, left: body });
  }

  // 존재양화식을 만듭니다. 예: ∃xFx
  static createExistential(variable, body) {
    return new Formula(FormulaType.Existential, { variable, left: body });
  }
}

// 문자열 양끝 공백 제거용 짧은 함수입니다.
function trim(s) {
  return s.trim();
}

// 문자가 대문자 A-Z인지 확인합니다.
// 명제기호와 술어기호 판정에 사용합니다.
function isAsciiUpper(ch) {
  return /^[A-Z]$/.test(ch);
}

// 문자가 소문자 a-z인지 확인합니다.
// 현재 코드에서는 직접 크게 쓰이지 않을 수 있습니다.
function isAsciiLower(ch) {
  return /^[a-z]$/.test(ch);
}

// 논리 기호로 예약된 문자인지 확인합니다.
// 식 파싱에서 일반 기호와 논리 기호를 구분할 때 쓸 수 있습니다.
function isReservedLogicalChar(ch) {
  return ["¬", "∧", "∨", "→", "∀", "∃", "(", ")", ",", "⊥"].includes(ch);
}

// 기본 서명(signature)을 만듭니다.
// 현재는 사용 가능한 변항 집합만 저장합니다.
function buildSignature() {
  return {
    variables: new Set(BUILTIN_VARIABLE_BASES),
  };
}

// Term 객체를 일반 문자열로 바꿉니다.
// 예: Term(Variable, x1) → "x1"
function termToString(term) {
  if (!term) return "";
  if ([TermType.Variable, TermType.Constant].includes(term.type)) return term.symbol;
  return "";
}

// 두 항이 같은지 비교합니다.
function equalTerm(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  if (a.type !== b.type) return false;
  if (a.symbol !== b.symbol) return false;
  if ((a.args || []).length !== (b.args || []).length) return false;

  // 함수항을 지원하게 될 경우 하위 항까지 비교합니다.
  for (let i = 0; i < (a.args || []).length; i++) {
    if (!equalTerm(a.args[i], b.args[i])) return false;
  }

  return true;
}

// 식을 비교용 문자열 key로 바꿉니다.
function formulaKey(f) {
  return formulaToString(f);
}

// 두 논리식이 구조적으로 같은지 비교합니다.
function equalFormula(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  if (a.type !== b.type) return false;
  if (a.symbol !== b.symbol) return false;
  if (a.variable !== b.variable) return false;
  if ((a.args || []).length !== (b.args || []).length) return false;

  // 술어식의 항 목록 비교
  for (let i = 0; i < (a.args || []).length; i++) {
    if (!equalTerm(a.args[i], b.args[i])) return false;
  }

  // 하위식까지 재귀적으로 비교
  return equalFormula(a.left, b.left) && equalFormula(a.right, b.right);
}

// 변항 토큰인지 확인합니다.
// 허용: u, v, w, x, y, z 또는 x1, y23 같은 형태
function isBuiltinVariableToken(token) {
  return /^(u|v|w|x|y|z)([1-9]\d*)?$/.test(token);
}

// 상항 토큰인지 확인합니다.
// 허용: a-t 또는 a1, b23 같은 형태
function isBuiltinConstantToken(token) {
  return /^([a-t])([1-9]\d*)?$/.test(token);
}

// 문자열을 Formula 객체로 바꾸는 파서 클래스입니다.
class FormulaParser {
  constructor(text, signature) {
    // 파싱할 원본 문자열
    this.text = text;

    // 현재 읽고 있는 위치
    this.pos = 0;

    // 허용 기호 정보
    this.signature = signature;
  }

  // 현재 위치부터 이어지는 공백을 건너뜁니다.
  skipSpaces() {
    while (this.pos < this.text.length && /\s/.test(this.text[this.pos])) {
      this.pos += 1;
    }
  }

  // 현재 위치의 문자를 반환합니다.
  // 먼저 공백을 건너뜁니다.
  currentChar() {
    this.skipSpaces();
    return this.text[this.pos] ?? "";
  }

  // 현재 문자를 소비하고 다음 위치로 이동합니다.
  // expected가 있으면 그 문자와 일치해야 합니다.
  consumeChar(expected = null) {
    this.skipSpaces();

    const ch = this.text[this.pos] ?? "";

    if (!ch) {
      throw new Error("식이 중간에서 끝났습니다.");
    }

    if (expected !== null && ch !== expected) {
      throw new Error(`'${expected}'가 와야 하는 위치입니다.`);
    }

    this.pos += 1;
    return ch;
  }

  // 문자열 끝까지 읽었는지 확인합니다.
  atEnd() {
    this.skipSpaces();
    return this.pos >= this.text.length;
  }

  // 현재 위치에 변항 토큰이 있는지 미리 확인합니다.
  // 실제 위치는 이동하지 않습니다.
  peekVariableToken() {
    this.skipSpaces();

    const rest = this.text.slice(this.pos);
    const match = rest.match(/^(u|v|w|x|y|z)([1-9]\d*)?/);

    return match ? match[0] : null;
  }

  // 양화사 뒤의 변항 토큰을 실제로 소비합니다.
  consumeVariableToken() {
    const token = this.peekVariableToken();

    if (!token) {
      throw new Error("양화사 뒤 변수는 u, v, w, x, y, z에 숫자를 붙이는 방식으로 써야 합니다.");
    }

    this.pos += token.length;
    return token;
  }

  // 현재 위치에 상항 토큰이 있는지 확인합니다.
  // 실제 위치는 이동하지 않습니다.
  peekConstantToken() {
    this.skipSpaces();

    const rest = this.text.slice(this.pos);
    const match = rest.match(/^([a-t])([1-9]\d*)?/);

    if (!match) return null;

    const token = match[0];
    return isBuiltinConstantToken(token) ? token : null;
  }

  // 식 전체를 파싱하는 최상위 함수입니다.
  parseFormula() {
    const result = this.parseImplication();

    if (!result) {
      throw new Error("올바른 식을 해석하지 못했습니다.");
    }

    // 식 하나를 다 읽은 뒤에도 문자가 남아 있으면 오류입니다.
    if (!this.atEnd()) {
      throw new Error(`해석되지 않은 부분이 남아 있습니다: ${this.text.slice(this.pos)}`);
    }

    return result;
  }

  // 함의식 파싱입니다.
  // 우선순위가 가장 낮고, 오른쪽 결합으로 처리합니다.
  // 예: A → B → C = A → (B → C)
  parseImplication() {
    const left = this.parseDisjunction();
    if (!left) return null;

    this.skipSpaces();

    if (this.currentChar() === "→") {
      this.consumeChar();

      const right = this.parseImplication();

      if (!right) {
        throw new Error("→ 오른쪽 식이 필요합니다.");
      }

      return Formula.createBinary(FormulaType.Implication, left, right);
    }

    return left;
  }

  // 선언식 ∨ 파싱입니다.
  // 함의보다 우선순위가 높고, ∧보다 낮습니다.
  parseDisjunction() {
    const left = this.parseConjunction();
    if (!left) return null;

    this.skipSpaces();

    if (this.currentChar() === "∨") {
      this.consumeChar("∨");

      const right = this.parseDisjunction();

      if (!right) {
        throw new Error("∨ 오른쪽 식이 필요합니다.");
      }

      return Formula.createBinary(FormulaType.Disjunction, left, right);
    }

    return left;
  }

  // 연언식 ∧ 파싱입니다.
  // ∨보다 우선순위가 높습니다.
  parseConjunction() {
    const left = this.parseUnary();
    if (!left) return null;

    this.skipSpaces();

    if (this.currentChar() === "∧") {
      this.consumeChar("∧");

      const right = this.parseConjunction();

      if (!right) {
        throw new Error("∧ 오른쪽 식이 필요합니다.");
      }

      return Formula.createBinary(FormulaType.Conjunction, left, right);
    }

    return left;
  }

  // 단항식 파싱입니다.
  // 부정, 양화사, 원자식, 괄호식을 처리합니다.
  parseUnary() {
    this.skipSpaces();

    const ch = this.currentChar();

    // 부정식 처리: ¬A
    if (ch === "¬") {
      this.consumeChar("¬");

      const child = this.parseUnary();

      if (!child) {
        throw new Error("¬ 뒤에 식이 필요합니다.");
      }

      return Formula.createNegation(child);
    }

    // 양화식 처리: ∀xFx, ∃xFx
    if (ch === "∀" || ch === "∃") {
      this.consumeChar();

      const variable = this.consumeVariableToken();
      const body = this.parseUnary();

      if (!body) {
        throw new Error("양화사 뒤에 식이 필요합니다.");
      }

      return ch === "∀"
        ? Formula.createUniversal(variable, body)
        : Formula.createExistential(variable, body);
    }

    // 부정이나 양화사가 아니면 괄호식/원자식으로 넘깁니다.
    return this.parsePrimary();
  }

  // 괄호식, 모순기호, 원자식을 처리합니다.
  parsePrimary() {
    this.skipSpaces();

    const ch = this.currentChar();

    // 괄호식 처리: (A → B)
    if (ch === "(") {
      this.consumeChar("(");

      const inside = this.parseImplication();

      this.consumeChar(")");

      return inside;
    }

    // 모순기호 처리
    if (ch === "⊥") {
      this.consumeChar("⊥");
      return Formula.createContradiction();
    }

    // 그 외에는 원자식으로 처리합니다.
    return this.parseAtomic();
  }

  // 원자식을 파싱합니다.
  // 대문자만 명제기호 또는 술어기호로 인정합니다.
  parseAtomic() {
    this.skipSpaces();

    const ch = this.currentChar();

    if (!ch) return null;

    // 대문자로 시작하지 않으면 원자식이 아닙니다.
    if (!isAsciiUpper(ch)) {
      return null;
    }

    // 대문자 기호 하나를 소비합니다.
    this.consumeChar();

    const args = [];

    // 대문자 뒤에 항들이 붙어 있으면 술어식으로 해석합니다.
    // 예: Pxy → P(x, y)
    while (true) {
      const startPos = this.pos;

      const term = this.parseTerm();

      if (!term) {
        // 항이 아니면 위치를 되돌리고 종료합니다.
        this.pos = startPos;
        break;
      }

      args.push(term);
    }

    // 항이 없으면 명제문자입니다. 예: A
    if (args.length === 0) {
      return Formula.createSentenceLetter(ch);
    }

    // 항이 있으면 술어식입니다. 예: Px, Rxy
    return Formula.createPredicate(ch, args);
  }

  // 항을 파싱합니다.
  // 변항 u-z를 먼저 확인하고, 그 다음 상항 a-t를 확인합니다.
  parseTerm() {
    this.skipSpaces();

    const ch = this.currentChar();

    if (!ch) return null;

    const variableToken = this.peekVariableToken();

    if (variableToken) {
      this.pos += variableToken.length;
      return Term.createVariable(variableToken);
    }

    const constantToken = this.peekConstantToken();

    if (constantToken) {
      this.pos += constantToken.length;
      return Term.createConstant(constantToken);
    }

    return null;
  }
}

// 문자열 하나를 Formula 객체 하나로 파싱합니다.
function parseSingleFormula(text, signature) {
  const parser = new FormulaParser(text, signature);
  return parser.parseFormula();
}

// 전제 입력 문자열을 쉼표 기준으로 나눕니다.
// 단, 괄호 안의 쉼표는 전제 구분자로 보지 않습니다.
function splitPremisesRaw(s) {
  const result = [];

  // 현재 괄호 깊이입니다.
  // depth가 0일 때만 쉼표가 전제 구분자로 인정됩니다.
  let depth = 0;

  // 현재 전제 문자열을 누적합니다.
  let current = "";

  for (const ch of s) {
    if (ch === "(") depth += 1;
    else if (ch === ")") depth -= 1;

    if (ch === "," && depth === 0) {
      const t = trim(current);

      if (t) result.push(t);

      current = "";
    } else {
      current += ch;
    }
  }

  const t = trim(current);

  if (t) result.push(t);

  return result;
}

// 전제 문자열 전체를 Formula 배열로 파싱합니다.
function parsePremises(text, signature) {
  const premisesOut = [];

  const raw = splitPremisesRaw(text);

  for (const s of raw) {
    const f = parseSingleFormula(s, signature);
    premisesOut.push(f);
  }

  return premisesOut;
}

// 출력할 때 괄호 필요 여부를 판단하기 위한 우선순위입니다.
// 숫자가 클수록 더 강하게 묶입니다.
function precedence(f) {
  if (!f) return 0;
  if (f.type === FormulaType.Implication) return 1;
  if (f.type === FormulaType.Disjunction) return 2;
  if (f.type === FormulaType.Conjunction) return 3;
  if ([FormulaType.Universal, FormulaType.Existential].includes(f.type)) return 4;
  if (f.type === FormulaType.Negation) return 5;

  // 원자식이 가장 강하게 묶입니다.
  return 6;
}

// 왼쪽 하위식에 괄호가 필요한지 판단합니다.
function needsParensLeft(parent, child) {
  if (!parent || !child) return false;

  if (precedence(child) < precedence(parent)) return true;

  // 같은 이항 연결사가 중첩되면 구조를 명확히 하기 위해 괄호를 붙입니다.
  if (child.type === parent.type && [FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(parent.type)) {
    return true;
  }

  return false;
}

// 오른쪽 하위식에 괄호가 필요한지 판단합니다.
function needsParensRight(parent, child) {
  if (!parent || !child) return false;

  return precedence(child) < precedence(parent);
}

// Formula 객체를 일반 문자열로 바꿉니다.
// 내부 비교나 구문 확인용으로 사용됩니다.
function formulaToString(f) {
  if (!f) return "";

  // 실제 재귀 출력 함수입니다.
  function render(node, isTopLevel = false) {
    if (!node) return "";

    // 명제문자
    if (node.type === FormulaType.SentenceLetter) return node.symbol;

    // 술어식
    if (node.type === FormulaType.Predicate) {
      return `${node.symbol}${(node.args || []).map(termToString).join("")}`;
    }

    // 모순기호
    if (node.type === FormulaType.Contradiction) return "⊥";

    // 부정식
    if (node.type === FormulaType.Negation) {
      let child = render(node.left, false);

      // 부정 아래에 이항식이 있으면 괄호를 붙입니다.
      if (node.left && [FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(node.left.type)) {
        child = `(${child})`;
      }

      return `¬${child}`;
    }

    // 양화식
    if ([FormulaType.Universal, FormulaType.Existential].includes(node.type)) {
      let body = render(node.left, false);

      // 양화사 본문이 이항식이면 괄호를 붙입니다.
      if (node.left && [FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(node.left.type)) {
        body = `(${body})`;
      }

      const quantifier = node.type === FormulaType.Universal ? "∀" : "∃";

      return `${quantifier}${node.variable}${body}`;
    }

    // 이항 연결사 기호를 정합니다.
    let op = "";

    if (node.type === FormulaType.Conjunction) op = "∧";
    if (node.type === FormulaType.Disjunction) op = "∨";
    if (node.type === FormulaType.Implication) op = "→";

    const leftText = render(node.left, false);
    const rightText = render(node.right, false);

    const combined = `(${leftText} ${op} ${rightText})`;

    // 최상위 식은 바깥 괄호를 생략합니다.
    return isTopLevel ? `${leftText} ${op} ${rightText}` : combined;
  }

  return render(f, true);
}

// 숫자를 아래첨자로 바꾸기 위한 표입니다.
const SUBSCRIPT_DIGITS = {
  "0": "₀",
  "1": "₁",
  "2": "₂",
  "3": "₃",
  "4": "₄",
  "5": "₅",
  "6": "₆",
  "7": "₇",
  "8": "₈",
  "9": "₉",
};

// x12 같은 기호를 x₁₂처럼 화면 표시용으로 바꿉니다.
function symbolWithNumericSuffixToDisplay(symbol, allowedBasesPattern) {
  const match = String(symbol).match(new RegExp(`^(${allowedBasesPattern})(\\d+)$`));

  if (!match) return symbol;

  const [, base, digits] = match;

  return `${base}${digits.split("").map((digit) => SUBSCRIPT_DIGITS[digit] || digit).join("")}`;
}

// 변항 표시용 변환입니다.
// 예: x12 → x₁₂
function variableSymbolToDisplay(symbol) {
  return symbolWithNumericSuffixToDisplay(symbol, "[uvwxyz]");
}

// 상항 표시용 변환입니다.
// 예: a12 → a₁₂
function constantSymbolToDisplay(symbol) {
  return symbolWithNumericSuffixToDisplay(symbol, "[a-t]");
}

// Term 객체를 화면 표시용 문자열로 바꿉니다.
function termToDisplayString(term) {
  if (!term) return "";

  if (term.type === TermType.Variable) return variableSymbolToDisplay(term.symbol);
  if (term.type === TermType.Constant) return constantSymbolToDisplay(term.symbol);

  return "";
}

// Formula 객체를 화면 표시용 문자열로 바꿉니다.
// 숫자 접미사가 아래첨자로 표시됩니다.
function formulaToDisplayString(f) {
  if (!f) return "";

  function render(node, isTopLevel = false) {
    if (!node) return "";

    if (node.type === FormulaType.SentenceLetter) return node.symbol;

    if (node.type === FormulaType.Predicate) {
      return `${node.symbol}${(node.args || []).map(termToDisplayString).join("")}`;
    }

    if (node.type === FormulaType.Contradiction) return "⊥";

    if (node.type === FormulaType.Negation) {
      const child = render(node.left, false);
      return `¬${child}`;
    }

    if ([FormulaType.Universal, FormulaType.Existential].includes(node.type)) {
      const body = render(node.left, false);
      const quantifier = node.type === FormulaType.Universal ? "∀" : "∃";

      return `${quantifier}${variableSymbolToDisplay(node.variable)}${body}`;
    }

    let op = "";

    if (node.type === FormulaType.Conjunction) op = "∧";
    if (node.type === FormulaType.Disjunction) op = "∨";
    if (node.type === FormulaType.Implication) op = "→";

    const leftText = render(node.left, false);
    const rightText = render(node.right, false);

    const combined = `(${leftText} ${op} ${rightText})`;

    return isTopLevel ? `${leftText} ${op} ${rightText}` : combined;
  }

  return render(f, true);
}
