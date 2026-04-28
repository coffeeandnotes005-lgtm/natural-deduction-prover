const TermType = {
  Variable: "Variable",
  Constant: "Constant",
};

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

const BUILTIN_VARIABLE_BASES = ["u", "v", "w", "x", "y", "z"];

class Term {
  constructor(type, { symbol = "", args = [] } = {}) {
    this.type = type;
    this.symbol = symbol;
    this.args = args;
  }

  static createVariable(symbol) {
    return new Term(TermType.Variable, { symbol });
  }

  static createConstant(symbol) {
    return new Term(TermType.Constant, { symbol });
  }
}

class Formula {
  constructor(type, { symbol = "", args = [], variable = "", left = null, right = null } = {}) {
    this.type = type;
    this.symbol = symbol;
    this.args = args;
    this.variable = variable;
    this.left = left;
    this.right = right;
  }

  static createSentenceLetter(symbol) {
    return new Formula(FormulaType.SentenceLetter, { symbol });
  }

  static createPredicate(symbol, args = []) {
    return new Formula(FormulaType.Predicate, { symbol, args });
  }

  static createContradiction() {
    return new Formula(FormulaType.Contradiction);
  }

  static createNegation(child) {
    return new Formula(FormulaType.Negation, { left: child });
  }

  static createBinary(type, lhs, rhs) {
    return new Formula(type, { left: lhs, right: rhs });
  }

  static createUniversal(variable, body) {
    return new Formula(FormulaType.Universal, { variable, left: body });
  }

  static createExistential(variable, body) {
    return new Formula(FormulaType.Existential, { variable, left: body });
  }
}

function trim(s) {
  return s.trim();
}

function isAsciiUpper(ch) {
  return /^[A-Z]$/.test(ch);
}

function isAsciiLower(ch) {
  return /^[a-z]$/.test(ch);
}

function isReservedLogicalChar(ch) {
  return ["¬", "∧", "∨", "→", "∀", "∃", "(", ")", ",", "⊥"].includes(ch);
}

function buildSignature() {
  return {
    variables: new Set(BUILTIN_VARIABLE_BASES),
  };
}

function termToString(term) {
  if (!term) return "";
  if ([TermType.Variable, TermType.Constant].includes(term.type)) return term.symbol;
  return "";
}

function equalTerm(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  if (a.type !== b.type) return false;
  if (a.symbol !== b.symbol) return false;
  if ((a.args || []).length !== (b.args || []).length) return false;
  for (let i = 0; i < (a.args || []).length; i++) {
    if (!equalTerm(a.args[i], b.args[i])) return false;
  }
  return true;
}

function formulaKey(f) {
  return formulaToString(f);
}

function equalFormula(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  if (a.type !== b.type) return false;
  if (a.symbol !== b.symbol) return false;
  if (a.variable !== b.variable) return false;
  if ((a.args || []).length !== (b.args || []).length) return false;
  for (let i = 0; i < (a.args || []).length; i++) {
    if (!equalTerm(a.args[i], b.args[i])) return false;
  }
  return equalFormula(a.left, b.left) && equalFormula(a.right, b.right);
}

function isBuiltinVariableToken(token) {
  return /^(u|v|w|x|y|z)([1-9]\d*)?$/.test(token);
}

function isBuiltinConstantToken(token) {
  return /^([a-t])([1-9]\d*)?$/.test(token);
}

class FormulaParser {
  constructor(text, signature) {
    this.text = text;
    this.pos = 0;
    this.signature = signature;
  }

  skipSpaces() {
    while (this.pos < this.text.length && /\s/.test(this.text[this.pos])) {
      this.pos += 1;
    }
  }

  currentChar() {
    this.skipSpaces();
    return this.text[this.pos] ?? "";
  }

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

  atEnd() {
    this.skipSpaces();
    return this.pos >= this.text.length;
  }

  peekVariableToken() {
    this.skipSpaces();
    const rest = this.text.slice(this.pos);
    const match = rest.match(/^(u|v|w|x|y|z)([1-9]\d*)?/);
    return match ? match[0] : null;
  }

  consumeVariableToken() {
    const token = this.peekVariableToken();
    if (!token) {
      throw new Error("양화사 뒤 변수는 u, v, w, x, y, z에 숫자를 붙이는 방식으로 써야 합니다.");
    }
    this.pos += token.length;
    return token;
  }

  peekConstantToken() {
    this.skipSpaces();
    const rest = this.text.slice(this.pos);
    const match = rest.match(/^([a-t])([1-9]\d*)?/);
    if (!match) return null;
    const token = match[0];
    return isBuiltinConstantToken(token) ? token : null;
  }

  parseFormula() {
    const result = this.parseImplication();
    if (!result) {
      throw new Error("올바른 식을 해석하지 못했습니다.");
    }
    if (!this.atEnd()) {
      throw new Error(`해석되지 않은 부분이 남아 있습니다: ${this.text.slice(this.pos)}`);
    }
    return result;
  }

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

  parseUnary() {
    this.skipSpaces();
    const ch = this.currentChar();

    if (ch === "¬") {
      this.consumeChar("¬");
      const child = this.parseUnary();
      if (!child) {
        throw new Error("¬ 뒤에 식이 필요합니다.");
      }
      return Formula.createNegation(child);
    }

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

    return this.parsePrimary();
  }

  parsePrimary() {
    this.skipSpaces();
    const ch = this.currentChar();

    if (ch === "(") {
      this.consumeChar("(");
      const inside = this.parseImplication();
      this.consumeChar(")");
      return inside;
    }

    if (ch === "⊥") {
      this.consumeChar("⊥");
      return Formula.createContradiction();
    }

    return this.parseAtomic();
  }

  parseAtomic() {
    this.skipSpaces();
    const ch = this.currentChar();
    if (!ch) return null;

    if (!isAsciiUpper(ch)) {
      return null;
    }

    this.consumeChar();
    const args = [];
    while (true) {
      const startPos = this.pos;
      const term = this.parseTerm();
      if (!term) {
        this.pos = startPos;
        break;
      }
      args.push(term);
    }

    if (args.length === 0) {
      return Formula.createSentenceLetter(ch);
    }
    return Formula.createPredicate(ch, args);
  }

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

function parseSingleFormula(text, signature) {
  const parser = new FormulaParser(text, signature);
  return parser.parseFormula();
}

function splitPremisesRaw(s) {
  const result = [];
  let depth = 0;
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

function parsePremises(text, signature) {
  const premisesOut = [];
  const raw = splitPremisesRaw(text);
  for (const s of raw) {
    const f = parseSingleFormula(s, signature);
    premisesOut.push(f);
  }
  return premisesOut;
}

function precedence(f) {
  if (!f) return 0;
  if (f.type === FormulaType.Implication) return 1;
  if (f.type === FormulaType.Disjunction) return 2;
  if (f.type === FormulaType.Conjunction) return 3;
  if ([FormulaType.Universal, FormulaType.Existential].includes(f.type)) return 4;
  if (f.type === FormulaType.Negation) return 5;
  return 6;
}

function needsParensLeft(parent, child) {
  if (!parent || !child) return false;
  if (precedence(child) < precedence(parent)) return true;
  if (child.type === parent.type && [FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(parent.type)) {
    return true;
  }
  return false;
}

function needsParensRight(parent, child) {
  if (!parent || !child) return false;
  return precedence(child) < precedence(parent);
}

function formulaToString(f) {
  if (!f) return "";

  function render(node, isTopLevel = false) {
    if (!node) return "";

    if (node.type === FormulaType.SentenceLetter) return node.symbol;
    if (node.type === FormulaType.Predicate) return `${node.symbol}${(node.args || []).map(termToString).join("")}`;
    if (node.type === FormulaType.Contradiction) return "⊥";
    if (node.type === FormulaType.Negation) {
      let child = render(node.left, false);
      if (node.left && [FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(node.left.type)) {
        child = `(${child})`;
      }
      return `¬${child}`;
    }
    if ([FormulaType.Universal, FormulaType.Existential].includes(node.type)) {
      let body = render(node.left, false);
      if (node.left && [FormulaType.Conjunction, FormulaType.Disjunction, FormulaType.Implication].includes(node.left.type)) {
        body = `(${body})`;
      }
      const quantifier = node.type === FormulaType.Universal ? "∀" : "∃";
      return `${quantifier}${node.variable}${body}`;
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

function symbolWithNumericSuffixToDisplay(symbol, allowedBasesPattern) {
  const match = String(symbol).match(new RegExp(`^(${allowedBasesPattern})(\\d+)$`));
  if (!match) return symbol;
  const [, base, digits] = match;
  return `${base}${digits.split("").map((digit) => SUBSCRIPT_DIGITS[digit] || digit).join("")}`;
}

function variableSymbolToDisplay(symbol) {
  return symbolWithNumericSuffixToDisplay(symbol, "[uvwxyz]");
}

function constantSymbolToDisplay(symbol) {
  return symbolWithNumericSuffixToDisplay(symbol, "[a-t]");
}

function termToDisplayString(term) {
  if (!term) return "";
  if (term.type === TermType.Variable) return variableSymbolToDisplay(term.symbol);
  if (term.type === TermType.Constant) return constantSymbolToDisplay(term.symbol);
  return "";
}

function formulaToDisplayString(f) {
  if (!f) return "";

  function render(node, isTopLevel = false) {
    if (!node) return "";

    if (node.type === FormulaType.SentenceLetter) return node.symbol;
    if (node.type === FormulaType.Predicate) return `${node.symbol}${(node.args || []).map(termToDisplayString).join("")}`;
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
