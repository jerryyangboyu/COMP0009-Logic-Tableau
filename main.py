# propositional and first order tableau

from typing import Union, List


class FormulaSymbol:
    And = "^"
    Or = "v"
    Not = "-"
    Implies = ">"
    Exist = "E"
    All = "A"


class Symbol:
    name: str

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return self.name == other.name


class Proposition(Symbol):
    def __init__(self, name):
        super().__init__(name)

    @staticmethod
    def isProp(c: str):
        return c == 'p' or c == 'q' or c == 'r' or c == 's'


class Variable(Symbol):
    def __init__(self, name):
        super().__init__(name)

    @staticmethod
    def isVar(c: str):
        return c == 'x' or c == 'y' or c == 'z' or c == 'w'


class Constant(Symbol):
    def __init__(self, name):
        super().__init__(name)


class Predicate(Symbol):
    _leftVar: Symbol
    _rightVar: Symbol

    def __init__(self, name, left: Variable, right: Variable):
        super().__init__(name)
        self._leftVar = left
        self._rightVar = right

    @staticmethod
    def isPredChar(c: str):
        return c == 'P' or c == 'Q' or c == 'R' or c == 'S'

    def getLeftVar(self):
        return self._leftVar

    def getRightVar(self):
        return self._rightVar

    def substitute(self, v: Variable, c: Constant):
        if self._leftVar == v:
            self._leftVar = c
        elif self._rightVar == v:
            self._rightVar = c


class Formula(Symbol):
    _children: []

    def __init__(self, name: str, left=None, right=None):
        super(Formula, self).__init__(name)
        self._children = [left, right]

    def getLeft(self):
        return self._children[0]

    def getRight(self):
        return self._children[1]

    def setLeft(self, child):
        self._children[0] = child

    def setRight(self, child):
        self._children[1] = child

    def expand(self):
        return None

    def __eq__(self, other):
        isNameEq = self.name == other.name
        isSameClass = type(self) is type(other)
        isLeftChildSame = self.getLeft() == other.getLeft()
        isRightChildSame = self.getRight() == other.getRight()
        return isNameEq and isSameClass and isLeftChildSame and isRightChildSame

    def __str__(self):
        if isinstance(self, NotFormula):
            return FormulaSymbol.Not + str(self.getLeft())
        if isinstance(self, ExistFormula):
            return FormulaSymbol.Exist + str(self.getVariable()) + str(self.getLeft())
        if isinstance(self, ForAllFormula):
            return FormulaSymbol.All + str(self.getVariable()) + str(self.getLeft())
        if isinstance(self, Proposition):
            return self.name
        if isinstance(self, Variable):
            return self.name
        if isinstance(self, Constant):
            return self.name
        if isinstance(self, Predicate):
            return self.name + "(" + str(self.getLeftVar()) + "," + str(self.getRightVar()) + ")"
        return "(" + str(self.getLeft()) + self.name + str(self.getRight()) + ")"


class AndFormula(Formula):

    def __init__(self, left=None, right=None):
        super().__init__(FormulaSymbol.And, left, right)


class OrFormula(Formula):

    def __init__(self, left=None, right=None):
        super().__init__(FormulaSymbol.Or, left, right)


class ImpliesFormula(Formula):

    def __init__(self, left=None, right=None):
        super().__init__(FormulaSymbol.Implies, left, right)

    def expand(self) -> Formula:
        return OrFormula(NotFormula(self.getLeft()), self.getRight())


class NotFormula(Formula):

    def __init__(self, formula=None):
        super().__init__(FormulaSymbol.Not, formula)

    def expand(self) -> Formula:
        formula = self.getLeft()
        if isinstance(formula, AndFormula):  # ~(A & B) = ~A | ~B
            return OrFormula(NotFormula(formula.getLeft()), NotFormula(formula.getRight()))
        elif isinstance(formula, OrFormula):  # ~(A | B) = ~A & ~B
            return AndFormula(NotFormula(formula.getLeft()), NotFormula(formula.getRight()))
        elif isinstance(formula, NotFormula):  # ~~A = A
            return formula.getLeft()
        elif isinstance(formula, ImpliesFormula):  # ~(A -> B) = A & ~B
            return AndFormula(formula.getLeft(), NotFormula(formula.getRight()))
        elif isinstance(formula, ForAllFormula):  # -Ax = E-x
            return ExistFormula(formula.getVariable(), NotFormula(formula))
        elif isinstance(formula, ExistFormula):  # -Ex = A-x
            return ForAllFormula(formula.getVariable(), NotFormula(formula))
        else:  # ~A = ~A
            return self

    def isNegativeLiteral(self):
        return isinstance(self.getLeft(), Symbol)


class ForAllFormula(Formula):
    _var: Variable

    def __init__(self, var: Variable, formula: Symbol):
        super().__init__(FormulaSymbol.All, formula)
        self._var = var

    def getVariable(self):
        return self._var


class ExistFormula(Formula):
    _var: Variable

    def __init__(self, var: Variable, formula: Symbol):
        super().__init__(FormulaSymbol.Exist, formula)
        self._var = var

    def getVariable(self):
        return self._var


class Parser:
    _tokens = []
    _p = 0
    _temp_p = 0

    def hasNext(self):
        return self._p != len(self._tokens)

    def readNext(self):
        if self.hasNext():
            value = self._tokens[self._p]
            self._p += 1
            self._temp_p = self._p
            return value
        return None

    def peekNext(self):
        if self.hasNext():
            value = self._tokens[self._temp_p]
            self._temp_p += 1
            return value
        return None

    def eatNext(self, symbol: str):
        actual = self.readNext()
        if actual != symbol:
            raise Exception("Syntax Error: Expecting " + symbol + " actual " + actual)
        return symbol

    def parse(self, formula: str) -> Symbol:
        # produces tokens
        self._tokens = list(formula)

        # building formula tree
        return self.parseFormula()

    def parseFormula(self) -> Symbol:
        first = self.peekNext()

        # empty formula
        if first is None:
            raise Exception("Unexpected empty sequence")

        # first order logic base case
        elif Predicate.isPredChar(first):
            name = self.readNext()
            self.eatNext("(")
            var1 = self.readNext()
            if not Variable.isVar(var1):
                raise Exception("var1 is not a variable")
            self.eatNext(",")
            var2 = self.readNext()
            if not Variable.isVar(var2):
                raise Exception("var2 is not a variable")
            self.eatNext(")")
            return Predicate(name, var1, var2)

        # propositional logic base case
        elif Proposition.isProp(first):
            self.eatNext(first)
            return Proposition(first)

        # negation
        elif first == FormulaSymbol.Not:
            self.eatNext(FormulaSymbol.Not)
            formula = self.parseFormula()
            return NotFormula(formula)

        # existentially quantified
        elif first == FormulaSymbol.Exist:
            self.eatNext(FormulaSymbol.Exist)
            var = self.readNext()
            if not Variable.isVar(var):
                raise Exception("existentially quantifier requires a variable")
            formula = self.parseFormula()
            return ExistFormula(var, formula)

        # universally quantified
        elif first == FormulaSymbol.All:
            self.eatNext(FormulaSymbol.All)
            var = self.readNext()
            if not Variable.isVar(var):
                raise Exception("universally quantifier requires a variable")
            formula = self.parseFormula()
            return ForAllFormula(var, formula)

        # parentheses
        # the only child inside parentheses is binary operation
        elif first == "(":
            self.eatNext("(")
            leftFormula = self.parseBinary()
            self.eatNext(")")
            return leftFormula

        # undefined rule
        else:
            raise Exception("Undefined rule, unexpected token" + first)

    def parseBinary(self):
        left = self.parseFormula()
        op = self.readNext()
        right = self.parseFormula()

        if op == FormulaSymbol.And:
            return AndFormula(left, right)
        elif op == FormulaSymbol.Or:
            return OrFormula(left, right)
        elif op == FormulaSymbol.Implies:
            return ImpliesFormula(left, right)
        else:
            raise Exception("Unrecognized operator " + op)


class ProofMachine:
    Element = Union[Formula, Symbol]
    SymbolElement = Union[NotFormula, Symbol]

    _process: List[str] = []
    _expand_id = 0

    def isValid(self, t: Formula) -> bool:
        return self._isFormulaClosed(NotFormula(t), [], [], "", "")

    @staticmethod
    def _isSymbolElement(t: Element):
        return (isinstance(t, NotFormula) and t.isNegativeLiteral()) or isinstance(t, Symbol)

    @staticmethod
    def _findContradictionSymbol(symbols: List[SymbolElement]) -> Union[NotFormula, None]:
        for symbol in symbols:
            if isinstance(symbol, NotFormula):
                for compare in symbols:
                    if compare.name == symbol.getLeft().name:
                        return symbol
        return None

    def _alpha(self, t: AndFormula, formulas: List[Element], symbols: List[SymbolElement],
               prefix: str, childrenPrefix: str) -> bool:
        self._process.append(prefix + str(t))

        left = t.getLeft()
        if isinstance(left, NotFormula) or isinstance(t, ImpliesFormula):
            left = left.expand()
        if ProofMachine._isSymbolElement(t.getLeft()):
            symbols.append(left)
        else:
            formulas.append(left)
        self._process.append(prefix + str(left))

        right = t.getRight()
        if isinstance(right, NotFormula) or isinstance(t, ImpliesFormula):
            right = right.expand()
        if ProofMachine._isSymbolElement(right):
            symbols.append(right)
        else:
            formulas.append(right)
        self._process.append(prefix + str(right))

        self._expand_id += 1
        return self._atom(formulas, symbols, prefix, childrenPrefix)

    def _atom(self, formulas: List[Element], symbols: List[SymbolElement], prefix: str, childrenPrefix: str) -> bool:
        symbol = ProofMachine._findContradictionSymbol(symbols)
        if symbol is not None:
            self._process.append(prefix + "Close because {0} contradict with {1}".format(symbol, symbol.getLeft()))
            return True
        elif len(formulas) == 0:
            self._process.append(prefix + "Branch is open for variables {0}".format([str(__s) for __s in symbols]))
            return False

        formula = formulas.pop(0)
        return self._isFormulaClosed(formula, formulas, symbols, prefix, childrenPrefix)

    def _beta(self, t: OrFormula, formulas: List[Element], symbols: List[SymbolElement],
              prefix: str, childrenPrefix: str) -> bool:
        self._process.append(prefix + str(t))
        self._expand_id += 1

        leftCondition = self._isFormulaClosed(t.getLeft(), formulas.copy(), symbols.copy(),
                                              childrenPrefix, childrenPrefix)
        rightCondition = self._isFormulaClosed(t.getRight(), formulas.copy(), symbols.copy(),
                                               childrenPrefix, childrenPrefix)
        return leftCondition and rightCondition

    def _isFormulaClosed(self, t: Formula, formulas: List[Element], symbols: List[SymbolElement],
                         prefix: str, childrenPrefix: str) -> bool:
        if isinstance(t, NotFormula) or isinstance(t, ImpliesFormula):
            t = t.expand()

        if ProofMachine._isSymbolElement(t):
            self._process.append(prefix + "├── " + str(t))
            symbols.append(t)
            return self._atom(formulas, symbols, prefix, childrenPrefix)

        if isinstance(t, AndFormula):
            return self._alpha(t, formulas, symbols, childrenPrefix +
                               "│ alpha({0}) ".format(self._expand_id), "│            ".format(self._expand_id))
        elif isinstance(t, OrFormula):
            return self._beta(t, formulas, symbols, childrenPrefix +
                              "├─beta({0})─ ".format(self._expand_id), childrenPrefix + "│            ")
        else:
            raise Exception("Cannot evaluate formula " + str(t))

    def getOutput(self) -> str:
        return "\n".join(self._process)


prop_input = """-(p>(q>p))
(-(p>q)^q)
(---pv(q^-q))
(p>p)
-(p>p)
((pvq)^
(p-q)
((pvq)^(-pv-q))
(q^-(pv-p))
p
((pvq)^((p>-p)^(-p>p)))
-----------q"""

pred_input = """(ExP(x,x)^Ax(-P(x,x)>P(x,x)))
-Ax(P(x,x)^-P(x,x))
-Ax-Ey-P(x,y)
ExAx(P(x,x)^-P(x,x))
ExAy(Q(x,x)>P(y,y))
(Q(x,x)-(P(y,y))
ExEy((Q(x,x)^Q(y,y))v-P(y,y))
ExEy((Q(x,x)^Q(y,y))v
Ex-P(x,x)
(AxEyP(x,y)^EzQ(z,z))
(Ax(P(x,x)^-P(x,x))^ExQ(x,x))
ExEy(P(x,y)^Ex-P(x,y))"""

if __name__ == '__main__':
    test_inputs = pred_input.split("\n")
    for s in test_inputs:
        parser = Parser()
        # try:
        tree = parser.parse(s)
        print(tree)
        # except Exception as err:
        #     print(err)

    # tableau = ProofMachine()
    # print(tableau.isValid(tree))
    # print(tableau.getOutput())
