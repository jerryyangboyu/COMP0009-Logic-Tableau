# propositional and first order tableau


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

    def isPrimary(self):
        return isinstance(self, Proposition) \
               or (isinstance(self, Predicate) and self.isQuantified())

    def isSymbol(self):
        return self.isPrimary() or (isinstance(self, NotFormula) and self.getLeft().isPrimary())


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

    def isQuantified(self):
        return isinstance(self._leftVar, Constant) and isinstance(self._rightVar, Constant)

    def __eq__(self, other):
        return self.getLeftVar() == other.getLeftVar() and self.getRightVar() == other.getRightVar()

    def __str__(self):
        return self.name + "(" + str(self.getLeftVar()) + "," + str(self.getRightVar()) + ")"


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

    def isBinary(self):
        return self.getLeft() is not None and self.getRight() is not None

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
        if isinstance(self, Proposition) or isinstance(self, Variable) \
                or isinstance(self, Constant) or isinstance(self, Predicate):
            return str(self)
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


class ParseException(Exception):
    def __init__(self, reason):
        super(ParseException, self).__init__(reason)


class TableauException(Exception):
    def __init__(self, reason):
        super(TableauException, self).__init__(reason)


class Parser:
    def __init__(self):
        self._isFirstOrder = False
        self._tokens = []
        self._p = 0
        self._temp_p = 0

    def isFirstOrderFormula(self):
        return self._isFirstOrder

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
            raise ParseException("Syntax Error: Expecting " + symbol + " actual " + actual)
        return symbol

    def assertEnd(self):
        if self.hasNext():
            value = self.readNext()
            raise ParseException("Unexpected token " + value)

    def parse(self, formula: str) -> Symbol:
        # produces tokens
        self._tokens = list(formula)

        # building formula tree
        formula = self.parseFormula()
        self.assertEnd()

        return formula

    def parseFormula(self) -> Symbol:
        first = self.peekNext()

        # empty formula
        if first is None:
            raise ParseException("Unexpected empty sequence")

        # first order logic base case
        elif Predicate.isPredChar(first):
            self._isFirstOrder = True
            name = self.readNext()
            self.eatNext("(")
            var1 = self.readNext()
            if not Variable.isVar(var1):
                raise ParseException("var1 is not a variable")
            self.eatNext(",")
            var2 = self.readNext()
            if not Variable.isVar(var2):
                raise ParseException("var2 is not a variable")
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
            self._isFirstOrder = True
            self.eatNext(FormulaSymbol.Exist)
            var = self.readNext()
            if not Variable.isVar(var):
                raise ParseException("existentially quantifier requires a variable")
            formula = self.parseFormula()
            return ExistFormula(var, formula)

        # universally quantified
        elif first == FormulaSymbol.All:
            self._isFirstOrder = True
            self.eatNext(FormulaSymbol.All)
            var = self.readNext()
            if not Variable.isVar(var):
                raise ParseException("universally quantifier requires a variable")
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
            raise ParseException("Undefined rule, unexpected token" + first)

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
            raise ParseException("Unrecognized operator " + op)


class Result:
    SATISFIABLE = 0
    NOT_SATISFIABLE = 1
    MAY_SATISFIABLE = 2

    def __init__(self, result):
        self.result = result

    def __str__(self):
        if self.result == Result.SATISFIABLE:
            return "satisfiable"
        elif self.result == Result.NOT_SATISFIABLE:
            return "not satisfiable"
        elif self.result == Result.MAY_SATISFIABLE:
            return "may satisfiable"
        else:
            raise TableauException("invalid result value")

    def __and__(self, other):
        if self.result == Result.SATISFIABLE and other.result == Result.SATISFIABLE:
            return Result(Result.SATISFIABLE)
        if self.result == Result.NOT_SATISFIABLE or other.result == Result.NOT_SATISFIABLE:
            return Result(Result.NOT_SATISFIABLE)
        if self.result == Result.MAY_SATISFIABLE or other.result == Result.MAY_SATISFIABLE:
            return Result(Result.MAY_SATISFIABLE)
        raise TableauException("Uncaught logic and evaluation, left: " + str(self) + " right: " + str(other))

    def __or__(self, other):
        if self.result == Result.SATISFIABLE or other.result == Result.SATISFIABLE:
            return Result(Result.SATISFIABLE)
        if self.result == Result.MAY_SATISFIABLE or other.result == Result.MAY_SATISFIABLE:
            return Result(Result.MAY_SATISFIABLE)
        if self.result == Result.NOT_SATISFIABLE and other.result == Result.NOT_SATISFIABLE:
            return Result(Result.NOT_SATISFIABLE)
        raise TableauException("Uncaught logic or evaluation, left: " + str(self) + " right: " + str(other))


class PriorityQueue:
    def __init__(self, fms=None, syms=None):
        if syms is None:
            syms = []
        if fms is None:
            fms = []

        # intermediate formula expansions
        self.formulas: [Formula] = fms
        # terminal terms along the proof trace
        self.symbols: [Symbol] = syms

    def addFormula(self, fm: Symbol):
        if fm.isSymbol():
            self.symbols.append(fm)
        else:
            # favor Existential formula, because it can introduce new variable
            if isinstance(fm, ExistFormula):
                self.formulas.insert(0, fm)
            # favor AND formula, to increase tableau efficiency
            elif isinstance(fm, AndFormula):
                self.formulas.insert(0, fm)
            else:
                self.formulas.append(fm)

    def getFormula(self) -> Symbol | None:
        if len(self.formulas) == 0:
            return None
        return self.formulas.pop(0)

    def getRemainingSymbols(self):
        return self.symbols

    def checkContradiction(self):
        for symbol in self.symbols:
            if isinstance(symbol, NotFormula):
                for compare in self.symbols:
                    if compare == symbol.getLeft():
                        return symbol
        return None

    def copy(self):
        return PriorityQueue(self.formulas.copy(), self.symbols.copy())


class ProofMachine:
    def __init__(self):
        self._process = []
        self._expand_id = 0

    def SAT(self, t: Formula) -> Result:
        return self._isFormulaClosed(NotFormula(t), PriorityQueue(), "", "")


    def _alpha(self, queue: PriorityQueue, prefix: str, childrenPrefix: str) -> Result:
        fm = queue.getFormula()
        assert isinstance(fm, AndFormula)
        self._process.append(prefix + str(fm))

        left = fm.getLeft()
        queue.addFormula(left)
        self._process.append(prefix + str(left))

        right = fm.getRight()
        queue.addFormula(right)
        self._process.append(prefix + str(right))

        self._expand_id += 1
        return self._atom(queue, prefix, childrenPrefix)

    def _atom(self, queue: PriorityQueue, prefix: str, childrenPrefix: str) -> Result:
        symbol = queue.checkContradiction()
        if symbol is not None:
            self._process.append(prefix + "Close because {0} contradict with {1}".format(symbol, symbol.getLeft()))
            # the negation result leads to contradiction, hence this branch is satisfiable
            return Result(Result.SATISFIABLE)

        fm = queue.getFormula()
        if fm is None:
            self._process.append(prefix + "Branch is open for variables {0}"
                                 .format([str(__s) for __s in queue.getRemainingSymbols()]))
            # the negation result stands in this branch, hench this branch is not satisfiable
            return Result(Result.NOT_SATISFIABLE)

        return self._isFormulaClosed(fm, queue, prefix, childrenPrefix)

    def _beta(self, queue: PriorityQueue, prefix: str, childrenPrefix: str) -> Result:
        fm = queue.getFormula()
        assert isinstance(fm, OrFormula)

        self._process.append(prefix + str(fm))
        self._expand_id += 1

        leftCondition = self._isFormulaClosed(fm.getLeft(), queue.copy(), childrenPrefix, childrenPrefix)
        rightCondition = self._isFormulaClosed(fm.getRight(), queue.copy(), childrenPrefix, childrenPrefix)
        return leftCondition and rightCondition

    def _isFormulaClosed(self, fm: Symbol, queue: PriorityQueue, prefix: str, childrenPrefix: str) -> Result:
        # default root negation expand
        if isinstance(fm, NotFormula) or isinstance(fm, ImpliesFormula):
            fm = fm.expand()

        queue.addFormula(fm)

        # end of branch, check if and remaining formulas unchecked
        if fm.isSymbol():
            self._process.append(prefix + "├── " + str(fm))
            return self._atom(queue, prefix, childrenPrefix)

        # alpha expansion
        if isinstance(fm, AndFormula):
            prefix = childrenPrefix + "│ alpha({0}) ".format(self._expand_id)
            childrenPrefix = "│            ".format(self._expand_id)
            return self._alpha(queue, prefix, childrenPrefix)

        # beta expansion
        elif isinstance(fm, OrFormula):
            prefix = childrenPrefix + "├─beta({0})─ ".format(self._expand_id)
            childrenPrefix = childrenPrefix + "│            "
            return self._beta(queue, prefix, childrenPrefix)

        else:
            raise TableauException("Cannot evaluate formula " + str(fm))

    def getOutput(self) -> str:
        return "\n".join(self._process)


# @MainCaller
# central information process
resultTree: Formula


class ParseOutputOption:
    NOT_FORMULA = 0
    ATOM = 1
    FIRST_ORDER_FORMULA_NEGATION = 2
    UNIVERSAL_QUANTIFIED_FORMULA = 3
    EXISTENTIALLY_QUANTIFIED_FORMULA = 4
    BINARY_FIRST_ORDER_FORMULA = 5
    PROPOSITION = 6
    PROPOSITIONAL_FORMULA_NEGATION = 7
    BINARY_PROPOSITIONAL_FORMULA = 8


# Parse a formula, consult parseOutputs for return values.
def parse(fm):
    global resultTree
    try:
        callerParser = Parser()
        resultTree = callerParser.parse(fm)
        if not isinstance(resultTree, Formula):
            if isinstance(resultTree, Proposition):
                return ParseOutputOption.PROPOSITION
            return ParseOutputOption.ATOM
        if callerParser.isFirstOrderFormula():
            if resultTree.isBinary():
                return ParseOutputOption.BINARY_FIRST_ORDER_FORMULA
            if isinstance(resultTree, ExistFormula):
                return ParseOutputOption.EXISTENTIALLY_QUANTIFIED_FORMULA
            if isinstance(resultTree, ForAllFormula):
                return ParseOutputOption.UNIVERSAL_QUANTIFIED_FORMULA
            if isinstance(resultTree, NotFormula):
                return ParseOutputOption.FIRST_ORDER_FORMULA_NEGATION
        else:
            if isinstance(resultTree, NotFormula):
                return ParseOutputOption.PROPOSITIONAL_FORMULA_NEGATION
            if resultTree.isBinary():
                return ParseOutputOption.BINARY_PROPOSITIONAL_FORMULA
            return ParseOutputOption.PROPOSITION
    except ParseException:
        return ParseOutputOption.NOT_FORMULA


# Return the LHS of a binary connective formula
def lhs():
    return str(resultTree.getLeft())


# Return the connective symbol of a binary connective formula
def con():
    return resultTree.name


# Return the RHS symbol of a binary connective formula
def rhs():
    return str(resultTree.getRight())


# You may choose to represent a theory as a set or a list
def theory(fm):  # initialise a theory with a single formula in it
    return None


# check for satisfiability
def sat(fm):
    # output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    return 0


# @Template Injected
# DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']

firstLine = f.readline()

PARSE = False
if 'PARSE' in firstLine:
    PARSE = True

SAT = False
if 'SAT' in firstLine:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5, 8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (
                lhs(), con(), rhs())
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
