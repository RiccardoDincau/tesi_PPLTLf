from FiniteAutomaton import FiniteAutomaton, Transition
from CLI.formulaInput import askFormula
from TSA import TSA
# s = askFormula()
# print(s)

formula_str = "a U c && (X b)"
formula_str = "b || X(b)"
# formula_str = "X(b)"
# formula_str = "a U c"

d = FiniteAutomaton(formulaStr=formula_str)
d.setName("1_DFA")
rev = d.reverseTransitions(reduce=True)
rev.setName("2_Rev")
det = rev.determinize(reduce=True)
det.setName("3_Det")


d.visualize()
rev.visualize()
det.visualize()

T = TSA(det)
# print(T.toDot())
# print(T)
T.visualize(True)