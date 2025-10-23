from FiniteAutomaton import FiniteAutomaton, Transition
from CLI.formulaInput import askFormula
from TSA import TSA

imagesFolder = "imgs/"

# s = askFormula()
# print(s)

formula_str = "a U c && (X b)"
formula_str = "b || X(b)"
# formula_str = "X(b)"
# formula_str = "a U c"

d = FiniteAutomaton(formulaStr=formula_str)
rev = d.reverseTransitions(reduce=True)
det = rev.determinize(reduce=True)

d.visualize("_1_dfa", imagesFolder)
rev.visualize("_2_rev", imagesFolder)
det.visualize("_3_det", imagesFolder)

T = TSA(det)
# print(T.toDot())
# print(T)
T.visualize(True, "tsa", imagesFolder)