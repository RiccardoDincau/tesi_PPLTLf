from FiniteAutomaton import FiniteAutomaton
from TSA import TSA
from CascadeDecomposition import CascadeDecomposition
# from CLI.formulaInput import askFormula

imagesFolder = "imgs/"

# s = askFormula()
# print(s)

formula_str = "a U c && (X b)"
formula_str = "b && X(b)"
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

CD = CascadeDecomposition(det)
# print(CD.toDot())
CD.visualize("CD", imagesFolder)