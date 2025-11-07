from FiniteAutomaton import FiniteAutomaton
from TSA import TSA
from CascadeDecomposition import CascadeDecomposition
# from CLI.formulaInput import askFormula

imagesFolder = "imgs/svgs/"

# s = askFormula()
# print(s)

formula_str = "a U c && (X b)"
# formula_str = "(a || c) && X(b)"
formula_str = "a && X(a && !X(a))"
formula_str = "a && X(a)"
# formula_str = "X(b)"
# formula_str = "a U c"


d = FiniteAutomaton(formulaStr=formula_str)
d.visualize("_1_dfa", imagesFolder, "svg")
rev = d.reverseTransitions(reduce=True)
rev.visualize("_2_rev", imagesFolder, "svg")

det = rev.determinize(reduce=False).removeUnreachableStates()
det.visualize("_3_det", imagesFolder, "svg")

T = TSA(det)
# print(T.toDot())
# print(T)
T.visualize(True, "tsa", imagesFolder, "svg")

CD = CascadeDecomposition(det)
# print(CD.toDot())
CD.visualize("CD", imagesFolder, "svg")