from ltlf2dfa.parser.ltlf import LTLfParser
from FiniteAutomaton import FiniteAutomaton
from CLI.formulaInput import askFormula

# s = askFormula()
# print(s)

parser = LTLfParser()
formula_str = "(a U b) || (X true)"
formula = parser(formula_str)

dfaStr = formula.to_dfa(False)

d = FiniteAutomaton(dotsFormat=dfaStr)
d.setName("1_DFA")
rev = d.reverseTransitions(reduce=True)
rev.setName("2_Rev")
det = rev.determinize(reduce=True)
det.setName("3_Det")

d.visualize()
rev.visualize()
det.visualize()