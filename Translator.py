from pylogics.syntax.base import Logic, Not, And, Or, FalseFormula, TrueFormula
from pylogics.syntax.pltl import Atomic as PltlAtomic, PropositionalTrue as PltlTrue, PropositionalFalse as PltlFalse
from pylogics.syntax.pltl import Before, Since, Once, Historically, Formula as PLTLFromula
from pylogics.syntax.ltl import Atomic as LtlAtomic, PropositionalTrue as LtlTrue, PropositionalFalse as LtlFalse
from pylogics.syntax.ltl import Next, Until, Formula as LTLFromula
from pylogics.parsers.pltl import parse_pltl 
from FiniteAutomaton import FiniteAutomaton
from CascadeDecomposition import CascadeDecomposition

class Translator:
    def __init__(self) -> None:
        pass
    
    def pltlToLtl(self, formula: str) -> LTLFromula:
        pltlF = parse_pltl(formula)
        
        switched = self.switchPltlToLtl(pltlF)
        
        print("Switched:", self.convertToString(switched))
        
        switchedDfa = FiniteAutomaton(formulaStr=self.convertToString(switched))
        switchedDfa.visualize("switchedDfa", "imgs/trn/")
        
        reversedNfa = switchedDfa.reverseTransitions(True)
        
        reversedNfa.visualize("reversed", "imgs/trn/")
        
        reverseSwitchedDfa = reversedNfa.determinize(True)
        
        reverseSwitchedDfa.visualize("switched_Det", "imgs/trn/")
        
        cascadeDecomposition = CascadeDecomposition(reverseSwitchedDfa)
        
        cascadeDecomposition.visualize("CD_Translator", "imgs/trn/")
        
        pltlSwitched = cascadeDecomposition.synthetizeFormula()
        
        ltlF = self.switchPltlToLtl(pltlSwitched)
        
        return ltlF
        
    
    def switchPltlToLtl(self, phi: PLTLFromula) -> LTLFromula:
        """Apply the switch function to a pltl formula"""
        
        if type(phi) == PltlAtomic:
            assert type(phi) is PltlAtomic
            return LtlAtomic(phi.name)
        
        elif type(phi) == PltlTrue:
            return LtlTrue()
        
        elif type(phi) == PltlFalse:
            return LtlFalse()
        
        elif type(phi) == Not:
            assert type(phi) is Not
            arg = phi.argument
            return Not(self.switchPltlToLtl(arg))
        
        elif type(phi) == And:
            assert type(phi) is And
            args = phi.operands
            return And(self.switchPltlToLtl(args[0]), self.switchPltlToLtl(args[1]))
        
        elif type(phi) == Or:
            assert type(phi) is Or
            args = phi.operands
            return Or(self.switchPltlToLtl(args[0]), self.switchPltlToLtl(args[1]))
        
        elif type(phi) == Before:
            assert type(phi) is Before
            arg = phi.argument
            return Next(self.switchPltlToLtl(arg))
        
        elif type(phi) == Since:
            assert type(phi) is Since
            args = phi.operands
            return Until(self.switchPltlToLtl(args[0]), self.switchPltlToLtl(args[1]))
        
        elif type(phi) == Once:
            assert type(phi) is Once
            arg = phi.argument
            return self.switchPltlToLtl(Since(PltlTrue(), arg))
        
        elif type(phi) == Historically:
            assert type(phi) is Historically
            arg = phi.argument
            return self.switchPltlToLtl(Not(Once(Not(arg))))

        # Non reachable 
        return phi          

    def convertToString(self, phi: LTLFromula) -> str:
        """Transform the formula to a string"""
        
        S = ""
        
        if type(phi) == LtlAtomic:
            assert type(phi) is LtlAtomic
            S = f"{phi.name}"
        
        elif type(phi) == FalseFormula or type(phi) == LtlFalse:
            S = "false"
            
        elif type(phi) == LtlTrue or type(phi) == TrueFormula:
            S = "true"
        
        elif type(phi) == Not:
            assert type(phi) is Not
            S = f" !{self.convertToString(phi.argument)}"
            
        elif type(phi) == And:
            assert type(phi) is And
            arg1, arg2 = (self.convertToString(phi.operands[0]), self.convertToString(phi.operands[1]))
            S = f"({arg1} && {arg2})"

        elif type(phi) == Or:
            assert type(phi) is Or
            arg1, arg2 = (self.convertToString(phi.operands[0]), self.convertToString(phi.operands[1]))
            S = f"({arg1} || {arg2})"
            
        elif type(phi) == Next:
            assert type(phi) is Next
            S = f" X({self.convertToString(phi.argument)})"
            
        elif type(phi) == Until:
            assert type(phi) is Until
            arg1, arg2 = (self.convertToString(phi.operands[0]), self.convertToString(phi.operands[1]))
            S = f"({arg1} U {arg2})"
        
        return S
    
if __name__ == "__main__":
    formula = "a && Y(b)"
    
    print("Translating:", formula)
    T = Translator()
    trans = T.pltlToLtl(formula)
    
    # print(trans)
    print(T.convertToString(trans))