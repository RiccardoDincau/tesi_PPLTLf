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
        
        reverseSwitchedDfa.visualize("switchedRevDfa", "imgs/trn/")
        
        # from itertools import combinations, chain, combinations_with_replacement
        # atProp = switchedDfa.atomicProps
        
        # alphabet_it = chain.from_iterable(combinations(atProp, r) for r in range(len(atProp) + 1))
        # alphabet = [set(char) for char in alphabet_it]
        # print("Alphabet:", alphabet)
        
        # word_it = chain.from_iterable(combinations_with_replacement(alphabet, r) for r in range(10))
        # words = [list(word) for word in word_it]
        # # print("Words:", words)
        
        # for word in words:
        #     dfaA = switchedDfa.recognizeWord(switchedDfa.initState, word)
        #     dfaB = reverseSwitchedDfa.recognizeWord(reverseSwitchedDfa.initState, list(reversed(word)))
            
        #     if len(word) > 0 and len(word[0]) == 0: print("len:", len(word))
        #     # print(f"A: {dfaA}, B: {dfaB}")
            
        #     if dfaA != dfaB: print("!!!!!!", word)
        
        cascadeDecomposition = CascadeDecomposition(reverseSwitchedDfa)
        
        cascadeDecomposition.tsa.visualize(True, "TSA", "imgs/trn/")
        
        cascadeDecomposition.tsa.isomorphicAutomaton().visualize("TSAisoFA", "imgs/trn/")    
        
        cascadeDecomposition.visualize("CD_Translator", "imgs/trn/")
        
        cascadeDecomposition.isomorphicAutomaton().visualize("CDisoFA", "imgs/trn/")    

        # pltlSwitched = cascadeDecomposition.synthetizeFormula()
        
        # ltlF = self.switchPltlToLtl(pltlSwitched)
        
        return switched
        
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
            S = f"(!{self.convertToString(phi.argument)})"
            
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
            S = f"X({self.convertToString(phi.argument)})"
            
        elif type(phi) == Until:
            assert type(phi) is Until
            arg1, arg2 = (self.convertToString(phi.operands[0]), self.convertToString(phi.operands[1]))
            S = f"({arg1} U {arg2})"
        
        return S
    
    def convertToVisualizer(self, phi: LTLFromula) -> str:
        """Transform the formula to a string"""
        
        S = ""
        if type(phi) == LtlAtomic:
            assert type(phi) is LtlAtomic
            S = f"{phi.name[0].upper()}"
        
        elif type(phi) == FalseFormula or type(phi) == LtlFalse:
            S = "false"
            
        elif type(phi) == LtlTrue or type(phi) == TrueFormula:
            S = "true"
        
        elif type(phi) == Not:
            assert type(phi) is Not
            S = f"not({self.convertToVisualizer(phi.argument)})"
            
        elif type(phi) == And:
            assert type(phi) is And
            arg1, arg2 = (self.convertToVisualizer(phi.operands[0]), self.convertToVisualizer(phi.operands[1]))
            S = f"and({arg1}, {arg2})"

        elif type(phi) == Or:
            assert type(phi) is Or
            arg1, arg2 = (self.convertToVisualizer(phi.operands[0]), self.convertToVisualizer(phi.operands[1]))
            S = f"or({arg1}, {arg2})"
            
        elif type(phi) == Next:
            assert type(phi) is Next
            S = f"next({self.convertToVisualizer(phi.argument)})"
            
        elif type(phi) == Until:
            assert type(phi) is Until
            arg1, arg2 = (self.convertToVisualizer(phi.operands[0]), self.convertToVisualizer(phi.operands[1]))
            S = f"until({arg1}, {arg2})"
        
        return S
    
    def reduceFormula(self, f: LTLFromula) -> LTLFromula:
        if type(f) == LtlAtomic:
            return f
        
        elif type(f) == FalseFormula or type(f) == LtlFalse:
            return f
            
        elif type(f) == LtlTrue or type(f) == TrueFormula:
            return f
        
        elif type(f) == Not:
            return Not(self.reduceFormula(f.argument))
        
        if type(f) == And:
            if type(f.operands[0]) == LtlTrue or type(f.operands[0]) == TrueFormula:
                return self.reduceFormula(f.operands[1])
    
            if type(f.operands[1]) == LtlTrue or type(f.operands[1]) == TrueFormula:
                return self.reduceFormula(f.operands[0])
            
            return And(self.reduceFormula(f.operands[0]), self.reduceFormula(f.operands[1]))
         
        elif type(f) == Or:
            arg1, arg2 = (f.operands[0], f.operands[1])
            if type(arg1) == And and type(arg2) == And:
                if type(arg1.operands[0]) == Not:
                    if arg1.operands[0].argument == arg2.operands[0] and arg1.operands[1] == arg2.operands[1]:
                            return self.reduceFormula(arg1.operands[1])
            return Or(self.reduceFormula(arg1), self.reduceFormula(arg2))
            
        elif type(f) == Next:
            return Next(f.argument)
                    
        elif type(f) == Until:
            arg1, arg2 = (self.reduceFormula(f.operands[0]), self.reduceFormula(f.operands[1]))
            return Until(arg1, arg2)
        
        return f
    
if __name__ == "__main__":
    # formula = "a S Y(b) && !Y(b) || Y(!a S b)"
    # formula = "a && true"
    # formula = "a && Y(c S !a)"
    # formula = "a && b"
    # formula = "Y(a)"
    # formula = "(a S b) || Y(a)" # !!!!!
    # formula = "a && (true S b)" 
    formula = "true" 
    # formula = "(a S b)" 
    
    print("Translating:", formula)
    T = Translator()
    trans = T.pltlToLtl(formula)
    print("rr:", T.convertToString(trans))
    trans = T.reduceFormula(trans)
    print("Res:", T.convertToString(trans))
    print("vis:", T.convertToVisualizer(trans))
    
    # (( (!X(true)) U (a && X(true)) ))
    