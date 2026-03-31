from pylogics.syntax.base import Logic, Not, And, Or, FalseFormula, TrueFormula
from pylogics.syntax.pltl import Atomic as PltlAtomic, PropositionalTrue as PltlTrue, PropositionalFalse as PltlFalse
from pylogics.syntax.pltl import Before, Since, Once, Historically, Formula as PLTLFormula, WeakSince
from pylogics.syntax.ltl import Atomic as LtlAtomic, PropositionalTrue as LtlTrue, PropositionalFalse as LtlFalse
from pylogics.syntax.ltl import Next, Until, Formula as LTLFormula
from pylogics.parsers.pltl import parse_pltl 
from pylogics.parsers.ltl import parse_ltl 
from FiniteAutomaton import FiniteAutomaton
from CascadeDecomposition import CascadeDecomposition

class Translator:
    def __init__(self) -> None:
        pass
    
    def ltlToPltl(self, ltlFormula: str) -> PLTLFormula:
        dfa = FiniteAutomaton(formulaStr=ltlFormula).removeUnreachableStates()
        dfa.visualize("ltlToPltlDfa", "imgs/trn/")
    
        CD = CascadeDecomposition(dfa)
        
        CD.tsa.visualize(True, "TSA", "imgs/trn/")
        
        CD.tsa.isomorphicAutomaton().visualize("TSAisoFA", "imgs/trn/")    
        
        CD.visualize("CD", "imgs/trn/")
        
        CD.homomorphicAutomaton().visualize("CDisoFA", "imgs/trn/")  
        CD.homomorphicAutomatonPhi().visualize("CDisoFA2", "imgs/trn/")  
        # print("CD phi:", CD.phi)
        
        for CA in CD.CAs:
            for state in CA.Q:
                print(chr(ord("A") + state.totalIndex), end = "")
                # print(CA.computeStateIns(state.index))
                # print(CA.computeStateOuts(state.index))
                print(" --> ", self.convertPltlToString(CD.CAStateFormula(state.totalIndex, state.index)))
        
        # return PltlTrue()
        return CD.synthetizeFormula()
        
    def pltlToLtl(self, formula: str) -> LTLFormula:
        pltlF = parse_pltl(formula)
        
        switched = self.switchPltlToLtl(pltlF)
        
        print("Switched:", self.convertLtlToString(switched))
        
        switchedDfa = FiniteAutomaton(formulaStr=self.convertLtlToString(switched))
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
        
        cascadeDecomposition.homomorphicAutomaton().visualize("CDisoFA", "imgs/trn/")    

        pltlSwitched = cascadeDecomposition.synthetizeFormula()
        
        ltlF = self.switchPltlToLtl(pltlSwitched)
        
        return ltlF
        
    def switchPltlToLtl(self, phi: PLTLFormula) -> LTLFormula:
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

    def convertLtlToString(self, phi: LTLFormula) -> str:
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
            S = f"(!{self.convertLtlToString(phi.argument)})"
            
        elif type(phi) == And:
            assert type(phi) is And
            S = ""
            for op in phi.operands:
                if (type(op) == TrueFormula or type(op) == LtlTrue):
                    continue
                if S == "":
                    S += self.convertLtlToString(op)
                else:
                    S += " && " + self.convertLtlToString(op)
                    
            S = f"({S})"

        elif type(phi) == Or:
            assert type(phi) is Or
            S = ""
            for op in phi.operands:
                if type(op) == FalseFormula or type(op) == LtlFalse:
                    continue
                if S == "":
                    S += self.convertLtlToString(op)
                else:
                    S += " || " + self.convertLtlToString(op)
                    
            S = f"({S})"
            
        elif type(phi) == Next:
            assert type(phi) is Next
            S = f"X({self.convertLtlToString(phi.argument)})"
            
        elif type(phi) == Until:
            assert type(phi) is Until
            arg1, arg2 = (self.convertLtlToString(phi.operands[0]), self.convertLtlToString(phi.operands[1]))
            S = f"({arg1} U {arg2})"
        
        return S
    
    def convertPltlToString(self, phi: PLTLFormula) -> str:
        """Transform the formula to a string"""
        
        S = ""
        
        if type(phi) == PltlAtomic:
            assert type(phi) is PltlAtomic
            S = f"{phi.name}"
        
        elif type(phi) == FalseFormula or type(phi) == PltlFalse:
            S = "false"
            
        elif type(phi) == PltlTrue or type(phi) == TrueFormula:
            S = "true"
        
        elif type(phi) == Not:
            assert type(phi) is Not
            S = f"!({self.convertPltlToString(phi.argument)})"
            
        elif type(phi) == And:
            assert type(phi) is And
            S = ""
            for op in phi.operands:
                if type(op) ==TrueFormula or type(op) == PltlTrue:
                    continue
                if S == "":
                    S += self.convertPltlToString(op)
                else:
                    S += " && " + self.convertPltlToString(op)
                    
            S = f"({S})"

        elif type(phi) == Or:
            assert type(phi) is Or

            S = ""
            for op in phi.operands:
                if type(op) == FalseFormula or type(op) == PltlFalse:
                    continue
                if S == "":
                    S += self.convertPltlToString(op)
                else:
                    S += " || " + self.convertPltlToString(op)
                    
            S = f"({S})"
            
        elif type(phi) == Before:
            assert type(phi) is Before
            S = f"Y({self.convertPltlToString(phi.argument)})"
            
        elif type(phi) == WeakSince:
            assert type(phi) is WeakSince
            arg1, arg2 = (self.convertPltlToString(phi.operands[0]), self.convertPltlToString(phi.operands[1]))
            S = f"({arg1} W {arg2})"
            
        elif type(phi) == Since:
            assert type(phi) is Since
            arg1, arg2 = (self.convertPltlToString(phi.operands[0]), self.convertPltlToString(phi.operands[1]))
            S = f"({arg1} S {arg2})"
        
        return S

    def convertToVisualizer(self, phi: LTLFormula) -> str:
        """Transform the formula to a string"""
        
        S = ""
        if type(phi) == LtlAtomic:
            assert type(phi) is LtlAtomic
            S = f"{phi.name[0].upper()}"
        
        elif type(phi) == FalseFormula or type(phi) == LtlFalse:
            S = "and(A, not(A))"
            
        elif type(phi) == LtlTrue or type(phi) == TrueFormula:
            S = "or(A, not(A))"
        
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
    
    def reduceFormula(self, f: LTLFormula) -> LTLFormula:
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
    
    def LTLtoBlackSyntax(self, phi: LTLFormula) -> str:
        """Transform the formula to a string"""
        
        S = ""
        
        if type(phi) == LtlAtomic:
            assert type(phi) is LtlAtomic
            S = f"{phi.name}"
        
        elif type(phi) == FalseFormula or type(phi) == LtlFalse:
            S = "False"
            
        elif type(phi) == LtlTrue or type(phi) == TrueFormula:
            S = "True"
        
        elif type(phi) == Not:
            assert type(phi) is Not
            S = f"(!{self.LTLtoBlackSyntax(phi.argument)})"
            
        elif type(phi) == And:
            assert type(phi) is And
            S = ""
            for op in phi.operands:
                if (type(op) == TrueFormula or type(op) == LtlTrue):
                    continue
                if S == "":
                    S += self.LTLtoBlackSyntax(op)
                else:
                    S += " && " + self.LTLtoBlackSyntax(op)
                    
            S = f"({S})"

        elif type(phi) == Or:
            assert type(phi) is Or
            S = ""
            for op in phi.operands:
                if type(op) == FalseFormula or type(op) == LtlFalse:
                    continue
                if S == "":
                    S += self.LTLtoBlackSyntax(op)
                else:
                    S += " || " + self.LTLtoBlackSyntax(op)
                    
            S = f"({S})"
            
        elif type(phi) == Next:
            assert type(phi) is Next
            S = f"X({self.LTLtoBlackSyntax(phi.argument)})"
            
        elif type(phi) == Until:
            assert type(phi) is Until
            arg1, arg2 = (self.LTLtoBlackSyntax(phi.operands[0]), self.LTLtoBlackSyntax(phi.operands[1]))
            S = f"({arg1} U {arg2})"
        
        return S
    
    def PLTLtoBlackSyntax(self, phi: PLTLFormula) -> str:
        """Transform the formula to a string in Black syntax"""
        
        S = ""
        
        if type(phi) == PltlAtomic:
            assert type(phi) is PltlAtomic
            S = f"{phi.name}"
        
        elif type(phi) == FalseFormula or type(phi) == PltlFalse:
            S = "False"
            
        elif type(phi) == PltlTrue or type(phi) == TrueFormula:
            S = "True"
        
        elif type(phi) == Not:
            assert type(phi) is Not
            S = f"!({self.PLTLtoBlackSyntax(phi.argument)})"
            
        elif type(phi) == And:
            assert type(phi) is And
            S = ""
            for op in phi.operands:
                if type(op) ==TrueFormula or type(op) == PltlTrue:
                    continue
                if S == "":
                    S += self.PLTLtoBlackSyntax(op)
                else:
                    S += " && " + self.PLTLtoBlackSyntax(op)
                    
            S = f"({S})"

        elif type(phi) == Or:
            assert type(phi) is Or

            S = ""
            for op in phi.operands:
                if type(op) == FalseFormula or type(op) == PltlFalse:
                    continue
                if S == "":
                    S += self.PLTLtoBlackSyntax(op)
                else:
                    S += " || " + self.PLTLtoBlackSyntax(op)
                    
            S = f"({S})"
            
        elif type(phi) == Before:
            assert type(phi) is Before
            S = f"Y({self.PLTLtoBlackSyntax(phi.argument)})"
            
        elif type(phi) == WeakSince:
            assert type(phi) is WeakSince
            arg1, arg2 = (self.PLTLtoBlackSyntax(phi.operands[0]), self.PLTLtoBlackSyntax(phi.operands[1]))
            # S = f"(({arg1} S {arg2}) || (!(Y(True))))"
            S = f"({arg1} S {arg2}) || (!(True S (!({arg1}))))"
            
        elif type(phi) == Since:
            assert type(phi) is Since
            arg1, arg2 = (self.PLTLtoBlackSyntax(phi.operands[0]), self.PLTLtoBlackSyntax(phi.operands[1]))
            S = f"({arg1} S {arg2})"
        
        return S
        
    
    def blackEquivalence(self, f1: LTLFormula, f2: PLTLFormula) -> str:
        return "(" + self.LTLtoBlackSyntax(f1) + ") <-> (True U (" + self.PLTLtoBlackSyntax(f2) + "))"
    
    def blackValidity(self, f1: LTLFormula, f2: PLTLFormula) -> str:
        return "!(" + self.blackEquivalence(f1, f2) + ")"
    
if __name__ == "__main__":
    from pylogics.parsers import parse_ltl
    
    # formula = "true U (b || a)"
    # formula = "a U b"
    formula = "b"
    # formula = "X (a)"
    # formula = "X(a) U b"
    # formula = "X(a) && X(!b)"
    # formula = "(a || b) U c"
    # formula = "a U b"
    formula = "true U (a)"
    # formula = "true U (X(a))"
    # formula = "a U b"
    # formula = "X (a)"
    
    formulaParsed = parse_ltl(formula)
        
    # print("Translating:", formula)
    T = Translator()
    trans = T.ltlToPltl(formula)
    # print("F:", trans)
    print("PltlFormula:", trans)
    print("PltlFormula:", T.convertPltlToString(trans))
    # print("Black syntax:", T.PLTLtoBlackSyntax(trans))
    print("Equiv:", T.blackValidity(formulaParsed, trans))
    # print(T.blackValidity(formulaParsed, trans))
    
    # print(T.LTLtoBlackSyntax(Next(LtlFalse())))
    
    print("Black weak:", T.PLTLtoBlackSyntax(WeakSince(PltlFalse(), PltlFalse())))
    
    # !((b) <-> (True S (( (True S ((b && (!((True)) S False) || ( !(True S (!(!((True)))   ))))))))))
    