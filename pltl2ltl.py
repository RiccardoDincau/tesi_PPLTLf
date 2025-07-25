from pylogics.syntax.base import Logic, Not, And, Or, Formula
from pylogics.syntax.pltl import Atomic as PltlAtomic, PropositionalTrue as PltlTrue, PropositionalFalse as PltlFalse
from pylogics.syntax.pltl import Before, Since, Once, Historically
from pylogics.syntax.ltl import Atomic as LtlAtomic, PropositionalTrue as LtlTrue, PropositionalFalse as LtlFalse
from pylogics.syntax.ltl import Next, Until

def switchPltlToLtl(phi: Formula | PltlAtomic) -> Formula | LtlAtomic:
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
        return Not(switchPltlToLtl(arg))
    
    elif type(phi) == And:
        assert type(phi) is And
        args = phi.operands
        return And(switchPltlToLtl(args[0]), switchPltlToLtl(args[1]))
    
    elif type(phi) == Or:
        assert type(phi) is Or
        args = phi.operands
        return Or(switchPltlToLtl(args[0]), switchPltlToLtl(args[1]))
    
    elif type(phi) == Before:
        assert type(phi) is Before
        arg = phi.argument
        return Next(switchPltlToLtl(arg))
    
    elif type(phi) == Since:
        assert type(phi) is Since
        args = phi.operands
        return Until(switchPltlToLtl(args[0]), switchPltlToLtl(args[1]))
    
    elif type(phi) == Once:
        assert type(phi) is Once
        arg = phi.argument
        return switchPltlToLtl(Since(PltlTrue(), arg))
    
    elif type(phi) == Historically:
        assert type(phi) is Historically
        arg = phi.argument
        return switchPltlToLtl(Not(Once(Not(arg))))

    # Non reachable 
    return phi          

def convertToString(phi: Formula | LtlAtomic) -> str:
    """Transform the formula to a string"""
    
    S = ""
    
    if type(phi) == LtlAtomic:
        assert type(phi) is LtlAtomic
        S = f"({phi.name})"
    
    elif type(phi) == LtlTrue:
        S = "(true)"
    
    elif type(phi) == LtlFalse:
        S = "(false)"
    
    elif type(phi) == Not:
        assert type(phi) is Not
        S = f" !{convertToString(phi.argument)}"
        
    elif type(phi) == And:
        assert type(phi) is And
        arg1, arg2 = (convertToString(phi.operands[0]), convertToString(phi.operands[1]))
        S = f"({arg1} && {arg2})"

    elif type(phi) == Or:
        assert type(phi) is Or
        arg1, arg2 = (convertToString(phi.operands[0]), convertToString(phi.operands[1]))
        S = f"({arg1} || {arg2})"
        
    elif type(phi) == Next:
        assert type(phi) is Next
        S = f" X{convertToString(phi.argument)}"
        
    elif type(phi) == Until:
        assert type(phi) is Until
        arg1, arg2 = (convertToString(phi.operands[0]), convertToString(phi.operands[1]))
        S = f"({arg1} U {arg2})"
    
    return S
    
    

if __name__ == "__main__":
    from pylogics.parsers.pltl import parse_pltl 
    from ltlf2dfa.parser.ltlf import LTLfParser
    from FiniteAutomaton import FiniteAutomaton
    
    # formula = parse_pltl("((!d) S e)" )
    formula = parse_pltl("(a S !b && H (d && e || !d)) S (a && b || ! ((!d) S e))" )
    
    newF = switchPltlToLtl(formula)
    # print("ltl:", newF)
    
    newFStr = convertToString(newF)
    # print("str:",newFStr)
    
    parser = LTLfParser()
    formula = parser(newFStr)

    dfaStr = formula.to_dfa(False)

    d = FiniteAutomaton(dotsFormat=dfaStr)
    d.setName("1_DFA")
    d.visualize()
    newD = d.reverseTransitions(reduce=True).determinize(reduce=True)
    newD.setName("2_DFA")
    newD.visualize()