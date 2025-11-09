from TSA import TSA
from FiniteAutomaton import FiniteAutomaton, State
from itertools import combinations, chain

from pylogics.syntax.base import Logic, Not, And, Or
from pylogics.syntax.pltl import Atomic as PltlAtomic, PropositionalTrue as PltlTrue, PropositionalFalse as PltlFalse
from pylogics.syntax.pltl import Formula, Before, Since, Once, Historically

class CascadeAutomaton:
    def __init__(self, layer: int, parentCA: "CascadeAutomaton | None", tsa: TSA) -> None:
        """A reset automaton representing a layer of a cascade decomposition"""
        # Theta is the identity function because it is a reset automaton
        
        self.layer = layer
        self.Q: list[int] = []

        self.psiInv: dict[tuple[int, ...], int] = {}  
        self.atomicProps: set[str] = tsa.atomicProps
        
        # (currentAutomatonState, parentState, propositionalInterpretation) => currentAutomatonState
        self.delta: dict[tuple[int, tuple[int, ...], tuple[str, ...]], int] = {}
        
        if layer == 0:
            self.Q.append(0)
            
            # For the fisrt layer (The root) the node is mapped to its self
            self.psiInv[(0,)] = 0
            
            alphabet_it = chain.from_iterable(combinations(tsa.atomicProps, r) for r in range(len(tsa.atomicProps)+1))
            
            for s in alphabet_it:
                coord: tuple[int, tuple[int, ...], tuple[str, ...]] = (0, tuple(), s) 
                self.delta[coord] = tsa.nodes[0].trans[str(set(s))]
        else:
            assert parentCA != None
            
            for parent in tsa.heightClasses[tsa.height - (layer - 1)]:
                self.Q.extend(tsa.nodes[parent].children)

            for p in parentCA.psiInv.keys():
                for q in self.Q:
                    # Because it's a reset automaton thetaInv of q is q
                    config: tuple[int, ...] = p + (q,)
                    
                    p_inv = parentCA.psiInv[p]
                    C = tsa.nodes[p_inv].children
                    
                    if q in C:
                        self.psiInv[config] = q
                        
                        alphabet_it = chain.from_iterable(combinations(tsa.atomicProps, r) for r in range(len(tsa.atomicProps)+1))
                
                        for s in alphabet_it:
                            coord: tuple[int, tuple[int, ...], tuple[str, ...]] = (q, p, s)
                            inv = self.psiInv[config]
                            key = str(set(s))
                            
                            if key in tsa.nodes[inv].trans:
                                self.delta[coord] = tsa.nodes[inv].trans[key]
                            else:
                                print("!!!! row 55")  
                                
    def computeStateIns(self, state: int) -> list[tuple[tuple[int, ...], set[str]]]:
        ins: list[tuple[tuple[int, ...], set[str]]] = [] 
        for k in self.delta.keys():
            if self.delta[k] == state:
                ins.append((k[1], set(k[2])))
        return ins
    
    def computeStateOuts(self, state: int) -> list[tuple[tuple[int, ...], set[str]]]:
        outs: list[tuple[tuple[int, ...], set[str]]] = [] 
        for k in self.delta.keys():
            if k[0] == state:
                outs.append((k[1], set(k[2])))    
        return outs

    def propIntToStr(self, propositionalInterpretation: set[str]) -> str:
        S = ""
        for p in self.atomicProps:
            if len(S) > 0:
                S += " && "
            if p in propositionalInterpretation:
                S += f"{p}"
            else:
                S += f"~{p}"
        
        return S     

    def configToStr(self, config: tuple[int, ...]) -> str:
        S = ""
        for l in list(config):
            if len(S) > 0:
                S += ","
            S += chr(ord("A") + l)

        return S
                                
    def toDot(self) -> str:
        S: str = f"digraph CA "
        S += """{
    rankdir = TD;
    center = true;
    edge [fontname = Courier];
    node [height = .5, width = .5];
    node [shape = square];\n"""
        
        S += self.toDotSubgraph()
            
        S += "\n}"
        return S
    
    def toDotSubgraph(self, tsa: TSA | None = None) -> str:
        S: str = ""
        S += "{"
        for q in self.Q:
            letter = chr(ord("A") + q)
            if tsa != None:
                S += f"\n\t{q} [label=\"{letter} {tsa.nodes[q].states}\"]"
            else:
                S += f"\n\t{q} [label=\"{letter}]"
            
        for k in self.delta.keys():
            S += f"\n\t{k[0]} -> {self.delta[k]} [label=\"[{self.configToStr(k[1])}] {self.propIntToStr(set(k[2]))}\"];"
    
        S += "\n}\n"
        return S
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        src.render(imagePath + imageName, format = "svg", view = False)
        
class CascadeDecomposition:
    def __init__(self, dfa: FiniteAutomaton):
        """Build the cascade decomposition of a counter-free deterministic
        FiniteAutomaton representing a temporal logic formula"""
        
        self.tsa = TSA(dfa)
        self.dfaStatesNumber = dfa.statesNumber
        self.dfaAcceptingStates = dfa.acceptingStates

        self.CAs: list[CascadeAutomaton] = [CascadeAutomaton(0, None, self.tsa)]
        for layer in range(1, self.tsa.height + 1):
            newCA = CascadeAutomaton(layer, self.CAs[layer - 1], self.tsa)
            self.CAs.append(newCA)
            
        self.stateToCa: dict[int, CascadeAutomaton] = {}
        for CA in self.CAs:
            for q in CA.Q:
                self.stateToCa[q] = CA
                
        self.phiInv = self.computePhiInv()
            
    def synthetizeFormula(self) -> Formula:
        res: Formula | None = None
        
        for state in self.dfaAcceptingStates:
            if res == None:
                res = self.accpetingStateFormula(state)
            else:
                res = Or(res, self.accpetingStateFormula(state))

        assert res != None
        
        return res

    def accpetingStateFormula(self, s: State) -> Formula:
        res: Formula | None = None
        
        for config in self.phiInv[s.index]:
            if res == None:
                res = self.configurationFormula(config)
            else:
                res = Or(res, self.configurationFormula(config))

        assert res != None
        
        return res
    
    def configurationFormula(self, config: tuple[int, ...]) -> Formula:
        res: Formula | None = None
        
        for q in list(config):
            if res == None:
                res = self.CAStateFormula(q)
            else:
                res = Or(res, self.CAStateFormula(q))
        
        assert res != None, print("Configuration is empty!")
        
        return res
        
    def CAStateFormula(self, q: int) -> Formula:
        # The first state is always the trivial one-state automaton
        if q == 0:
            return PltlTrue()
        
        CA = self.stateToCa[q]
        
        ins = CA.computeStateIns(q)
        outs = CA.computeStateOuts(q)
        
        inFromula: Formula | None = None
        
        for c in ins:
            f: Formula = Or(self.propIntToFormula(c[1]), Before(self.configurationFormula(c[0])))
            
            if inFromula == None:
                inFromula = f
            else:
                inFromula = Or(inFromula, f)  
                 
        outFromula: Formula | None = None
        
        for c in outs:
            f: Formula = Or(self.propIntToFormula(c[1]), Before(self.configurationFormula(c[0])))
            
            if outFromula == None:
                outFromula = f
            else:
                outFromula = Or(outFromula, f)    
        
        assert inFromula != None
        assert outFromula != None            

        return Since(Not(outFromula), inFromula) 
    
    def propIntToFormula(self, propInt: set[str]) -> Formula:
        res: Formula | None = None
        
        for s in self.tsa.atomicProps:
            f: Formula
            if s in propInt:
                f = PltlAtomic(s)
            else:
                f = Not(PltlAtomic(s))
            
            if res == None:
                res = f
            else:
                res = And(res, f)
                
        assert res != None, print("There is not an atomic proposition!")
                
        return res

    def computePhiInv(self) -> list[list[tuple[int, ...]]]:
        phiInv: list[list[tuple[int, ...]]] = [[] for _ in range(self.dfaStatesNumber)]
        
        lastCa = self.CAs[len(self.CAs) - 1]
        for config in lastCa.psiInv.keys():
            for q in self.tsa.nodes[lastCa.psiInv[config]].states:
                phiInv[q].append(config)
        
        return phiInv

    def toDot(self) -> str:
        S: str = f"digraph CD "
        S += """{
    rankdir = TD;
    center = true;
    edge [fontname = Courier];
    node [height = .5, width = .5];
    node [shape = square];"""
        S += "\n\tgraph [nodesep=0.7, rankdir=RL];"
        
        for CA in reversed(self.CAs):
            S += "\n\t" + CA.toDotSubgraph(self.tsa)
        S += "\n}"
        
        return S
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/", format = "svg") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        src.render(imagePath + imageName, format = format, view = False)
  