from TSA import TSA, TSANode
from FiniteAutomaton import FiniteAutomaton, State
from itertools import combinations, chain

from pylogics.syntax.base import Logic, Not, And, Or
from pylogics.syntax.pltl import Atomic as PltlAtomic, PropositionalTrue as PltlTrue, PropositionalFalse as PltlFalse
from pylogics.syntax.pltl import Formula, Before, Since, Once, Historically

class CascadeState:
    def __init__(self, index: int, tsaNode: TSANode) -> None:
        self.index = index
        self.totalIndex = -1
        self.tsaNode = tsaNode
        
class CascadeAutomaton:
    def __init__(self, layer: int, parentCA: "CascadeAutomaton | None", tsa: TSA) -> None:
        """A reset automaton representing a layer of a cascade decomposition"""
        # Theta is the identity function because it is a reset automaton
        
        self.tsa = tsa
        self.parentCA = parentCA
        self.layer = layer
        self.Q: list[CascadeState] = []

        self.psiInv: dict[tuple[int, ...], TSANode] = {}  
        self.atomicProps: set[str] = tsa.atomicProps
        
        # delta: (currentAutomatonState, parentState, propositionalInterpretation) => currentAutomatonState
        self.delta: dict[tuple[int, tuple[int, ...], tuple[str, ...]], CascadeState] = {}
        
        # theta: equivalenceClass => (m => caState)
        self.theta: dict[int, dict[int, CascadeState]] = {}
        
        # thetaInv: caState.index => list[TSA]
        self.thetaInv: dict[int, list[TSANode]] = {}
        self.stateSum = parentCA.stateSum if parentCA != None else 0
            
        if layer == 0:
            m = tsa.heightClasses[0][0]
            self.addState(m)
            root = self.Q[len(self.Q) - 1]
            
            self.theta[m.equivClass] = {}
            self.theta[m.equivClass][m.index] = root
            
            self.thetaInv[root.index] = [m]
            
            # For the fisrt layer (The root) the node is mapped to its self
            self.psiInv[(root.index,)] = m
            
            alphabet_it = chain.from_iterable(combinations(tsa.atomicProps, r) for r in range(len(tsa.atomicProps)+1))
            
            for s in alphabet_it:
                coord: tuple[int, tuple[int, ...], tuple[str, ...]] = (root.index, tuple(), s) 
                
                self.delta[coord] = root
                
        else:
            assert parentCA != None

            for m in tsa.heightClasses[layer - 1]:
                if not m.equivClass in self.theta:
                    self.theta[m.equivClass] = {}
                    m._CAvisited = True
                    
                    for idx in m.children:
                        self.addState(tsa.nodes[idx])
                        self.theta[m.equivClass][idx] = self.Q[len(self.Q) - 1]
                    
                    self.assignTheta(m, self.theta[m.equivClass], [])
                
            for q in self.Q:
                self.thetaInv[q.index] = []
                
            for thetaEq in self.theta.values():
                for key in thetaEq:
                    q = thetaEq[key]
                    m = self.tsa.nodes[key]
                    
                    self.thetaInv[q.index].append(m)

            for p in parentCA.psiInv:
                for q in self.Q:
                    intersectionElement: TSANode | None = None
                    
                    for m in self.thetaInv[q.index]:
                        if m.index in parentCA.psiInv[p].children:
                            intersectionElement = m
                            # print("int:", intersectionElement)

                    if intersectionElement != None:
                        self.psiInv[p + (q.index, )] = intersectionElement
                        
                        alphabet_it = chain.from_iterable(combinations(tsa.atomicProps, r) for r in range(len(tsa.atomicProps)+1))
                
                        for s in alphabet_it:
                            m = intersectionElement.computeTransition(set(s))
                            assert m != None
                            assert m.parent != None
                            
                            self.delta[(q.index, p, s)] = self.theta[m.parent.equivClass][m.index]
        # print("Psi")
        # for k in self.psiInv:
        #     print(f"{k}: {self.psiInv[k]}")                 
        # print("Delta:")
        # for key in self.delta:
        #     print(f"({key[1]}, {key[0]}), {key[2]} => {self.delta[key].index}")
    
        # print("ThetaInv:")
        # for key in self.thetaInv:
        #     print(f"{self.Q[key].index} =>", end="")
            
        #     for m in self.thetaInv[key]:
        #         print(m.states, end="")
            
        #     print()
            
        for q in self.Q:
            q.totalIndex = q.index + self.stateSum
            
        self.stateSum += len(self.Q)
        
    
    def assignTheta(self, m: TSANode, theta_i: dict[int, CascadeState], word: list[set[str]]) -> None:
        for t in m.trans:
            if not t.target._CAvisited:
                t.target._CAvisited = True
                
                newWord: list[set[str]] = word.copy()
                newWord.append(t.ap)
                
                for c in t.target.children:
                    r = self.tsa.nodes[c]
                    
                    equivalenceWord = self.computeWordTo(t.target, m, [False for _ in range(len(self.tsa.nodes))], [])
                    assert equivalenceWord != None
                    
                    representative = r.computeWord(r, equivalenceWord)
                    
                    theta_i[c] = theta_i[representative.index]
                
                self.assignTheta(t.target, theta_i, newWord)
    
    def computeWordTo(self, start: TSANode, end: TSANode, visited: list[bool], word: list[set[str]]) -> list[set[str]] | None:
        if start == end:
            return word
        
        visited[start.index] = True
        
        # print(start.states, start.trans)
        for t in start.trans:
            newWord = word.copy()
            newWord.append(t.ap)
            
            if not visited[t.target.index]:
                res = self.computeWordTo(t.target, end, visited, newWord)
                
                if res != None:
                    return res       

    def addState(self, tsaNode: TSANode) -> None:
        self.Q.append(CascadeState(len(self.Q), tsaNode))           
                     
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

    def configToStr(self, config: tuple[int, ...], layerCa: "CascadeAutomaton | None") -> str:
        if layerCa == None: return ""
        else:
            return self.configToStr(config[:-1], layerCa.parentCA) + "," + chr(ord("A") + layerCa.Q[config[len(config) - 1]].totalIndex)
                                
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
    
    def toDotSubgraph(self) -> str:
        S: str = ""
        S += "{"
        for q in self.Q:
            letter = chr(ord("A") + q.totalIndex)
            
            S += f"\n\t{q.totalIndex} [label=\"{letter} {q.tsaNode.states}\"]"
            
        for k in self.delta.keys():
            S += f"\n\t{self.Q[k[0]].totalIndex} -> {self.delta[k].totalIndex} [label=\"[{self.configToStr(k[1], self.parentCA)}] {self.propIntToStr(set(k[2]))}\"];"
    
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
        self.tsa.visualize(True, "TSA_in_CD", "imgs/trn/")
        self.dfaStatesNumber = dfa.statesNumber
        self.dfaAcceptingStates = dfa.acceptingStates
        self.dfaInitState = dfa.initState

        self.CAs: list[CascadeAutomaton] = [CascadeAutomaton(0, None, self.tsa)]
        for layer in range(1, self.tsa.height):
            print("layer:", layer)
            newCA = CascadeAutomaton(layer, self.CAs[layer - 1], self.tsa)
            self.CAs.append(newCA)
            
        self.stateToCa: dict[int, CascadeAutomaton] = {}
        for CA in self.CAs:
            for q in CA.Q:
                self.stateToCa[q.index] = CA
    
        self.phi: dict[tuple[int, ...], TSANode] = self.computePhi()
        print("PHI:")
        for c in self.phi:
            print(f"{c}: {self.phi[c]}")
            
        self.visualizeWithTsa("withTSA", "imgs/trn/")
        # self.phiInv = self.computePhiInv()
            
    def synthetizeFormula(self) -> Formula:
        res: Formula | None = None
        
        for state in self.dfaAcceptingStates:
            f: Formula = self.automatonStateFormula(state)
            
            if res == None:
                res = f
            else:
                res = Or(res, f)
                
        assert res != None
        
        return res

    def automatonStateFormula(self, s: State) -> Formula:
        res: Formula | None = None
        
        for config in self.phiInv[s.index]:
            f: Formula = self.configurationFormula(config)

            if res == None:
                res = f
            else:
                res = Or(res, f)
                
        # print("State:", s.index, ", f:", res)

        assert res != None
        
        return res
    
    def configurationFormula(self, config: tuple[int, ...]) -> Formula:
        res: Formula | None = None
        
        for q in list(config):
            f: Formula = self.CAStateFormula(q)

            if res == None:
                res = f
            else:
                res = And(res, f)
        
        assert res != None, print("Configuration is empty!")
        
        return res
        
    def CAStateFormula(self, q: int) -> Formula:
        # The first state is always the trivial one-state automaton
        CA = self.stateToCa[q]
        
        ins = CA.computeStateIns(q)
        outs = CA.computeStateOuts(q)
        
        inFromula: Formula | None = None
        
        for c in ins:
            f: Formula
            if q == 0:
                f = self.propIntToFormula(c[1])
            else:
                f = And(self.propIntToFormula(c[1]), Before(self.configurationFormula(c[0])))
                
            if inFromula == None:
                inFromula = f
            else:
                inFromula = Or(inFromula, f)  
                 
        outFromula: Formula | None = None
        
        for c in outs:
            f: Formula
            if q == 0:
                f = self.propIntToFormula(c[1])
            else:
                f = And(self.propIntToFormula(c[1]), Before(self.configurationFormula(c[0])))
                
            if outFromula == None:
                outFromula = f
            else:
                outFromula = Or(outFromula, f)    
        
        if inFromula == None:
            inFromula = PltlFalse()
            
        assert outFromula != None     
        
        # print("q:", q, ", f:", Since(Not(outFromula), inFromula))

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
        
    #     name: str = ""
    #     for s in self.tsa.atomicProps:
    #         f: str
    #         if s in propInt:
    #             f = s
    #         else:
    #             f = f""
            
    #         if name == "None":
    #             name = f
    #         else:
    #             name = f"{name}{f}"
                
    #     if name == "":
    #         name = "empt"
        
    #     return PltlAtomic(name)

    def computePhiInv(self) -> list[list[tuple[int, ...]]]:
        phiInv: list[list[tuple[int, ...]]] = [[] for _ in range(self.dfaStatesNumber)]
        
        lastCa = self.CAs[len(self.CAs) - 1]
        for config in lastCa.psiInv.keys():
            for q in self.tsa.nodes[lastCa.psiInv[config]].states:
                phiInv[q].append(config)
        
        return phiInv
    
    def computePhi(self) -> dict[tuple[int, ...], TSANode]:
        phi: dict[tuple[int, ...], TSANode] = {}
        configs = self.computeConfigurations(0, [()])
        print("conf:", configs)
        for config in configs:
            if config in self.CAs[len(config) - 1].psiInv:
                phi[config] = self.CAs[len(config) - 1].psiInv[config]
                
        return phi
    
    def isomorphicAutomaton(self) -> FiniteAutomaton:
        fa = FiniteAutomaton(len(self.phi), self.tsa.atomicProps)
        print("PHI:", self.phi)
        alphabet_it = chain.from_iterable(combinations(fa.atomicProps, r) for r in range(len(fa.atomicProps)+1))
        
        for s in alphabet_it:
            for config in self.phi:
                start = list(self.phi[config].states)[0]
                targetConfig = self.computeConfigurationTransition(0, config, (), s)
                if targetConfig != None:
                    target = list(self.phi[targetConfig].states)[0]
                    
                    alreadyExists = False
                    for t in fa.states[start].transitions:
                        if t.target == fa.states[target] and t.ap == set(s):
                            alreadyExists = True
                            break
                        
                    if not alreadyExists:
                        fa.addTransition(fa.states[start],  fa.states[target], set(s))
        
        for accState in self.dfaAcceptingStates:
            fa.acceptingStates.append(fa.states[accState.index])
            
        fa.initState = fa.states[self.dfaInitState.index]
        
        return fa
        return fa.minimize()
    
    def computeConfigurations(self, layer: int, config: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
        newConfig = []
        for i in range(len(config)):
            for state in self.CAs[layer].Q:
                newConfig.append(config[i] + (state.index, ))
        
        if layer == len(self.CAs) - 1:
            return newConfig
        else:
            return self.computeConfigurations(layer + 1, newConfig)
        
    def computeConfigurationTransition(self, layer: int, config: tuple[int, ...], prevTarget: tuple[int, ...], s: tuple[str, ...]) -> tuple[int, ...] | None:
        if (config[layer], prevTarget, s) in self.CAs[layer].delta:
            target: tuple[int, ...] = prevTarget + (self.CAs[layer].delta[(config[layer], prevTarget, s)].index, )
        else:
            return None
        
        if layer == len(self.CAs) - 1:
            return target
        else:
            return self.computeConfigurationTransition(layer + 1, config, target, s)

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
            S += "\n\t" + CA.toDotSubgraph()
        S += "\n}"
        
        return S
    
    def visualizeWithTsa(self, imageName = "Unnamed", imagePath = "img/", format = "svg"):
        offset = self.CAs[len(self.CAs) - 1].stateSum 
        offset = offset * offset
        
        S: str = "digraph CD "
        S += """{
    rankdir = TD;
    center = true;
    edge [fontname = Courier];
    node [height = .3, width = .3];
    node [shape = square];
    ranksep = 2;"""
        S += """\nsubgraph CD{"""
        S += "rankdir = RL;"
        for CA in reversed(self.CAs):
            S += "\n\t" + CA.toDotSubgraph()
            
            # S += "\n\t{rank = same;"
            # for q in CA.Q:
            #     S += f" {q.totalIndex};"
            # S += "};"
            
            for q in CA.thetaInv:
                for m in CA.thetaInv[q]:
                    S += f"\n\t {m.index + offset} -> {CA.Q[q].totalIndex} [color=\"blue\"]"
                    
        
                    
        S += "\n}"
        
        
        S += "\nsubgraph TSA{"
        for n in self.tsa.nodes:
            S += f"\n\t{n.index + offset} [label=\"{n.states} {n.equivClass}\", color=\"green\"]"
            # S += f"\n\t{n.index + offset} [label=\"{n.states}\", color=\"green\" ]"
            
            for t in n.trans:
                S += f"\n\t{n.index + offset} -> {t.target.index + offset} [label=\"{t.ap}\"];"
    
        for idx in range(1, len(self.tsa.nodes)):
            n = self.tsa.nodes[idx]
            assert n.parent != None
            S += f"\n\t{n.parent.index + offset} -> {idx + offset} [dir=none, color=\"red\"]"
        
        # for heightClass in self.tsa.heightClasses:
        #     if len(heightClass) == 0: continue
        #     S += "\n\t{rank = same;"
        #     for v in heightClass:
        #         S += f" {v.index + offset};"
        #     S += "};"
        
        S += "}"
        
        for i in range(len(self.CAs)):
            S += "\n\t{rank = same;"
            for v in self.tsa.heightClasses[i]:
                S += f" {v.index + offset};"

            for q in self.CAs[i].Q:
                S += f" {q.totalIndex};"

            S += "};"
            
        S += "}"
        
        from graphviz import Source
        
        src = Source(S)
        src.render(imagePath + imageName, format = format, view = False)
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/", format = "svg") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        src.render(imagePath + imageName, format = format, view = False)