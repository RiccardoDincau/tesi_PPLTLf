from TSA import TSA, TSANode
from FiniteAutomaton import FiniteAutomaton, State, Transition
from itertools import combinations, chain

from pylogics.syntax.base import Logic, Not, And, Or
from pylogics.syntax.pltl import Atomic as PltlAtomic, PropositionalTrue as PltlTrue, PropositionalFalse as PltlFalse
from pylogics.syntax.pltl import Formula as PLTLFormula, Before, Since, Once, Historically, WeakSince

class CascadeState:
    """A state of a cascade automaton."""
    
    def __init__(self, index: int, tsaNode: TSANode) -> None:
        # The state index in the cascade automaton
        self.index = index
        
        # A unique index of the state for all the decomposition
        self.totalIndex = -1
        self.tsaNode = tsaNode
        
class CascadeAutomaton:
    def __init__(self, layer: int, parentCA: "CascadeAutomaton | None", tsa: TSA) -> None:
        """A semi-automaton representing a layer of a cascade decomposition."""
        
        self.tsa = tsa
        self.parentCA = parentCA
        self.atomicProps: set[str] = tsa.atomicProps
        
        # Layer number in the cascade decomposition
        self.layer = layer
        
        # Representatives of TSA equivalence classes
        # (aka states of the decomposition)
        self.Q: list[CascadeState] = []


        # Note that the following declarations are restrictions
        # of the corresponding mappings to the current layer

        # Injection from TSA nodes to configuration in the automaton
        self.psi: dict[int, tuple[int, ...]] = {}
        
        # Inverse of psi
        self.psiInv: dict[tuple[int, ...], TSANode] = {}  
        
        # Transition function of the Cascade Automaton s.t.
        #   delta[(q, config, propositionalInterpretation)] => target
        # where q is the index of the starting cascade state, config is 
        # a configuration in the parent layer and propositionalInterpretation is
        # a word of the alphabet
        self.delta: dict[tuple[int, tuple[int, ...], tuple[str, ...]], CascadeState] = {}
        
        # Mapping beetween TSA nodes and their representatives in the 
        # decomposition s.t.
        #   theta[equivalenceClass][tsaNodeIndex] => representative
        # Note that theta is not only restricted to this layer, but
        # is also divided by equivalence class of the parents nodes 
        # in the TSA
        self.theta: dict[int, dict[int, CascadeState]] = {}
        
        # Inverse of theta
        self.thetaInv: dict[int, list[TSANode]] = {}

        # The automaton is computed starting from the
        # corresponding layer in the TSA
        
        if parentCA == None:
            # This is the automaton of the first layer, it is
            # the trvial automaton (Is it????)
            
            m = tsa.heightClasses[0][0]
            self.addState(m)
            root = self.Q[len(self.Q) - 1]
            
            self.theta[m.equivClass] = {}
            self.theta[m.equivClass][m.index] = root
            
            self.thetaInv[root.index] = [m]
            
            self.psi[m.index] = (root.index, )
            self.psiInv[(root.index,)] = m
            
            alphabet_it = chain.from_iterable(combinations(tsa.atomicProps, r) for r in range(len(tsa.atomicProps)+1))
            
            for s in alphabet_it:
                coord: tuple[int, tuple[int, ...], tuple[str, ...]] = (root.index, tuple(), s) 
                
                self.delta[coord] = root
                
        else:
            for m in tsa.heightClasses[layer - 1]:
                if not (m.equivClass in self.theta):
                    self.theta[m.equivClass] = {}
                    m._CAvisited = True
                    
                    # For each equivalence class in the parent layer choose 
                    # a node, then select its children as representatives in 
                    # the current layer and add the corresponding new states in 
                    # the cascade automaton
                    for idx in m.children:
                        newState = self.addState(tsa.nodes[idx])
                        self.theta[m.equivClass][idx] = newState
                    
                    # Assign a representative in the decomposition to 
                    # all the children of the other nodes in the equivalence 
                    # class at the parent layers
                    self.assignTheta(m, m, self.theta[m.equivClass], [])
                
            for q in self.Q:
                self.thetaInv[q.index] = []
                
            # Evaluate the inverse of theta
            for thetaEq in self.theta.values():
                for key in thetaEq:
                    q = thetaEq[key]
                    m = self.tsa.nodes[key]
                    
                    self.thetaInv[q.index].append(m)


            for m in parentCA.psi.keys():
                for child in self.tsa.nodes[m].children:
                    parentNode = self.tsa.nodes[m]
                    
                    if (parentNode.equivClass in self.theta) and (child in self.theta[parentNode.equivClass]):
                        # Compute the current layer psi as the configuration of the parent TSA node
                        # concatenated with the current layer representative of the TSA node (If 
                        # this exists)
                        
                        self.psi[child] = parentCA.psi[m] + (self.theta[parentNode.equivClass][child].index, )
                
            # Evaluate the inverse of psi
            for m in self.psi.keys():
                config = self.psi[m]
                self.psiInv[config] = self.tsa.nodes[m]

            alphabet_it = chain.from_iterable(combinations(tsa.atomicProps, r) for r in range(len(tsa.atomicProps)+1))

            # Add transition in the automaton
            for s in alphabet_it:
                for config in self.psiInv:
                    # Find the corresponding target in the TSA
                    targetNode = self.psiInv[config].computeTransition(set(s))

                    assert targetNode.parent != None, print("Target:", targetNode.states, ", layer:" ,layer,  ", config: ", config, ", psi:", self.psiInv)
                    
                    # If the target node in the TSA exists get its representative
                    targetState = self.theta[targetNode.parent.equivClass][targetNode.index]
                    
                    self.delta[(config[-1:][0], config[:-1], s)] = targetState

        # Compute the total indexes, which are the indexes of the cascade states
        # relative to the entire cascade decomposition
        self.stateSum = parentCA.stateSum if parentCA != None else 0

        for q in self.Q:
            q.totalIndex = q.index + self.stateSum
            
        self.stateSum += len(self.Q)
        
    def assignTheta(self, m: TSANode, reprParent: TSANode, theta_i: dict[int, CascadeState], word: list[set[str]]) -> None:
        """Given a TSA node assigns the representative to each children of the nodes in the
        same equivalence class."""
        
        # Visit the equivalence class in the parent layer
        for t in m.trans:
            if not t.target._CAvisited and t.target.equivClass == reprParent.equivClass:
                t.target._CAvisited = True
                
                newWord: list[set[str]] = word.copy()
                newWord.append(t.ap)
                
                for c in t.target.children:
                    r = self.tsa.nodes[c]
                    
                    # Compute the equivalence word from the target to the parent 
                    # of the representative
                    equivalenceWord = self.tsa.computeWordTo(t.target, reprParent, [False for _ in range(len(self.tsa.nodes))], [])
                    assert equivalenceWord != None
                    
                    # Follow the equivalence word in the current layer
                    # to determine the representative
                    representative = r.computeWord(r, equivalenceWord)
                    
                    theta_i[c] = theta_i[representative.index]
                
                self.assignTheta(t.target, reprParent, theta_i, newWord)

    def addState(self, tsaNode: TSANode) -> CascadeState:
        newState = CascadeState(len(self.Q), tsaNode)
        self.Q.append(newState)           
                     
        return newState
    
    def getResetsLetters(self) -> set[tuple[tuple[int, ...], tuple[str, ...]]]:
        resets: set[tuple[tuple[int, ...], tuple[str, ...]]] = set()
        
        T: dict[tuple[tuple[int, ...], tuple[str, ...]], list[CascadeState]] = {}
        
        for t in self.delta:
            letter = (t[1], t[2])
            if letter in T:
                T[letter].append(self.delta[t])  
            else:
                T[letter] = []         
                T[letter].append(self.delta[t])           
    
        for letter in T:
            isReset = True
            target = T[letter][0]
            
            for t in T[letter]:
                if t != target:
                    isReset = False
                    break
                
            if isReset:
                resets.add(letter)
    
        return resets
    
    def computeStateIns(self, state: int) -> list[tuple[tuple[int, ...], set[str]]]:
        """Returns all the transitions entering the state"""
        
        ins: list[tuple[tuple[int, ...], set[str]]] = [] 
        for k in self.delta.keys():
            if self.delta[k].index == state and ((k[1], k[2]) in self.getResetsLetters())  and not ( (k[1], set(k[2])) in ins):
                ins.append((k[1], set(k[2])))
        return ins
    
    def computeStateOuts(self, state: int) -> list[tuple[tuple[int, ...], set[str]]]:
        """Returns all the transitions exiting the state."""
        
        outs: list[tuple[tuple[int, ...], set[str]]] = [] 
        for k in self.delta.keys():
            if k[0] == state and ((k[1], k[2]) in self.getResetsLetters()) and not ( (k[1], set(k[2])) in outs):
                outs.append((k[1], set(k[2])))    
        return outs

    def propIntToStr(self, propositionalInterpretation: set[str]) -> str:
        """Transforms a propositional interpretation over the alphabet in a string."""
        
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
        """Returns a configuration as a string."""
        
        if layerCa == None: return ""
        else:
            return self.configToStr(config[:-1], layerCa.parentCA) + "," + chr(ord("A") + layerCa.Q[config[len(config) - 1]].totalIndex)
                                
    def toDot(self) -> str:
        """Returns a string in dot format of the automaton."""
        
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
        """Build the cascade decomposition of a FiniteAutomaton"""
        
        self.dfa = dfa
        
        # Holonomy three associated to the automaton
        self.tsa = TSA(dfa)
        self.tsa.visualize(True, "TSA_in_CD", "imgs/trn/")
        
        self.dfaStatesNumber = dfa.statesNumber
        self.dfaAcceptingStates = dfa.acceptingStates
        self.dfaInitState = dfa.initState

        # Layers of the decomposition. Construction the root layer
        self.CAs: list[CascadeAutomaton] = [CascadeAutomaton(0, None, self.tsa)]
        for layer in range(1, self.tsa.height):
            newCA = CascadeAutomaton(layer, self.CAs[layer - 1], self.tsa)
            self.CAs.append(newCA)
            
        # Map of each state (Using total index) to its layer
        self.stateToCa: dict[int, CascadeAutomaton] = {}
        for CA in self.CAs:
            for q in CA.Q:
                self.stateToCa[q.totalIndex] = CA
    
        self.visualizeWithTsa("withTSA", "imgs/trn/")
        
        self.phiInv = self.computePhiInv()
        self.phi: dict[tuple[int, ...], State] = self.computePhi()
            
    def synthetizeFormula(self) -> PLTLFormula:
        """Returns the PLTLf formula associated to the input DFA.
        
        The formula is the conjuction of the 
        formulas associated to the accepting states.
        """
        
        res: PLTLFormula | None = None

        for state in self.dfaAcceptingStates:
            f: PLTLFormula = self.automatonStateFormula(state)
            
            if res == None:
                res = f
            else:
                res = Or(res, f)
                
        assert res != None
        
        return res

    def automatonStateFormula(self, s: State) -> PLTLFormula:
        """Returns the PLTLf formula associated to a state in the DFA.
        
        The formula is built as the conjunction of the formulas for the
        configurations associated to the state.
        """
        res: PLTLFormula | None = None
        
        for config in self.phiInv[s.index]:
            f: PLTLFormula = self.configurationFormula(config)
            
            if res == None:
                res = f
            else:
                res = Or(res, f)
                
        assert res != None
        
        return res
    
    def configurationFormula(self, config: tuple[int, ...]) -> PLTLFormula:
        """Returns the PLTLf formula associated to a configuration.
        
        The formula is built as the disjunction of the formulas 
        associated to each state in the configuration.
        """
        res: PLTLFormula | None = None
        
        
        for i in range(len(config)):
            q = config[i]
            
            f: PLTLFormula = self.CAStateFormula(self.CAs[i].Q[q].totalIndex, q)
            
            if res == None:
                res = f
            else:
                res = And(res, f)
                
        # print("Config:", config, ", formula:", res)
                
        assert res != None, print("Configuration is empty!")
        
        return res
        
    def CAStateFormula(self, totalIndex: int, CAindex: int) -> PLTLFormula:
        """Returns the PLTLf formula associated to a state in the decomposition.
        
        The formula is built as (!outs) S (ins), where ins are the transitions
        entering the state and outs are the ones leaving.
        """
        
        # The first state is always the trivial one-state automaton (?????)
        if totalIndex == 0:
            return PltlTrue()
        
        CA = self.stateToCa[totalIndex]
        
        # Set of transition entering the automaton
        ins = CA.computeStateIns(CAindex)
        
        # Set of transition exiting the automaton
        outs = CA.computeStateOuts(CAindex)
        
        inFromula: PLTLFormula = PltlFalse()
        
        for c in ins:
            f: PLTLFormula
            if totalIndex == 0:
                f = self.propIntToFormula(c[1])
            else:
                # For all the states not in the root layer the letter of a transition consists
                # in a configuration and an interpretation for each proposition, which are 
                # decomposed in the following way
                f = And(self.propIntToFormula(c[1]), self.configurationFormula(c[0]))
                
            inFromula = Or(inFromula, f)  
            
        outFromula: PLTLFormula = PltlFalse()
        
        for c in outs:
            f: PLTLFormula
            if totalIndex == 0:
                f = self.propIntToFormula(c[1])
            else:
                # For all the states not in the root layer the letter of a transition consists
                # in a configuration and an interpretation for each proposition, which are 
                # decomposed in the following way
                f = And(self.propIntToFormula(c[1]), self.configurationFormula(c[0]))
                
            outFromula = Or(outFromula, f)    
        
        if self.dfa.initState.index in CA.Q[CAindex].tsaNode.states:
            return WeakSince(Not(outFromula), inFromula) 
        
        return Since(Not(outFromula), inFromula) 
    
    def propIntToFormula(self, propInt: set[str]) -> PLTLFormula:
        """Converts a propositional interpretation to a PLTLf formula."""
        res: PLTLFormula | None = None
        
        for s in self.tsa.atomicProps:
            f: PLTLFormula
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
        """Computes the mapping from states in the DFA to configuration representing 
        that state.
        
        At each index i in the returned list there is the list of configurations
        for the i-th state in the automaton.
        """
        
        phiInv: list[list[tuple[int, ...]]] = []
        
        # Mapping of the states in the DFA to nodes in the holonomy tree
        statesToNodes: list[set[TSANode]] = []
        
        for _ in range(self.dfaStatesNumber):
            statesToNodes.append(set())
            phiInv.append([])
        
        for node in self.tsa.nodes:
            for q in node.states:
                statesToNodes[q].add(node)

        for q in range(self.dfaStatesNumber):
            for node in statesToNodes[q]:
                for CA in self.CAs:
                    if node.index in CA.psi:
                        if len(CA.psi[node.index]) == len(self.CAs):
                            # For each state in the DFA, first compute the corresponding 
                            # nodes of the holonomy tree, then for each node get 
                            # the corresponding state in the decomposition
                            phiInv[q].append(CA.psi[node.index])

        return phiInv
    
    def computePhi(self) -> dict[tuple[int, ...], State]:
        """Returns the mapping from configurations in the decompositions
        to states in the automaton."""
        phi: dict[tuple[int, ...], State] = {}
        
        for q in range(len(self.phiInv)):
            for config in self.phiInv[q]:
                if len(config) == len(self.CAs):
                    phi[config] = self.dfa.states[q]
        
        return phi
        
    def homomorphicAutomaton(self) -> FiniteAutomaton:
        """Builds the automaton homomorphic to the decomposition.
        
        This construction does not correctly assign the inital 
        and accepting states.
        """
        
        configs = self.computeLastLayerConfigurations(0, [()])
        lastCa = self.CAs[len(self.CAs) - 1]
        
        for config in configs:
            if not (config in lastCa.psiInv.keys()):
                configs.remove(config)
               
        # Initiate the homomorphic automaton
        fa = FiniteAutomaton(len(configs), self.tsa.atomicProps)
        
        # Declaration of the homomorphism function
        phi: dict[tuple[int, ...], State] = {}
        
        # Assignment of each configuration to a state in the
        # newly created automaton
        index = 0
        for config in configs:
            phi[config] = fa.states[index]
            index += 1
        
        # Generation of the transition function in the automaton
        for k in lastCa.delta.keys():
            startConfig: tuple[int, ...] = k[1] + (k[0], )
            
            targetConfig: tuple[int, ...] | None = self.computeConfigurationTransition(len(self.CAs) - 1, startConfig, k[2])

            # If the transition from startConfig with letter k[2] 
            # exists, adda a transition between the corresponding
            # states in the automaton
            if targetConfig != None:
                fa.addTransition(phi[startConfig], phi[targetConfig], set(k[2]))
        
        return fa
    
    def homomorphicAutomatonPhi(self) -> FiniteAutomaton:
        """Builds the automaton homomorphic to the decomposition.
        
        This method directly uses the mapping phi. This also 
        allows to correctly detremine the initial and accepting states.
        """
        
        # Initialization of the homomorphic automaton
        FA = FiniteAutomaton(len(self.phi.keys()), self.dfa.atomicProps)
        
        alphabet_it = chain.from_iterable(combinations(self.dfa.atomicProps, r) for r in range(len(self.dfa.atomicProps)+1))
            
        for s in alphabet_it:
            for config in self.phi.keys():
                targetConfig = self.computeConfigurationTransition(len(config) - 1, config, s)
                
                if targetConfig != None:
                    startState = FA.states[self.phi[config].index]
                    targetState = FA.states[self.phi[targetConfig].index]
                    FA.addTransition(startState, targetState, set(s))
                    
        for accState in self.dfaAcceptingStates:
            FA.acceptingStates.append(FA.states[accState.index])
    
        FA.initState = FA.states[self.dfaInitState.index]
    
        return FA
    
    def computeLastLayerConfigurations(self, layer: int, config: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
        """Returns all the possible configurations, including the empty ones."""
        
        newConfig = []
        for i in range(len(config)):
            for state in self.CAs[layer].Q:
                newConfig.append(config[i] + (state.index, ))
        
        if layer == len(self.CAs) - 1:
            return newConfig
        else:
            return self.computeLastLayerConfigurations(layer + 1, newConfig)
        
    def computeConfigurationTransition(self, layer: int, config: tuple[int, ...], s: tuple[str, ...]) -> tuple[int, ...] | None:
        """Returns the target state of a transition in the configuration tree. If there 
        is no such transition, None is returned instead."""
        
        assert layer < len(self.CAs)
        
        targetConfig: tuple[int, ...] = ()
        
        for i in range(layer + 1):
            # Compute the transition in each layer for the letter
            # given by the i-th subconfiguration of the starting configuration
            # and the given propositional interpretation
            layerTargetState: CascadeState | None = self.CAs[i].delta[(config[i], config[:i], s)]
            
            if (layerTargetState == None): 
                return None
            else:
                # If there is a target for the transition in the current layer
                # add it to the target configuration
                targetConfig += (layerTargetState.index, )

        return targetConfig

    def toDot(self) -> str:
        """Returns a string containing the decomposition in Dot format."""
        
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
            
        from datetime import datetime
        S +=  '\tlabelloc="t"; \n' + '\tlabel ="' + str(datetime.now()) + '";\n'
        
        S += "\n}"
        
        return S
    
    def visualizeWithTsa(self, imageName = "Unnamed", imagePath = "img/", format = "svg"):
        """Saves an image containing the decomposition, the associated TSA
        and the theta function which connects TSA nodes to their representative 
        in the decomposition"""
        
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
            
        from datetime import datetime
        S +=  '\tlabelloc="t"; \n' + '\tlabel ="' + str(datetime.now()) + '";\n'
            
        S += "}"
        
        from graphviz import Source
        
        src = Source(S)
        src.render(imagePath + imageName, format = format, view = False)
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/", format = "svg") -> None:
        """Saves a SVG image of the decomposition."""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        
        src.render(imagePath + imageName, format = format, view = False)