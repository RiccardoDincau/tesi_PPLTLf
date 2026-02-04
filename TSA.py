from FiniteAutomaton import FiniteAutomaton, State
from itertools import combinations, chain

class TSATransition:
    def __init__(self, target: "TSANode", propAt: set[str]) -> None:
        self.target = target
        self.ap = propAt
        
    def evaluate(self, atProps: set[str]) -> bool:
        """Return True if atProps satisfies the transition formula, False otherwise."""
        
        return self.ap == atProps
        
    def __str__(self) -> str:
        return f"{self.ap} -> {self.target.index}"   
    
class TSANode:
    """Contains nodes used in TSA. It has a parenthood 
    function, a transition function and a map to
    subsets of states of the FA."""
    
    def __init__(self, index: int, states: set[int]) -> None:
        self.index = index
        
        self.parent: TSANode | None = None # if < 0, then it is the root
        self.children: set[int] = set()
        
        self.trans: list[TSATransition] = []
        self.states: set[int] = states #Subset of states of the FA
        
        self.equivClass = -1
        self.tarjanIdx = -1
        self.height = -1
        
        self._CAvisited = False
        
    def addParent(self, newParent: "TSANode"):
        if self.parent != None:
            self.parent.children.remove(self.index)
            
        self.parent = newParent
        newParent.children.add(self.index)
        
    def addTransition(self, target: "TSANode", prop_int: set[str]):
        for t in self.trans:
            if t.ap == prop_int:
                self.trans.remove(t)
                break
            
        self.trans.append(TSATransition(target, prop_int))
        
    def computeTransition(self, atProp: set[str]) -> "TSANode":
        res = None
        for t in self.trans:
            if t.evaluate(atProp):
                res = t.target
                break
            
        assert res != None 
        
        return res
    
    # Parameter m might be redundant
    def computeWord(self, m: "TSANode", word: list[set[str]]) -> "TSANode":
        if len(word) == 0:
            return m
        
        next = m.computeTransition(word[0])
        assert next != None
        
        return self.computeWord(next, word[1:])
    
    def __str__(self) -> str:
        S = f"{self.index}|{self.states}) pi: {self.parent.index if self.parent != None else 'None'}, phi: {self.states}, h: {self.height}, delta: ["
        for t in self.trans:
            S += str(t) + ", "           
        
        return S + " ]"
        
class TSA:
    """Tree Subset Automaton"""
    
    def __init__(self, DFA: FiniteAutomaton) -> None:
        """Generates a TSA starting from a determinized automaton."""
        
        self.nodes: list[TSANode] = []
        self.height = -1
        self.heightClasses: list[list[TSANode]] = []
        self.atomicProps: set[str] = DFA.atomicProps
        self.dfaAcceptingstates = DFA.acceptingStates
        self.dfaInitstate = DFA.initState
        
        self.fromDfa(DFA)
        
        self.computeHeight()

        self.balance()
        
        newHeights: list[list[TSANode]] = []
        for i in range(self.height):
            oldHeight = self.height - i - 1
            newHeights.append(self.heightClasses[oldHeight])
            
            for m in newHeights[i]:
                m.height = i
                
        self.heightClasses = newHeights
        
        self.liftTransitions()
                
    def fromDfa(self, DFA: FiniteAutomaton) -> None:
        """Build the corrseponding TSA of the given DFA."""
        
        root = self.addNewNode(set(range(DFA.statesNumber)))
        
        L: list[TSANode] = [root]
        
        while len(L) > 0:
            alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps)+1))
            m = L[0]
            
            for s in alphabet_it: 
                rSet = set()
                for stateIdx in m.states:
                    rSet.add(DFA.states[stateIdx])
                    
                F: set[int] = DFA.computeSetTransition(rSet, list(s))
                
                m_1: TSANode | None = None
                
                if m.parent == None:
                    for node in self.nodes:
                        if node.states == F:
                            m_1 = node
                            break    
                
                    if m_1 == None:
                        m_1 = self.addNewNode(F)
                        m_1.addParent(m)
                        
                        L.append(m_1)
                else:
                    parentTarget = m.parent.computeTransition(set(s))
                    
                    for node in self.nodes:
                        ancestors = self.getAncestors(node)
                        
                        if node.states == F and parentTarget in ancestors:
                            m_1 = node
                            break  
                        
                    if m_1 == None:
                        m_1 = self.addNewNode(F)
                        
                        L.append(m_1)
                        
                        r = self.deepestDescendentContainingSubset(m.parent.computeTransition(set(s)), F)
                        
                        for idx in r.children.copy():
                            r_1 = self.nodes[idx]
                            if r_1.states.issubset(F):
                                r_1.addParent(m_1)
                        
                        m_1.addParent(r)
                        
                m.addTransition(m_1, set(s))
                    
            L.remove(m)
            
        self.addSingleton(root, DFA)
        
    def addSingleton(self, r: TSANode, dfa: FiniteAutomaton):
        if len(r.states) == 1:
            return
        
        childrenStates: set[int] = set()
        for child in r.children:
            childrenStates = childrenStates.union(self.nodes[child].states)


        L: list[TSANode] = []
        
        for q in r.states.difference(childrenStates):
            m: TSANode = self.addNewNode({q})
            m.addParent(r)
            L.append(m)
        

        while len(L) > 0:
            m = L.pop()
            assert m.parent != None
                        
            alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps)+1))
            for s in alphabet_it: 
                rSet = set()
                for stateIdx in m.states:
                    rSet.add(dfa.states[stateIdx])
                    
                F: set[int] = dfa.computeSetTransition(rSet, list(s))
                
                m_1: TSANode | None = None
                
                parentTarget = m.parent.computeTransition(set(s))
                    
                for node in self.nodes:
                    ancestors = self.getAncestors(node)
                    
                    if node.states == F and parentTarget in ancestors:
                        m_1 = node
                        break  
                        
                if m_1 == None:
                    m_1 = self.addNewNode(F)
                    
                    n = self.deepestDescendentContainingSubset(m.parent.computeTransition(set(s)), F)
                    
                    for idx in n.children.copy():
                        r_1 = self.nodes[idx]
                        if r_1.states.issubset(F):
                            r_1.addParent(m_1)
                    
                    m_1.addParent(n)
                    
                    L.append(m_1)
                        
                m.addTransition(m_1, set(s))
                    
        for childIdx in r.children:
            self.addSingleton(self.nodes[childIdx], dfa)

    def computeHeight(self) -> None:
        """Computes the height for each node in the TSA."""
        
        self.S: list[TSANode] = []
        self.tarjanIdx = 0
        self.inStack: list[bool] = [False] * len(self.nodes)
        
        for v in self.nodes:
            if (v.tarjanIdx < 0):
                self.tarjanEquiv(v) 
 
        visited: list[bool] = [False for _ in range(len(self.nodes))]
        
        self.heightClasses.append([])
        for m in self.nodes:
            if len(m.states) == 1:
                self.heightClasses[0].append(m)
                visited[m.index] = True
                m.height = 0
                
        self.height = 1
        
        while not (len(self.heightClasses[self.height - 1]) == 1 and self.heightClasses[self.height - 1][0] == self.nodes[0]):
            self.heightClasses.append([])
            
            for n in self.nodes:
                if not visited[n.index]:
                    self.heightClasses[self.height].append(n)
                    
            updated = True
            while updated:
                updated = False
                
                for m in self.heightClasses[self.height]:
                    for m_1 in self.nodes:
                        canReach = False

                        for t in m.trans:
                            if t.target == m_1:
                                canReach = True
                                break
                            
                        if not visited[m_1.index] and m.equivClass != m_1.equivClass and (m_1.parent == m or canReach):
                            self.heightClasses[self.height].remove(m)
                            updated = True
                            break
                        
                    if updated: break
        
            for m in self.heightClasses[self.height]:
                visited[m.index] = True
                m.height = self.height

            self.height += 1
                        
        # self.computeHeightRec(self.nodes[0])
        # self.height = self.nodes[0].height
        
        # for i in range(self.height + 1):
        #     self.heightClasses.append([])
            
        # for m in self.nodes:
        #     self.heightClasses[m.height].append(m)
            
    def computeHeightRec(self, v: TSANode) -> None:
        """Helper function for computing the height."""
        v.height = 0

        if len(v.states) == 1:
            return
        
        maxHeight = 0
        
        for t in v.trans:
            currHeight = 0 
            m = t.target
            if m.height < 0:
                self.computeHeightRec(m)
            
            currHeight = m.height
            
            if m.equivClass != v.equivClass:
                currHeight += 1
                
            maxHeight = max(currHeight, maxHeight)
           
        for idx in v.children:
            currHeight = 0 
            m = self.nodes[idx]
            if m.height < 0:
                self.computeHeightRec(m)
            
            currHeight = m.height + 1
            
            maxHeight = max(currHeight, maxHeight)
            
        v.height = maxHeight
          
    def tarjanEquiv(self, v: TSANode) -> None:
        """Uses Tarjan's algorithm to search the SCC. Each SCC represents an equivalence 
        class of the nodes."""
        
        v.tarjanIdx = self.tarjanIdx
        v.equivClass = self.tarjanIdx
        self.tarjanIdx += 1
        self.S.append(v)
        self.inStack[v.index] = True
        
        for t in v.trans:
            m = t.target
            if m == v:
                continue
            
            if (m.tarjanIdx < 0):
                self.tarjanEquiv(m)
                v.equivClass = min(v.equivClass, m.equivClass)
            elif (self.inStack[m.index]):
                v.equivClass = min(v.equivClass, m.equivClass)
                
        if v.equivClass == v.tarjanIdx:
            w = self.S.pop()
            self.inStack[w.index] = False
            
            while (w.tarjanIdx != v.tarjanIdx):
                w = self.S.pop()
                self.inStack[w.index] = False
            
    def balance(self) -> None:
        """Balances the TSA."""
        
        for i in range(self.height - 1):
            M = self.heightClasses[i]
            
            for r in M:
                p = r.parent
                assert p != None
            
                if p.height != r.height + 1:
                    m = self.addNewNode(r.states)
                    m.addParent(p)
                    m.trans = r.trans.copy()
                    m.height = r.height + 1
                    m.equivClass = r.equivClass
                    self.heightClasses[m.height].append(m)
                    r.addParent(m)
                    
    def liftTransitions(self) -> None:
        """Remove the transition between layers, lifting them to the appropiate level."""
        
        for height in range(self.height):
            M = self.heightClasses[height]
            
            for m in M:
                newTransitions: list[tuple[TSANode, set[str]]] = []
                
                for t in m.trans:
                    m_1 = t.target
                    
                    if m_1.height != m.height:
                        assert m_1.parent != None, print("m:", m.states, ", m_1:", m_1.states)
                        anc = m_1.parent
                        
                        while anc.height > m.height:
                            assert anc.parent != None, print(anc.states)
                            anc = anc.parent

                        newTransitions.append((anc, t.ap))

                for (anc, ap) in newTransitions:
                    m.addTransition(anc, ap)
                    
    def getDescendants(self, m: TSANode) -> set[int]:
        """Returns the inedxes of all the descendants of a node."""
        
        desc: set[int] = set()
        S: list[int] = [m.index]
        
        while len(S) > 0:
            n = S.pop()
            
            if not (n in desc):
                desc.add(n)
                S.extend(self.nodes[n].children)
                
        return desc
    
    def getAncestors(self, m: TSANode) -> set[TSANode]:
        """Returns the inedxes of all the ancestors of a node."""
        
        anc: set[TSANode] = set()
        S: list[TSANode] = [m]
        
        while len(S) > 0:
            n = S.pop()
            
            if not (n in anc):
                anc.add(n)
                parent = n.parent
                
                if parent != None:
                    S.append(parent)
                
        return anc
    
    def deepestDescendentContainingSubset(self, m: TSANode, F: set[int]) -> TSANode:
        deepest = (m, 0)
        
        S = [(m, 0)]
        while len(S) > 0:
            n = S.pop()
            
            for child in n[0].children:
                newDesc = (self.nodes[child], n[1] + 1)
                if (newDesc[0].states.issubset(F)):
                    S.append(newDesc)
                    
                    if newDesc[1] > deepest[1]:
                        deepest = newDesc
                    
        return deepest[0]
        
    def minimalDescendentStateSuperset(self, ancestor: TSANode, subset: set[int]) -> TSANode:
        """Find the minimal node, descendent of 'ancestor', with the smallest states 
        set associated such that it contains 'subset'. (Complexity ???)"""
        
        # phi(m_1) is a superset of 'subset' when r_1 is choosen as by the algorithm
        res: TSANode = ancestor
        
        for idx in self.getDescendants(ancestor):
            m = self.nodes[idx]
                
            if (m.states.issuperset(subset)) and len(m.states) < len(res.states):
                res = m
        
        return res
    
    def isomorphicAutomaton(self) -> FiniteAutomaton:
        fa = FiniteAutomaton(len(self.heightClasses[self.height - 1]), self.atomicProps)
        for m in self.heightClasses[self.height - 1]:
            stateIdx = list(m.states)[0]
            for t in m.trans:
                targetIdx = list(t.target.states)[0]
                
                fa.addTransition(fa.states[stateIdx], fa.states[targetIdx], t.ap)

        for q in self.dfaAcceptingstates:
            fa.acceptingStates.append(fa.states[q.index])

        fa.initState = fa.states[self.dfaInitstate.index]
        # print(fa)
        return fa.minimize()

    def addNewNode(self, states: set[int]) -> TSANode:
        """Creates a new node, appends it to the list of nodes and return the newly created state."""
        newNode = TSANode(len(self.nodes), states)
        self.nodes.append(newNode)
        
        return newNode
    
    def __str__(self) -> str:
        S = ""
        for m in self.nodes:
            S += str(m) + "\n"
        
        return S
    
    def toDot(self, forceHeight = True) -> str:
        """Return the dots format of the automaton."""
        S: str = f"digraph TSA "
        S += """{
    rankdir = TD;
    center = true;
    edge [fontname = Courier];
    node [height = .5, width = .5];
    node [shape = square];"""

        for n in self.nodes:
            S += f"\n\t{n.index} [label=\"{n.states} {n.equivClass} {n.height}\"]"
            # S += f"\n\t{n.index} [label=\"{n.states}\"]"
            
            for t in n.trans:
                S += f"\n\t{n.index} -> {t.target.index} [label=\"{t.ap}\"];"
    
        for idx in range(1, len(self.nodes)):
            n = self.nodes[idx]
            assert n.parent != None
            S += f"\n\t{n.parent.index} -> {idx} [dir=none, color=\"red\"]"
            
        if forceHeight:
            # S += "\n\tsplines=false;"
            for heightClass in self.heightClasses:
                if len(heightClass) == 0: continue
                S += "\n\t{rank = same;"
                for v in heightClass:
                    S += f" {v.index};"
                S += "};"
        from datetime import datetime
        S +=  '\tlabelloc="t"; \n' + '\tlabel ="' + str(datetime.now()) + '";\n'
        
        S += "\n}"
        return S
    
    def visualize(self, forceHeight = True, imageName = "Unnamed", imagePath = "img/", format = "svg") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot(forceHeight))
        src.render(imagePath + imageName, format = format, view = False)