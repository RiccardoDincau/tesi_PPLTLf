from FiniteAutomaton import FiniteAutomaton
from itertools import combinations, chain

class TSANode:
    """Contains nodes used in TSA. It has a parenthood 
    function, a transition function and a map to
    subsets of states of the FA."""
    
    def __init__(self, index: int, states: set[int]) -> None:
        self.index = index
        
        self.parent: TSANode | None = None # if < 0, then it is the root
        self.children: set[int] = set()
        
        self.trans: dict[str, int] = {} 
        self.states: set[int] = states #Subset of states of the FA
        
        self.equivClass = -1
        self.tarjanIdx = -1
        self.height = -1
        
    def addParent(self, newParent: "TSANode"):
        if self.parent != None:
            self.parent.children.remove(self.index)
            
        self.parent = newParent
        newParent.children.add(self.index)
        
    def setTransition(self, target: "TSANode", prop_int: str):
        self.trans[prop_int] = target.index
    
    def __str__(self) -> str:
        S = f"{self.index}) pi: {self.parent.index if self.parent != None else 'None'}, phi: {self.states}, delta: ["
        for k in self.trans.keys():
            S += f" {k} -> {self.trans[k]},"
        return S + " ]"
        
class TSA:
    """Tree Subset Automaton"""
    
    def __init__(self, DFA: FiniteAutomaton) -> None:
        """Generates a TSA starting from a determinized automaton."""
        
        self.nodes: list[TSANode] = []
        self.height = -1
        self.heightClasses: list[list[int]] = []
        self.atomicProps: set[str] = DFA.atomicProps
        
        self.fromDfa(DFA)
        
        self.computeHeight()

        self.balance()
        
        self.liftTransitions()
        
    def fromDfa(self, DFA: FiniteAutomaton) -> None:
        """Build the corrseponding TSA of the given DFA."""
        
        root = TSANode(0, set(range(DFA.statesNumber)))
        
        L: list[TSANode] = [root]
        self.nodes.append(root)
        
        while len(L) > 0:
            alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps)+1))
            r = L[0]
            
            for s in alphabet_it: 
                rSet = set()
                for stateIdx in r.states:
                    rSet.add(DFA.states[stateIdx])
                F: set[int] = DFA.computeSetTransition(rSet, list(s))
                
                r_1: TSANode = TSANode(-1, set())
                
                # Check the case r is the root
                if r.parent == None:
                    r_1 = TSANode(len(self.nodes), F)
    
                    L.append(r_1)
                    self.nodes.append(r_1)
                    
                    r_1.addParent(r)
                else:
                    m = r.parent
                    m_1 = self.nodes[m.trans[str(set(s))]]
                    
                    for n in self.nodes:
                        # Condition??
                        if n.states == F and (m_1.index in self.getAncestors(n)): # Complexity ???
                            r_1 = n
                            break # Use the first fitting state found
                    
                    # r_1 not found. The root cannot be choosen as r_1 in the previous loop (?)
                    if r_1.parent == None:
                        z = self.minimalDescendentStateSuperset(m_1, F)
                        r_1 = TSANode(len(self.nodes), F)

                        L.append(r_1)
                        self.nodes.append(r_1)
                        
                        newChildren: list[TSANode]= []
                        for idx in z.children:
                            child = self.nodes[idx]
                            if F.issubset(child.states):
                                newChildren.append(child)
                        
                        for child in newChildren:
                            child.addParent(r_1)    
                                
                        r_1.addParent(z)
                    
                r.setTransition(r_1, str(set(s)))
                    
            L.remove(r)
        
        for m in self.nodes:
            if len(m.states) == 1: continue
            
            childrenStates: set[int] = set()
            for child in m.children:
                childrenStates = childrenStates.union(self.nodes[child].states)

            for q in m.states.difference(childrenStates):
                r = TSANode(len(self.nodes), {q})
                r.addParent(m)
                
                self.nodes.append(r)
                L.append(r)
                
        while len(L) > 0:
            alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps)+1))
            
            r = L[0]
            m = r.parent
            assert m != None
            
            for s in alphabet_it:
                rSet = set()
                for stateIdx in r.states:
                    rSet.add(DFA.states[stateIdx])
                F: set[int] = DFA.computeSetTransition(rSet, list(s))
                m_1 = self.nodes[m.trans[str(set(s))]]
                
                for r_1 in self.nodes:
                    # Condition???
                    if r_1.states == F and (m_1.index in self.getAncestors(r_1)):
                        r.setTransition(r_1, str(set(s)))
                        break
                    
            L.remove(r)

    def computeHeight(self) -> None:
        """Computes the height for each node in the TSA."""
        
        self.S: list[TSANode] = []
        self.tarjanIdx = 0
        self.inStack: list[bool] = [False] * len(self.nodes)
        
        for v in self.nodes:
            if (v.tarjanIdx < 0):
                self.tarjanEquiv(v) 

        self.computeHeightRec(self.nodes[0])
        self.height = self.nodes[0].height
        
        for i in range(self.height + 1):
            self.heightClasses.append([])
            
        for m in self.nodes:
            self.heightClasses[m.height].append(m.index)
            
    def computeHeightRec(self, v: TSANode) -> None:
        """Helper function for computing the height."""
        v.height = 0

        if len(v.states) == 1:
            return
        
        maxHeight = 0
        
        for idx in v.trans.values():
            currHeight = 0 
            m = self.nodes[idx]
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
        
        for k in v.trans.keys():
            m = self.nodes[v.trans[k]]
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
        """Balences the TSA."""
        
        for i in range(self.height):
            M = self.heightClasses[i]
            for rIdx in M:
                r = self.nodes[rIdx]
                p = r.parent
                assert p != None
            
                if p.height != r.height + 1:
                    m = TSANode(len(self.nodes), r.states)
                    m.addParent(p)
                    m.trans = r.trans.copy()
                    m.height = r.height + 1
                    self.heightClasses[m.height].append(m.index)
                    r.addParent(m)
                    self.nodes.append(m)
                    
    def liftTransitions(self) -> None:
        """Remove the transition between layers, lifting them to the appropiate level."""
        for m in self.nodes:
            for k in m.trans.keys():
                m_1 = self.nodes[m.trans[k]]
                assert m_1.parent != None
                
                if m_1.height != m.height:
                    anc = m_1.parent
                    
                    while anc.height < m.height:
                        assert anc.parent != None, print(anc.states)
                        anc = anc.parent

                    m.setTransition(anc, k)
        
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
    
    def getAncestors(self, m: TSANode) -> set[int]:
        """Returns the inedxes of all the ancestors of a node."""
        
        desc: set[int] = set()
        S: list[int] = [m.index]
        
        while len(S) > 0:
            n = S.pop()
            
            if not (n in desc):
                desc.add(n)
                p = self.nodes[n].parent
                if p != None:
                    assert p != None
                    S.append(p.index)
                
        return desc
 
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
            S += f"\n\t{n.index} [label=\"{n.states}\"]"
            # S += f"\n\t{n.index} [label=\"{n.states}\"]"
            
            for t in n.trans.keys():
                S += f"\n\t{n.index} -> {n.trans[t]} [label=\"{t}\"];"
    
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
                    S += f" {v};"
                S += "};"
    
        S += "\n}"
        return S
    
    def visualize(self, forceHeight = True, imageName = "Unnamed", imagePath = "img/", format = "svg") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot(forceHeight))
        src.render(imagePath + imageName, format = format, view = False)