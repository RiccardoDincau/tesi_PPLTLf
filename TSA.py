from FiniteAutomaton import FiniteAutomaton
from itertools import combinations, chain

class ExtendedNode:
    """Contains nodes used in TSA and STT. Has a parenthood 
    function, a transition function and a map to
    subsets of states of the FA."""
    
    def __init__(self, index: int, states: set[int]) -> None:
        self.index = index
        
        self.parent: ExtendedNode | None = None # if < 0, then it is the root
        self.children: set[int] = set()
        
        self.trans: dict[str, int] = {} 
        self.states: set[int] = states #Subset of states of the FA
        
        self.height = -1
        self.tarjanIdx = -1
        
    def addParent(self, newParent: "ExtendedNode"):
        if self.parent != None:
            self.parent.children.remove(self.index)
            
        self.parent = newParent
        newParent.children.add(self.index)
        
    def setTransition(self, target: "ExtendedNode", prop_int: str):
        self.trans[prop_int] = target.index
    
    def __str__(self) -> str:
        S = f"{self.index}) pi: {self.parent.index if self.parent != None else 'None'}, phi: {self.states}, delta: ["
        for k in self.trans.keys():
            S += f" {k} -> {self.trans[k]},"
        return S + " ]"
        
class TSA:
    """Tree Subset Automaton"""
    
    def __init__(self, DFA: FiniteAutomaton) -> None:
        self.nodes: list[ExtendedNode] = []
        self.height = -1
        self.heightClasses: list[list[int]] = []
        
        self.fromDfa(DFA)
        
        self.computeHeight()
        
        # self.balance()
        
        # self.liftTransitions()
        
    def fromDfa(self, DFA: FiniteAutomaton) -> None:
        """Build the corrseponding TSA of the given DFA."""
        
        at_prop: list[str] = ["a", "b"] # !!! GET THE ATOMIC PROPOSITION IN THE FORMULA OF THE DFA
        at_prop: list[str] = ["b"] # !!! GET THE ATOMIC PROPOSITION IN THE FORMULA OF THE DFA
        
        root = ExtendedNode(0, set(range(DFA.statesNumber)))
        
        L: list[ExtendedNode] = [root]
        self.nodes.append(root)
        
        while len(L) > 0:
            alphabet_it = chain.from_iterable(combinations(at_prop, r) for r in range(len(at_prop)+1))
            # alphabet_it = at_prop # !!!!!!!
            r = L[0]
            
            for s in alphabet_it: 
                F: set[int] = DFA.computeSetTransition(r.states, list(s))
                
                r_1: ExtendedNode = ExtendedNode(-1, set())
                
                # Check the case r is the root
                if r.parent == None:
                    r_1 = ExtendedNode(len(self.nodes), F)
    
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
                        r_1 = ExtendedNode(len(self.nodes), F)

                        L.append(r_1)
                        self.nodes.append(r_1)
                        
                        newChildren: list[ExtendedNode]= []
                        for idx in z.children:
                            child = self.nodes[idx]
                            if F.issubset(child.states):
                                newChildren.append(child)
                        
                        for child in newChildren:
                            child.addParent(r_1)    
                                
                        r_1.addParent(z)
                    
                r.setTransition(r_1, str(set(s)))
                    
            L.remove(r)
        
        # Check if added m is looped over !!!
        for m in self.nodes:
            if len(m.states) == 1: continue
            
            childrenStates: set[int] = set()
            for child in m.children:
                childrenStates = childrenStates.union(self.nodes[child].states)

            for q in m.states.difference(childrenStates):
                if (q == 0): continue # !!!!!!!

                r = ExtendedNode(len(self.nodes), {q})
                r.addParent(m)
                
                self.nodes.append(r)
                L.append(r)
                
        while len(L) > 0:
            alphabet_it = chain.from_iterable(combinations(at_prop, r) for r in range(len(at_prop)+1))
            # alphabet_it = at_prop # !!!!!!!
            
            r = L[0]
            m = r.parent
            assert m != None
            
            for s in alphabet_it:
                F: set[int] = DFA.computeSetTransition(r.states, list(s))
                m_1 = self.nodes[m.trans[str(set(s))]]
                
                for r_1 in self.nodes:
                    # print(r_1.states == F, (m_1 in self.getAncestors(r_1)), ", r_1:", r_1.states, )
                    # Condition???
                    if r_1.states == F and (m_1.index in self.getAncestors(r_1)):
                        r.setTransition(r_1, str(set(s)))
                        break
                    
            L.remove(r)

    # Should be modified accoring to the olda paper (1994)       
    def computeHeight(self) -> None:
        self.S = []
        self.tarjanIdx = 0
        self.inStack: list[bool] = [False] * len(self.nodes)
        
        self.tarjanEquiv(self.nodes[0]) 

        for v in self.nodes:
            self.height = max(self.height, v.height)

        for v in self.nodes:
            if v.height >= 0:
                v.height = self.height - v.height
            else:
                v.height = 0
        for _ in range(self.height + 1):
            self.heightClasses.append([])

        for v in self.nodes:
            self.heightClasses[v.height].append(v.index)
    
    def tarjanEquiv(self, v: ExtendedNode) -> None:
        v.tarjanIdx = self.tarjanIdx
        v.height = self.tarjanIdx
        self.tarjanIdx += 1
        self.S.append(v)
        self.inStack[v.index] = True
        
        for k in v.trans.keys():
            m = self.nodes[v.trans[k]]
            
            if (m.tarjanIdx < 0):
                self.tarjanEquiv(m)
                v.height = min(v.height, m.height)
            elif (self.inStack[m.index]):
                v.height = min(v.height, m.height)
                
        if v.height == v.index:
            w = self.S.pop()
            self.inStack[w.index]
            
            while (w.index != v.index):
                w = self.S.pop()
                self.inStack[w.index]
         
    def balance(self) -> None:
        for i in range(self.height):
            M = self.heightClasses[i]
            for rIdx in M:
                r = self.nodes[rIdx]
                p = r.parent
                assert p != None
            
                if p.height != r.height + 1:
                    m = ExtendedNode(len(self.nodes), r.states)
                    m.addParent(p)
                    m.trans = r.trans.copy()
                    m.height = r.height + 1
                    self.heightClasses[m.height].append(m.index)
                    r.addParent(m)
                    self.nodes.append(m)
                    
    def liftTransitions(self) -> None:
        for m in self.nodes:
            for k in m.trans.keys():
                m_1 = self.nodes[m.trans[k]]
                assert m_1.parent != None
                
                if m_1.height != m.height:
                    anc = m_1.parent
                    
                    while anc.height < m.height:
                        assert anc.parent != None
                        anc = anc.parent

                    m.setTransition(anc, k)
        
    def getDescendants(self, m: ExtendedNode) -> set[int]:
        desc: set[int] = set()
        S: list[int] = [m.index]
        
        while len(S) > 0:
            n = S.pop()
            
            if not (n in desc):
                desc.add(n)
                S.extend(self.nodes[n].children)
                
        return desc
    
    def getAncestors(self, m: ExtendedNode) -> set[int]:
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
 
    def minimalDescendentStateSuperset(self, ancestor: ExtendedNode, subset: set[int]) -> ExtendedNode:
        """Find the minimal node, descendent of 'ancestor', with the smallest states 
        set associated such that it contains 'subset'. (Complexity ???)"""
        
        # phi(m_1) is a superset of 'subset' when r_1 is choosen as by the algorithm
        res: ExtendedNode = ancestor
        
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
    size = "7.5,10.5";
    edge [fontname = Courier];
    node [height = .5, width = .5];
    node [shape = square];"""

        for n in self.nodes:
            # S += f"\n\t{n.index} [label=\"{n.states}\"]"
            S += f"\n\t{n.index} [label=\"{n.states}, {n.height}\"]"
            
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
    
    def visualize(self, forceHeight = True) -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot(forceHeight))
        src.render("imgs/" + "TSA", format = "svg", view = False)