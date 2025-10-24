from TSA import TSA, ExtendedNode
from FiniteAutomaton import FiniteAutomaton
from itertools import combinations, chain

class CascadeAutomaton:
    def __init__(self, layer: int, parentCA: "CascadeAutomaton | None", tsa: TSA) -> None:
        """A reset automaton representing a layer of a cascade decomposition"""
        # Theta is the identity function because it is a reset automaton
        
        self.layer = layer
        self.Q: list[int] = [] # Each set represent a group of siblings

        self.psiInv: dict[tuple[int, ...], int] = {}  
        
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
                                # print(f"inv: { self.psiInv[config]}, ts: {tsa.nodes[self.psiInv[config]].trans}")
                                self.delta[coord] = tsa.nodes[inv].trans[key]
                            else:
                                print("!!!! row 55")                            
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
            if tsa != None:
                S += f"\n\t{q} [label=\"{q} {tsa.nodes[q].states}\"]"
            else:
                S += f"\n\t{q}"
            
        for k in self.delta.keys():
            S += f"\n\t{k[0]} -> {self.delta[k]} [label=\"{k[1]}{k[2]}\"];"
    
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

        self.CAs: list[CascadeAutomaton] = [CascadeAutomaton(0, None, self.tsa)]
        self.CAs[0].visualize("ca_0", "imgs/CA/")
        for layer in range(1, self.tsa.height + 1):
            newCA = CascadeAutomaton(layer,self.CAs[layer - 1], self.tsa)
            self.CAs.append(newCA)
            # newCA.visualize(f"ca_{layer}", "imgs/CA/")

    def computeTheta(self):
        """Computes the theta function of the i-th level. Given that
        the automaton is counter-free this is effectevly a function from
        the children of each node to this same nodes."""
        
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
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        src.render(imagePath + imageName, format = "svg", view = False)
  