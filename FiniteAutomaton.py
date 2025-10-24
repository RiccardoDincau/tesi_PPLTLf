from itertools import combinations, chain
from pylogics.parsers import parse_pl
from pylogics.semantics.pl import evaluate_pl

class Transition:
    def __init__(self, startState: int, endState: int, label: str):
        self.s: int = startState
        self.e: int = endState
        self.label: str = label
        self.formula = parse_pl(self.label)
        
    def evaluate(self, at_props: set[str]) -> bool:
        return evaluate_pl(self.formula, at_props)
        
    def __str__(self) -> str:
        return str(self.s) + " -> " + str(self.e) + " ( " + self.label + " )"   
        
class FiniteAutomaton:
    def __init__(self, statesNumber: int = 0, initState: int = 0, acceptingStates: list[int] = [], atomicProps: set[str] = set(), formulaStr: str = ""):
        """The automaton can either be created by passing the number of states, the 
        initial state, the accepting states and the atomic propsitions of the formula 
        or by passing a string representing an LTLf formula"""
        
        if formulaStr != "":
            from parse import parse, Result
            from ltlf2dfa.parser.ltlf import LTLfParser
            import re
            
            parser = LTLfParser()
            formula = parser(formulaStr)
            
            self.atomicProps: set[str] = set(re.findall('[a-z]+', formulaStr))

            dotsFormat = formula.to_dfa(False)
            
            strLines = dotsFormat.splitlines()
            
            firstLineT = parse("digraph {name} {", strLines[0])
            
            name = firstLineT["name"]
    
            acceptingLine = strLines[6].split(";")
            acceptingLine = acceptingLine[1:len(acceptingLine) - 1]
            
            acceptingStates = []
            for n in acceptingLine:
                acceptingStates.append(int(n))
                
            initLine = strLines[9].split("->")
            initState = int(initLine[1].removesuffix(";"))
            
            strLines = strLines[10:len(strLines) - 1]
            
            transitions = []
            statesNumber = 0
            
            for line in strLines:
                T = parse(" {start} -> {end} [label=\"{label}\"];", line)
                
                transitions.append(Transition(int(T["start"]), int(T["end"]), T["label"]))
                statesNumber = max(statesNumber, int(T["start"]), int(T["end"]))
                
            statesNumber += 1
            
            self.statesNumber = statesNumber
            self.initState = initState
            self.acceptingStates = acceptingStates
            self.transitions: list[list[Transition]] = [[] for _ in range(self.statesNumber)]
            
            for t in transitions:
                self.addTransition(t)
                
        else:
            self.statesNumber: int = statesNumber
            self.initState: int = initState
            self.acceptingStates: list[int] = acceptingStates
            self.transitions: list[list[Transition]] = [[] for _ in range(self.statesNumber)]
            self.atomicProps = atomicProps
        
    def addTransition(self, newTransition: Transition):
        """Add a new transition"""
        
        self.transitions[newTransition.s].append(newTransition)
        
    def reverseTransitions(self, reduce: bool = False) -> "FiniteAutomaton":
        """Returns the NFA obtained from reversing all the transitions"""
        
        nfa = FiniteAutomaton(self.statesNumber + 1, self.statesNumber, [self.initState], self.atomicProps) 
        
        for state in range(self.statesNumber - 1):
            for t in self.transitions[state + 1]:
                reversedTransition = Transition(t.e, t.s, t.label)
                nfa.addTransition(reversedTransition)
        
        # Add a new state that serves as the initial state
        # Add a transition from this new state to each old accepting state
        for state in self.acceptingStates:
            nfa.addTransition(Transition(nfa.statesNumber - 1, state, "true"))
            
        if reduce:
            return nfa.reduce()
            
        return nfa
    
    def statesPowersetIterator(self):
        """Returns an iterator that cylces over the ordered powerset of the states"""
        
        s = list(range(1, self.statesNumber))
        return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))
    
    def determinize(self, reduce: bool = False) -> "FiniteAutomaton":
        """Compute the determinized DFA of an NFA"""
        
        # The new DFA has 2^n states
        newStatesNumber = pow(2, self.statesNumber - 1)
        
        newInitState = 0
        
        newAcceptingStates: list[int] = []
        
        # For each subset of the states save its index in the ordered powerset
        # The index is used as the id of the subset in the new automaton
        powerStateIndex = {}
        statesPowersetIter = self.statesPowersetIterator()
        for i in range(newStatesNumber):
            currNewState = next(statesPowersetIter)
            powerStateIndex[str(currNewState)] = i

        newTransitions: list[list[Transition]] = [[] for _ in range(newStatesNumber)]

        # Compute the new transitions, every new state (a subset 
        # of the old states) is associated with its index i.
        # i is the index of the subset in the sorted powerset
        statesPowersetIter = self.statesPowersetIterator()
        for i in range(newStatesNumber):
            currNewState = next(statesPowersetIter)
            
            # The subset of the old states containg only the initial old state 
            # is the new initial state
            if (len(currNewState) == 1 and currNewState[0] == self.initState):
                newInitState = i
                
            newStateTransitions: list[tuple[str, set[int]]] = []
            
            for state in currNewState:
                for t in self.transitions[state]:
                    # For each state in the current new state compute the union of
                    # the arriving states of all the transitions with the same label 
                    foundLabel = False
                    for newT in newStateTransitions:
                        if newT[0] == t.label:
                            newT[1].add(t.e)
                            foundLabel = True

                    if not foundLabel:
                        newStateTransitions.append((t.label, {t.e})) 
                
                # If there is an intersection beetween the old accepting state
                # and the new current state i add i to the new accepting states
                for oldAcceptingState in self.acceptingStates:
                    if oldAcceptingState == state:
                        newAcceptingStates.append(i)
                        break
                    
            for t in newStateTransitions:
                L = list(t[1])
                L.sort()
                newTransitions[i].append(Transition(i, powerStateIndex[str(tuple(L))], t[0]))
                
        dfa = FiniteAutomaton(newStatesNumber, newInitState, newAcceptingStates, self.atomicProps)
        dfa.transitions = newTransitions
        
        # dfa.completeTransitions()
        
        if reduce:
            return dfa.reduce()

        return dfa
    
    def reduce(self) -> "FiniteAutomaton":
        """Remove all the states that cannot be visited"""
        
        newStateId: list[int] = [-1 for _ in range(self.statesNumber)]
        newTransitions: list[list[Transition]] = [[]]
        newAcceptingStates: list[int] = []
        
        nVisited = self.visitAutomaton(self.initState, 1, newStateId, newTransitions, newAcceptingStates)

        newAutomaton = FiniteAutomaton(nVisited + 1, 1, newAcceptingStates, self.atomicProps)
        newAutomaton.transitions = newTransitions        
        
        return newAutomaton
    
    def visitAutomaton(self, i: int, count: int, newStateId: list[int], newTransitions: list[list[Transition]], newAcceptingStates: list[int]) -> int:
        """Search the automaton with a DFS"""
        
        newStateId[i] = count
        newTransitions.append([])
        
        for state in self.acceptingStates:
            if state == i:
                newAcceptingStates.append(newStateId[i])
                break
            
        nVisited = 1
        
        for t in self.transitions[i]:
            vic = t.e
            
            if (newStateId[vic] < 0):
                newlyVisited = self.visitAutomaton(vic, count + 1, newStateId, newTransitions, newAcceptingStates)
                count += newlyVisited
                nVisited += newlyVisited
                
            start = newStateId[i]
            end = newStateId[vic]
            
            newTransitions[start].append(Transition(start, end, t.label))
        
        return nVisited
    
    def computeSetTransition(self, statesSet: set[int], prop_int: list[str]) -> set[int]:
        S: set[int] = set()
        
        for q in statesSet:
            for t in self.transitions[q]:
                if t.evaluate(set(prop_int)):
                    S.add(t.e)
        
        return S

    def completeTransitions(self) -> None:
        sinkStateIdx = self.statesNumber
        self.statesNumber += 1
        self.transitions.append([Transition(sinkStateIdx, sinkStateIdx, "true")])
        
        for i in range(self.statesNumber):
            T: list[Transition] = self.transitions[i]
            
            if len(T) == 0:
                self.addTransition(Transition(i, i, "true"))
                continue
            else:
                formula = ""
                trueFound = False
                for t in T:
                    if t.label == "true":
                        trueFound = True
                        break
                    
                    formula += f"(~({t.label})) && "
                formula += "true"
                
                if trueFound:
                    continue

                self.addTransition(Transition(i, sinkStateIdx, formula))

    def __str__(self) -> str:
        S: str = f"""Numero di stati: {self.statesNumber}
Stato iniziale: {self.initState}
Stati accettanti: """
        for state in self.acceptingStates:
            S += str(state) + " "
            
        S += "\nTransizioni: \n"
        for state in range(self.statesNumber - 1):
            for transition in self.transitions[state + 1]:
                S += str(transition) + "\n"
        return S
    
    def toDot(self) -> str:
        """Return the dots format of the automaton."""
        S: str = "digraph FA "
        S += """{
    rankdir = LR;
    center = true;
    size = "7.5,10.5";
    edge [fontname = Courier];
    node [height = .5, width = .5];
    node [shape = doublecircle];"""
        for state in self.acceptingStates:
            S += str(state) + ";"
        S += "\n\tnode [shape = circle];" + str(self.initState) + ";"
        S += "\n\tinit [shape = plaintext, label = \"\"];\n\tinit -> " + str(self.initState) + ";\n"
        
        for state in range(self.statesNumber - 1):
            for transition in self.transitions[state + 1]: 
                S += f"\t{transition.s} -> {transition.e} [label=\"{transition.label}\"];\n"
        
        S += "}"
        return S
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/") -> None:
        """Save a SVG image of the graph using graphiz"""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        src.render(imagePath + imageName, format = "svg", view = False)