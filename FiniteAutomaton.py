from itertools import combinations, chain
from pylogics.parsers import parse_pl
from pylogics.semantics.pl import evaluate_pl

class Transition:
    def __init__(self, target: "State", atomicPropositions: set[str], isEps: bool = False):
        self.target: State = target
        self.ap: set[str] = atomicPropositions
        self.isEps = isEps
        
    def evaluate(self, atProps: set[str]) -> bool:
        """Return True if atProps satisfies the transition formula, False otherwise."""
        
        return self.ap == atProps
    
    def formulaToStr(self, allProps: set[str]) -> str:
        if self.isEps:
            return "eps"
        
        S = ""
        for p in allProps:
            if len(S) > 0:
                S += " && "
            if p in self.ap:
                S += f"{p}"
            else:
                S += f"~({p})"
        return S
    
    def __str__(self) -> str:
        return f"-> {self.target.index} ({self.ap if not self.isEps else 'eps'})"
        
class State:
    def __init__(self, index: int) -> None:
        self.index: int = index
        self.transitions: list[Transition] = []
        
    def addTransition(self, target: "State", atomicPropositions: set[str], isEps: bool = False) -> None:
        for t in self.transitions:
            if t.target == target and t.ap.issubset(atomicPropositions) and atomicPropositions.issubset(t.ap):
                return
        
        self.transitions.append(Transition(target, atomicPropositions, isEps))
        
    def computeTransition(self, atomicPropositions: set[str]) -> set["State"]:
        """Computes the set of states reachable from this one with the given
        atomic propositions. The result set can contain more than one transition only
        if this is a non deterministic automaton"""
        
        res: set["State"] = set()
        
        for t in self.transitions:
            if t.isEps:
                res = res.union(t.target.computeTransition(atomicPropositions))
            else:
                if t.evaluate(atomicPropositions):
                    res.add(t.target)
            
        return res
    
    def transitionsToDot(self, allProps: set[str]) -> str:
        S = ""
        for t in self.transitions:
            S += f"\t{self.index} -> {t.target.index} [label=\"{t.formulaToStr(allProps)}\"];\n"
        return S
    
    def __str__(self):
        S = f"{self.index}:"
        for t in self.transitions:
            S += f"\t {t}\n"
        return S

class FiniteAutomaton:
    def __init__(self, statesNumber: int = 0, atomicProps: set[str] = set(), formulaStr: str = ""):
        """The automaton can either be created by passing the number of states, 
        and the atomic propsitions of the formula or by passing a string 
        representing an LTLf formula"""
        
        if formulaStr != "":
            from parse import parse
            from ltlf2dfa.parser.ltlf import LTLfParser
            import re
            
            self.atomicProps: set[str] = set(re.findall('[a-z]+', formulaStr))
            if "true" in self.atomicProps: self.atomicProps.remove("true")
            if "false" in self.atomicProps: self.atomicProps.remove("false")
            
            parser = LTLfParser()
            formula = parser(formulaStr)

            dotsFormat = formula.to_dfa(False)
            
            strLines = dotsFormat.splitlines()
            
            firstLineT = parse("digraph {name} {", strLines[0])
            
            self.name = firstLineT["name"]
            
            initLine = strLines[9].split("->")
    
            acceptingLine = strLines[6].split(";")
            acceptingLine = acceptingLine[1:len(acceptingLine) - 1]
            
            strLines = strLines[10:len(strLines) - 1]
            
            self.states: list[State] = [State(i) for i in range(len(strLines))]
            self.statesNumber = len(strLines)
            
            self.acceptingStates: list[State] = []
            for n in acceptingLine:
                self.acceptingStates.append(self.states[int(n) - 1])
                
            self.initState: State = self.states[int(initLine[1].removesuffix(";")) - 1]
            
            
            for line in strLines:
                T = parse(" {start} -> {target} [label=\"{label}\"];", line)

                formula = parse_pl(T["label"])        
                
                alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps) + 1))
            
                for s in alphabet_it:
                    if evaluate_pl(formula, set(s)):
                        self.states[int(T["start"]) - 1].addTransition(self.states[int(T["target"]) - 1], set(s))
            
        else:
            self.statesNumber: int = statesNumber
            self.states: list[State] = [State(i) for i in range(self.statesNumber)]
            self.initState: State = self.states[0]
            self.acceptingStates: list[State] = []
            self.atomicProps = atomicProps
        
    def addTransition(self, start: State, target: State, atomicPropositions: set[str]):
        """Add a new transition"""

        self.states[start.index].addTransition(target, atomicPropositions)
        
    def reverseTransitions(self, reduce: bool = False) -> "FiniteAutomaton":
        """Returns a FA obtained from reversing all the transitions. 
        The FA generated is non deterministic, but has complete transitions."""
        
        nfa = FiniteAutomaton(self.statesNumber + 2, self.atomicProps) 

        for state in self.states:
            for t in state.transitions:
                nfa.states[t.target.index].addTransition(nfa.states[state.index], t.ap)
        
        nfa.acceptingStates = [nfa.states[self.initState.index]]
        
        sinkState = nfa.states[nfa.statesNumber - 1]
        nfa.initState = nfa.states[nfa.statesNumber - 2]
        for state in self.acceptingStates:
            nfa.initState.addTransition(nfa.states[state.index], set(), True)
        
        for state in nfa.states:
            alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps) + 1))

            for s in alphabet_it:
                if len(state.computeTransition(set(s))) == 0:
                    nfa.addTransition(state, sinkState, set(s))
                    
        if reduce:
            return nfa.removeUnreachableStates()
            
        return nfa
    
    def statesPowersetIterator(self):
        """Returns an iterator that cylces over the ordered powerset of the automaton states"""
        
        s = self.states
        return chain.from_iterable(combinations(s, r) for r in range(1, len(s) + 1))
    
    def determinize(self, reduce: bool = False) -> "FiniteAutomaton":
        """Return the determinized automaton of this automaton"""
        
        # The new DFA has 2^n - 1 states (Cardinality of the power set minus the empty set)
        dfa = FiniteAutomaton(pow(2, self.statesNumber) - 1, self.atomicProps)

        # For each subset of the states save its index in the ordered powerset
        # The index is used as the id of the subset in the new automaton
        powerStateIndex = {}
        statesPowersetIter = self.statesPowersetIterator()
        
        for i in range(0, dfa.statesNumber):
            currNewState = next(statesPowersetIter)
            currNewStateIdx = set()
            for m in currNewState:
                currNewStateIdx.add(m.index)
            powerStateIndex[str(currNewStateIdx)] = i
            
        epsClosure = {self.initState.index}
        for t in self.initState.transitions:
            if t.isEps:
                epsClosure.add(t.target.index)
                
        dfa.initState = dfa.states[powerStateIndex[str(epsClosure)]]
            
        # Compute the new transitions, every new state (a subset 
        # of the old states) is associated with its index i.
        # i is the index of the subset in the sorted powerset
        statesPowersetIter = self.statesPowersetIterator()
        for i in range(0, dfa.statesNumber):
            currNewState = next(statesPowersetIter)

            # The subset of the old states containg only the initial old state 
            # is the new initial state
            # if (len(currNewState) == 1 and currNewState[0] == self.initState):
            #     dfa.initState = dfa.states[i]
                    
            alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps) + 1))
            
            for s in alphabet_it:
                targetState: set[State] = set()
                
                currNewStateIdx = set()
                for m in currNewState:
                    currNewStateIdx.add(m.index)
                    
                for state in currNewState:
                    targetState = targetState.union(state.computeTransition(set(s)))

                    # If there is an intersection beetween the old accepting state
                    # and the new current state i add i to the new accepting states
                    for oldAcceptingState in self.acceptingStates:
                        if oldAcceptingState.index == state.index:
                            dfa.acceptingStates.append(dfa.states[powerStateIndex[str(currNewStateIdx)]])
                            break
                
                if len(targetState) > 0:
                    targetStateIdx = set()
                    for m in targetState:
                        targetStateIdx.add(m.index)
                    dfa.states[i].addTransition(dfa.states[powerStateIndex[str(targetStateIdx)]], set(s))

        if reduce:
            return dfa.minimize()

        return dfa
    
    def minimize(self) -> "FiniteAutomaton":
        # print("------")
        # print(self)
        # self.visualize("reduced1", "imgs/trn/")
        reduced = self.removeUnreachableStates()
        # print(reduced)
        # reduced.visualize("reduced", "imgs/trn/")
        
        P: list[set[int]] = [set([s.index for s in reduced.acceptingStates]), set()]
        W: list[set[int]] = [set([s.index for s in reduced.acceptingStates]), set()]
    
        for s in reduced.states:
            if s not in reduced.acceptingStates:
                P[1].add(s.index)
                W[1].add(s.index)
                
        if len(P[1]) == 0:
            P.remove(P[1])
            W.remove(W[1])
                
        while len(W) > 0:
            A = W.pop()
            
            alphabet_it = chain.from_iterable(combinations(reduced.atomicProps, r) for r in range(len(reduced.atomicProps) + 1))
            
            for s in alphabet_it:
                X = set()
                for state in reduced.states:
                    if list(state.computeTransition(set(s)))[0].index in A:
                        X.add(state.index)
                        
                newSets = []
                removeSet = []
                for Y in P:
                    interSet = X.intersection(Y)
                    diffSet = Y.difference(X)
                    if len(interSet) > 0 and len(diffSet) > 0:
                        removeSet.append(Y)
                        newSets.append(interSet)
                        newSets.append(diffSet)
                        
                for i in range(len(removeSet)):
                    Y = removeSet[i]
                    
                    if Y in P:
                        P.remove(Y)
                    
                    if Y in W:
                        W.remove(Y)
                        W.append(newSets[i * 2])
                        W.append(newSets[i * 2 + 1])
                    else:
                        if (len(newSets[i * 2]) < len(newSets[i * 2 + 1])):
                            W.append(newSets[i * 2])
                        else:
                            W.append(newSets[i * 2 + 1])
                            
                P.extend(newSets)
                    
        minDFA = FiniteAutomaton(len(P), reduced.atomicProps)
        
        # print("P:")
        # for p in P:
        #     print(p, end=", ")
        # print()
        
        for i in range(len(P)):
            statesSet = P[i]
            # print(statesSet)
            
            alphabet_it = chain.from_iterable(combinations(reduced.atomicProps, r) for r in range(len(reduced.atomicProps) + 1))
            
            for s in alphabet_it:
                targetSubset = set()
                for q in statesSet:
                    for state in reduced.states[q].computeTransition(set(s)):
                        targetSubset.add(state.index)
                # print("p: ", statesSet, ", s:", s, ", target:", targetSubset)
                
                for q in targetSubset:
                    for j in range(len(P)):
                        if q in P[j]:
                            minDFA.addTransition(minDFA.states[i], minDFA.states[j], set(s))
                            break
                     
                
            # for s in alphabet_it:
            #     target = list(reduced.states[q].computeTransition(set(s)))[0]
            #     for j in range(len(P)):
            #         if target.index in P[j]:
            #             minDFA.addTransition(minDFA.states[i], minDFA.states[j], set(s))
            #             break
                
            for idx in statesSet:
                if reduced.states[idx] in reduced.acceptingStates:
                    minDFA.acceptingStates.append(minDFA.states[i])
                    
                if reduced.states[idx] == reduced.initState:
                    minDFA.initState = minDFA.states[i]              
                    
        return minDFA

    def removeUnreachableStates(self) -> "FiniteAutomaton":
        """Removes all the dead states in the automaton."""
        
        reachable: set[int] = {self.initState.index}
        newStates: set[int] = {self.initState.index}
        
        while len(newStates) > 0:
            temp: set[int] = set()
            
            for q in newStates:
                alphabet_it = chain.from_iterable(combinations(self.atomicProps, r) for r in range(len(self.atomicProps) + 1))
            
                for s in alphabet_it:
                    temp = temp.union(self.computeSetTransition({self.states[q]}, list(s)))
                    
            newStates = temp.difference(reachable)
            reachable = reachable.union(newStates)
            
        FA = FiniteAutomaton(len(reachable), self.atomicProps)  
            
        newStateId: list[int] = [-1 for _ in range(self.statesNumber)]
        reachableL = list(reachable)
        
        for i in range(len(reachableL)):
            q = reachableL[i]
            newStateId[q] = i
            
            if self.states[q] in self.acceptingStates:
                FA.acceptingStates.append(FA.states[newStateId[q]])
            
        FA.initState = FA.states[newStateId[self.initState.index]]
        
        for q in reachableL:
            oldState = self.states[q]
            
            for t in oldState.transitions:
                if t.target.index in reachable:
                    FA.states[newStateId[q]].addTransition(FA.states[newStateId[t.target.index]], t.ap, t.isEps)
        
        return FA    
    
    def computeSetTransition(self, statesSet: set[State], propositionalInterpretation: list[str]) -> set[int]:
        """Given a set of states returns all the indexes of the state reachable with the given 
        propositional interpretation"""
        
        # TODO: prop_int list[str] -> set[str]
        S: set[int] = set()
        
        for q in statesSet:
            for state in q.computeTransition(set(propositionalInterpretation)):
                S.add(state.index)
        
        return S
    
    def recognizeWord(self, state: State, word: list[set[str]]) -> bool:
        if len(word) == 0:
            return state in self.acceptingStates
        
        return self.recognizeWord(list(state.computeTransition(word[0]))[0], word[1:])

    def __str__(self) -> str:
        S: str = f"""Numero di stati: {self.statesNumber}
Stato iniziale: {self.initState.index}
Stati accettanti: """
        for state in self.acceptingStates:
            S += str(state.index) + " "
            
        S += "\nTransizioni: \n"
        for state in self.states:
            S += state.transitionsToDot(self.atomicProps)
            
        return S
    
    def toDot(self) -> str:
        """Return a string representing the dot format of the automaton."""
        
        S: str = "digraph FA "
        S += """{
    rankdir = LR;
    center = true;
    edge [fontname = Courier];
    node [height = .5, width = .5];
    node [shape = doublecircle];"""
        for state in self.acceptingStates:
            S += str(state.index) + ";"
        S += "\n\tnode [shape = circle];" + str(self.initState.index) + ";"
        S += "\n\tinit [shape = plaintext, label = \"\"];\n\tinit -> " + str(self.initState.index) + ";\n"
        
        for state in self.states:
            S += state.transitionsToDot(self.atomicProps)
        
        from datetime import datetime
        S +=  '\tlabelloc="t"; \n' + '\tlabel ="' + str(datetime.now()) + '";\n'
        
        S += "}"
        return S
    
    def visualize(self, imageName = "Unnamed", imagePath = "img/", format = "svg") -> None:
        """Save a representation in the given format of the automaton using graphiz."""
        
        from graphviz import Source
        
        src = Source(self.toDot())
        src.render(imagePath + imageName, format = format, view = False)