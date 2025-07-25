def askFormula():
    print("Select logic: ")
    print(" (p) Past Linear Temporal Logic")
    print(" (l) Linear Temporal Logic")
    
    logicType = input("(P/l)")
    
    formulaStr = formulaInput()
    
    if (str.lower(logicType) != "l"):
        from pylogics.parsers.pltl import parse_pltl 
        formula = parse_pltl(formulaStr)
    else:
        from pylogics.parsers.ltl import parse_ltl 
        formula = parse_ltl(formulaStr)
        
    return formula

def formulaInput():
    print("Select input type: ")
    print(" (c) Command line")
    print(" (f) File")

    formula = ""
    inputType = input("(C/f) ")
    if (str.lower(inputType) == "f"):
        fileName = input("Insert file name: ")
        with open(fileName, 'r') as file:
            formula = file.read()
    else:
        formula = input("Insert formula: ")
        
    return formula

if __name__ == "__main__":
    print(askFormula())