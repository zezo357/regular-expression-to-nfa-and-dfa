
from texttable import Texttable
from graphviz import Digraph




class EdgesClass:
    edges={}
    def __init__(self):
        self.edges={}
        #self.addEdge(nameOfTarget,eps)
    def addEdge(self,nameOfTarget,textRequired):
        if(textRequired in self.edges):
            self.edges[textRequired].append(nameOfTarget)
        else:
            self.edges[textRequired]=[nameOfTarget]




eps = '-'


class Nfa:
    states={}
    symbols=[]
    DFAAcceptedStates=[]
    listofDfastates=[]
    listofNfastates=[]
    start=-1
    end=-1
    dot = Digraph()
    
    def __init__(self):
        self.states={}
        self.symbols=[]
        self.listofNfastates=[]
        self.dot=Digraph()
        self.dot.graph_attr['rankdir'] = 'LR'
        self.dot.node_attr['shape'] = 'circle'

    def addState(self,name):
        if(name not in self.states):
            self.states[name]=EdgesClass()
        self.dot.node(str(name),"<"+str(name)+">")
            #print(self.states)
            
    def AddSymbol(self,symbol):
        if (symbol not in self.symbols):
            self.symbols.append(symbol)
            
    def addEdgeToState(self,name,target,textRequired,constraint='true'):
        self.states[name].addEdge(target,textRequired)
        self.dot.edge(str(name),str(target) , label=textRequired,constraint=constraint)
    

    def SetStartAndEnd(self,start,end):
        self.start=start
        self.end=end
        self.dot.node('BEGIN', '', shape='none')
        self.dot.edge('BEGIN',str(self.start), label='start')
        self.dot.node(str(self.end), shape='doublecircle')
    def makeTableHeadersNfa(self):        
        #making the headers for table
        tmp=["state"]
        for symbol in self.symbols:
            tmp.append(symbol)
        return tmp

    def makeNfaListOfStates(self):
        if(eps not in self.symbols):
            self.symbols.append(eps)
        listofstates=[]
        
        #getting every State trannstions 
        #loops over every State
        for CheckingState in self.states:
            State=[CheckingState]
            #loops over every input in the loop
            for symbol in self.symbols:
                Edgedestinations=[]
                if symbol in self.states[CheckingState].edges:
                    Edgedestinations.extend(self.states[CheckingState].edges[symbol])
                State.append(Edgedestinations)
            listofstates.append(State)
            
        self.listofNfastates=listofstates
        
    def drawNfaTable(self):
        self.makeNfaListOfStates()
        listofstates=self.listofNfastates[:]
        t = Texttable()
        listofstates.insert(0,self.makeTableHeadersNfa())
        for state in listofstates:
            if state[0]==self.start:
                state[0]="start "+str(state[0])
            elif state[0]==self.end:
                state[0]="final "+str(state[0])
        t.add_rows(listofstates)
        print(t.draw())
        
    def drawNfaGraph(self):
        self.dot.render(filename='Nfa.gv', view=True)
        
    def subgraphForSymbol(self, symbol, State_count):
        State1 = State_count
        State2 = State_count+1
        self.addState(State1)
        self.addState(State2)
        self.addEdgeToState(State1, State2,symbol)

        return [State1, State2]

    def subgraphForUnion(self, LeftOperrands, RightOperrands, State_count):
        State1 = State_count
        State2 = State_count+1
        self.addState(State1)
        self.addState(State2)

        self.addEdgeToState(State1, LeftOperrands[0],eps)
        self.addEdgeToState(State1, RightOperrands[0],eps)

        self.addEdgeToState(LeftOperrands[1], State2,eps)
        self.addEdgeToState(RightOperrands[1], State2,eps)

        return [State1, State2]

    def subgraphForConcatenation(self, LeftOperrands,RightOperrands):
        self.addEdgeToState(LeftOperrands[1], RightOperrands[0],eps)
        return [LeftOperrands[0], RightOperrands[1]]

    def subgraphForClosure(self, States, State_count):
        #State = str(State_count)
        State = State_count
        self.addState(State)

        self.addEdgeToState(State, States[0], eps,constraint='true')
        self.addEdgeToState(States[1], States[0], eps,constraint='false')
        self.addEdgeToState(State, States[1], eps,constraint='false')

        return [State,States[1]]
    def subgraphForPositiveclosure(self, States):
        self.addEdgeToState(States[1], States[0], eps,constraint='false')
        return [States[0], States[1]]





# In[4]:


class Dfa:
    Nfa=[]
    symbols=[]
    DFAAcceptedStates=[]
    listofDfastates=[]
    Renaming={}
    def __init__(self,nfa):
        self.Nfa=nfa
        self.symbols=self.Nfa.symbols
        self.DFAAcceptedStates=[]
        self.listofDfastates=[]
        self.Renaming={}
        self.convertToDfa()
        

    def GetEpsilonTransition(self,StatetoBeChecked,listofstates):
        toBeChecked=[StatetoBeChecked]
        EpsilonTransition=[StatetoBeChecked]
        #to be checked is the list of the states to check for its EpsilonTransition
        while(len(toBeChecked)!=0):
            #print("start the loop",StatetoBeChecked)
            #print(toBeChecked)
            #for every state in toBeChecked
            for statedest in toBeChecked:
                #if there isnt any EpsilonTransition 
                if len(listofstates[statedest][-1])==0:
                    EpsilonTransition.append(statedest)
                    toBeChecked.remove(statedest)
                else:
                    #0->1,2,3
                    #1->5,6
                    #toBeChecked=[0,1,2,3]
                    #EpsilonTransition=[0,1,2,3]
                    #for every Epsilon Transition in the to be checked element
                    for trans in listofstates[statedest][-1]:
                        toBeChecked.append(trans)
                        #EpsilonTransition.append(trans)
                    #print(listofstates[statedest][-1])
                    
            for checking in toBeChecked:
                #if already added to the list remove from toBeChecked
                if checking in EpsilonTransition:
                    toBeChecked.remove(checking)
                else:
                    #will get this if EpsilonTransition  didnt have the destination and it was in the tobechecked
                    #will added it to destiontin and the while loop will check on it again
                    EpsilonTransition.append(checking)
            #print("ended the loop",StatetoBeChecked)
        EpsilonTransition=list(set(EpsilonTransition))
        EpsilonTransition.sort()
        return EpsilonTransition
    
    def convertToDfa(self):
        listofDfastates=[]
        
        self.Nfa.makeNfaListOfStates()
        
        listofstates=self.Nfa.listofNfastates[:]
        
        #getting start state Epsilon Transitions
        #print("start")
        listofDfastates.append([self.GetEpsilonTransition(self.Nfa.start,listofstates)])
        #print("end of start")
        while(len(listofDfastates[-1])!=len(self.symbols)):
            #for every state in the dfa 
            for dfaState in listofDfastates:
                    #print("dfaState",dfaState)
                    #check every input (ignoring the Epsilon Transition)
                    for symbol in range(len(self.symbols)-1):
                        #print("symbol",self.symbols[symbol])
                        
                        listOfStatesToBeReachedWithSymbol=[[]]  
                        #for every state in the new dfa list(example [1,2,3,4] will check for each input for every state in that list)
                        for dfaStateElement in dfaState[0]:
                            
                            #check for every destination possible (for that input)
                            for Edgedestination in listofstates[dfaStateElement][symbol+1]:
                                listOfStatesToBeReachedWithSymbol[0].extend(self.GetEpsilonTransition(Edgedestination,listofstates))
                        
                        #clean duplicates
                        listOfStatesToBeReachedWithSymbol[0]=list(set(listOfStatesToBeReachedWithSymbol[0]))
                        listOfStatesToBeReachedWithSymbol[0].sort()
                        #if this dfa is new add it to list (to check for inputs on it again)
                        if listOfStatesToBeReachedWithSymbol[0] not in [item[0] for item in listofDfastates]:
                            listofDfastates.append(listOfStatesToBeReachedWithSymbol)
                        
                        dfaState.append(listOfStatesToBeReachedWithSymbol[0])
        
        #append Accepeted States to list
        for state in listofDfastates:
                #print(state[0])
                if self.Nfa.end in state[0]:
                    if state[0] not in self.DFAAcceptedStates:
                        self.DFAAcceptedStates.append(state[0])

        self.listofDfastates=listofDfastates
        return listofDfastates
    
    def makeTableHeadersDfa(self):        
        #making the headers for table
        tmp=["state"]
        for symbol in self.symbols[:-1]:
            tmp.append(symbol)
        return tmp
    
    def DrawDfaGraph(self,UseListsAsNames,WithDeadState=False):
        dot = Digraph()
        dot.graph_attr['rankdir'] = 'LR'
        dot.node_attr['shape'] = 'circle'
        #print(listofDfastates)
        self.convertToDfa()
        if UseListsAsNames:
            listofDfastates=self.listofDfastates[:]
        else:
            listofDfastates=self.convertDfaToNumbers()
            if '[]' not in self.Renaming:
                self.Renaming['[]']=9999
        #print("listofDfastates",listofDfastates)
        #print("renaming",self.Renaming)

        for state in listofDfastates:
            if WithDeadState:
                if state[0] in self.DFAAcceptedStates:
                    dot.node(str(state[0]),"<"+str(state[0])+">", shape='doublecircle')
                else:
                    dot.node(str(state[0]),"<"+str(state[0])+">")
                #symbol is indexed +1 in states list(since its statename,and its transtions) and same in symbol list
                for symbol in range(len(self.symbols)-1):
                    dot.edge(str(state[0]),str(state[symbol+1]) , label=self.symbols[symbol])
            else:
                #inCase of lists As Names
                if UseListsAsNames:
                    #if not dead State create it
                    if not (len(state[0])==0):
                        if state[0] in self.DFAAcceptedStates:
                            dot.node(str(state[0]),"<"+str(state[0])+">", shape='doublecircle')
                        else:
                            dot.node(str(state[0]),"<"+str(state[0])+">")
                #inCase of numbers As Names
                else:
                    
                    #if not dead State create it
                    if not (self.Renaming['[]']==state[0]):
                        if state[0] in self.DFAAcceptedStates:
                            dot.node(str(state[0]),"<"+str(state[0])+">", shape='doublecircle')
                        else:
                            dot.node(str(state[0]),"<"+str(state[0])+">")                    

                #symbol is indexed +1 in states list(since its statename,and its transtions) and same in symbol list
                for symbol in range(len(self.symbols)-1):
                    #if len(state[symbol+1])!=0:
                    isDeadState=False
                    if UseListsAsNames:
                        isDeadState=((len(state[0])==0) or (len(state[symbol+1])==0))
                    else:
                        isDeadState=isDeadState or ((self.Renaming['[]']==state[0]) or (self.Renaming['[]']==state[symbol+1]))
                    
                    if not isDeadState:
                        dot.edge(str(state[0]),str(state[symbol+1]) , label=self.symbols[symbol])
        
       
        dot.node('BEGIN', '', shape='none')
        dot.edge('BEGIN',str(listofDfastates[0][0]), label='start')
        
        
        fileName=""
        if UseListsAsNames:
            if WithDeadState:
                fileName="Lists With Dead State Dfa.gv"
            else:
                fileName="Lists Without Dead State Dfa.gv"
        else:
            if WithDeadState:
                fileName="With Dead State Dfa.gv"
            else:
                fileName="Without Dead State Dfa.gv"
                
        
        dot.render(filename=fileName, view=True)

    
    def DrawDfaTable(self,UseListsAsNames):
        t = Texttable()
        self.convertToDfa()

        if UseListsAsNames:
            listofDfastates=self.listofDfastates[:]
        else:
            listofDfastates=self.convertDfaToNumbers()

        #add table headers
        t.add_row(self.makeTableHeadersDfa())  

        
        #add start state row
        statetmp=listofDfastates[0][:]
        #if the element is in the list of accepted states make it accepeted
        if statetmp[0] in self.DFAAcceptedStates:
            statetmp[0]="Start & Accept "+str(statetmp[0])
        else:
            statetmp[0]="Start "+str(statetmp[0])
        t.add_row(statetmp)        
        
        
        #add rest of the states
        for state in range(1,len(listofDfastates)):
            #this line to avoid changing the states names (list[:] makes a copy of the list values)
            statetmp=listofDfastates[state][:]
            #if the element is in the list of accepted states make it accepeted
            if statetmp[0] in self.DFAAcceptedStates:
                statetmp[0]="Accept "+str(statetmp[0])
            t.add_row(statetmp)


        print(t.draw())
        
        
    def convertDfaToNumbers(self):
        #make a dict and rename each element to new name
        self.convertToDfa()
        listofDfastates=self.listofDfastates[:]
        nodeCount=0
        #Renaming={'[]':[]}
        #Making a dict for every node new name
        for state in listofDfastates:
            #print(state[0])
            for symbol in range(len(self.symbols)): 
                #if state name is not in the dict of the new names (add it)
                if str(state[symbol]) not in self.Renaming:
                    self.Renaming[str(state[symbol])]=nodeCount
                    
                    #if the old name is accpeted make the new one accepted
                    if state[symbol] in self.DFAAcceptedStates:
                        if nodeCount not in self.DFAAcceptedStates:
                            self.DFAAcceptedStates.append(nodeCount)
                    state[symbol]=nodeCount
                    nodeCount+=1
                #if new name exist use it and add this Transition to it
                else:
                    state[symbol]=self.Renaming[str(state[symbol])]
        return listofDfastates
    
    def testString(self,string,listofDfastates,withSteps=False):
        stateIndex=0
        for char in string: 
            
            try:
                indexOfSymbol=self.symbols.index(char)
            except:
                #if the char is not known
                stateIndex=-1
                break
            
            destintionState=listofDfastates[stateIndex][indexOfSymbol+1]
            if withSteps:
                print(char," From ",stateIndex," To ",destintionState)
            stateIndex=destintionState
            
        if  stateIndex ==-1:
            print(string," Rejected")
            
        else:
            if listofDfastates[stateIndex][0] in self.DFAAcceptedStates:
                print(string," Is accepted :)")
            else:
                print(string," Is Rejected :_( try another one")

    def testStrings(self,withSteps=False):
        string = input("input test string (@ to terminate)")
        self.convertToDfa()
        listofDfastates=self.convertDfaToNumbers()[:]
        while(string!="@"):
            self.testString(string,listofDfastates,withSteps)
            string = input("input test string (@ to terminate)")


# In[5]:


class Stack:
    def __init__(self):
        self.stack = []

    def push(self, item):
        self.stack.append(item)

    def pop(self):
        return self.stack.pop()

    def empty(self):
        if self.stack.__len__ == 0:
            return True
        else:
            return False

    def top(self):
        return self.stack[-1]


# In[6]:


def isOperator(token):
    if token in ['*', '.', '|','+']:
        return True
    else:
        return False

def isSymbol(token):
    if token.isalnum():
        return True
    else:
        return False

def precedenceOf(op):
    if op=='|':
        return 1
    elif op=='.':
        return 2
    elif op=='+':
        return 3
    elif op=='*':
        return 4
    
    


# In[7]:


def addMissingDots(infixWithoutDots):
    #adding . if missing
    infix = infixWithoutDots[0]
    prev = infixWithoutDots[0]
    #if the characheter is normal char and before it another normal one or ) or *
    #or the char is ( and the before it a normal char
    for i in range(1,len(infixWithoutDots)):
        if (isSymbol(infixWithoutDots[i]) and ( isSymbol(prev) or prev == ')' or prev == '*'))or (infixWithoutDots[i] == '(' and (prev==')' or prev=='*' or prev=='+'))  or (infixWithoutDots[i] == '(' and isSymbol(prev)):
            infix += '.'
        infix += infixWithoutDots[i]
        prev = infixWithoutDots[i]


    infix= '(' + infix + ')'

    print('infix:', infix)
    return infix

def infixToPostFix(infix):
    postfix = ''

    #converting infix to postix
    stack = Stack()
    #https://gregorycernera.medium.com/converting-regular-expressions-to-postfix-notation-with-the-shunting-yard-algorithm-63d22ea1cf88
    for token in infix:
        if isSymbol(token):
            postfix += token
        elif isOperator(token):
            while stack.top() != '(' and precedenceOf(stack.top()) >= precedenceOf(token):
                postfix += stack.pop()
            stack.push(token)
        elif token == '(':
            stack.push(token)
        elif token == ')':
            while stack.top() != '(':
                postfix += stack.pop()
            stack.pop()

    print("Postfix:", postfix)
    return postfix

def postFixToNfa(postFix):
    
    node_count = 0

    #converting postfix to nfa
    stack = Stack()
    nfa=Nfa()
    for token in postFix:
        if isSymbol(token):
            symbol = token
            nfa.AddSymbol(symbol)
            nodes = nfa.subgraphForSymbol(symbol, node_count)
            node_count += 2
            stack.push(nodes)
        else:
            if token == '*':#zero or more
                nodes = stack.pop()
                #print('*',"nodesToBeConnected",nodes,"node",node_count)
                newNodes = nfa.subgraphForClosure(nodes, node_count)
                node_count += 1
                #print("newNodes",newNodes, "*")
                stack.push( newNodes )
            elif token == '+':#one or more
                nodesToBeConnected = stack.pop()
                #print('+',"nodesToBeConnected",nodesToBeConnected,"node",node_count)
                newNodes = nfa.subgraphForPositiveclosure(nodesToBeConnected)
                #print("newNodes",newNodes, "+")
                stack.push( newNodes )
            elif token == '.':
                RightOperrands = stack.pop()
                LeftOperrands = stack.pop()
                #print("right operrand of the .",RightOperrands,"node",node_count)
                #print("left operrand of the .",LeftOperrands)
                newFinalNodes = nfa.subgraphForConcatenation(LeftOperrands, RightOperrands)
                stack.push( newFinalNodes )
            elif token == '|':
                RightOperrands = stack.pop()
                LeftOperrands = stack.pop()
                #print("right operrand of the or",RightOperrands,"node",node_count)
                #print("left operrand of the or",LeftOperrands)
                newFinalNodes = nfa.subgraphForUnion(LeftOperrands, RightOperrands, node_count)
                node_count += 2
                stack.push( newFinalNodes )


    finalNodes = stack.pop()

    nfa.SetStartAndEnd(finalNodes[0],finalNodes[1])
    return nfa

def GenerateNfa(infixWithoutDots):
    #add dots for concatenation
    infixWithDots=addMissingDots(infixWithoutDots)
    #Convert infix To Postfix
    postFix=infixToPostFix(infixWithDots)
    #Convert Postfix To Nfa class
    nfa=postFixToNfa(postFix)
    return nfa


# In[ ]:


infixWithoutDots = input("infix RegEx (you may skip . operator): ")

if infixWithoutDots == '':
    raise IOError('infix RegEx cannot be empty')


nfa=GenerateNfa(infixWithoutDots)

#will draw nfa graph
nfa.drawNfaGraph()

#will draw nfa table
nfa.drawNfaTable()

dfa=Dfa(nfa)

###will draw dfa graph with all the e trans in it

#here with dead states
dfa.DrawDfaGraph(UseListsAsNames=True,WithDeadState=True)
#here without dead states
dfa.DrawDfaGraph(UseListsAsNames=True,WithDeadState=False)
######




###will draw dfa graph with new names

#here with dead states
dfa.DrawDfaGraph(UseListsAsNames=False,WithDeadState=True)
#here without dead states
dfa.DrawDfaGraph(UseListsAsNames=False,WithDeadState=False)
###########

###will draw dfa table with all the e trans in it
dfa.DrawDfaTable(UseListsAsNames=True)

###will draw dfa table with new names
dfa.DrawDfaTable(UseListsAsNames=False)


#will test if the string is accepted or not with steps
dfa.testStrings(withSteps=True)

#will test if the string is accepted or not without steps
dfa.testStrings(withSteps=False)




