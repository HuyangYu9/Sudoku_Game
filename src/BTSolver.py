import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random

class BTSolver:

    # ==================================================================
    # Constructors
    # ==================================================================

    def __init__ ( self, gb, trail, val_sh, var_sh, cc ):
        self.network = ConstraintNetwork.ConstraintNetwork(gb)
        self.hassolution = False
        self.gameboard = gb
        self.trail = trail

        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc

    # ==================================================================
    # Consistency Checks
    # ==================================================================

    # Basic consistency check, no propagation done
    def assignmentsCheck ( self ):
        for c in self.network.getConstraints():
            if not c.isConsistent():
                return False
        return True

    """
        Part 1 TODO: Implement the Forward Checking Heuristic

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        Note: remember to trail.push variables before you assign them
        Return: a tuple of a dictionary and a bool. The dictionary contains all MODIFIED variables, mapped to their MODIFIED domain.
                The bool is true if assignment is consistent, false otherwise.
    """
    def forwardChecking ( self ):
        result = {}
        assignedVars = set()

        pushSet = set()
        
        for c in self.network.getModifiedConstraints():
            for v in c.vars:
                if v.isAssigned() and v not in assignedVars:
                    assignedVars.add(v)      
        while len(assignedVars) > 0:
            av = assignedVars.pop()
            if av.domain.size() == 0:
                return (result,False)
            for neighbor in self.network.getNeighborsOfVariable(av):
                    if neighbor.isChangeable() and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                        if neighbor not in pushSet:
                            self.trail.push(neighbor)
                            pushSet.add(neighbor)
                        
                        #self.trail.push(neighbor)
                        neighbor.removeValueFromDomain(av.getAssignment())
                        result[neighbor] = neighbor.domain
                        if neighbor.domain.size() == 0:
                            return (result,False)
        return (result,self.network.isConsistent())

    # =================================================================
	# Arc Consistency
	# =================================================================
    def arcConsistency( self ):
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable() and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        neighbor.assignValue(neighbor.domain.values[0])
                        assignedVars.append(neighbor)

        
    
    """
        Part 2 TODO: Implement both of Norvig's Heuristics

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        (2) If a constraint has only one possible place for a value
            then put the value there.

        Note: remember to trail.push variables before you assign them
        Return: a pair of a dictionary and a bool. The dictionary contains all variables 
		        that were ASSIGNED during the whole NorvigCheck propagation, and mapped to the values that they were assigned.
                The bool is true if assignment is consistent, false otherwise.
    """
    def norvigCheck ( self ):
        
        #part 1
        result = {}
        assignedVars = set()
        pushSet = set()
        for c in self.network.getModifiedConstraints():
            for v in c.vars:
                if v.isAssigned() and v not in assignedVars:
                    assignedVars.add(v)


        while len(assignedVars) > 0:
            av = assignedVars.pop()
            if av.domain.size() == 0:
                return (result,False)
            for neighbor in self.network.getNeighborsOfVariable(av):
                    if neighbor.isChangeable() and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                        if neighbor not in pushSet:
                            self.trail.push(neighbor)
                            pushSet.add(neighbor)                     
                        #self.trail.push(neighbor)
                        neighbor.removeValueFromDomain(av.getAssignment())
                        result[neighbor] = neighbor.domain
                        if neighbor.domain.size() == 0:
                            return (result,False)

        #part 2
        n = self.gameboard.N
        for c in self.network.getConstraints():
            #update counter for this constraint
            count = [0]*n
            #for each variable in this constraint, we get their domain value and add it to a new counter
            for v in c.vars:
                #this variable has to be not assigned for it to work
                if not v.isAssigned():
                    for i in v.domain.values:
                        count[i-1] += 1
                        
            
            #for each constraint, we check counter, find 1 and assign the value, then check for consistence
            variables_set = set()
            for i in range(n):
                if count[i] == 1:
                #find that var that contain 1 in its domain
                    
                    var = self.findVarContainValue(i+1,c)
                    variables_set.add((var,i+1))

            #I have found all the 1 variables, assign them value, remove neighbor, and check for consistency
            for var,value in variables_set:
                if var not in pushSet:
                    pushSet.add(var)
                    self.trail.push(var)
                result[var] = var.domain
                var.assignValue(value)
                #after update this var, forward check on its neighbor
                if not self.removeValueFromNeighbors(var,result,pushSet):
                    return result,False
                #check for consistence
                if not self.network.isConsistent():
                    return result,False
        
        
            
        #print(f"found {len(variables_set)} variables","push: ",self.trail.getPushCount(),"backTrack: ",self.trail.getUndoCount())
        return result,self.network.isConsistent()

    def removeValueFromNeighbors(self,var:"Variable",result:'result',pushSet:'set')->bool:
        for neighbor in self.network.getNeighborsOfVariable(var):
            #if this neighbor is assigned, and is the value we just assigned, inconsistent, return false
            if neighbor.getDomain().contains(var.getAssignment()):
                if neighbor.isAssigned():
                    return False
                #otherwise, we can eliminate that value from its domain
                if neighbor not in pushSet:
                    pushSet.add(neighbor)
                    self.trail.push(neighbor)
                neighbor.removeValueFromDomain(var.getAssignment())
        return True

    def findVarContainValue(self,v:'value',c:"constrain"):
        for var in c.vars:
            #this var should not be assigend already
            if var.domain.contains(v) and not var.isAssigned():
                return var
        for v in c.vars:
            print(v)
        return None
    

        
    """
         Optional TODO: Implement your own advanced Constraint Propagation

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournCC ( self ):
        return self.norvigCheck()

    # ==================================================================
    # Variable Selectors
    # ==================================================================

    # Basic variable selector, returns first unassigned variable
    def getfirstUnassignedVariable ( self ):
        for v in self.network.variables:
            if not v.isAssigned():
                return v

        # Everything is assigned
        return None

    """
        Part 1 TODO: Implement the Minimum Remaining Value Heuristic

        Return: The unassigned variable with the smallest domain
    """
    def getMRV ( self ):
        result = None
        for c in self.network.constraints:
            for v in c.vars:
                if not v.isAssigned():
                    if result == None:
                        result = v
                    else:
                        result = min(result,v,key=lambda x:x.domain.size())
        return result

    """
        Part 2 TODO: Implement the Minimum Remaining Value Heuristic
                       with Degree Heuristic as a Tie Breaker

        Return: The unassigned variable with the smallest domain and affecting the  most unassigned neighbors.
                If there are multiple variables that have the same smallest domain with the same number of unassigned neighbors, add them to the list of Variables.
                If there is only one variable, return the list of size 1 containing that variable.
    """
    def MRVwithTieBreaker ( self ):
        temp = set()
        for c in self.network.constraints:
            for v in c.vars:
                if v not in temp and not v.isAssigned():
                    temp.add(v)

        if len(temp) == 0:
            return [None]
        
        if len(temp) == 1:
            return list(temp)

        result = []
        temp = sorted(temp,key=lambda x:(x.domain.size(),-len([n for n in self.network.getNeighborsOfVariable(x) if not n.isAssigned()])))
        min_neighbor_size = len(self.network.getNeighborsOfVariable(temp[0]))
        for v in temp:
            if len(self.network.getNeighborsOfVariable(v)) == min_neighbor_size:
                result.append(v)
            else:
                break
        return result

    """
         Optional TODO: Implement your own advanced Variable Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVar ( self ):
        #part1, find the smallest domain first by using MAD
        var_candidate = self.MRVwithTieBreaker() # a list of all the smallest domain variable with the same number of unasigned neighbor
        return var_candidate[0]
        #part2
        
        '''
        print(f"{len(var_candidate)}")
        value = 10000
        if len(var_candidate) > 1:
            for var in var_candidate:
                count = 0
                for neighbor in self.network.getNeighborsOfVariable(var):
                    if not neighbor.isAssigned():
                        count += neighbor.domain.size()
                if count < value:
                    result = var
                    value = count
        return result
        '''
        
        

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder ( self, v ):
        values = v.domain.values
        return sorted( values )

    """
        Part 1 TODO: Implement the Least Constraining Value Heuristic

        The Least constraining value is the one that will knock the least
        values out of it's neighbors domain.

        Return: A list of v's domain sorted by the LCV heuristic
                The LCV is first and the MCV is last
    """
    def getValuesLCVOrder ( self, v ):
        order = list(v.getDomain().values)
        neighbors = []
        vtocount={}
        for neighbor in self.network.getNeighborsOfVariable(v):
            if not neighbor.isAssigned():
                neighbors.append(neighbor)
        for assignment in order:
            count = 0
            for neighbor in neighbors:
                if neighbor.getDomain().contains(assignment):
                    count += neighbor.getDomain().size() -1
                else:
                    count += neighbor.getDomain().size()
            vtocount[assignment] = count
        return sorted(order,key = lambda x:vtocount[x])

    """
         Optional TODO: Implement your own advanced Value Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVal ( self, v ):
        
        return self.getValuesLCVOrder(v)

    # ==================================================================
    # Engine Functions
    # ==================================================================

    def solve ( self, time_left=600):
        if time_left <= 60:
            return -1

        start_time = time.time()
        if self.hassolution:
            return 0

        # Variable Selection
        v = self.selectNextVariable()

        # check if the assigment is complete
        if ( v == None ):
            # Success
            self.hassolution = True
            return 0

        # Attempt to assign a value
        for i in self.getNextValues( v ):

            # Store place in trail and push variable's state on trail
            self.trail.placeTrailMarker()
            self.trail.push( v )

            # Assign the value
            v.assignValue( i )

            # Propagate constraints, check consistency, recur
            if self.checkConsistency():
                elapsed_time = time.time() - start_time 
                new_start_time = time_left - elapsed_time
                if self.solve(time_left=new_start_time) == -1:
                    return -1
                
            # If this assignment succeeded, return
            if self.hassolution:
                return 0

            # Otherwise backtrack
            self.trail.undo()
        
        return 0

    def checkConsistency ( self ):
        if self.cChecks == "forwardChecking":
            return self.forwardChecking()[1]

        if self.cChecks == "norvigCheck":
            return self.norvigCheck()[1]

        if self.cChecks == "tournCC":
            return self.getTournCC()

        else:
            return self.assignmentsCheck()

    def selectNextVariable ( self ):
        if self.varHeuristics == "MinimumRemainingValue":
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
            return self.MRVwithTieBreaker()[0]

        if self.varHeuristics == "tournVar":
            return self.getTournVar()

        else:
            return self.getfirstUnassignedVariable()

    def getNextValues ( self, v ):
        if self.valHeuristics == "LeastConstrainingValue":
            return self.getValuesLCVOrder( v )

        if self.valHeuristics == "tournVal":
            return self.getTournVal( v )

        else:
            return self.getValuesInOrder( v )

    def getSolution ( self ):
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)
