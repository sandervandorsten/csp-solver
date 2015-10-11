#!/usr/bin/env python
# CSP-problem class by Ilse van der Linden & Sander van Dorsten

""" Module that is able to solve CSPs. The problems are modelled as a constraints, which this module tries to satisfy. The solver implemented uses a recursive backtracker to search the searchspace (depth-first search) and returns a single solution found.

"""

import time
from collections import namedtuple
from copy import deepcopy
from pprint import pprint

# namedtuple for statistics. lighter datastructure than an class, but has a lot of accessibility options. easily configurable if you want to return more sorts of statistics.
Statistics = namedtuple("Statistics", "runtime, splits")

class Problem(object):
    """ An instance of a CSP problem

    """
    def __init__(self, minimal_remaining_values = False, forward_checking = False, degree_heuristic = False ):
        """ set some init values for the instantiated CSP.
        """

        # heuristics
        self.fc = forward_checking
        self.mrv = minimal_remaining_values
        self.dh = degree_heuristic

        # init assignments
        self.solver = BacktrackingSolver(forward_checking=self.fc, minimal_remaining_values=self.mrv, degree_heuristic = self.dh)
        self.constraints = []
        self.variables = {}
        self.var_constr_dict = {}
        
        #statistical values
        self.runtime = 0
        self.splits = 0 

    def addConstraint(self, constrained_variables=None):
        """ Add a constraint over the variables to the problem

        @param  constrained_variables: a list of variables over which the constraint works. Default is all variables.
        @type   constrained_variables: a list
        """
        if constrained_variables == None:
            constrained_variables = self.variables
        constraint = AllDifferentConstraint(constrained_variables)
        self.constraints.append(constraint)

    def addVariable(self, variable, domain):
        """ Add a single variable to the Problem with a given domain

        @param variable: variable that we add to our problem variables
        @type variable:  some single value, for example a string, an int. In the sudoku case, it's a tuple.
        @param domain:   Domain of the added variable
        @type domain:    instance of Domain, a list
        """
        self.variables[variable] = domain

    def addVariables(self, variables, domain):
        """ Add multiple variables to the problem with the same given domain

        @param variables: variable that we add to our problem variables
        @type variables:  something we can iterate over, a list, a range.
        @param domain: Domain of the added variable
        @type domain:  instance of Domain, a list
        """
        for variable in variables:
            self.addVariable(variable, domain)

    def mapVarToConstraints(self):
        """ Based on variables and constraint list, make dictionary that
        maps variables to their constraints.
        """

        for variable in self.variables:
            self.var_constr_dict[variable] = []

        for constraint_obj in self.constraints:
            for key in constraint_obj.const_vars:
                # add the constraint object itself to the list of constraints for that variable
                self.var_constr_dict[key].append(constraint_obj)
        return self.var_constr_dict

    def getSolution(self):
        """
        Returns a solution for the CSP-problem. The type of solver is specified in the __init__, as are the heuristics for the solver.

        @rtype: a dictionary with an assignment of variables.

        """
        self.var_constr_dict = self.mapVarToConstraints()

        start = time.time()
        solution = self.solver.getSolution(self)
        self.runtime = time.time() - start
        # solution is an assignment of problem, where the assignments for all variables are filled in. 
        return solution, self.getStatistics()

    def getStatistics(self):
        """ gets the statistics for this problem, for analysis.
        """
        stats = Statistics(runtime = self.runtime, splits = self.splits)
        return stats


class BacktrackingSolver(object):
    """ simple solver object that uses backtracking.

    """

    def __init__(self, forward_checking = False, minimal_remaining_values = False, degree_heuristic = False):
        self.forward_checking = forward_checking
        self.mrv = minimal_remaining_values
        self.dh = degree_heuristic

    def getSolution(self, problem):
        """ Gets a solution for the given problem. 

            @rtype: a dictionary with an assignment of variables, or False if no consistent assignment is found.

        """
        if self.forward_checking:
            problem, assigned = self.update_domains(problem,[])

        return self.backtrack(problem)

    def backtrack(self, problem):
        """ The backtracking part of the solver. backtracks depth-first through the searchspace to find a solution.

        """

        #OLD CODE
        # # find unassigned variables
        # u = (v for v in problem.variables if len(problem.variables[v]) > 1 )
         
        # Find unassigned variables
        u = [var for var,d in problem.variables.iteritems() if len(problem.variables[var]) > 1 ]

        if len(u) == 0:
            return problem.variables
        
        # Decide which unassigned variable to assign a value first
        if self.mrv and not self.dh:
            unassigned = self.sort_mrv(u, problem.variables)
        elif not self.mrv and self.dh:
            unassigned = self.sort_dh(u, problem.var_constr_dict)
        elif self.dh and self.mrv:
            unassigned = self.sort_both(u, problem.variables, problem.var_constr_dict)
        elif not self.mrv and not self.dh:
            u = (v for v in problem.variables if len(problem.variables[v]) > 1 )
            unassigned_vars = [ (len(problem.variables[v]), v) for v in u ]
            unassigned = unassigned_vars[0][1]

        # OLD CODE
        # order unassigned variables
        # if self.mrv:
        #     unassigned_vars.sort()
        # unassigned = unassigned_vars[0][1]

        # make a copy of current state for backtracking
        copy_variables = deepcopy(problem.variables)      

        # Get domain of unassigned variable
        domain = problem.variables[unassigned]
        for value in domain:
            # Assign value to variable
            problem.variables[unassigned] = [value]
            # Update domains
            problem, assigned = self.update_domains(problem, [unassigned])
            if self.check_assignment(problem, assigned):
                problem.splits += 1
                result = self.backtrack(problem)
                if isinstance(result, dict):
                    return result
            problem.variables = deepcopy(copy_variables)

        problem.variables = deepcopy(copy_variables)
        return False

    def update_domains(self, problem, assigned):
        """ updates the domains for a problem, after assigning values.
            this reduces the domains, if forward_checking is enabled.

            we only update the domains locally, and do this only once.

        """

        # For first update round: find all assigned values
        if len(assigned) == 0:
            assigned = [ v for v in problem.variables if len(problem.variables[v]) == 1 ]

        # Loop over assigned variables    
        for var1 in assigned:
            # Find constraints for assigned var
            myconstraints = problem.var_constr_dict[var1]
            for constraint_obj in myconstraints:
                # Find variables that assigned var is constrained by
                other_vars = constraint_obj.getOthers(var1)
                for var2 in other_vars:
                    # If variables that assigned var is constrained by
                    # have its assigned value in domain, remove it
                    if len(problem.variables[var2]) != 1:
                        assigned_value = problem.variables[var1][0]
                        if assigned_value in problem.variables[var2]:
                            problem.variables[var2].remove(assigned_value)
                            if len(problem.variables[var2]) == 1:
                                assigned.append(var2)
        return problem, assigned


    def check_assignment(self, problem, assigned):
        """ after updating a domain, check if the assignment of a variable causes a clash with the rest of the solution.

        """
        flag = True
        for variable in assigned:
            myconstraints = problem.var_constr_dict[variable]
            for constraint_obj in myconstraints:
                flag = constraint_obj.check(problem, variable)
                if flag == False:
                    return flag
        return flag

    def sort_mrv(self, unassigned, variables):
        domain_order = [(len(variables[v]), v) for v in unassigned]
        domain_order.sort()
        return domain_order[0][1]
  
    def sort_dh(self, unassigned, var_constr_dict):
        count_cvars = []
        for var in unassigned:
            c_list = []
            myconstraints = var_constr_dict[var]
            for constraint in myconstraints:
                for other_var in constraint.getOthers(var):
                    if (other_var in unassigned) and (other_var not in c_list):
                        c_list.append(other_var)
            count_cvars.append((len(c_list), var))
        count_cvars.sort()     
        return count_cvars[0][1]

    def sort_both(self, unassigned, variables, var_constr_dict):
        mrv = []
        domain_size = 2
        while len(mrv) == 0:
            mrv = [v for v in unassigned if len(variables[v]) == domain_size]
            domain_size += 1
        return self.sort_dh(mrv, var_constr_dict)

 
class AllDifferentConstraint(object):
    """ init a constraint over variables. If these variables are not given, the constraint will be over all variables.
    """

    def __init__(self, constrained_variables):
        """ init a constraint. 
            
            @param constrained_variables: variables over which the constraint is. the default is all variables
            @type constrained_variables: a list.
        """
        self.const_vars = constrained_variables

    def getOthers(self, variable):
        """ returns a list of all the constraint variables, except the argument variable.
        """
        return [item for item in self.const_vars if item != variable]

    def check(self, problem, updated_var):
        """ check if constraint is still satisfied, after an update. 
        """
        for var in self.getOthers(updated_var):
            if len(problem.variables[var]) == 1:
                if problem.variables[var] == problem.variables[updated_var]:
                    return False
        return True
