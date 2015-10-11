#!/usr/bin/env python

# for a full implementation of a python constraint solver, see https://pypi.python.org/pypi/python-constraint.
# for a crashcourse on creating a CSP-solver in a weekend, see http://www.cs.northwestern.edu/~ian/GDCConstraintsHowTo.pdf

"""
    main file for this assignment. This is where we do all the meta CSP stuff, create the CSP's and do some statistics, printing

"""


from constraintproblem import *
import sys
from pprint import pprint
import os
import csv
from random import shuffle
from datetime import datetime
from collections import OrderedDict

CHECK_X_SUDOKUS = 0
SUDOKUS = []
N_SUDOKUS = 0

class Sudoku(object):
    """ instance of a sudoku. we use this to save some valuable statistics, and other useful information for fast access.

    """

    def __init__(self, sudoku):
        self.sudoku = sudoku
        self.string_representation = array2output(sudoku)
        self.givens = len(self.string_representation) - self.string_representation.count("0")
        self.freq_d = self.calculate_frequency(sudoku)
        self.variance = self.variance(self.freq_d)
        self.runtime = 0
        self.splits = 0
        self.solved = False

    def calculate_frequency(self, grid):
        """ calculates the freqency distribution of a distribution of numbers in a sudoku, i.e. the number of occurences, of the number of occurences.
            returns a dictionary with the frequency distribution.
        """ 
        d = {1: 0, 2: 0, 3: 0,
             4: 0, 5: 0, 6: 0, 
             7: 0, 8: 0, 9: 0}
        # first, we calculate the frequency of every number that is not 0
        for row in grid:
            for digit in row:
                if d.has_key(digit):
                    d[digit] += 1

        # because we dont care about which number occurs how many times, we calculate the frequency of the frequency. We take this distribution to be the distinguisable attribute of a sudoku, where the total number of given numbers is the same between the sudoku's we compare.
        freq_d = {}
        for key,value in d.iteritems():
            if value in freq_d.keys():
                freq_d[value] += 1
            else: 
                freq_d[value] = 1
        return freq_d

    def variance(self, distribution):
        """
            calculates the variance of a dictionary, containing the distribution
        """ 
        freq_sum = 0
        n = 0
        d = 0
        for key,value in distribution.iteritems():
            freq_sum += key * value
            n += value
        mean = float(freq_sum) / n
        for key,value in distribution.iteritems():
            d += value * (key - mean)**2
        variance = float(d) / n
        return variance


def read_sudokus(filename):
    """import all sudoku's from file given by user"""

    try:
        with open(filename,'r') as f:
            # For each sudoku in the file
            for line in f:
                line = line.replace(".","0")
                sudoku = []
                row = []
                for character in line:
                    if character.isdigit():
                        row.append(int(character))
                    # Go to next row when all columns are read    
                    if (len(row) == 9):
                        sudoku.append(row)
                        row = []
                sud = Sudoku(sudoku)
                SUDOKUS.append(sud)
            f.close()
    except IOError as e:
        print "I/O error({0}): {1}".format(e.errno, e.strerror)

def variable_domains(problem,sudoku):
    """ Add variables with domain 1-9 for each variable
    we also have to somehow translate all the sudokuchars to constraints. i.e. if (1,1) = 1 at init, there needs to be a constraint over variable (1,1) so that its domain is only [1]. 
    """
    for row in range(9):
        for col in range(9):
            if sudoku[row][col] == 0:
                problem.addVariable((row + 1, col + 1), range(1,10))
            else:
                problem.addVariable((row + 1, col + 1), [sudoku[row][col]])
    return problem

def sudoku_constraints(problem):
    """ Add constraints standard for all sudokus """

    # Add row constraints
    for i in range(1,10):        
        problem.addConstraint([(i,1), (i,2), (i,3), (i,4), (i,5), (i,6), (i,7), (i,8), (i,9)])
    # Add column constraints   
    for j in range(1,10):
        problem.addConstraint([(1,j), (2,j), (3,j), (4,j), (5,j), (6,j), (7,j), (8,j), (9,j)])

    # Add box constraints 
    problem.addConstraint([(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)])
    problem.addConstraint([(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)])
    problem.addConstraint([(1,7),(1,8),(1,9),(2,7),(2,8),(2,9),(3,7),(3,8),(3,9)])

    problem.addConstraint([(4,1),(4,2),(4,3),(5,1),(5,2),(5,3),(6,1),(6,2),(6,3)])
    problem.addConstraint([(4,4),(4,5),(4,6),(5,4),(5,5),(5,6),(6,4),(6,5),(6,6)])
    problem.addConstraint([(4,7),(4,8),(4,9),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9)])

    problem.addConstraint([(7,1),(7,2),(7,3),(8,1),(8,2),(8,3),(9,1),(9,2),(9,3)])
    problem.addConstraint([(7,4),(7,5),(7,6),(8,4),(8,5),(8,6),(9,4),(9,5),(9,6)])
    problem.addConstraint([(7,7),(7,8),(7,9),(8,7),(8,8),(8,9),(9,7),(9,8),(9,9)])
    return problem

def solution2array(solution):
    """ rewrites an solution of the form  {(1,1): [4], (1,2): [5] , .... (9,9) : [1]} to an 2dimensional array.
        this is useful if we want to output it in a human readable form.
        this is also used as intermediate step for rewriting the sudoku back to the original format.
    """
    sudoku_array = []
    for i in range(9):
        sudoku_array.append([])
        for j in range(9):
            sudoku_array[i].append(0)
    for variable, assignment in solution.iteritems():
        if len(assignment) == 1:
            sudoku_array[variable[0] -1][variable[1] - 1] = assignment[0]
    return sudoku_array

def array2output(solution_array):
    """ rewrite a 2dimensional array to long string, just like the input.

    """
    outputstring = ""
    for i in range(9):
        for j in range(9):
            outputstring += str(solution_array[i][j])
    return outputstring

def output_data(outputfile, output):
    """ outputs the solutions to the specified outputfile
    """
    with open(outputfile, 'w') as f:
        for sudoku in output:
                f.write(sudoku)
                f.write("\n")

def print_statistics(forward_checking = False, minimal_remaining_values = False, degree_heuristic = False):
    """ method that prints statistics to a file.

    """
    os.chdir("statistics/")

    dt = datetime.now().strftime("%Y-%m-%d-%H-%M-%S")
    filename = str(CHECK_X_SUDOKUS) + "-"

    if forward_checking:
        filename += "fc-"
    if minimal_remaining_values:
        filename += "mrv-"
    if degree_heuristic:
        filename += "dh-"
    filename += str(dt) + ".csv"

    with open(filename, 'wb') as csvfile:

        spamwriter = csv.writer(csvfile, delimiter=',',
                                quotechar='|', quoting=csv.QUOTE_MINIMAL)
        runtime = 0
        avg_splits = 0
        for sudoku_obj in SUDOKUS:
            runtime += sudoku_obj.runtime        
            avg_splits += sudoku_obj.splits 
        avg_splits = avg_splits/N_SUDOKUS
        spamwriter.writerow(['Heuristics:', 'forward_checking = ' + str(forward_checking), 'minimal_remaining_values = ' + str(minimal_remaining_values)])

        spamwriter.writerow(['--------------------------'])
        spamwriter.writerow(['Number of sudokus', N_SUDOKUS])
        spamwriter.writerow(['total runtime', round(runtime,3)])
        spamwriter.writerow(['average splits:', avg_splits])
        spamwriter.writerow(['--------------------------'])

        # NOW CALCULATE statistics for givens
        givens_dict = {}
        givens_solved_dict = {}
        for sudoku_obj in SUDOKUS:
            if sudoku_obj.givens in givens_dict.keys():
                givens_dict[sudoku_obj.givens].append(sudoku_obj)
            else:
                givens_dict[sudoku_obj.givens] = [sudoku_obj]

        givens_solved_dict = dict.fromkeys(givens_dict.keys(),0)
        for sudoku_obj in SUDOKUS:
            if sudoku_obj.solved:
                    givens_solved_dict[sudoku_obj.givens] += 1

        spamwriter.writerow(['givens', 'number of occurences', 'average runtime', 'average splits'])
        for givens, sudoku_objs in givens_dict.iteritems():
            avg_runtime = 0
            avg_splits = 0
            for sudoku_obj in sudoku_objs:
                avg_runtime += sudoku_obj.runtime
                avg_splits += sudoku_obj.splits
            n_suds = givens_solved_dict[givens]
            if n_suds > 0:
                avg_runtime = avg_runtime/n_suds
                avg_splits = avg_splits/n_suds
            else:
                avg_runtime = 0
                avg_splits = 0
            spamwriter.writerow([givens, givens_solved_dict[givens], avg_runtime, avg_splits])
        spamwriter.writerow(['--------------------------'])

        for n_givens, objects in givens_dict.iteritems():
            # Now we calculate statistics for variances per n_givens
            variance_dict = {}
            variance_solved_dict = {}
            for sudoku_obj in givens_dict[n_givens]:
                if sudoku_obj.variance in variance_dict.keys():
                    variance_dict[sudoku_obj.variance].append(sudoku_obj)
                else:
                    variance_dict[sudoku_obj.variance] = [sudoku_obj]

            variance_solved_dict = dict.fromkeys(variance_dict.keys(),0)
            for sudoku_obj in givens_dict[n_givens]:
                if sudoku_obj.solved:
                        variance_solved_dict[sudoku_obj.variance] += 1
            spamwriter.writerow(['variance distribution for givens = ' + str(n_givens)])
            spamwriter.writerow(['variances','number of occurences', 'average runtime', 'average splits'])

            od = OrderedDict(sorted(variance_dict.items()))
            for variance, sudoku_objs in od.iteritems():
                avg_runtime = 0
                avg_splits = 0
                for sudoku_obj in sudoku_objs:
                    avg_runtime += sudoku_obj.runtime 
                    avg_splits += sudoku_obj.splits
                n_suds = variance_solved_dict[variance]
                if n_suds > 0:
                    avg_runtime = avg_runtime/n_suds
                    avg_splits = avg_splits/n_suds
                else:
                    avg_runtime = 0
                    avg_splits = 0
                spamwriter.writerow([variance, variance_solved_dict[variance], avg_runtime, avg_splits])
            spamwriter.writerow(['--------------------------'])
    os.chdir("../")

def main(arg, forward_checking = False, minimal_remaining_values=False, degree_heuristic = False):
    """ main function of our CSP sudoku solver. reads in an inputfile with sudokus and outputs the result to a .txt file specified, or to the command line if the outputfile is not specified explicitly as an argument.

        @param forward_checking: search heuristic, default is False
        @param minimal_remaining_values: search heuristic, default is False


    A good thing to notice is that we can call this function multiple times (for example if you want to execute multiple heuristic settings). It has some overhead, but it works perfectly. A seperate statistics-file is generated for every run, so you can track the performance when tweaking values.

    """


    #if only a portion of the inputfile is parsed, N_SUDOKUS calculates how much that is (this is for averaging in statistics)
    global N_SUDOKUS
    global CHECK_X_SUDOKUS
    N_SUDOKUS = 0
    # We only print to file if specified in the commandline.
    print_to_file = False 
    outputfile = ""

    # User input size sudoku
    if len(arg) > 2 and arg[2][-4:] == ".txt":
        print_to_file = True
        outputfile = arg[2]

    # Read sudokus from text file
    read_sudokus(arg[1])

    # output is OR outputted to the screen, or to the outputfile. This is a buffer where we save all solutions as a string of 81 characters for 1 sudoku.
    output = []
    output_stats = []

    # set CHECK_X_SUDOKUS to all if its init value = 0
    if CHECK_X_SUDOKUS == 0:
        CHECK_X_SUDOKUS = len(SUDOKUS)
    for sudoku_obj in SUDOKUS[:CHECK_X_SUDOKUS]:
        N_SUDOKUS += 1
        print "solving sudoku " + str(N_SUDOKUS)

        # Here, we are initializing the sudoku.
        sudoku = sudoku_obj.sudoku
        problem = Problem(forward_checking=forward_checking, minimal_remaining_values=minimal_remaining_values, degree_heuristic = degree_heuristic)
        problem = variable_domains(problem, sudoku)
        problem = sudoku_constraints(problem)
        problem.mapVarToConstraints()

        # Get solution (this is of the form {(1,1): [4], (1,2): [5] , .... (9,9) : [1]})
        solution, statistics = problem.getSolution()
        sudoku_obj.solved = True

        # get live feedback on runtimes.
        print statistics
        sudoku_obj.runtime = getattr(statistics, 'runtime')
        sudoku_obj.splits = getattr(statistics, 'splits')

        # rewrite the sudoku ...
        solution_array = solution2array(solution)
        if not print_to_file:
            # ... so we can output it on the screen....
            pprint(solution_array)
        else:
            #... or to a file.
            output.append(array2output(solution_array))

    #if an outputfile is specified
    if outputfile:
        # log all the sudokus to a txt-file
        output_data(outputfile, output)
    # print statistics to a csv file.
    print_statistics(forward_checking=forward_checking, minimal_remaining_values=minimal_remaining_values, degree_heuristic = degree_heuristic)

if __name__ == '__main__':
    # how many sudokus do we want to check?
    # default = 0, then we check all.
    CHECK_X_SUDOKUS = 0
    if len(sys.argv) == 1:
        print "Please give a input filename, output filename"
        print "if no outputfile is given, the solutions will be outputted on the screen"
        print "Example: python sudoku.py \"input.txt\" \"output.txt\" "
    else:
        main(sys.argv,forward_checking=True, minimal_remaining_values=False, degree_heuristic = True)
