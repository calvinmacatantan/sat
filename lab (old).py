"""
6.101 Lab 8:
SAT Solver
"""

#!/usr/bin/env python3

import sys
import typing

sys.setrecursionlimit(10_000)
# NO ADDITIONAL IMPORTS

def reformat_formula(formula, literal):
    """
    """
    if [] in formula:
        return [[]]
    variable, setting = literal
    updated_formula = []
    for clause in formula:
        if literal in clause:
            continue
        elif (variable, not setting) in clause:
            copied_clause = clause.copy()
            copied_clause.remove((variable, not setting))
            updated_formula.append(copied_clause)
        else:
            updated_formula.append(clause.copy())
    return updated_formula

def satisfying_assignment(formula):
    """
    Find a satisfying assignment for a given CNF formula.
    Returns that assignment if one exists, or None otherwise.
    """
    
    ## literals that have been tried
    def remove_one_clauses(formula, assignments):
        """
        does not mutate formula
        returns a new, reformmated forumla without 1 literal clauses
        mutates assignments
        """
        reformatted = formula.copy()
        counter = 1
        while reformatted != [] and counter != 0 : # while we haven't finished this
            # if the formula is solved or if there are no more
            # no more length one clauses, we run this

            removed_literals = set()
            counter = 0
            for clause in reformatted:
                if clause == []: # if theres a [] clause (means impossible)
                    return [[]]
                if len(clause) == 1:
                    counter += 1 # if theres a length 1 clause
                    # add clause to assignments
                    literal = clause[0]
                    if literal[0] in assignments:
                        if assignments[literal[0]] != literal[1]:
                        # if its already in there, we run into a contradiction
                            return [[]]
                    assignments[literal[0]] = literal[1]
                    removed_literals.add(literal)

            # reformat formula
            for literal in removed_literals:
                reformatted = reformat_formula(reformatted, literal)
    
            # if reformatted == []:
            #     return assignments
        return reformatted

    # if were still going, we need to do process of eliminations with back tracking
    def _satisfying_assignment(formula, i):
        print(f'Level {i}')
        print(formula)
        # print(f'{formula}')
        literals = set()
        for clause in formula:
            # iterate through the clauses that aren't one literal
            if clause == []:
                return None # unsolvable

            for literal in clause:
                # we try that literal out
                if literal in literals:
                    continue

                attempt = reformat_formula(formula, literal)

                attempts_assignments = {literal[0]: literal[1]}

                # reformat attempt to remove single clauses
                attempt = remove_one_clauses(attempt, attempts_assignments)

                # check is if solved or unsolvable
                if attempt == []:
                    return attempts_assignments
                elif [] in attempt:
                    continue
                
                # we haven't solved it :(
                # we already removed single clauses so now we must do the rest
                attempts_assignments_continued = _satisfying_assignment(attempt, i+1)
                print(f'{attempts_assignments_continued= }')
                # recurse
                # if no possible soltion with literal
                if attempts_assignments_continued is None:
                    print(':(')
                    continue # not satisfiable with that literal
                print(f'{attempts_assignments= }')
                
                ass = {**attempts_assignments, **attempts_assignments_continued}
                print(f'{ass=}')
                return {**attempts_assignments, **attempts_assignments_continued}
                
        return None
    
    assignments = dict() # assignments we want to return
    reformatted = remove_one_clauses(formula, assignments)


    if reformatted == []:
        # we have solved it already
        return assignments
    if [] in reformatted:
        # impossible, cannot be satisfied
        return None

    assignments_continued = _satisfying_assignment(reformatted, 1)

    if assignments_continued is None:
        return None
    else:
        final_assignment = {**assignments, **assignments_continued}
        print(final_assignment)
        return final_assignment


def sudoku_board_to_sat_formula(sudoku_board):
    """
    Generates a SAT formula that, when solved, represents a solution to the
    given sudoku board.  The result should be a formula of the right form to be
    passed to the satisfying_assignment function above.
    """
    raise NotImplementedError


def assignments_to_sudoku_board(assignments, n):
    """
    Given a variable assignment as given by satisfying_assignment, as well as a
    size n, construct an n-by-n 2-d array (list-of-lists) representing the
    solution given by the provided assignment of variables.

    If the given assignments correspond to an unsolvable board, return None
    instead.
    """
    raise NotImplementedError


if __name__ == "__main__":
    # # making reformat
    # formula = [[('a', True), ('b', True), ('c', False)], [('c', True), ('d', True)]]
    # without_c = reformat_formula(formula, ('c', False))
    # print(without_c)
    # without_d = reformat_formula(without_c, ('d', True))
    # print(without_d)

    # 3.2.2 examples
    # formula = [
    #         [('a', True), ('b', True), ('c', True)],
    #         [('a', False), ('f', True)],
    #         [('d', False), ('e', True), ('a', True), ('g', True)],
    #         [('h', False), ('c', True), ('a', False), ('f', True)],
    #     ]
    # a_true = reformat_formula(formula, ('a', True))
    # a_false= reformat_formula(formula, ('a', False))
    # print(a_true)
    # print(a_false)

    # print(reformat_formula(a_true, ('f', False)))

    # test satis solver
    formula = [
        [("a", True), ("b", True)],
        [("a", False), ("b", False), ("c", True)],
        [("b", True), ("c", True)],
        [("b", True), ("c", False)],
    ]

    print(satisfying_assignment(formula))