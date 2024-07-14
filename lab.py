"""
6.101 Lab 8:
SAT Solver
"""

#!/usr/bin/env python3

import sys

# import typing

sys.setrecursionlimit(10_000)
# NO ADDITIONAL IMPORTS


class Frame:
    """
    Frame objects store variable within a certain scope
    """

    def __init__(self, parent_frame=None):
        self.parent = {} if parent_frame is None else parent_frame
        self.frame = {}

    def __getitem__(self, key):
        if key in self.frame:
            return self.frame[key]
        elif key in self.parent:
            return self.parent[key]

        raise NameError(f"Variable {key} not found!!")

    def __setitem__(self, key, value):
        self.frame[key] = value

    def __contains__(self, key):
        if key in self.frame:
            return True
        elif key in self.parent:
            return True
        return False

    def in_local(self, key):
        return key in self.frame

    def get_local(self):
        return self.frame

    def get_frame(self, key):
        if not self.in_except_builtins(key):
            raise NameError(f"No frame where {key} is found")

        if key in self.get_local():
            return self
        else:
            return self.parent.get_frame(key)

    def __iter__(self):
        yield from self.frame
        yield from self.parent

    def __str__(self):
        return str(self.frame)

    def __repr__(self):
        return f"Frame({self.parent})"

def inverse(literal):
    """
    Returns the inverse of a literal
    """
    variable, setting = literal
    return (variable, not setting)

def reformat_formula(formula, literal):
    """
    Given a setting in the form of a literal, returns a reformatted formula assuming
    the given setting to be true
    """

    # [] Indicates formula is unsolvable because there is an unsolveable clause
    if [] in formula:
        return [[]]

    updated_formula = []

    # Iterates through each clause in CNF formula
    for clause in formula:
        # Deletes duplicate clauses
        clause = list(set(clause))

        if literal in clause:
            # If literal in clause, clause is not needed in new formula
            # Move to next clause 
            continue
        elif inverse(literal) in clause:
            # If the opposite in the clause, copy the clause
            copied_clause = clause.copy()

            # Remove instances the inverse in copied clause
            copied_clause.remove(inverse(literal))
            
            # Append modified copied clause to formula
            updated_formula.append(copied_clause)
        else:
            # Append copy of clause to formula
            updated_formula.append(clause.copy())
    
    return updated_formula


def satisfying_assignment(formula, assignments=None, frame=None):
    """
    Find a satisfying assignment for a given CNF formula.
    Returns that assignment if one exists, or None otherwise.
    """

    def remove_unit_clauses(formula):
        """
        Removes unit clauses, by reformatting formula by assuming them to be true
        Returns a tuple consisting of the updated formula and unit clauses taken to be true
        """
        unit_assignments = {}
        updated_formula = formula.copy()

        # Counts how many unit clauses
        counter = 1

        while counter > 0:
            # While there are more than one unit clauses
            counter = 0

            for clause in updated_formula.copy():
                if clause == []:
                    return ([[]], unit_assignments)

                if len(clause) == 1:
                    literal = clause[0]
                    unit_assignments[literal[0]] = literal[1]
                    updated_formula = reformat_formula(updated_formula, literal)
                    counter += 1

        return (updated_formula, unit_assignments)

    # Default parameters
    if assignments is None:
        assignments = {}

    if frame is None:
        frame = Frame()

    # Creates a dictionary of assignments
    new_assignments = {}

    reformatted_formula = formula.copy()  # sorted(formula.copy(), key=len)

    reformatted_formula, unit_assignments = remove_unit_clauses(reformatted_formula)

    for assignment in unit_assignments:
        frame[assignment] = unit_assignments[assignment]

    new_assignments.update(unit_assignments)

    if reformatted_formula == []:
        return {**new_assignments, **assignments}
    if [] in reformatted_formula:
        return None

    for clause in reformatted_formula:
        for literal in clause:
            if literal[0] in frame:
                continue

            frame[literal[0]] = literal[1]

            assignment_attempt = {literal[0]: literal[1]}

            attempt = satisfying_assignment(
                reformat_formula(reformatted_formula, literal),
                assignment_attempt,
                Frame(frame),
            )

            if attempt is None:
                assignment_attempt = {}
                literal = inverse(literal)
                assignment_attempt = {literal[0]: literal[1]}
                frame[literal[0]] = literal[1]

                attempt = satisfying_assignment(
                    reformat_formula(reformatted_formula, literal),
                    assignment_attempt,
                    Frame(frame),
                )

                if attempt is None:
                    # print("Neither worked, returning None")
                    return None

            # print("attempt worked!")
            # print(formula)
            # print({**new_assignments, **attempt, **assignment_attempt})
            # print("Assignments: ")
            # print({**new_assignments, **attempt, **assignment_attempt})
            return {**new_assignments, **attempt, **assignment_attempt}

    return None

def values_in_row(board, r):
    return set(board[r]) - {0}

def values_in_column(board, c):
    return {row[c] for row in board} - {0}

def values_in_subgrid(board, r, c, size):
    sub_size = int(size ** (0.5))
    tr, tc = (r // sub_size) * sub_size, (c // sub_size) * sub_size
    return set(
        board[tr + r][tc + c] for r in range(sub_size) for c in range(sub_size)
    ) - {0}

def create_ass(val, row, col, assignment):
    return ((val, row, col), assignment)

def all_vars(size):
    return {
        (val, row, col)
        for row in range(size)
        for col in range(size)
        for val in range(1, size + 1)
    }

def each_group_has(size):
    """
    each row, col, block has all the numbers
    """
    all_values = set(range(1, size + 1))
    sub_size = int(size ** (0.5))
    formula = []
    for val in all_values:
        for tr in range(sub_size):
            for tc in range(sub_size):
                clause = []
                for r in range(sub_size):
                    for c in range(sub_size):
                        clause += [
                            create_ass(val, tr * sub_size + r, tc * sub_size + c, True)
                        ]
                formula += [clause]

        # each col has all the numbers
        formula += [
            [create_ass(val, row, col, True) for row in range(size)]
            for col in range(size)
        ]

        # each row has all the numbers
        formula += [
            [create_ass(val, row, col, True) for col in range(size)]
            for row in range(size)
        ]
    return formula

def falsehood_and_truth(size):
    """
    each group has at most one number and at least one number
    """
    all_values = set(range(1, size + 1))

    formula = []
    for row in range(size):
        for col in range(size):
            for val1 in range(1, size + 1):
                for val2 in range(val1 + 1, size + 1):
                    formula += [
                        [
                            create_ass(val1, row, col, False),
                            create_ass(val2, row, col, False),
                        ]
                    ]
            # one of them has to be true
            formula += [[create_ass(val, row, col, True) for val in all_values]]

    return formula

def sudoku_board_to_sat_formula(sudoku_board):
    """
    Generates a SAT formula that, when solved, represents a solution to the
    given sudoku board.  The result should be a formula of the right form to be
    passed to the satisfying_assignment function above.
    """

    size = len(sudoku_board)  # number of columns rows and subgrid
    all_values = set(
        range(1, size + 1)
    )  # possible value(str(other_val) + "." + str(row) + "." + str(col), True)'s
    # print(f'{all_values=}')

    def possible_values(row, col):
        row_values = values_in_row(sudoku_board, row)
        col_values = values_in_column(sudoku_board, col)
        grid_values = values_in_subgrid(sudoku_board, row, col, size)

        # gets possible values given the values of its row, col, and grid
        possible_values = all_values - (row_values | col_values | grid_values)

        clause = []

        for val in possible_values:
            clause += [(create_ass(val, row, col, True))]

        return [clause]

    def known_value_and_clauses(val, row, col):
        # if we know val is at row, col
        # we need to set the other rows, cols, and subs to false

        partial_formula = []

        # for the row
        row_clauses = []
        for c in range(size):
            if col != c:
                row_clauses += [[create_ass(val, row, c, False)]]
        # row_clauses = [
        #     [create_ass(val, row, c, False)].copy() for c in range(size) if col != c
        # ]
        # print(f'{len(row_clauses) =}')
        partial_formula += row_clauses

        # for the col
        col_clauses = []
        for r in range(size):
            if r != row:
                col_clauses += [[create_ass(val, r, col, False)]]
        # row_clauses = [
        # col_clauses = [
        #     [create_ass(val, r, col, False)].copy() for r in range(size) if r != row
        # ]
        # print(f'{len(col_clauses) =}')

        partial_formula += col_clauses

        sub_size = int(size ** (0.5))

        tr, tc = (row // sub_size) * sub_size, (col // sub_size) * sub_size

        grid_clauses = []

        for r in range(sub_size):
            for c in range(sub_size):
                if (tr + r, tc + c) != (row, col):
                    grid_clauses += [[create_ass(val, tr + r, tc + c, False)]]

        # sub_clauses = [
        # [create_ass(val, tr + r, tc + c, False)].copy()
        # for r in range(sub_size)
        # for c in range(sub_size)
        # if (tr + r, tc + c) != (row, col)
        # ]
        # print(f'{len(sub_clauses) =}')

        partial_formula += grid_clauses

        false_clauses = []

        for num in all_values:
            if num != val:
                false_clauses += [[create_ass(num, row, col, False)]]
        # false_clauses = [
        #     [create_ass(num, row, col, False)].copy()
        # for num in all_values if num != val
        # ]

        partial_formula += false_clauses

        # print(f'{len(partial_formula) =}')
        # partial_formula.remove([create_ass(val, row, col, False)])
        # print(f"known value = {(val, row, col)}")
        # print(f"{partial_formula=}")
        return partial_formula

    formula = []

    # hello = []
    sub_size = int(size ** (0.5))

    formula += each_group_has(size)

    # for val in all_values:
    # each block has all the numbers
    # for tr in range(sub_size):
    #     for tc in range(sub_size):
    #         clause = []
    #         for r in range(sub_size):
    #             for c in range(sub_size):
    #                 clause += [
    #                     create_ass(val, tr * sub_size + r, tc * sub_size + c, True)
    #                 ]
    #         formula += [clause]
    #         hello += [clause]
    # # print()
    # # print(hello)
    # # each col has all the numbers
    # formula += [
    #     [create_ass(val, row, col, True) for row in range(size)]
    #     for col in range(size)
    # ]

    # # each row has all the numbers
    # formula += [
    #     [create_ass(val, row, col, True) for col in range(size)]
    #     for row in range(size)
    # ]

    # for row in range(size):
    #     for col in range(size):
    #         for val1 in range(1, size + 1):
    #             for val2 in range(val1 + 1, size + 1):
    #                 formula += [
    #                     [
    #                         create_ass(val1, row, col, False),
    #                         create_ass(val2, row, col, False),
    #                     ]
    #                 ]
    #         # one of them has to be true
    #         formula += [[create_ass(val, row, col, True) for val in all_values]]

    formula += falsehood_and_truth(size)

    # apply logic
    # counter = 0
    for row in range(size):
        for col in range(size):
            element = sudoku_board[row][col]
            if element == 0:
                formula += possible_values(row, col)
            else:
                formula += [[create_ass(element, row, col, True)]]
                formula += known_value_and_clauses(element, row, col)

    return formula

def assignments_to_sudoku_board(assignments, n):
    """
    Given a variable assignment as given by satisfying_assignment, as well as a
    size n, construct an n-by-n 2-d array (list-of-lists) representing the
    solution given by the provided assignment of variables.

    If the given assignments correspond to an unsolvable board, return None
    instead.
    """

    # print(assignments)
    if assignments is None:
        return None

    line = [0 for _ in range(n)]
    sudoku_board = [line.copy() for _ in range(n)]
    for variable in assignments:
        assignment = assignments[variable]
        if assignment is True:
            val, row, col = variable
            val = int(val)
            row = int(row)
            col = int(col)
            sudoku_board[row][col] = val

    if [] in sudoku_board_to_sat_formula(sudoku_board):
        print("impossible")
        return None

    # print(sudoku_board)
    return sudoku_board

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

    # # test satis solver
    # TEST_DIRECTORY = os.path.join(os.path.dirname(__file__), "test_inputs")

    # ## HELPER FUNCTIONS

    # with open(os.path.join(TEST_DIRECTORY,"J.json")) as f:
    #     formula = json.load(f)

    # formula.sort(reverse = True, key = lambda x: len(x))
    # print(formula)
    # print('done')

    # board = [
    #     [2, 0, 0, 9, 0, 0, 0, 0, 0],
    #     [0, 0, 0, 0, 0, 0, 0, 6, 0],
    #     [0, 0, 0, 0, 0, 1, 0, 0, 0],
    #     [5, 0, 2, 6, 0, 0, 4, 0, 7],
    #     [0, 0, 0, 0, 0, 4, 1, 0, 0],
    #     [0, 0, 0, 0, 9, 8, 0, 2, 3],
    #     [0, 0, 0, 0, 0, 3, 0, 8, 0],
    #     [0, 0, 5, 0, 1, 0, 0, 0, 0],
    #     [0, 0, 7, 0, 0, 0, 0, 0, 0],
    # ]

    # board = [[1, 2, 3, 4], [4, 3, 2, 1], [3, 1, 4, 2], [2, 4, 1, 3]]
    # formula = sudoku_board_to_sat_formula(board)
    # assignments = satisfying_assignment(formula)
    # print()
    # print(assignments)

    # print(assignments)
    # print(len(assignments))
    # new_board = assignments_to_sudoku_board(assignments, len(board))
    # print("level 3")

    # print(new_board)
    pass
