# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_constant(formula.root):
        prm = Formula('p')
        if formula.root == 'T':
            return Formula('|', prm, Formula('~', prm))
        return Formula('&', prm, Formula('~', prm))
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    lft = to_not_and_or(formula.first)
    rgt = to_not_and_or(formula.second)
    if formula.root == '&':
        return Formula('&', lft, rgt)
    if formula.root == '|':
        return Formula('|', lft, rgt)
    if formula.root == '->':
        return Formula('|', Formula('~', lft), rgt)
    if formula.root == '+':
        return Formula('|',
                       Formula('&', lft, Formula('~', rgt)),
                       Formula('&', Formula('~', lft), rgt))
    if formula.root == '<->':
        return Formula('|',
                       Formula('&', lft, rgt),
                       Formula('&', Formula('~', lft), Formula('~', rgt)))
    if formula.root == '-&':
        return Formula('~', Formula('&', lft, rgt))
    if formula.root == '-|':
        return Formula('~', Formula('|', lft, rgt))
    return Formula('F')

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    formula = to_not_and_or(formula)
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_unary(formula.root):
        return Formula('~', to_not_and(formula.first))
    if formula.root == '&':
        lft = to_not_and(formula.first)
        rgt = to_not_and(formula.second)
        return Formula('&', lft, rgt)
    if formula.root == '|':
        lft = to_not_and(formula.first)
        rgt = to_not_and(formula.second)
        return Formula('~', Formula('&',
                                    Formula('~', lft),
                                    Formula('~', rgt)))
    return Formula('F')

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    formula = to_not_and(formula)
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_unary(formula.root):
        innr = to_nand(formula.first)
        return Formula('-&', innr, innr)
    if formula.root == '&':
        lft = to_nand(formula.first)
        rgt = to_nand(formula.second)
        both = Formula('-&', lft, rgt)
        return Formula('-&', both, both)
    return Formula('F')

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    formula = to_not_and_or(formula)
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))
    if formula.root == '|':
        lft = to_implies_not(formula.first)
        rgt = to_implies_not(formula.second)
        return Formula('->', Formula('~', lft), rgt)
    if formula.root == '&':
        lft = to_implies_not(formula.first)
        rgt = to_implies_not(formula.second)
        return Formula('~', Formula('->', lft, Formula('~', rgt)))
    return Formula('F')

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    formula = to_implies_not(formula)
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_constant(formula.root):
        if formula.root == 'F':
            return Formula('F')
        return Formula('->', Formula('F'), Formula('F'))
    if is_unary(formula.root):
        innr = to_implies_false(formula.first)
        return Formula('->', innr, Formula('F'))
    if formula.root == '->':
        return Formula('->',
                       to_implies_false(formula.first),
                       to_implies_false(formula.second))
    return Formula('F')
