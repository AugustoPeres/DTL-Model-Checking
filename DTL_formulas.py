# AUGUSTO PERES
# DTL formulas implementation in python

class DTLFormula():
    def __init__(self, first, rest = 0):
        self.first = first
        self.rest = rest

class Implies():
    def __init__(self, psi1, psi2):
        self.formula = DTLFormula(psi1, psi2)

class Not():
    def __init__(self, psi):
        self.formula = DTLFormula(Not(psi))

class PropositionalSymbol():
    def __init__(self, name):
        self.name = name
