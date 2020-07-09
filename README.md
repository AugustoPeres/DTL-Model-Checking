# DTL-Model-Checking

# Introduction

Distributed temporal logic(DTL) been used to reason about properties of
distributed transition systems from the point of its local agents. However, to
this day only a few model checking tools and algorithms are available for said
logic.

Currently very few model checking tools exist for distributed temporal logic.

In this repository you can find two implementations of model checking algorithm
for DTL interpreted over distributed transition systems. The first consists of
an automata theoretic approach based and the second is a bounded model checking
procedure.

Both implementations are discussed in detail on my thesis.

There is also a `python` notebook with a brief comparison on both methods.

# On the implementation

# Installation

Unfortunately currently there is no fancy way to install the program. The only
way to install is to copy the contents of the folder ´dtl-model-checking´ and
then using ´stack build´, or any other preferred method of compilation, to
compile and install.

# Usage

This is meant to be used as a command line tool where the user provides a file
with the encoded transition systems and a formula. For example

´´´
./Main -modelCheck <path-to-the-transition-system> <formula> <number-of-agents>
´´´

will run the automata theoretic approach with the given formula and transition
system.

## Encoding formulas

The parser for the formulas is very strict regarding the usage of parenthesis.
Parenthesis should be used whenever an operator is used. This includes the
binary operators $\implies$, $\vee$ $\wedge$.

## Encoding transition systems

## Command line options

# Structure of the repository

# License

