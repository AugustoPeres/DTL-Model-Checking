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

## Automata

### Buchi automata

### General buchi automata

## Transition systems

# Installation

Unfortunately currently there is no fancy way to install the program. The only
way to install is to copy the contents of the folder ´dtl-model-checking´ and
then using ´stack build´, or any other preferred method of compilation, to
compile and install.

# Usage

This is meant to be used as a command line tool where the user provides a file
with the encoded transition systems and a formula. For example

```./Main -modelCheck <path-to-the-transition-system> <formula> <number-of-agents>```


will run the automata theoretic approach with the given formula and transition
system.

## Encoding formulas

The parser for the formulas is very strict regarding the usage of parenthesis.
Parenthesis should be used whenever an operator is used. This includes the
binary operators.

Formulas should therefore be inputed as `@_1((p)=>(q))` but never `@_1(p=>q)` or
`(@_1(p))`. Spaces must not also be used

## Encoding transition systems

The transition system should be encoded in a file. The lines in that file must
be of the following form:

1. `states 1 2 3 4`. This line says the states present in the system
2. `initial 1 2`. This lines states the initial states
3. `actions agent a1 a2`. This line states the actions of each agent. agent
   should be an integer
4. `symbols agent p1 p2 p1`. States the propositional symbols available to each
   agent.
5. `label state agent p1 p2`. States the propositional symbols in the language
   of the agent that are present in the state.
6. `state action state`. Describes the transition relation.

## Command line options

There are only a few command line output arguments.

The first one is of the type

```./Main -modelCheck <path-to-the-transition-system> <formula> <number-of-agents>```

uses the automata theoretic approach.

To use the bounded approach use

```
./Main -modelCheck <path-to-transition-system> <formula> <number of agents> -bounded <maxbound>

```

where `<maxbound>` will be the max bound used. If no counter example is found
until this bound then the algorithm returns true.

There is also the possibility of printing a transition systems system to the dot
format which can the be copy pasted [here](http://www.webgraphviz.com/) for a
visualization of the transition system.

# Structure of the repository

# License

