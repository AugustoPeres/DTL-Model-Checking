# DTL-Model-Checking

# Introduction

Distributed temporal logic(DTL) been used to reason about properties of
distributed transition systems from the point of its local agents. However, to
this day only a few model checking tools and algorithms are available for said
logic.

Currently very few model checking tools exist for distributed temporal logic.

In this repository you can find two implementations of model checking algorithm
for DTL interpreted over distributed transition systems. The first consists of
an automata theoretic approach and the second is a bounded model checking
procedure.

Both implementations are discussed in detail in my thesis.

There is also a `python` notebook with a brief comparison on both methods.

# Structure of the repository

This repository contains several two main folders. The folder
`dtl-model-checking` contains the source code for the model checking algorithm.

The folder `plots` simply contains simulations and tests used for the plots in
my thesis.

# Installation

Unfortunately currently there is no fancy way to install the program. The only
way to install is to copy the contents of the folder `dtl-model-checking` and
then using `stack build`, or any other preferred method of compilation, to
compile and install.

The usual `stack ghc Main.hs` will also work

# Usage

This is meant to be used as a command line tool where the user provides a file
with the encoded transition systems and a formula. For example

```
./Main -modelCheck <path-to-the-transition-system> <formula> <number-of-agents>
```

will run the automata theoretic approach with the given formula and transition
system.

## Encoding formulas

The parser for the formulas is very strict regarding the usage of parenthesis.
Parenthesis should be used whenever an operator is used. This includes the
binary operators.

Formulas should therefore be inputed as `@_1((p)=>(q))` but never `@_1(p=>q)` or
`(@_1(p))`. Spaces must not be used

If `f1` and `f2` are formulas properly expressed in the parser language then the
rest of the operators can be added inductively as follows

* Any propositional symbol is entered just as `p`
* The negation of a formula is entered as `~(f)`
* Globally `G(f)`
* Eventually `F(f)`
* Next `X(f)`
* Communication `c_j(f)` where `j` is an integer
* Implication `(f1)=>(f2)`
* And `(f1)/\\(f2)`
* Or `(f1)\\/(f2)`

At the global level we then have

* `@_i[f]` where `i` is an integer
* The operators And, Or and negation are represented as previously.

**Note:** for the automata theoretic approach formulas should be introduced
using the standard grammar *i.e*, without the operators *F*, *N*, *x_j* and the
only dual operator allowed for is the implication. This is because the automata
theoretic approach was implemented first and currently there is no converter
from formulas in the extended grammar to the standard grammar.

## Encoding transition systems

The transition system should be encoded in a file. The lines in that file must
be of the following form:

* `states 1 2 3 4`. This line says the states present in the system
* `initial 1 2`. This lines states the initial states
* `actions agent a1 a2`. This line states the actions of each agent. agent
* should be an integer
* `symbols agent p1 p2 p1`. States the propositional symbols available to each
* agent.
* `label state agent p1 p2`. States the propositional symbols in the language
* of the agent that are present in the state.
* `state action state`. Describes the transition relation.

There are several files already containing transition systems in the folder
`dtl-model-checking/ExampleFiles/`

## Command line options

### Model Checking

There are only a few command line output arguments.

The first one is of the type

```
./Main -modelCheck <path-to-the-transition-system> <formula> <number-of-agents>
```

uses the automata theoretic approach.

To use the bounded approach use

```
./Main -modelCheck <path-to-transition-system> <formula> <number of agents> -bounded <maxbound>
```

where `<maxbound>` will be the max bound used. If no counter example is found
until this bound then the algorithm returns true.

In both the previous commands the user gets only an answer stating whether or
not the transition systems satisfies the formula.

To get a counter example the commands are

```
./Main -oneCounterExample <path-to-transition-system> <formula> <number of agents>
```

using the automata theoretic approach

or

```
./Main -oneCounterExample <path-to-transition-system> <formula> <number of agents> -bounded <max-bound>
```

for the bounded approach.

In the first case the output will be something like `CounterExample [ [(s1, x1),
(s2, x2)...(sn, x2)], [(sn, xn), ..., (sn, xn)] ]`. This corresponds to the
infinite path in the dot product of DTS with the automaton that witnesses the
persistence property. Projecting the first coordinates yields an infinite path
in the transition system. The first list contains the shortest path to a state
that violates the persistence property and the second list contains the shortest
path from that state to itself.

In the second case we get an output of the form `Just (fromList
[("0_a":True)..("0_p1":True)...], k)`. Corresponding to the solution of the
formula and the symbols present in each state. The number before “_” indicates
the action taken at that step. k corresponds to the bound for which a counter
example was found.

### Visualization

There is also the possibility of printing a transition systems system to the dot
format using the command

```
./Main -toGraphviz <file-with-the-transition-system>
```

The output can then be copy pasted [here](http://www.webgraphviz.com/) for a
visualization of the transition system.

### Usage examples

```
./Main -modelCheck t8States2Agents1.txt "(@_1(p1))=>~(@_2(q1))" 2
True


./Main -modelCheck t8States2Agents1.txt "@_2(X(c_1(p2)))" 2
True


./Main -modelCheck t8States2Agents4.txt "(@_1(c_2(q1)))=>(@_1(p1))" 2
False


./Main -modelCheck t8States2Agents4.txt "@_1(F((p1)/\\(p2)))" 2 -bounded 0
True

./Main -modelCheck t8States2Agents4.txt "@_1(F((p1)/\\(p2)))" 2 -bounded 2
False


./Main -oneCounterExample t8States2Agents4.txt "@_1(F((p1)/\\(p2)))" 2 -bounded 2
Just (fromList [(0_"a",True),(0_"b",False),(0_"c",False),(0_p1,False),(0_p2,False),(0_q1,False),(1_"a",False),(1_"b",True),(1_"c",False),(1_p1,True),(1_p2,False),(1_q1,False)],1)
```

# Disclaimer

The reader of this source code should bear in mind that this was my first
project written in `Haskell`. Since writing the first modules such as
`DTLFormulas.hs` I have acquired more knowledge in the language and there are
therefore things I would do differently in some of the modules.

Since `Haskell` is quite a complex language I expect that there are parts that
may make the more experienced programmer cringe. Therefore anyone should feel
free to download and change the source code.

# License

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the “Software”), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
