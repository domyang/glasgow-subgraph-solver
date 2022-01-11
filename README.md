The Equivalence Boosted Glasgow Subgraph Solver
============================================

This is an adapted version of the Glasgow Subgraph solver used for the subgraph isomorphism problem.
This software is adapted to handle multiplex multichannel graphs as well as incorporate structural
equivalence-inspired ideas for acceleration of solve time and better understanding of the solution space.

These adaptations were made by Dominic Yang, Jacob Moorman, and Denali Molitor
at University of California, Los Angeles. The original solver on which these adaptations are built was
based on papers by Blair Archibald, Ciaran McCreesh, Patrick Prosser and James Trimble at the University
of Glasgow, Fraser Dunlop and Ruth Hoffman at the University of St Andrews.
The original solver can be found at [this Github page](https://github.com/ciaranm/glasgow-subgraph-solver).

Any questions about this software should be referred to [Dominic Yang](mailto:domyang@math.ucla.edu)

Structural Equivalence in Subgraph Isomorphism
--------------

Subgraph Isomorphism is the task of finding a copy of a small pattern graph within a larger target graph.
We wish to assign every pattern vertex to an associated target vertex while ensuring that the target vertices
have the same neighborhood structure apparent in the pattern. For example, the mapping (A->1, B->2, C->3) is
such a mapping but (A->1, B->2, C->6) is not because 6 is not adjacent to 1 while C is adjacent to A.
We wish to accelerate the state-of-the-art solver Glasgow by incorporating structural equivalence into
the algorithm.

Structural Equivalence, in the simplest terms, is the property of vertices of a graph having the exact
same neighborhood. For example, in the above figure, vertices B and C would be structurally equivalent
for they share the same neighbor, namely A. It is under these circumstances, that we can interchange 
pattern vertex assignments in any subgraph isomorphism to produce a new one. 

We can go further by acknowledging, that in many circumstances, certain edges are effectively irrelevant
to subgraph search, and obscure structural equivalence. To explain what we mean by this, consider mapping
vertex A to vertex 1. In order to ensure a subgraph isomorphism, we need only assign B and C to any
vertex adjacent to 1; any edges between the neighbors only obscures the similarity and are thus irrelevant.
The task of determining *relevancy* is difficult and will be expounded upon in an associated paper
to this package.

Installation
---------

Compilation of the solver can be done with the `make` command. This requires a C++17 compiler as well
as Boost to be installed.

Execution
-------

To run the basic implementation to find a single isomorphism for pattern graph stored in `pattern-file`
in a target graph stored in `target-file`

```shell session
$ ./glasgow_subgraph_solver pattern-file target-file
```

There are a wide variety of options which can be found by executing
```shell session
$ ./glasgow_subgraph_solver --help
```

We list some commonly used options:
1. --induced: Restrict algorithm to only find induced isomorphisms.
2. --count-solutions: Count all solutions, instead of stopping at the first found solution.
3. --print-all-solutions: Print all solutions found, if equivalence is used this will only print representative solutions.
4. --pattern-equivalence: One of `none`, `structural`, indicates equivalence level on pattern.
5. --target-equivalence: One of `none`, `structural`, `candidate`, `full`, or `node_cover`, indicates equivalence level on target.
6. --format: Indicate the format used for the graph files.

The solver currently only supports both pattern equivalence and target equivalence simultaneously
if both are set to `structural`.

File Format
------------

The file format which is currently supported by this library for multiplex graph processing
is the `csv` format. This format is given by listing each edge in comma-separated format
as three fields: the name of the first node, the name of the second node, and the edge label.
If the edge is to be directed, the first comma is to be replaced by a `>` symbol.
In order to support multigraphs, each edge is repeated according to its multiplicity.
To include node labels, you can put the node name in the first field, leave the second field
blank, and put the node label in the third field.

The following snippet adapted from the original Glasgow solver repository, demonstrates
how to write in this format.
```
first>second,red
first>second,red
second>first,blue
first,third,purple
first>first,green
first,,circle
second,,circle
third,,square
fourth,,square
```

