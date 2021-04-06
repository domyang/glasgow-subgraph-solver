#ifndef GLASGOW_SUBGRAPH_SOLVER_GRAPH_EQUIVALENCE_HH
#define GLASGOW_SUBGRAPH_SOLVER_GRAPH_EQUIVALENCE_HH 1

enum class PatternEquivalence
{
    None,
    Structural
};

enum class TargetEquivalence
{
    None,
    Structural,
    Candidate,
    Full,
    NodeCover
};

#endif
