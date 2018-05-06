/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GUARD_GRAPH_HH
#define GUARD_GRAPH_HH 1

#include <set>
#include <string>
#include <type_traits>
#include <cstdint>

/**
 * A graph, in a convenient format for reading in from files. We don't do any
 * performance critical operations on this: the algorithms re-encode as
 * necessary.
 *
 * Indices start at 0.
 */
class Graph
{
    private:
        int _size = 0;
        std::set<std::pair<int, int> > _edges;


    public:
        /**
         * \param initial_size can be 0, if resize() is called afterwards.
         */
        Graph(int initial_size);

        Graph(const Graph &) = default;

        explicit Graph() = default;

        /**
         * Number of vertices.
         */
        auto size() const -> int;

        /**
         * Change our size. Must be called before adding an edge.
         */
        auto resize(int size) -> void;

        /**
         * Add an edge from a to b (and from b to a).
         */
        auto add_edge(int a, int b) -> void;

        /**
         * Are vertices a and b adjacent?
         */
        auto adjacent(int a, int b) const -> bool;

        /**
         * What is the degree of a given vertex?
         */
        auto degree(int a) const -> int;
};

#endif
