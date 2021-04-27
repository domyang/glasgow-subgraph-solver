/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_SUBGRAPH_SOLVER_SOLVER_FORMATS_INPUT_GRAPH_HH
#define GLASGOW_SUBGRAPH_SOLVER_SOLVER_FORMATS_INPUT_GRAPH_HH 1

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <set> 
#include <map>
#include <tuple>
#include <string_view>

/**
 * A graph, in a convenient format for reading in from files. We don't do any
 * performance critical operations on this: the algorithms re-encode as
 * necessary.
 *
 * Indices start at 0.
 */
class InputGraph
{
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

    public:
        /**
         * \param initial_size can be 0, if resize() is called afterwards.
         */
        InputGraph(int initial_size, bool has_vertex_labels, bool has_edge_labels);
        InputGraph(int initial_size, bool has_vertex_labels, bool has_edge_labels, bool directed, bool loopy);

        InputGraph(const InputGraph &) = delete;

        InputGraph(InputGraph &&);

        ~InputGraph();

        /**
         * Number of vertices.
         */
        auto size() const -> int;

        /**
         * Number of (directed, even if the graph is undirected) edges.
         */
        auto number_of_directed_edges() const -> int;

        /**
         * Do we have any loops?
         */
        auto loopy() const -> bool;

        /**
         * Change our size. Must be called before adding an edge.
         */
        auto resize(int size) -> void;

        /**
         * Add edges in both directions for each labeled edge.
         */
        auto add_edges(std::vector<std::tuple<int, int, std::string>> & edges ) -> void;

        auto add_edge(int a, int b) -> void;

        /**
         * Add edge in both directions.
         */
        auto add_edge(int a, int b, std::string label) -> void;

        /**
         * Add a directed edge from a to b, with a label.
         */
        auto add_directed_edge(int a, int b, std::string label) -> void;

        /**
         * Are vertices a and b adjacent?
         */
        auto adjacent(int a, int b) const -> bool;

        /**
         * What is the degree of a given vertex?
         */
        auto degree(int a) const -> int;

        /**
         * Set a vertex label.
         */
        auto set_vertex_label(int v, std::string_view label) -> void;

        /**
         * What is the label associated with a given vertex?
         */
        auto vertex_label(int v) const -> std::string_view;

        auto has_vertex_labels() const -> bool;

        /**
         * Set a vertex name (for output purposes).
         */
        auto set_vertex_name(int v, std::string_view label) -> void;

        /**
         * What is the name associated with a given vertex (for output purposes)?
         */
        auto vertex_name(int v) const -> std::string;

        /**
         * Find a given vertex by name.
         */
        auto vertex_from_name(std::string_view n) const -> std::optional<int>;

        /**
         * What is the label associated with a given edge?
         */
        auto edge_label(int a, int b) const -> std::multiset<std::string>;

        auto has_edge_labels() const -> bool;

        auto directed() const -> bool;

        using EdgesIterator = std::map<std::pair<int, int>, std::multiset<std::string>>::const_iterator;
        
		auto edges() const -> std::map<std::pair<int, int>, std::multiset<std::string> >;

        auto begin_edges() const -> EdgesIterator;

        auto end_edges() const -> EdgesIterator;

        auto for_each_edge(const std::function<auto (int, int, std::multiset<std::string>) -> void> &) const -> void;
};

#endif
