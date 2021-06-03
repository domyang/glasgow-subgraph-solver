/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_SUBGRAPH_SOLVER_GUARD_SRC_HOMOMORPHISM_MODEL_HH
#define GLASGOW_SUBGRAPH_SOLVER_GUARD_SRC_HOMOMORPHISM_MODEL_HH 1

#include "formats/input_graph.hh"
#include "svo_bitset.hh"
#include "homomorphism.hh"
#include "homomorphism_domain.hh"
#include "proof.hh"
#include "loooong.hh"
#include "equivalence.hh"

#include <memory>
#include <boost/functional/hash.hpp>

class HomomorphismModel
{
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        std::vector<std::vector<bool> > edge_label_compatibility;

        auto _build_exact_path_graphs(std::vector<SVOVector> & graph_rows, unsigned size, unsigned & idx,
                unsigned number_of_exact_path_graphs, bool directed) -> void;

        auto _build_distance3_graphs(std::vector<SVOVector> & graph_rows, unsigned size, unsigned & idx) -> void;

        auto _build_k4_graphs(std::vector<SVOVector> & graph_rows, unsigned size, unsigned & idx) -> void;

        auto _build_k4_graphs(std::vector<SVOVector> & graph_rows, unsigned size, unsigned & idx, std::string &str) -> void;
		auto _build_channel_graphs(std::vector<SVOVector> & graph_rows, unsigned & idx, const InputGraph &graph, std::string &str) -> void;

        auto _build_structural_equivalence(bool is_pattern, std::vector<HomomorphismDomain> &domains) -> void;

        auto _check_degree_compatibility(
                int p,
                int t,
                unsigned graphs_to_consider,
                std::vector<std::vector<std::vector<int> > > & patterns_ndss,
                std::vector<std::vector<std::optional<std::vector<int> > > > & targets_ndss,
                bool do_not_do_nds_yet
                ) const -> bool;


        auto _check_loop_compatibility(int p, int t) const -> bool;

        auto _check_label_compatibility(int p, int t) const -> bool;

        auto _check_vertex_label_compatibility(const int p, const int t) const -> bool;

		auto _check_multi_degree_compatibility(std::vector<HomomorphismDomain> &domains) const -> void;

        auto _check_nbr_compatibility(std::vector<HomomorphismDomain> &domains) const -> void;


        auto _multiset_item_counts(const std::multiset<std::string>&) const -> std::map<std::string, int>;

        auto _populate_degrees(std::vector<std::vector<int> > & degrees, const std::vector<SVOVector> & graph_rows, int size) -> void;

        auto _record_edge_labels(std::map<std::multiset<std::string>, int>& label_map, const InputGraph & graph, std::unordered_map<std::pair<int,int>,int, boost::hash<std::pair<int,int>>>& graph_edge_labels) -> void;

		auto _is_pattern_structurally_equivalent(int p, int q) const -> bool;
		auto _is_target_structurally_equivalent(int p, int q) const -> bool;

    public:
        using PatternAdjacencyBitsType = uint64_t;

        unsigned max_graphs;
        unsigned pattern_size, target_size;

        auto has_less_thans() const -> bool;
        auto has_occur_less_thans() const -> bool;
        std::vector<std::pair<unsigned, unsigned> > pattern_less_thans_in_convenient_order, target_occur_less_thans_in_convenient_order;

        HomomorphismModel(const InputGraph & target, const InputGraph & pattern, const HomomorphismParams & params);
        ~HomomorphismModel();

        auto pattern_vertex_for_proof(int v) const -> NamedVertex;
        auto target_vertex_for_proof(int v) const -> NamedVertex;

        auto prepare() -> bool;

        auto pattern_adjacency_bits(int p, int q) const -> PatternAdjacencyBitsType;
        auto pattern_graph_row(int g, int p) const -> const SVOVector &;

        auto forward_pattern_graph_row(int t) const -> const SVOVector &;
        auto reverse_pattern_graph_row(int t) const -> const SVOVector &;

        auto target_graph_row(int g, int t) const -> const SVOVector &;

        auto forward_target_graph_row(int t) const -> const SVOVector &;
        auto reverse_target_graph_row(int t) const -> const SVOVector &;

        auto pattern_degree(int g, int p) const -> unsigned;
        auto target_degree(int g, int t) const -> unsigned;
        auto largest_target_degree() const -> unsigned;

        auto has_vertex_labels() const -> bool;
        auto has_edge_labels() const -> bool;
        auto directed() const -> bool;
        auto pattern_vertex_label(int p) const -> int;
        auto target_vertex_label(int p) const -> int;
        auto pattern_edge_label(int p, int q) const -> int;
        auto target_edge_label(int t, int u) const -> int;

		auto is_pattern_equivalent(int p, int q) const -> bool;
		auto is_target_equivalent(int p, int q) const -> bool;

        auto get_target_equivalence() const -> const DisjointSet&;

		auto pattern_equivalence_multiplier() const -> loooong;
		auto target_equivalence_multiplier() const -> loooong;
        auto target_class_size(int t) const -> int;
        auto merge_target_classes(int x, int y) -> void;

		auto pattern_representative(int p) const -> int;
		auto target_representative(int t) const -> int;

        auto initialise_domains(std::vector<HomomorphismDomain> & domains) -> bool;
        auto restore_equivalence(DisjointSet &target_equivalence) -> void;

        auto get_target_num_used(int x) -> unsigned;
        auto up_target_num_used(int x) -> void;
        auto down_target_num_used(int x) -> void;

        auto check_edge_label_compatibility(const std::multiset<std::string>&, const std::multiset<std::string>&) const -> bool;
        auto check_edge_label_compatibility(const int t_v1, const int t_v2, const int p_lid) const -> bool;

        auto num_pattern_loops(int p) const -> int;
        auto num_target_loops(int t) const -> int;

        auto topology_filter(std::vector<HomomorphismDomain> &domains) const -> void;

        auto compute_stats(std::vector<std::map<std::string,std::vector<int>>> &stats, unsigned graph_size, 
                           const InputGraph &graph, std::vector<SVOVector> &graph_rows) -> void;

        auto stats_filter(std::vector<HomomorphismDomain> &domains) const -> void;
};

#endif
