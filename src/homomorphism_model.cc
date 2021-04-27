/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "homomorphism_model.hh"
#include "homomorphism_traits.hh"
#include "configuration.hh"
#include "equivalence.hh"
#include "loooong.hh"
#include "graph_equivalence.hh"

#include <algorithm>
#include <functional>
#include <queue>
#include <list>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

using std::greater;
using std::list;
using std::map;
using std::max;
using std::optional;
using std::pair;
using std::set;
using std::multiset;
using std::string;
using std::string_view;
using std::to_string;
using std::vector;

namespace
{
    auto calculate_n_shape_graphs(const HomomorphismParams & params) -> unsigned
    {
        return 1 +
            (supports_exact_path_graphs(params) ? params.number_of_exact_path_graphs : 0) +
            (supports_distance3_graphs(params) ? 1 : 0) +
            (supports_k4_graphs(params) ? 1 : 0);
    }
}

struct HomomorphismModel::Imp
{
    const HomomorphismParams & params;

	const InputGraph &pattern;
	const InputGraph &target;

    vector<PatternAdjacencyBitsType> pattern_adjacencies_bits;
    vector<SVOBitset> pattern_graph_rows, forward_pattern_graph_rows, reverse_pattern_graph_rows;
    vector<SVOBitset> target_graph_rows, forward_target_graph_rows, reverse_target_graph_rows;

    vector<vector<int> > patterns_degrees, targets_degrees;
	map<string,vector<int> > patterns_multi_degrees, targets_multi_degrees;
    int largest_target_degree = 0;
    bool has_less_thans = false, has_occur_less_thans = false, directed = false;

    vector<int> pattern_vertex_labels, target_vertex_labels, pattern_edge_labels, target_edge_labels;
    vector<int> pattern_loops, target_loops;

    DisjointSet pattern_equivalence;
    DisjointSet target_equivalence;

    vector<string> pattern_vertex_proof_names, target_vertex_proof_names;
    
	map<multiset<string>, int> pattern_edge_labels_map, target_edge_labels_map;
	
	set<string> channels;

    Imp(const HomomorphismParams & p, const InputGraph &pat, const InputGraph &tar ) :
        params(p), pattern(pat), target(tar)
    {
    }
};

HomomorphismModel::HomomorphismModel(const InputGraph & target, const InputGraph & pattern, const HomomorphismParams & params) :
    _imp(new Imp(params, pattern, target)),
    max_graphs(calculate_n_shape_graphs(params)),
    pattern_size(pattern.size()),
    target_size(target.size())
{


    if (max_graphs > 8 * sizeof(PatternAdjacencyBitsType))
        throw UnsupportedConfiguration{ "Supplemental graphs won't fit in the chosen bitset size" };

    if (_imp->params.proof) {
        for (int v = 0 ; v < pattern.size() ; ++v)
            _imp->pattern_vertex_proof_names.push_back(pattern.vertex_name(v));
        for (int v = 0 ; v < target.size() ; ++v)
            _imp->target_vertex_proof_names.push_back(target.vertex_name(v));
    }

    _imp->directed = pattern.directed();

	if (pattern.has_edge_labels())
	{
		// Map each unique edge_label to an integer.
		// Resize vector recording integers corresponding to each edge's label.
		//TODO: move line below into function?
		_imp->pattern_edge_labels.resize(pattern_size * pattern_size);
		// Fill edge_labels_map labels -> int and edge_labels with labels.
		_record_edge_labels(_imp->pattern_edge_labels_map, pattern, _imp->pattern_edge_labels);
		
		// Resize vector recording integers corresponding to each edge's label.
		_imp->target_edge_labels.resize(target_size * target_size);
		// Fill edge_labels_map labels -> int and edge_labels with labels.
		_record_edge_labels(_imp->target_edge_labels_map, target, _imp->target_edge_labels);

		for (auto it = pattern.begin_edges(); it != pattern.end_edges(); it++)
			for (auto str : it->second)
				_imp->channels.emplace(str);

		max_graphs += _imp->channels.size();
		for (auto str : _imp->channels)
		{
			vector<int> p_degrees(pattern_size, 0);
			vector<int> t_degrees(target_size, 0);
			_imp->patterns_multi_degrees.emplace(str, p_degrees);
			_imp->targets_multi_degrees.emplace(str, t_degrees);
		}
	}

    _imp->patterns_degrees.resize(max_graphs);
    _imp->targets_degrees.resize(max_graphs);

    // recode pattern to a bit graph, and strip out loops
    _imp->pattern_graph_rows.resize(pattern_size * max_graphs, SVOBitset(pattern_size, 0));
    _imp->pattern_loops.resize(pattern_size);
    for (unsigned i = 0 ; i < pattern_size ; ++i) {
        for (unsigned j = 0 ; j < pattern_size ; ++j) {
            if (pattern.adjacent(i, j)) {
                if (i == j)
                    _imp->pattern_loops[i] += 1;
                else
                    _imp->pattern_graph_rows[i * max_graphs + 0].set(j);
            }
        }
    }
	


    // re-encode and store pattern labels
    map<string, int> vertex_labels_map;
    int next_vertex_label = 1;
    if (pattern.has_vertex_labels()) {
        for (unsigned i = 0 ; i < pattern_size ; ++i) {
            if (vertex_labels_map.emplace(pattern.vertex_label(i), next_vertex_label).second)
                ++next_vertex_label;
        }

        _imp->pattern_vertex_labels.resize(pattern_size);
        for (unsigned i = 0 ; i < pattern_size ; ++i)
            _imp->pattern_vertex_labels[i] = vertex_labels_map.find(string{ pattern.vertex_label(i) })->second;
		
		// target vertex labels
        for (unsigned i = 0 ; i < target_size ; ++i) {
            if (vertex_labels_map.emplace(target.vertex_label(i), next_vertex_label).second)
                ++next_vertex_label;
        }

        _imp->target_vertex_labels.resize(target_size);
        for (unsigned i = 0 ; i < target_size ; ++i)
            _imp->target_vertex_labels[i] = vertex_labels_map.find(string{ target.vertex_label(i) })->second;
    }

//    // re-encode and store edge labels
//    map<string, int> edge_labels_map;
//    int next_edge_label = 1;
//    if (pattern.has_edge_labels()) {
//        _imp->pattern_edge_labels.resize(pattern_size * pattern_size);
//        for (unsigned i = 0 ; i < pattern_size ; ++i)
//            for (unsigned j = 0 ; j < pattern_size ; ++j)
//                if (pattern.adjacent(i, j)) {
//                    auto r = edge_labels_map.emplace(pattern.edge_label(i, j), next_edge_label);
//                    if (r.second)
//                        ++next_edge_label;
//                    _imp->pattern_edge_labels[i * pattern_size + j] = r.first->second;
//                }
//    }
	
    // // TODO: Find better way to get indices.
    // Form edge compatibility matrix.
    // std::cout<< "Compat table" << std::endl;
    edge_label_compatibility.resize(_imp->pattern_edge_labels_map.size(), vector<bool>(_imp->target_edge_labels_map.size()));
    for (const auto& [labels1, label1_id] : _imp->pattern_edge_labels_map) {
        for (const auto& [labels2, label2_id] : _imp->target_edge_labels_map) {
            // TODO: Deal with the induced case.
            edge_label_compatibility[label1_id][label2_id] = check_edge_label_compatibility(labels1, labels2);
        }
    }

    // recode target to a bit graph, and take out loops
    _imp->target_graph_rows.resize(target_size * max_graphs, SVOBitset{ target_size, 0 });
    _imp->target_loops.resize(target_size);
    for (auto e = target.begin_edges(), e_end = target.end_edges() ; e != e_end ; ++e) {
        if (e->first.first == e->first.second)
            _imp->target_loops[e->first.first] += 1;
        else
            _imp->target_graph_rows[e->first.first * max_graphs + 0].set(e->first.second);
    }

    // if directed, do both directions
    if (pattern.directed()) {
        _imp->forward_pattern_graph_rows.resize(pattern_size, SVOBitset{ pattern_size, 0 });
        _imp->reverse_pattern_graph_rows.resize(pattern_size, SVOBitset{ pattern_size, 0 });
        for (auto e = pattern.begin_edges(), e_end = pattern.end_edges() ; e != e_end ; ++e) {
            if (e->first.first != e->first.second) {
                _imp->forward_pattern_graph_rows[e->first.first].set(e->first.second);
                _imp->reverse_pattern_graph_rows[e->first.second].set(e->first.first);
            }
        }

        _imp->forward_target_graph_rows.resize(target_size, SVOBitset{ target_size, 0 });
        _imp->reverse_target_graph_rows.resize(target_size, SVOBitset{ target_size, 0 });
        for (auto e = target.begin_edges(), e_end = target.end_edges() ; e != e_end ; ++e) {
            if (e->first.first != e->first.second) {
                _imp->forward_target_graph_rows[e->first.first].set(e->first.second);
                _imp->reverse_target_graph_rows[e->first.second].set(e->first.first);
            }
        }
    }


//    // target edge labels
//    if (pattern.has_edge_labels()) {
//        _imp->target_edge_labels.resize(target_size * target_size);
//        target.for_each_edge([&] (int f, int t, string_view l) {
//            auto r = edge_labels_map.emplace(l, next_edge_label);
//            if (r.second)
//                ++next_edge_label;
//
//            _imp->target_edge_labels[f * target_size + t] = r.first->second;
//        });
//    }

    auto decode = [&] (const InputGraph & g, string_view s) -> int {
        auto n = g.vertex_from_name(s);
        if (! n)
            throw UnsupportedConfiguration{ "No vertex named '" + string{ s } + "'" };
        return *n;
    };

    // pattern less than constraints
    if (! _imp->params.pattern_less_constraints.empty()) {
        _imp->has_less_thans = true;
        list<pair<unsigned, unsigned> > pattern_less_thans_in_wrong_order;
        for (auto & [ a, b ] : _imp->params.pattern_less_constraints) {
            auto a_decoded = decode(pattern, a), b_decoded = decode(pattern, b);
            pattern_less_thans_in_wrong_order.emplace_back(a_decoded, b_decoded);
        }

        // put them in a convenient order, so we don't need a propagation loop
        while (! pattern_less_thans_in_wrong_order.empty()) {
            bool loop_detect = true;
            set<unsigned> cannot_order_yet;
            for (auto & [ _, b ] : pattern_less_thans_in_wrong_order)
                cannot_order_yet.emplace(b);
            for (auto p = pattern_less_thans_in_wrong_order.begin() ; p != pattern_less_thans_in_wrong_order.end() ; ) {
                if (cannot_order_yet.count(p->first))
                    ++p;
                else {
                    loop_detect = false;
                    pattern_less_thans_in_convenient_order.push_back(*p);
                    pattern_less_thans_in_wrong_order.erase(p++);
                }
            }

            if (loop_detect)
                throw UnsupportedConfiguration{ "Pattern less than constraints form a loop" };
        }
    }

    // target less than constraints
    if (! _imp->params.target_occur_less_constraints.empty()) {
        _imp->has_occur_less_thans = true;
        list<pair<unsigned, unsigned> > target_occur_less_thans_in_wrong_order;
        for (auto & [ a, b ] : _imp->params.target_occur_less_constraints) {
            auto a_decoded = decode(target, a), b_decoded = decode(target, b);
            target_occur_less_thans_in_wrong_order.emplace_back(a_decoded, b_decoded);
        }

        // put them in a convenient order, so we don't need a propagation loop
        while (! target_occur_less_thans_in_wrong_order.empty()) {
            bool loop_detect = true;
            set<unsigned> cannot_order_yet;
            for (auto & [ _, b ] : target_occur_less_thans_in_wrong_order)
                cannot_order_yet.emplace(b);
            for (auto t = target_occur_less_thans_in_wrong_order.begin() ; t != target_occur_less_thans_in_wrong_order.end() ; ) {
                if (cannot_order_yet.count(t->first))
                    ++t;
                else {
                    loop_detect = false;
                    target_occur_less_thans_in_convenient_order.push_back(*t);
                    target_occur_less_thans_in_wrong_order.erase(t++);
                }
            }

            if (loop_detect)
                throw UnsupportedConfiguration{ "Target less than constraints form a loop" };
        }
    }
}

/** Record map from label sets to integers and vertex adjacencies to integers.*/
auto HomomorphismModel::_record_edge_labels(map<multiset<string>, int>& label_map, const InputGraph & graph, vector<int>& graph_edge_labels) -> void
{
    int next_edge_label = 0;
    for (auto e = graph.begin_edges(), e_end = graph.end_edges() ; e != e_end ; ++e) {
        auto r = label_map.emplace(e->second, next_edge_label);
        // Increase count if we have seen a new edge.
        if (r.second)
            ++next_edge_label;
        // Record label_set integer code.
        graph_edge_labels[e->first.first * graph.size() + e->first.second] = r.first->second;
    }
}

auto HomomorphismModel::_multiset_item_counts(const multiset<string>& labels) const -> map<string, int>
{
    map<string, int> label_counts;
    for (const auto & label : labels) {
        if (!label_counts.emplace(label, 1).second)
            label_counts.emplace(label, 1).first->second += 1;
    }
    return label_counts;
}

/** Check that at least as many of each label occur for the target as pattern edge.
TODO: Change to exact count for induced case.
*/
auto HomomorphismModel::check_edge_label_compatibility(const multiset<string>& labels1, const multiset<string>& labels2) const -> bool
{
    // Map labels to the number of occurences for each multiset.
    map<string, int> label_counts1 = _multiset_item_counts(labels1);
    map<string, int> label_counts2 = _multiset_item_counts(labels2);

    // Check compatibility for each label.
    for (const auto & [label, count] : label_counts1) {
        if (label_counts2.find(label) == label_counts2.end() || count > label_counts2[label])
            return false;
    }
    return true;
}

auto HomomorphismModel::check_edge_label_compatibility(const int t_v1, const int t_v2, const int p_lid) const -> bool
{
    int t_lid = target_edge_label(t_v1, t_v2);
    return edge_label_compatibility[p_lid][t_lid];
}

HomomorphismModel::~HomomorphismModel() = default;

auto HomomorphismModel::_check_label_compatibility(int p, int t) const -> bool
{
    if (! has_vertex_labels())
        return true;
    else
        return pattern_vertex_label(p) == target_vertex_label(t);
}

auto HomomorphismModel::_check_loop_compatibility(int p, int t) const -> bool
{
    if (num_pattern_loops(p) > num_target_loops(t))
        return false;
    else if (_imp->params.induced && (num_pattern_loops(p) != num_target_loops(t)))
        return false;

    return true;
}

auto HomomorphismModel::_check_degree_compatibility(
        int p,
        int t,
        unsigned graphs_to_consider,
        vector<vector<vector<int> > > & patterns_ndss,
        vector<vector<optional<vector<int> > > > & targets_ndss,
        bool do_not_do_nds_yet
        ) const -> bool
{
    if (! degree_and_nds_are_preserved(_imp->params))
        return true;

    for (unsigned g = 0 ; g < graphs_to_consider ; ++g) {
        if (target_degree(g, t) < pattern_degree(g, p)) {
            // not ok, degrees differ
            if (_imp->params.proof) {
                // get the actual neighbours of p and t, in their original terms
                vector<int> n_p, n_t;

                auto np = pattern_graph_row(g, p);
                for (unsigned j = 0 ; j < pattern_size ; ++j)
                    if (np.test(j))
                        n_p.push_back(j);

                auto nt = target_graph_row(g, t);
                for (auto j = nt.find_first() ; j != decltype(nt)::npos ; j = nt.find_first()) {
                    nt.reset(j);
                    n_t.push_back(j);
                }

                _imp->params.proof->incompatible_by_degrees(g, pattern_vertex_for_proof(p), n_p,
                        target_vertex_for_proof(t), n_t);
            }
            return false;
        }
        else if (degree_and_nds_are_exact(_imp->params, pattern_size, target_size)
                && target_degree(g, t) != pattern_degree(g, p)) {
            // not ok, degrees must be exactly the same
            return false;
        }
    }
    if (_imp->params.no_nds || do_not_do_nds_yet)
        return true;

    // full compare of neighbourhood degree sequences
    if (! targets_ndss.at(0).at(t)) {
        for (unsigned g = 0 ; g < graphs_to_consider ; ++g) {
            targets_ndss.at(g).at(t) = vector<int>{};
            auto ni = target_graph_row(g, t);
            for (auto j = ni.find_first() ; j != decltype(ni)::npos ; j = ni.find_first()) {
                ni.reset(j);
                targets_ndss.at(g).at(t)->push_back(target_degree(g, j));
            }
            sort(targets_ndss.at(g).at(t)->begin(), targets_ndss.at(g).at(t)->end(), greater<int>());
        }
    }

    for (unsigned g = 0 ; g < graphs_to_consider ; ++g) {
        for (unsigned x = 0 ; x < patterns_ndss.at(g).at(p).size() ; ++x) {
            if (targets_ndss.at(g).at(t)->at(x) < patterns_ndss.at(g).at(p).at(x)) {
                if (_imp->params.proof) {
                    vector<int> p_subsequence, t_subsequence, t_remaining;

                    // need to know the NDS together with the actual vertices
                    vector<pair<int, int> > p_nds, t_nds;

                    auto np = pattern_graph_row(g, p);
                    for (auto w = np.find_first() ; w != decltype(np)::npos ; w = np.find_first()) {
                        np.reset(w);
                        p_nds.emplace_back(w, pattern_graph_row(g, w).count());
                    }

                    auto nt = target_graph_row(g, t);
                    for (auto w = nt.find_first() ; w != decltype(nt)::npos ; w = nt.find_first()) {
                        nt.reset(w);
                        t_nds.emplace_back(w, target_graph_row(g, w).count());
                    }

                    sort(p_nds.begin(), p_nds.end(), [] (const pair<int, int> & a, const pair<int, int> & b) {
                            return a.second > b.second; });
                    sort(t_nds.begin(), t_nds.end(), [] (const pair<int, int> & a, const pair<int, int> & b) {
                            return a.second > b.second; });

                    for (unsigned y = 0 ; y <= x ; ++y) {
                        p_subsequence.push_back(p_nds[y].first);
                        t_subsequence.push_back(t_nds[y].first);
                    }
                    for (unsigned y = x + 1 ; y < t_nds.size() ; ++y)
                        t_remaining.push_back(t_nds[y].first);

                    _imp->params.proof->incompatible_by_nds(g, pattern_vertex_for_proof(p),
                            target_vertex_for_proof(t), p_subsequence, t_subsequence, t_remaining);
                }
                return false;
            }
            else if (degree_and_nds_are_exact(_imp->params, pattern_size, target_size)
                    && targets_ndss.at(g).at(t)->at(x) != patterns_ndss.at(g).at(p).at(x))
                return false;
        }
    }

    return true;
}

auto HomomorphismModel::_check_multi_degree_compatibility(
        int p,
        int t,
        vector<vector<vector<int> > > & patterns_mdss,
        vector<vector<vector<int> > > & targets_mdss
        ) const -> bool
{
    if (! degree_and_nds_are_preserved(_imp->params))
		return true;
	
	for (auto str : _imp->channels)
	{
		if (_imp->targets_multi_degrees.at(str).at(t) < _imp->patterns_multi_degrees.at(str).at(p)) {
			return false;
		}
		else if (degree_and_nds_are_exact(_imp->params, pattern_size, target_size)
				&& _imp->targets_multi_degrees.at(str).at(t) != _imp->patterns_multi_degrees.at(str).at(p)) {
			// not ok, degrees must be exactly the same
			return false;
		}
	}
    if (_imp->params.no_nds)
        return true;

    for (unsigned i = 0; i < _imp->channels.size(); i++) {
        for (unsigned x = 0 ; x < patterns_mdss.at(i).at(p).size() ; ++x) {
            if (targets_mdss.at(i).at(t).at(x) < patterns_mdss.at(i).at(p).at(x)) {
                return false;
            }
            else if (degree_and_nds_are_exact(_imp->params, pattern_size, target_size)
                    && targets_mdss.at(i).at(t).at(x) != patterns_mdss.at(i).at(p).at(x))
                return false;
        }
    }
	
    return true;
}

auto HomomorphismModel::initialise_domains(vector<HomomorphismDomain> & domains) const -> bool
{
    unsigned graphs_to_consider = max_graphs;

    /* pattern and target neighbourhood degree sequences */
    vector<vector<vector<int> > > patterns_ndss(graphs_to_consider);
    vector<vector<optional<vector<int> > > > targets_ndss(graphs_to_consider);

    vector<vector<vector<int> > > patterns_mdss(_imp->channels.size());
    vector<vector<vector<int> > > targets_mdss(_imp->channels.size());

    if (degree_and_nds_are_preserved(_imp->params) && ! _imp->params.no_nds) {
        for (unsigned g = 0 ; g < graphs_to_consider ; ++g) {
            patterns_ndss.at(g).resize(pattern_size);
            targets_ndss.at(g).resize(target_size);
        }

        for (unsigned g = 0 ; g < graphs_to_consider ; ++g) {
            for (unsigned i = 0 ; i < pattern_size ; ++i) {
                auto ni = pattern_graph_row(g, i);
                for (auto j = ni.find_first() ; j != decltype(ni)::npos ; j = ni.find_first()) {
                    ni.reset(j);
                    patterns_ndss.at(g).at(i).push_back(pattern_degree(g, j));
                }
                sort(patterns_ndss.at(g).at(i).begin(), patterns_ndss.at(g).at(i).end(), greater<int>());
            }
        }

		if (has_edge_labels())
		{
			int ch = 0;
			for (auto str : _imp->channels)
			{
				patterns_mdss.at(ch).resize(pattern_size);
				targets_mdss.at(ch).resize(target_size);
				
				for (unsigned i = 0 ; i < pattern_size ; ++i) {
					auto ni = pattern_graph_row(0, i);
					for (auto j : ni) {
						patterns_mdss.at(ch).at(i).push_back(_imp->patterns_multi_degrees.at(str).at(j));
					}
					sort(patterns_mdss.at(ch).at(i).begin(), patterns_mdss.at(ch).at(i).end(), greater<int>());
				}

				for (unsigned i = 0 ; i < target_size ; ++i) {
					auto ni = target_graph_row(0, i);
					for (auto j : ni) {
						targets_mdss.at(ch).at(i).push_back(_imp->targets_multi_degrees.at(str).at(j));
					}
					sort(targets_mdss.at(ch).at(i).begin(), targets_mdss.at(ch).at(i).end(), greater<int>());
				}
				ch++;
			}
		}
    }

    for (unsigned i = 0 ; i < pattern_size ; ++i) {
        domains.at(i).v = i;
        domains.at(i).values.reset();

        for (unsigned j = 0 ; j < target_size ; ++j) {
            bool ok = true;

            if (! _check_label_compatibility(i, j))
                ok = false;
            else if (! _check_loop_compatibility(i, j))
                ok = false;
            else if (! _check_degree_compatibility(i, j, graphs_to_consider, patterns_ndss, targets_ndss, _imp->params.proof.get()))
                ok = false;
			else if (has_edge_labels() && ! _check_multi_degree_compatibility(i, j, patterns_mdss, targets_mdss))
				ok = false;

            if (ok)
                domains.at(i).values.set(j);
        }

        domains.at(i).count = domains.at(i).values.count();
        if (0 == domains.at(i).count)
            return false;
    }

    // for proof logging, we need degree information before we can output nds proofs
    if (_imp->params.proof && degree_and_nds_are_preserved(_imp->params) && ! _imp->params.no_nds) {
        for (unsigned i = 0 ; i < pattern_size ; ++i) {
            for (unsigned j = 0 ; j < target_size ; ++j) {
                if (domains.at(i).values.test(j) &&
                        ! _check_degree_compatibility(i, j, graphs_to_consider, patterns_ndss, targets_ndss, false)) {
                    domains.at(i).values.reset(j);
                    if (0 == --domains.at(i).count)
                        return false;
                }
            }
        }
    }

    // quick sanity check that we have enough values
    if (is_nonshrinking(_imp->params)) {
        SVOBitset domains_union{ target_size, 0 };
        for (auto & d : domains)
            domains_union |= d.values;

        unsigned domains_union_popcount = domains_union.count();
        if (domains_union_popcount < unsigned(pattern_size)) {
            if (_imp->params.proof) {
                vector<int> hall_lhs, hall_rhs;
                for (auto & d : domains)
                    hall_lhs.push_back(d.v);
                auto dd = domains_union;
                for (auto v = dd.find_first() ; v != decltype(dd)::npos ; v = dd.find_first()) {
                    dd.reset(v);
                    hall_rhs.push_back(v);
                }
                _imp->params.proof->emit_hall_set_or_violator(hall_lhs, hall_rhs);
            }
            return false;
        }
    }

    for (auto & d : domains) {
        d.count = d.values.count();
        if (0 == d.count && _imp->params.proof) {
            _imp->params.proof->initial_domain_is_empty(d.v);
            return false;
        }
    }

    if (_imp->params.lackey) {
        // If we're dealing with a model from Essence, it's possible some values will
        // be completely eliminated from the upper and lower bounds of certain domains,
        // in which case they won't show up as being deleted during propagation.
        bool wipeout = false;
        if (! _imp->params.lackey->reduce_initial_bounds([&] (int p, int t) -> void {
                for (auto & d : domains)
                    if (d.v == unsigned(p)) {
                        if (d.values.test(t)) {
                            d.values.reset(t);
                            if (0 == --d.count)
                                wipeout = true;
                        }
                        break;
                    }
                }) || wipeout) {
            return false;
        }
    }

    return true;
}

auto HomomorphismModel::pattern_vertex_for_proof(int v) const -> NamedVertex
{
    if (v < 0 || unsigned(v) >= _imp->pattern_vertex_proof_names.size())
        throw ProofError{ "Oops, there's a bug: v out of range in pattern" };
    return pair{ v, _imp->pattern_vertex_proof_names[v] };
}

auto HomomorphismModel::target_vertex_for_proof(int v) const -> NamedVertex
{
    if (v < 0 || unsigned(v) >= _imp->target_vertex_proof_names.size())
        throw ProofError{ "Oops, there's a bug: v out of range in target" };
    return pair{ v, _imp->target_vertex_proof_names[v] };
}

auto HomomorphismModel::prepare() -> bool
{
    if (is_nonshrinking(_imp->params) && (pattern_size > target_size))
        return false;

    // pattern and target degrees, for the main graph
    _imp->patterns_degrees.at(0).resize(pattern_size);
    _imp->targets_degrees.at(0).resize(target_size);

    for (unsigned i = 0 ; i < pattern_size ; ++i)
	{
        _imp->patterns_degrees.at(0).at(i) = _imp->pattern_graph_rows[i * max_graphs + 0].count();
	}

	for (unsigned i = 0 ; i < target_size ; ++i)
        _imp->targets_degrees.at(0).at(i) = _imp->target_graph_rows[i * max_graphs + 0].count();

	if (has_edge_labels())
	{
		for (unsigned i = 0; i < pattern_size; i++)
			for (auto j : _imp->pattern_graph_rows[i * max_graphs + 0])
				for (auto label : _imp->pattern.edge_label(i, j))
					_imp->patterns_multi_degrees.at(label).at(i)++;

		for (unsigned i = 0; i < target_size; i++)
			for (auto j : _imp->target_graph_rows[i * max_graphs + 0])
				for (auto label : _imp->target.edge_label(i, j))
					_imp->targets_multi_degrees.at(label).at(i)++;
	}



    if (global_degree_is_preserved(_imp->params)) {
        vector<pair<int, int> > p_gds, t_gds;
        for (unsigned i = 0 ; i < pattern_size ; ++i)
            p_gds.emplace_back(i, _imp->patterns_degrees.at(0).at(i));
        for (unsigned i = 0 ; i < target_size ; ++i)
            t_gds.emplace_back(i, _imp->targets_degrees.at(0).at(i));

        sort(p_gds.begin(), p_gds.end(), [] (const pair<int, int> & a, const pair<int, int> & b) {
                return a.second > b.second; });
        sort(t_gds.begin(), t_gds.end(), [] (const pair<int, int> & a, const pair<int, int> & b) {
                return a.second > b.second; });

        for (unsigned i = 0 ; i < p_gds.size() ; ++i)
            if (p_gds.at(i).second > t_gds.at(i).second) {
                if (_imp->params.proof) {
                    for (unsigned p = 0 ; p <= i ; ++p) {
                        vector<int> n_p;
                        auto np = _imp->pattern_graph_rows[p_gds.at(p).first * max_graphs + 0];
                        for (unsigned j = 0 ; j < pattern_size ; ++j)
                            if (np.test(j))
                                n_p.push_back(j);

                        for (unsigned t = i ; t < t_gds.size() ; ++t) {
                            vector<int> n_t;
                            auto nt = _imp->target_graph_rows[t_gds.at(t).first * max_graphs + 0];
                            for (auto j = nt.find_first() ; j != decltype(nt)::npos ; j = nt.find_first()) {
                                nt.reset(j);
                                n_t.push_back(j);
                            }

                            _imp->params.proof->incompatible_by_degrees(0,
                                    pattern_vertex_for_proof(p_gds.at(p).first), n_p,
                                    target_vertex_for_proof(t_gds.at(t).first), n_t);
                        }
                    }

                    vector<int> patterns, targets;
                    for (unsigned p = 0 ; p <= i ; ++p)
                        patterns.push_back(p_gds.at(p).first);
                    for (unsigned t = 0 ; t < i ; ++t)
                        targets.push_back(t_gds.at(t).first);

                    _imp->params.proof->emit_hall_set_or_violator(patterns, targets);
                }
                return false;
            }
    }

    unsigned next_pattern_supplemental = 1, next_target_supplemental = 1;
    // build exact path graphs
    if (supports_exact_path_graphs(_imp->params)) {
        _build_exact_path_graphs(_imp->pattern_graph_rows, pattern_size, next_pattern_supplemental, _imp->params.number_of_exact_path_graphs, _imp->directed);
        _build_exact_path_graphs(_imp->target_graph_rows, target_size, next_target_supplemental, _imp->params.number_of_exact_path_graphs, _imp->directed);

        if (_imp->params.proof) {
            for (int g = 1 ; g <= _imp->params.number_of_exact_path_graphs ; ++g) {
                for (unsigned p = 0 ; p < pattern_size ; ++p) {
                    for (unsigned q = 0 ; q < pattern_size ; ++q) {
                        if (p == q || ! _imp->pattern_graph_rows[p * max_graphs + g].test(q))
                            continue;

                        auto named_p = pattern_vertex_for_proof(p);
                        auto named_q = pattern_vertex_for_proof(q);

                        auto n_p_q = _imp->pattern_graph_rows[p * max_graphs + 0];
                        n_p_q &= _imp->pattern_graph_rows[q * max_graphs + 0];
                        vector<NamedVertex> between_p_and_q;
                        for (auto v = n_p_q.find_first() ; v != decltype(n_p_q)::npos ; v = n_p_q.find_first()) {
                            n_p_q.reset(v);
                            between_p_and_q.push_back(pattern_vertex_for_proof(v));
                            if (between_p_and_q.size() >= unsigned(g))
                                break;
                        }

                        for (unsigned t = 0 ; t < target_size ; ++t) {
                            auto named_t = target_vertex_for_proof(t);

                            vector<NamedVertex> named_n_t, named_d_n_t;
                            vector<pair<NamedVertex, vector<NamedVertex> > > named_two_away_from_t;
                            auto n_t = _imp->target_graph_rows[t * max_graphs + 0];
                            for (auto w = n_t.find_first() ; w != decltype(n_t)::npos ; w = n_t.find_first()) {
                                n_t.reset(w);
                                named_n_t.push_back(target_vertex_for_proof(w));
                            }

                            auto nd_t = _imp->target_graph_rows[t * max_graphs + g];
                            for (auto w = nd_t.find_first() ; w != decltype(nd_t)::npos ; w = nd_t.find_first()) {
                                nd_t.reset(w);
                                named_d_n_t.push_back(target_vertex_for_proof(w));
                            }

                            auto n2_t = _imp->target_graph_rows[t * max_graphs + 1];
                            for (auto w = n2_t.find_first() ; w != decltype(n2_t)::npos ; w = n2_t.find_first()) {
                                n2_t.reset(w);
                                auto n_t_w = _imp->target_graph_rows[w * max_graphs + 0];
                                n_t_w &= _imp->target_graph_rows[t * max_graphs + 0];
                                vector<NamedVertex> named_n_t_w;
                                for (auto x = n_t_w.find_first() ; x != decltype(n_t_w)::npos ; x = n_t_w.find_first()) {
                                    n_t_w.reset(x);
                                    named_n_t_w.push_back(target_vertex_for_proof(x));
                                }
                                named_two_away_from_t.emplace_back(target_vertex_for_proof(w), named_n_t_w);
                            }

                            _imp->params.proof->create_exact_path_graphs(g, named_p, named_q, between_p_and_q,
                                    named_t, named_n_t, named_two_away_from_t, named_d_n_t);
                        }
                    }
                }
            }
        }
    }

    if (supports_distance3_graphs(_imp->params)) {
        _build_distance3_graphs(_imp->pattern_graph_rows, pattern_size, next_pattern_supplemental);
        _build_distance3_graphs(_imp->target_graph_rows, target_size, next_target_supplemental);
    }

    if (supports_k4_graphs(_imp->params)) {
        _build_k4_graphs(_imp->pattern_graph_rows, pattern_size, next_pattern_supplemental);
        _build_k4_graphs(_imp->target_graph_rows, target_size, next_target_supplemental);
    }

	if (has_edge_labels())
	{
		for (auto str : _imp->channels)
		{
			_build_channel_graphs(_imp->pattern_graph_rows, pattern_size, next_pattern_supplemental, _imp->pattern, str);
			_build_channel_graphs(_imp->target_graph_rows, target_size, next_target_supplemental, _imp->target, str);
		}
	}

    if (next_pattern_supplemental != max_graphs || next_target_supplemental != max_graphs)
        throw UnsupportedConfiguration{ "something has gone wrong with supplemental graph indexing: " + to_string(next_pattern_supplemental)
            + " " + to_string(next_target_supplemental) + " " + to_string(max_graphs) };

    // pattern and target degrees, for supplemental graphs
    for (unsigned g = 1 ; g < max_graphs ; ++g) {
        _imp->patterns_degrees.at(g).resize(pattern_size);
        _imp->targets_degrees.at(g).resize(target_size);
    }

    for (unsigned g = 1 ; g < max_graphs ; ++g) {
        for (unsigned i = 0 ; i < pattern_size ; ++i)
            _imp->patterns_degrees.at(g).at(i) = _imp->pattern_graph_rows[i * max_graphs + g].count();

        for (unsigned i = 0 ; i < target_size ; ++i)
            _imp->targets_degrees.at(g).at(i) = _imp->target_graph_rows[i * max_graphs + g].count();
    }

    for (unsigned i = 0 ; i < target_size ; ++i)
        _imp->largest_target_degree = max(_imp->largest_target_degree, _imp->targets_degrees[0][i]);

    // pattern adjacencies, compressed
    _imp->pattern_adjacencies_bits.resize(pattern_size * pattern_size);
    for (unsigned g = 0 ; g < max_graphs ; ++g)
        for (unsigned i = 0 ; i < pattern_size ; ++i)
            for (unsigned j = 0 ; j < pattern_size ; ++j)
                if (_imp->pattern_graph_rows[i * max_graphs + g].test(j))
                    _imp->pattern_adjacencies_bits[i * pattern_size + j] |= (1u << g);

    if (_imp->params.pattern_equivalence == PatternEquivalence::Structural)
        _build_structural_equivalence(true);
    if (_imp->params.target_equivalence != TargetEquivalence::None)
        _build_structural_equivalence(false);

    return true;
}

auto HomomorphismModel::_build_exact_path_graphs(vector<SVOBitset> & graph_rows, unsigned size, unsigned & idx,
        unsigned number_of_exact_path_graphs, bool directed) -> void
{
    vector<vector<unsigned> > path_counts(size, vector<unsigned>(size, 0));

    // count number of paths from w to v (unless directed, only w >= v, so not v to w)
    for (unsigned v = 0 ; v < size ; ++v) {
        auto nv = graph_rows[v * max_graphs + 0];
        for (auto c = nv.find_first() ; c != decltype(nv)::npos ; c = nv.find_first()) {
            nv.reset(c);
            auto nc = graph_rows[c * max_graphs + 0];
            for (auto w = nc.find_first() ; w != decltype(nc)::npos && (directed ? true : w <= v) ; w = nc.find_first()) {
                nc.reset(w);
                ++path_counts[v][w];
            }
        }
    }

    for (unsigned v = 0 ; v < size ; ++v) {
        for (unsigned w = (directed ? 0 : v) ; w < size ; ++w) {
            // unless directed, w to v, not v to w, see above
            unsigned path_count = path_counts[w][v];
            for (unsigned p = 1 ; p <= number_of_exact_path_graphs ; ++p) {
                if (path_count >= p) {
                    graph_rows[v * max_graphs + idx + p - 1].set(w);
                    if (! directed)
                        graph_rows[w * max_graphs + idx + p - 1].set(v);
                }
            }
        }
    }

    idx += number_of_exact_path_graphs;
}

auto HomomorphismModel::_build_distance3_graphs(vector<SVOBitset> & graph_rows, unsigned size, unsigned & idx) -> void
{
    for (unsigned v = 0 ; v < size ; ++v) {
        auto nv = graph_rows[v * max_graphs + 0];
        for (auto c = nv.find_first() ; c != decltype(nv)::npos ; c = nv.find_first()) {
            nv.reset(c);
            auto nc = graph_rows[c * max_graphs + 0];
            for (auto w = nc.find_first() ; w != decltype(nc)::npos ; w = nc.find_first()) {
                nc.reset(w);
                // v--c--w so v is within distance 3 of w's neighbours
                graph_rows[v * max_graphs + idx] |= graph_rows[w * max_graphs + 0];
            }
        }
    }

    ++idx;
}

auto HomomorphismModel::_build_k4_graphs(vector<SVOBitset> & graph_rows, unsigned size, unsigned & idx) -> void
{
    for (unsigned v = 0 ; v < size ; ++v) {
        auto nv = graph_rows[v * max_graphs + 0];
        for (unsigned w = 0 ; w < v ; ++w) {
            if (nv.test(w)) {
                // are there two common neighbours with an edge between them?
                auto common_neighbours = graph_rows[w * max_graphs + 0];
                common_neighbours &= nv;
                common_neighbours.reset(v);
                common_neighbours.reset(w);
                auto count = common_neighbours.count();
                if (count >= 2) {
                    bool done = false;
                    auto cn1 = common_neighbours;
                    for (auto x = cn1.find_first() ; x != decltype(cn1)::npos && ! done ; x = cn1.find_first()) {
                        cn1.reset(x);
                        auto cn2 = common_neighbours;
                        for (auto y = cn2.find_first() ; y != decltype(cn2)::npos && ! done ; y = cn2.find_first()) {
                            cn2.reset(y);
                            if (v != w && v != x && v != y && w != x && w != y && graph_rows[x * max_graphs + 0].test(y)) {
                                graph_rows[v * max_graphs + idx].set(w);
                                graph_rows[w * max_graphs + idx].set(v);
                                done = true;
                            }
                        }
                    }
                }
            }
        }
    }

    ++idx;
}

auto HomomorphismModel::_build_channel_graphs(vector<SVOBitset> & graph_rows, unsigned size, unsigned & idx, const InputGraph &graph, string &str) -> void
{
	for (auto it = graph.begin_edges(); it != graph.end_edges(); it++)
	{
		int src = it->first.first;
		int dst = it->first.second;
		if (it->second.find(str) != it->second.end())
			graph_rows[src * max_graphs + idx].set(dst);
    }

    ++idx;
}

auto HomomorphismModel::pattern_adjacency_bits(int p, int q) const -> PatternAdjacencyBitsType
{
    return _imp->pattern_adjacencies_bits[pattern_size * p + q];
}

auto HomomorphismModel::pattern_graph_row(int g, int p) const -> const SVOBitset &
{
    return _imp->pattern_graph_rows[p * max_graphs + g];
}

auto HomomorphismModel::forward_pattern_graph_row(int p) const -> const SVOBitset &
{
    return _imp->forward_pattern_graph_rows[p];
}

auto HomomorphismModel::reverse_pattern_graph_row(int p) const -> const SVOBitset &
{
    return _imp->reverse_pattern_graph_rows[p];
}

auto HomomorphismModel::target_graph_row(int g, int t) const -> const SVOBitset &
{
    return _imp->target_graph_rows[t * max_graphs + g];
}

auto HomomorphismModel::forward_target_graph_row(int t) const -> const SVOBitset &
{
    return _imp->forward_target_graph_rows[t];
}

auto HomomorphismModel::reverse_target_graph_row(int t) const -> const SVOBitset &
{
    return _imp->reverse_target_graph_rows[t];
}

auto HomomorphismModel::pattern_degree(int g, int p) const -> unsigned
{
    return _imp->patterns_degrees[g][p];
}

auto HomomorphismModel::target_degree(int g, int t) const -> unsigned
{
    return _imp->targets_degrees[g][t];
}

auto HomomorphismModel::largest_target_degree() const -> unsigned
{
    return _imp->largest_target_degree;
}

auto HomomorphismModel::has_vertex_labels() const -> bool
{
    return ! _imp->pattern_vertex_labels.empty();
}

auto HomomorphismModel::has_edge_labels() const -> bool
{
    return ! _imp->pattern_edge_labels.empty();
}

auto HomomorphismModel::pattern_vertex_label(int p) const -> int
{
    return _imp->pattern_vertex_labels[p];
}

auto HomomorphismModel::target_vertex_label(int t) const -> int
{
    return _imp->target_vertex_labels[t];
}

auto HomomorphismModel::pattern_edge_label(int p, int q) const -> int
{
    return _imp->pattern_edge_labels[p * pattern_size + q];
}

auto HomomorphismModel::target_edge_label(int t, int u) const -> int
{
    return _imp->target_edge_labels[t * target_size + u];
}

auto HomomorphismModel::num_pattern_loops(int p) const -> int
{
    return _imp->pattern_loops[p];
}

auto HomomorphismModel::num_target_loops(int t) const -> int
{
    return _imp->target_loops[t];
}

auto HomomorphismModel::has_less_thans() const -> bool
{
    return _imp->has_less_thans;
}

auto HomomorphismModel::has_occur_less_thans() const -> bool
{
    return _imp->has_occur_less_thans;
}

auto HomomorphismModel::directed() const -> bool
{
    return _imp->directed;
}

// Function which checks the actual equivalence criterion, i.e.,
// whether or not the vertices have the same neighbor.
auto HomomorphismModel::_is_pattern_structurally_equivalent(int x, int y) const -> bool
{
    auto nx = pattern_graph_row(0, x);
    auto ny = pattern_graph_row(0, y);
    
    // Both must have or not have loops
    if (num_pattern_loops(x) != num_pattern_loops(y))
        return false;

    if (has_vertex_labels())
        // Vertex labels must match
        if (pattern_vertex_label(x) != pattern_vertex_label(y))
            return false;

    if (!directed())
    {
        // If after anding the bitsets, the result is different, 
        // they are not equivalent.
        nx.reset(y);
        ny.reset(x);
        if (nx != ny)
            return false;

        // Otherwise, they have the same neighbors, we check the edge labels now
        if (has_edge_labels())
            for (auto w: nx)
                if (pattern_edge_label(x, w) != pattern_edge_label(y, w))
                    return false;
    }
    else
    {
        // Check if x,y either fully connected or disconnected
        if (nx.test(y) != ny.test(x))
            return false;

        // Check that the labels match
        if (nx.test(y) && has_edge_labels())
            if (pattern_edge_label(x, y) != pattern_edge_label(y, x))
                return false;

        // Resetting connections between x and y, so we can just check connections
        // to other vertices
        auto n_out_x = forward_pattern_graph_row(x);
        n_out_x.reset(y);
        auto n_in_x = reverse_pattern_graph_row(x);
        n_in_x.reset(y);

        auto n_out_y = forward_pattern_graph_row(y);
        n_out_y.reset(x);
        auto n_in_y = reverse_pattern_graph_row(y);
        n_in_y.reset(x);

        // Check if have the same set of in neighbors and out neighbors
        if (n_out_x != n_out_y)
            return false;

        if (n_in_x != n_in_y)
            return false;

        // Otherwise, they have the same neighbors, we check the edge labels now
        if (has_edge_labels())
        {
            for (auto w: n_in_x)
                if (pattern_edge_label(w, x) != pattern_edge_label(w, y))
                    return false;

            for (auto w: n_out_x)
                if (pattern_edge_label(x, w) != pattern_edge_label(y, w))
                    return false;
        }
    }
    return true;
}

// Function which checks the actual equivalence criterion, i.e.,
// whether or not the vertices have the same neighbor.
// This is just _is_pattern_structurally_equivalent copy/pasted with s/pattern/target.
// There is probably a way to merge the two functions seamlessly.
auto HomomorphismModel::_is_target_structurally_equivalent(int x, int y) const -> bool
{
    auto nx = target_graph_row(0, x);
    auto ny = target_graph_row(0, y);
    
    // Both must have or not have loops
    if (num_target_loops(x) != num_target_loops(y))
        return false;

    if (has_vertex_labels())
        // Vertex labels must match
        if (target_vertex_label(x) != target_vertex_label(y))
            return false;

    if (!directed())
    {
        // If after anding the bitsets, the result is different, 
        // they are not equivalent.
        nx.reset(y);
        ny.reset(x);
        if (nx != ny)
            return false;

        // Otherwise, they have the same neighbors, we check the edge labels now
        if (has_edge_labels())
            for (auto w: nx)
                if (target_edge_label(x, w) != target_edge_label(y, w))
                    return false;
    }
    else
    {
        // Check if x,y either fully connected or disconnected
        if (nx.test(y) != ny.test(x))
            return false;

        // Check that the labels match
        if (nx.test(y) && has_edge_labels())
            if (target_edge_label(x, y) != target_edge_label(y, x))
                return false;

        // Resetting connections between x and y, so we can just check connections
        // to other vertices
        auto n_out_x = forward_target_graph_row(x);
        n_out_x.reset(y);
        auto n_in_x = reverse_target_graph_row(x);
        n_in_x.reset(y);

        auto n_out_y = forward_target_graph_row(y);
        n_out_y.reset(x);
        auto n_in_y = reverse_target_graph_row(y);
        n_in_y.reset(x);

        // Check if have the same set of in neighbors and out neighbors
        if (n_out_x != n_out_y)
            return false;

        if (n_in_x != n_in_y)
            return false;

        // Otherwise, they have the same neighbors, we check the edge labels now
        if (has_edge_labels())
        {
            for (auto w: n_in_x)
                if (target_edge_label(w, x) != target_edge_label(w, y))
                    return false;

            for (auto w: n_out_x)
                if (target_edge_label(x, w) != target_edge_label(y, w))
                    return false;
        }
    }
    return true;
}

auto HomomorphismModel::_build_structural_equivalence(bool is_pattern) -> void
{
    std::queue<unsigned> queue;
    if (is_pattern)
        _imp->pattern_equivalence.add_elems(pattern_size);
    else
        _imp->target_equivalence.add_elems(target_size);
   
    unsigned size = is_pattern ? pattern_size : target_size;
    std::vector<bool> visited(size, false);
    // A vector to mark vertices we have already categorized
    std::vector<bool> categorized(size, false);

    for (unsigned i = 0; i < size; i++)
    {
        if (visited[i])
            continue;
        queue.push(i);

        while (!queue.empty())
        {
            unsigned curr_vert = queue.front();
            queue.pop();
            visited[curr_vert] = true;

            // Construct neighbor set for the current vertex
            SVOBitset nv;
            if (!directed())
            {
                if (is_pattern)
                    nv = pattern_graph_row(0, curr_vert);
                else
                    nv = target_graph_row(0, curr_vert);
            }
            else
            {
                if (is_pattern)
                {
                    nv = forward_pattern_graph_row(curr_vert);
                    nv |= reverse_pattern_graph_row(curr_vert);
                }
                else
                {
                    nv = forward_target_graph_row(curr_vert);
                    nv |= reverse_target_graph_row(curr_vert);
                }
            }

            // Remove any already categorized neighbor from the list.
            for (auto x : nv)
                if (categorized[x])
                    nv.reset(x);
            
            // Partition the neighbors into equivalence sets
            for (auto it = nv.begin(); it != nv.end(); it++)
            {
                auto x = *it;
                for (auto it2 = it+1; it2 != nv.end(); it2++)
                {
                    auto y = *it2;
                    if (is_pattern)
                    {
                        if (_is_pattern_structurally_equivalent(x, y))
                            _imp->pattern_equivalence.merge(x, y);
                    }
                    else
                        if (_is_target_structurally_equivalent(x, y))
                            _imp->target_equivalence.merge(x, y);
                }
                // Check if it is equivalent to the current vertex
                if (is_pattern)
                {
                    if (_is_pattern_structurally_equivalent(curr_vert, x))
                        _imp->pattern_equivalence.merge(curr_vert, x);
                }
                else
                    if (_is_target_structurally_equivalent(curr_vert, x))
                        _imp->target_equivalence.merge(curr_vert, x);
                if (!visited[x])
                    queue.push(x);

                // mark as categorized
                categorized[x] = true;
            }

        }
    }
}

// Function which checks if the equivalence data structure has p and q
// equivalent.
auto HomomorphismModel::is_pattern_equivalent(int p, int q) const -> bool
{
    return _imp->pattern_equivalence.find(p) == _imp->pattern_equivalence.find(q);
}

// Function which checks if the equivalence data structure has p and q
// equivalent.
auto HomomorphismModel::is_target_equivalent(int p, int q) const -> bool
{
    return _imp->target_equivalence.find(p) == _imp->target_equivalence.find(q);
}

auto HomomorphismModel::get_target_equivalence() const -> const DisjointSet&
{
    return _imp->target_equivalence;
}

auto HomomorphismModel::pattern_representative(int p) const -> int
{
    return _imp->pattern_equivalence.find(p);
}

auto HomomorphismModel::target_representative(int t) const -> int
{
    return _imp->target_equivalence.find(t);
}

auto HomomorphismModel::target_class_size(int t) const -> int
{
    return _imp->target_equivalence.get_size(t);
}

auto HomomorphismModel::pattern_equivalence_multiplier() const -> loooong
{
    return _imp->pattern_equivalence.get_multiplier();
}

auto HomomorphismModel::target_equivalence_multiplier() const -> loooong
{
    return _imp->target_equivalence.get_multiplier();
}

auto HomomorphismModel::merge_target_classes(int x, int y) -> void
{
    _imp->target_equivalence.merge(x, y);
}

auto HomomorphismModel::restore_equivalence(DisjointSet &target_equivalence) -> void
{
    _imp->target_equivalence = std::move(target_equivalence);
}

auto HomomorphismModel::get_target_num_used(int x) -> unsigned
{
    return _imp->target_equivalence.get_num_used(x);
}

auto HomomorphismModel::up_target_num_used(int x) -> void
{
    _imp->target_equivalence.up_num_used(x);
}

auto HomomorphismModel::down_target_num_used(int x) -> void
{
    _imp->target_equivalence.down_num_used(x);
}
