#include <algorithm>
#include <vector>

#include "equivalence.hh"
#include "svo_bitset.hh"

DisjointSet::find(unsigned x)
{
	// Traverse up until the root
	unsigned root = x;
	while (parents[root] != root)
		root = parents[root];

	// Path Compression
	while (parents[x] != root)
	{
		unsigned parent = parents[x];
		parents[x] = root;
		sizes[x] = 1;
		x = parent;
	}

	return root
}

DisjointSet::merge(unsigned x, unsigned y)
{
	unsigned x_root = find(x);
	unsigned y_root = find(y);
	if (x_root != y_root)
	{
		if (sizes[x_root] < sizes[y_root])
			std::swap(x_root, y_root);

		parents[y_root] = x_root;
		sizes[x_root] = sizes[x_root] + sizes[y_root];
	}

}

bool is_equivalent(std::vector<SVOBitset> &graph_rows, unsigned x, unsigned y)
{
	auto nx = graph_rows[x * max_graphs + 0];
	auto ny = graph_rows[y * max_graphs + 0];

	x.reset(y);
	y.reset(x);
}


