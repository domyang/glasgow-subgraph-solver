#ifndef GLASGOW_SUBGRAPH_SOLVER_EQUIVALENCE_HH
#define GLASGOW_SUBGRAPH_SOLVER_EQUIVALENCE_HH 1

#include <vector>

#include "loooong.hh"

class DisjointSet
{
	private:
		unsigned count;
		std::vector<unsigned> parents;
		// For performing union by size
		std::vector<unsigned> sizes;
        // A count of how many vertices appear in the current match
        std::vector<unsigned> num_used;
        loooong multiplier = 1;
        bool has_multiplier = false;

	public:
		DisjointSet(): count(0), parents(), sizes(), num_used() {}

		DisjointSet(unsigned n): count(n), parents(), sizes(n, 1), num_used(n, 0)
		{
			parents.reserve(n);
			for (unsigned i = 0; i < n; i++)
				parents.push_back(i);
		}

        DisjointSet(const DisjointSet &other): count(other.count), parents(other.count), sizes(other.count), num_used(other.count)
        {
            for (unsigned i = 0; i < count; i++)
            {
                parents[i] = other.parents[i];
                sizes[i] = other.sizes[i];
                num_used[i] = other.num_used[i];
            }
            multiplier = other.multiplier;
            has_multiplier = other.has_multiplier;
        }

		void add_elems(unsigned n)
		{
			count = n;
			parents.reserve(n);
			sizes.reserve(n);
            num_used.reserve(n);
			for (unsigned i = 0; i < n; i++)
			{
				parents.push_back(i);
				sizes.push_back(1);
                num_used.push_back(0);
			}
		}

		/*
		 * Find representative for equivalence class
		 */
		unsigned find(unsigned x)
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

            return root;
        }

		/*
		 * Merge two equivalence classes together
		 */
		void merge(unsigned x, unsigned y)
        {
            unsigned x_root = find(x);
            unsigned y_root = find(y);
            if (x_root != y_root)
            {
                if (sizes[x_root] < sizes[y_root])
                    std::swap(x_root, y_root);

                parents[y_root] = x_root;
                sizes[x_root] = sizes[x_root] + sizes[y_root];
                num_used[x_root] = num_used[x_root] + num_used[y_root];
            }
        }
        
        loooong get_multiplier()
        {
            if (has_multiplier)
                return multiplier;

            loooong m = 1;
            for (unsigned i = 0; i < count; i++)
                if (find(i) == i)
                    for (unsigned j = 1; j <= sizes[i]; j++)
                        m *= j;
            multiplier = m;
            has_multiplier = true;
            return m;
        }

        unsigned get_size(int x)
        {
            return sizes.at(find(x));
        }

        unsigned get_num_used(int x)
        {
            return num_used.at(find(x));
        }

        void up_num_used(int x)
        {
            num_used[find(x)]++;
        }

        void down_num_used(int x)
        {
            num_used[find(x)]--;
        }

        void restore_base_equivalence()
        {
            for (unsigned i = 0; i < count; i++)
            {
                parents[i] = i;
                sizes[i] = 1;
            }
            has_multiplier = false;
        }
        

        auto operator= (const DisjointSet &other) -> DisjointSet &
        {
            if (&other == this)
                return *this;

            parents.reserve(other.count);
            sizes.reserve(other.count);
            num_used.reserve(other.count);
            for (unsigned i = 0; i < count; i++)
            {
                parents[i] = other.parents[i];
                sizes[i] = other.sizes[i];
                num_used[i] = other.num_used[i];
            }
            multiplier = other.multiplier;
            has_multiplier = other.has_multiplier;

            return *this;
        }

        void copy_equivalence(const DisjointSet &other)
        {
            for (unsigned i = 0; i < count; i++)
            {
                parents[i] = other.parents[i];
                sizes[i] = other.parents[i];
            }
            has_multiplier = false;
        }
};

#endif
