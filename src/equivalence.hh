#ifndef GLASGOW_SUBGRAPH_SOLVER_EQUIVALENCE_HH
#define GLASGOW_SUBGRAPH_SOLVER_EQUIVALENCE_HH 1

#include <vector>

class DisjointSet
{
		private:
				unsigned count;
				std::vector<int> parents;
				// For performing union by size
				std::vector<int> sizes;

		public:
				DisjointSet(unsigned n): count(n), parents(), sizes(n, 1)
				{
						parents.reserve(n);
						for (unsigned i = 0; i < n; i++)
								parents.push_back(i);
				}

				/*
				 * Find representative for equivalence class
				 */
				unsigned find(unsigned);

				/*
				 * Merge two equivalence classes together
				 */
				void merge(unsigned, unsigned);
}

#endif
