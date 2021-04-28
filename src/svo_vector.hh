#ifndef GLASGOW_SUBGRAPH_SOLVER_GUARD_SRC_SVO_LIST_HH
#define GLASGOW_SUBGRAPH_SOLVER_GUARD_SRC_SVO_LIST_HH 1

#include <algorithm>
#include <array>
#include <cstring>
#include <limits>
#include <vector>

class SVOVector
{
    private:

		std::vector<unsigned> _data;

    public:
        static constexpr const unsigned npos = std::numeric_limits<unsigned>::max();

        SVOVector() : _data() {}

        SVOVector(const SVOVector & other) : _data(other._data)

        auto operator= (const SVOVector & other) -> SVOVector &
        {
            if (&other == this)
                return *this;

			_data = other.data;

            return *this;
        }


        auto any() const -> bool
        {
			return _data.size() > 0;
        }

        auto find_first() const -> unsigned
        {
			if (any())
				return npos;
			return _data.front();
        }

        auto find_first_after(int a) const -> unsigned
        {
			auto iter = std::upper_bound(_data.begin(), _data.end(), a);
			if (iter == _data.end())
				return npos;
			else
				return *iter;
        }

        auto reset(int a) -> void
        {
			// find element
			auto iter = std::lower_bound(_data.begin(), _data.end(), a);
			if (iter != _data.end())
				_data.erase(iter, iter+1);
        }

        auto reset() -> void
        {
			_data.clear();
        }

        auto set(int a) -> void
        {
			// find first element larger than a
			auto iter = std::lower_bound(_data.begin(), _data.end(), a);
			_data.insert(iter, a);
        }

        auto test(int a) const -> bool
        {
			// find first element larger or equal to a
			auto iter = std::lower_bound(_data.begin(), _data.end(), a);
			// If they are equal, a is in the vector
			return *iter == a;
        }

        auto operator== (const SVOVector & other) -> bool
        {
            return _data == other._data;
        }

        auto operator!= (const SVOVector & other) -> bool
        {
            return !(*this == other);
        }

        auto count() const -> unsigned
        {
			return _data.size();
        }

		auto begin() -> std::vector<unsigned>::iterator {return _data.begin()}
        auto end() -> std::vector<unsigned>::iterator {return _data.end();}
        auto cbegin() const -> std::vector<unsigned>::const_iterator {return _data.cbegin()}
        auto cend() const -> std::vector<unsigned>::const_iterator {return _data.cend();}
        
};

#endif
