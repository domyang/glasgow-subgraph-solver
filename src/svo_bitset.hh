/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_SUBGRAPH_SOLVER_GUARD_SRC_SVO_BITSET_HH
#define GLASGOW_SUBGRAPH_SOLVER_GUARD_SRC_SVO_BITSET_HH 1

#include <algorithm>
#include <array>
#include <cstring>
#include <limits>

class SVOBitset
{
    private:
        using BitWord = unsigned long long;
        static const constexpr int bits_per_word = sizeof(BitWord) * 8;
        static const constexpr int svo_size = 16;

        union
        {
            BitWord short_data[svo_size];
            BitWord * long_data;
        } _data;

        unsigned n_words;

        constexpr auto _is_long() const -> bool
        {
            return n_words > svo_size;
        }

    public:
        static constexpr const unsigned npos = std::numeric_limits<unsigned>::max();

        SVOBitset()
        {
            n_words = 0;
        }

        SVOBitset(unsigned size, unsigned bits);

        SVOBitset(const SVOBitset & other)
        {
            if (other._is_long()) {
                n_words = other.n_words;
                _data.long_data = new BitWord[n_words];
                std::copy(other._data.long_data, other._data.long_data + other.n_words, _data.long_data);
            }
            else {
                n_words = other.n_words;
                std::copy(&other._data.short_data[0], &other._data.short_data[svo_size], &_data.short_data[0]);
            }
        }

        ~SVOBitset()
        {
            if (_is_long())
                delete[] _data.long_data;
        }

        auto operator= (const SVOBitset & other) -> SVOBitset &
        {
            if (&other == this)
                return *this;

            if (other._is_long()) {
                if (! _is_long()) {
                    n_words = other.n_words;
                    _data.long_data = new BitWord[n_words];
                }
                else if (n_words != other.n_words) {
                    delete[] _data.long_data;
                    _data.long_data = new BitWord[n_words];
                }

                std::copy(other._data.long_data, other._data.long_data + other.n_words, _data.long_data);
            }
            else {
                if (_is_long())
                    delete[] _data.long_data;
                n_words = other.n_words;
                std::copy(&other._data.short_data[0], &other._data.short_data[svo_size], &_data.short_data[0]);
            }

            return *this;
        }


        auto any() const -> bool
        {
            if (! _is_long()) {
                for (unsigned i = 0 ; i < n_words ; ++i)
                    if (0 != _data.short_data[i])
                        return true;

                return false;
            }
            else {
                for (unsigned i = 0, i_end = n_words ; i < i_end ; ++i)
                    if (0 != _data.long_data[i])
                        return true;

                return false;
            }
        }

        auto find_first() const -> unsigned
        {
            if (! _is_long()) {
                for (unsigned i = 0 ; i < n_words ; ++i) {
                    int x = __builtin_ffsll(_data.short_data[i]);
                    if (0 != x)
                        return i * bits_per_word + x - 1;
                }
                return npos;
            }
            else {
                for (unsigned i = 0, i_end = n_words ; i < i_end ; ++i) {
                    int x = __builtin_ffsll(_data.long_data[i]);
                    if (0 != x)
                        return i * bits_per_word + x - 1;
                }
                return npos;
            }
        }

        auto find_first_after(int a) const -> unsigned
        {
            unsigned start = a / bits_per_word;
            unsigned offset = a % bits_per_word + 1;

            // If at the end of a word, move to the next word.
            if (offset == bits_per_word)
            {
                start++;
                // If at end of data, return.
                if (start == n_words)
                    return npos;
                offset = 0;
            }

            auto data = _is_long() ? _data.long_data : _data.short_data;

            // We shift to find our current position.
            int x = __builtin_ffsll(data[start] >> offset);
            if (x != 0)
                return start * bits_per_word + x + offset - 1;

            for (unsigned i = start + 1 ; i < n_words ; ++i) 
            {
                x = __builtin_ffsll(data[i]);
                if (0 != x)
                    return i * bits_per_word + x - 1;
            }
            return npos;
        }

        auto reset(int a) -> void
        {
            BitWord * b = (_is_long() ? _data.long_data : _data.short_data);
            b[a / bits_per_word] &= ~(BitWord{ 1 } << (a % bits_per_word));
        }

        auto reset() -> void
        {
            if (! _is_long())
                std::fill(&_data.short_data[0], &_data.short_data[svo_size], 0);
            else
                std::fill(_data.long_data, _data.long_data + n_words, 0);
        }

        auto set(int a) -> void
        {
            BitWord * b = (_is_long() ? _data.long_data : _data.short_data);
            b[a / bits_per_word] |= (BitWord{ 1 } << (a % bits_per_word));
        }

        auto test(int a) const -> bool
        {
            const BitWord * b = (_is_long() ? _data.long_data : _data.short_data);
            return b[a / bits_per_word] & (BitWord{ 1 } << (a % bits_per_word));
        }

        auto operator&= (const SVOBitset & other) -> SVOBitset &
        {
            if (! _is_long()) {
                for (unsigned i = 0 ; i < svo_size ; ++i)
                    _data.short_data[i] &= other._data.short_data[i];
            }
            else {
                for (unsigned i = 0 ; i < n_words ; ++i)
                    _data.long_data[i] &= other._data.long_data[i];
            }

            return *this;
        }

        auto operator|= (const SVOBitset & other) -> SVOBitset &
        {
            if (! _is_long()) {
                for (unsigned i = 0 ; i < svo_size ; ++i)
                    _data.short_data[i] |= other._data.short_data[i];
            }
            else {
                for (unsigned i = 0 ; i < n_words ; ++i)
                    _data.long_data[i] |= other._data.long_data[i];
            }

            return *this;
        }

        auto operator== (const SVOBitset & other) -> bool
        {
            if (! _is_long()) {
                for (unsigned i = 0 ; i < svo_size ; ++i)
                    if (_data.short_data[i] != other._data.short_data[i])
                        return false;
            }
            else {
                for (unsigned i = 0 ; i < n_words ; ++i)
                    if (_data.long_data[i] != other._data.long_data[i])
                        return false;
            }

            return true;
        }

        auto operator!= (const SVOBitset & other) -> bool
        {
            return !(*this == other);
        }

        auto intersect_with_complement(const SVOBitset & other) -> void
        {
            if (! _is_long()) {
                for (unsigned i = 0 ; i < svo_size ; ++i)
                    _data.short_data[i] &= ~other._data.short_data[i];
            }
            else {
                for (unsigned i = 0 ; i < n_words ; ++i)
                    _data.long_data[i] &= ~other._data.long_data[i];
            }
        }

        auto count() const -> unsigned
        {
            unsigned result = 0;
            const BitWord * b = (_is_long() ? _data.long_data : _data.short_data);
            for (unsigned i = 0, i_end = n_words ; i < i_end ; ++i)
                result += __builtin_popcountll(b[i]);

            return result;
        }

        struct Iterator
        {
            using iterator_category = std::forward_iterator_tag;
            using difference_type = std::ptrdiff_t;
            using value_type = unsigned;
            using pointer = unsigned*;
            using reference = unsigned&;

            Iterator(SVOBitset& set, unsigned p): bitset(set), pos(p) {}
            reference operator*() { return pos; }
            pointer operator->() { return &pos; }

            Iterator& operator++() {pos = bitset.find_first_after(pos); return *this;}
            Iterator& operator++(int) {pos = bitset.find_first_after(pos); return *this;}
            Iterator operator+(int x) const {Iterator iter(this->bitset, pos+x); iter.pos = bitset.find_first_after(pos+x-1); return iter;}
            friend bool operator==(const Iterator& a, const Iterator& b){return a.pos == b.pos;}
            friend bool operator!=(const Iterator& a, const Iterator& b){return a.pos != b.pos;}

        private:
            SVOBitset& bitset;
            unsigned pos;
        };

        struct ConstIterator
        {
            using iterator_category = std::forward_iterator_tag;
            using difference_type = std::ptrdiff_t;
            using value_type = unsigned;
            using pointer = unsigned const*;
            using reference = unsigned const&;

            ConstIterator(const SVOBitset& set, unsigned p): bitset(set), pos(p) {}
            reference operator*() { return pos; }
            pointer operator->() { return &pos; }

            ConstIterator& operator++() {pos = bitset.find_first_after(pos); return *this;}
            ConstIterator& operator++(int) {pos = bitset.find_first_after(pos); return *this;}
            friend bool operator==(const ConstIterator& a, const ConstIterator& b){return a.pos == b.pos;}
            friend bool operator!=(const ConstIterator& a, const ConstIterator& b){return a.pos != b.pos;}

        private:
            const SVOBitset& bitset;
            unsigned pos;
        };

        Iterator begin() {int pos = find_first(); return Iterator(*this, pos);}
        Iterator end() {return Iterator(*this, npos);}
        ConstIterator cbegin() const {int pos = find_first(); return ConstIterator(*this, pos);}
        ConstIterator cend() const {return ConstIterator(*this, npos);}
        
};

#endif
