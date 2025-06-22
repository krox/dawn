/**
 * Basic definitions and Clause Storage.
 */

#pragma once

#include "fmt/format.h"
#include "fmt/ranges.h"
#include "util/functional.h"
#include "util/iterator.h"
#include "util/memory.h"
#include "util/vector.h"
#include <cassert>
#include <cstdint>
#include <functional>
#include <ranges>
#include <span>
#include <tuple>
#include <vector>

namespace dawn {

// A literal is a variable number + sign.
// Also there are some special lits: one, zero, undef, elim
class Lit
{
	uint32_t val_;

  public:
	// constructors
	Lit() = default;
	explicit constexpr Lit(uint32_t val) : val_(val) {}
	constexpr Lit(int var, bool s) : val_(2 * var + (s ? 1 : 0)) {}

	// special values
	static constexpr Lit zero() { return Lit{(uint32_t)-1}; }
	static constexpr Lit one() { return Lit{(uint32_t)-2}; }
	static constexpr Lit undef() { return Lit{(uint32_t)-4}; }
	static constexpr Lit elim() { return Lit{(uint32_t)-6}; }
	static constexpr Lit fixed(bool sign) { return one() ^ sign; }

	// basic accesors and properties
	constexpr operator int() const { return (int)val_; }
	constexpr int var() const { return val_ >> 1; }
	constexpr bool sign() const { return (val_ & 1) != 0; }
	constexpr bool proper() const { return (int32_t)val_ >= 0; }
	constexpr bool fixed() const { return (val_ & ~1) == (uint32_t)-2; }

	// IO in dimacs convention
	constexpr static Lit fromDimacs(int x)
	{
		return Lit(x > 0 ? 2 * x - 2 : -2 * x - 1);
	}
	constexpr int toDimacs() const { return sign() ? -var() - 1 : var() + 1; }

	// misc
	constexpr bool operator==(Lit b) const { return val_ == b.val_; }
	constexpr Lit neg() const { return Lit(val_ ^ 1); }
	constexpr Lit operator^(bool sign) const { return Lit(val_ ^ sign); }
};

// the binary part of a sat instance, in the form of a (directed) graph
struct BinaryGraph
{
	// semi-private, use with care. only invariant is symmetry:
	// bins[a] contains b if and only if bins[b] contains a.
	std::vector<util::small_vector<Lit, 7>> bins_;

	BinaryGraph() = default;
	BinaryGraph(int n) : bins_(2 * n) {}

	int add_var()
	{
		bins_.emplace_back();
		bins_.emplace_back();
		return (int)(bins_.size() / 2 - 1);
	}
	int var_count() const noexcept { return (int)(bins_.size() / 2); }

	auto &operator[](Lit a) noexcept { return bins_.at(a); }
	auto const &operator[](Lit a) const noexcept { return bins_.at(a); }

	void add(Lit a, Lit b)
	{
		assert(a.proper() && uint32_t(a) < bins_.size());
		assert(b.proper() && uint32_t(b) < bins_.size());
		assert(a.var() != b.var());

		bins_[a].push_back(b);
		bins_[b].push_back(a);
	}

	size_t clause_count() const noexcept
	{
		size_t count = 0;
		for (auto const &v : bins_)
			count += v.size();
		return count / 2;
	}

	void clear() noexcept
	{
		for (auto &v : bins_)
			v.clear();
	}

	size_t memory_usage() const noexcept
	{
		size_t size = bins_.capacity() * sizeof(bins_[0]);
		for (auto const &v : bins_)
			size += v.capacity() * sizeof(Lit);
		return size;
	}
};

// - removes duplicates and Lit::zero()
// - returns -1 for tautologies and Lit::one()
// - otherwiese, returns new size
inline int normalize_clause(std::span<Lit> lits)
{
	int j = 0;
	for (int i = 0; i < (int)lits.size(); ++i)
	{
		if (lits[i] == Lit::one()) // literal true -> remove clause
			return -1;
		if (lits[i] == Lit::zero()) // literal false -> remove lit
			goto next;

		assert(lits[i].proper()); // disallow Lit::undef()/Lit::elim()

		for (int k = 0; k < i; ++k)
		{
			if (lits[i] == lits[k].neg()) // tautology -> remove clause
				return -1;
			if (lits[i] == lits[k]) // duplicate literal -> remove lit
				goto next;
		}

		// no special case -> keep the literal
		lits[j++] = lits[i];

	next:;
	}

	return j;
}

enum class Color : uint8_t
{
	// removed clause
	//   - ignored by 'PropEngine' immediately
	//   - physical removal by calling 'ClauseStorage::prune()'
	black = 0,

	// reducible clause
	//   - might be kept for a while depending a local searcher heuristics
	red = 1,

	// also reducible, but estimated to be good enough to keep around
	//   - worth to spend inprocessing time on (i.e. vivification)
	//   - communicated across threads
	green = 2,

	// irreducible clause.
	//   - only these have to be satisfied for a valid solution
	//   - only these need to be considered by BVE (though heuristically, some
	//     reducibles are resolved as well)
	blue = 3,
};

inline Color min(Color a, Color b) { return a < b ? a : b; }
inline Color max(Color a, Color b) { return a > b ? a : b; }

enum class Flag : uint8_t
{
	vivified = 1, // clause was fully vivified at some point
};

class Clause
{
	// 4 byte header. Might be extended in the future.
	// (as a comparison: Minisat uses 4 bytes header plus optionally 4 bytes
	// footer. Cryptominisat seems to use 28 bytes header by default)
	uint32_t size_ : 10;
	uint32_t capacity_ : 10;
	uint32_t color_ : 4;
	uint32_t flags_ : 8;

	// array of Lits
	// Lit _lits[]; // not valid C++
  public:
	// maximum size of a clause (current implementation limit)
	static constexpr size_t max_size() { return (1 << 10) - 1; }

	Clause(const Clause &) = delete;
	Clause &operator=(const Clause &) = delete;

	explicit Clause(size_t size, Color color)
	    : size_((uint32_t)size), capacity_((uint32_t)size),
	      color_(uint32_t(color)), flags_(0)
	{
		assert(size <= max_size());
	}

	// array-like access to literals
	std::span<Lit> lits() { return std::span<Lit>{(Lit *)(this + 1), size()}; }
	std::span<const Lit> lits() const
	{
		return std::span<const Lit>{(Lit *)(this + 1), size()};
	}

	// make Clause usable as span<Lit> without calling '.lits()' explicitly
	uint16_t size() const { return size_; }
	uint16_t capacity() const { return capacity_; }
	Color color() const { return (Color)color_; }
	Lit &operator[](size_t i) { return lits()[i]; }
	Lit operator[](size_t i) const { return lits()[i]; }
	operator std::span<Lit>() { return lits(); }
	operator std::span<const Lit>() const { return lits(); }
	auto begin() { return lits().begin(); }
	auto begin() const { return lits().begin(); }
	auto end() { return lits().end(); }
	auto end() const { return lits().end(); }

	void set_size(size_t s)
	{
		assert(s <= capacity_);
		size_ = (uint32_t)s;
	}

	void shrink_unsafe()
	{
		assert(size_ <= capacity_);
		capacity_ = size_;
	}

	void set_color(Color c) { color_ = (uint32_t)c; }

	void set_flag(Flag f) { flags_ |= (uint8_t)f; }
	void clear_flag(Flag f) { flags_ &= ~(uint8_t)f; }
	bool has_flag(Flag f) const { return (flags_ & (uint8_t)f) != 0; }

	// remove a literal from this clause. returns false if not found
	bool remove_literal(Lit a)
	{
		for (int i = 0; i < size_; ++i)
			if (lits()[i] == a)
			{
				for (int j = i + 1; j < size_; ++j)
					lits()[j - 1] = lits()[j];
				size_ -= 1;
				return true;
			}
		return false;
	}

	// remove two literals from this clause, only if both are found
	bool remove_litarals(Lit a, Lit b)
	{
		if (!contains(a) || !contains(b))
			return false;
		int i = 0;
		for (int j = 0; j < size_; ++j)
		{
			if (lits()[j] == a || lits()[j] == b)
				continue;
			lits()[i++] = lits()[j];
		}
		assert(i == size_ - 2);
		size_ -= 2;
		return true;
	}

	// Add a literal to the clause.
	// Requires size < capacity of course.
	void add_literal(Lit a)
	{
		assert(size_ < capacity_);
		size_ += 1;
		lits()[size_ - 1] = a;
	}

	// check if this clause contains some literal
	bool contains(Lit a) const
	{
		for (Lit b : lits())
			if (a == b)
				return true;
		return false;
	}

	// check if this clause contains some variable (either sign)
	bool contains_variable(int v) const
	{
		for (Lit b : lits())
			if (b.var() == v)
				return true;
		return false;
	}

	// - remove duplicate/fixed lits
	// - remove clause if tautological
	void normalize()
	{
		if (int s = normalize_clause(lits()); s == -1)
			set_color(Color::black);
		else
			set_size(s);
	}

	// move literal 'a' to the front. asserts that 'a' is in the clause
	void move_to_front(Lit a)
	{
		for (Lit &b : lits())
			if (b == a)
			{
				std::swap(lits()[0], b);
				return;
			}
		assert(false);
	}

	// pointer to next clause, assuming dense storage in 'ClauseStorage'
	Clause *next() { return (Clause *)((Lit *)(this + 1) + capacity_); }
	Clause const *next() const
	{
		return (Clause const *)((Lit const *)(this + 1) + capacity_);
	}
};

// iterator that advances by calling 'p->next()'.
template <class T> class NextIterator
{
	T *ptr_;

  public:
	using value_type = T;
	using reference = T &;
	using pointer = T *;
	using difference_type = ptrdiff_t;

	NextIterator() = default;
	NextIterator(T *ptr) : ptr_(ptr) {}
	NextIterator &operator++()
	{
		ptr_ = ptr_->next();
		return *this;
	}
	NextIterator operator++(int)
	{
		auto tmp = *this;
		ptr_ = ptr_->next();
		return tmp;
	}
	T &operator*() const { return *ptr_; }
	T *operator->() const { return ptr_; }
	constexpr bool operator==(NextIterator const &) const = default;
};

static_assert(std::forward_iterator<NextIterator<Clause>>);
static_assert(std::forward_iterator<NextIterator<Clause const>>);

// Reference to a clause inside a ClauseStorage object.
// Technically just an index, limited to 30 bits, so that we can use up to two
// high bits in the 'Reason' and 'Watch' classes.
class CRef
{
	uint32_t _val = UINT32_MAX;

  public:
	CRef() = default;
	constexpr explicit CRef(uint32_t val) : _val(val) {}

	static constexpr uint32_t max() { return UINT32_MAX >> 2; }
	static constexpr CRef undef() { return CRef{UINT32_MAX}; }

	constexpr operator uint32_t() const { return _val; }

	constexpr bool proper() const { return _val <= max(); }
};

class ClauseStorage
{
	// TODO: could extract a 'UntypedVector' class, avoiding 'vector' altogether
	util::vector<Lit> store_;

  public:
	using iterator = NextIterator<Clause>;
	using const_iterator = NextIterator<Clause const>;

	iterator begin() { return (Clause *)store_.begin(); }
	iterator end() { return (Clause *)store_.end(); }
	const_iterator begin() const { return (Clause *)store_.begin(); }
	const_iterator end() const { return (Clause *)store_.end(); }

	// index of a clause in the store
	CRef get_index(Clause const &cl) const
	{
		auto p = ptrdiff_t(&cl);
		auto start = ptrdiff_t(store_.begin());
		auto end = ptrdiff_t(store_.end());
		assert(start <= p && p <= end);
		return CRef((uint32_t)((p - start) / sizeof(Lit)));
	}

	// add a new clause, no checking of lits done
	CRef add_clause(std::span<const Lit> lits, Color color)
	{
		// allocate space for the new clause
		store_.reserve_with_spare(store_.size() + lits.size() +
		                          sizeof(Clause) / sizeof(Lit));
		if (store_.size() > CRef::max())
			throw std::runtime_error("clause storage overflow");
		auto r = CRef((uint32_t)store_.size());
		Clause &cl = *(Clause *)(store_.end());
		store_.set_size_unsafe(store_.size() + lits.size() +
		                       sizeof(Clause) / sizeof(Lit));

		// copy it over
		std::construct_at<Clause>(&cl, lits.size(), color);
		for (size_t i = 0; i < lits.size(); ++i)
			cl[i] = lits[i];

		return r;
	}

	CRef add_binary(Lit a, Lit b)
	{
		return add_clause(std::array<Lit, 2>{a, b}, Color::blue);
	}

	Clause &operator[](CRef i) { return *(Clause *)&store_[i]; }
	const Clause &operator[](CRef i) const { return *(Clause *)&store_[i]; }

	auto all()
	{
		return std::ranges::subrange(begin(), end()) |
		       std::views::filter(
		           [](auto &cl) { return cl.color() != Color::black; });
	}
	auto all() const
	{
		return std::ranges::subrange(begin(), end()) |
		       std::views::filter(
		           [](auto &cl) { return cl.color() != Color::black; });
	}

	auto crefs() const
	{
		return all() | std::views::transform(
		                   [this](auto &cl) { return get_index(cl); });
	}
	auto enumerate()
	{
		return all() | std::views::transform([this](Clause &cl) {
			       return std::make_tuple(get_index(cl), std::ref(cl));
		       });
	}

	auto enumerate() const
	{
		return all() | std::views::transform([this](Clause const &cl) {
			       return std::make_tuple(get_index(cl), std::ref(cl));
		       });
	}

	// number of (non-removed) clauses
	size_t count() const
	{
		size_t r = 0;
		for (auto &_ [[maybe_unused]] : all())
			++r;
		return r;
	}

	// count == 0
	bool empty() const
	{
		for (auto &_ [[maybe_unused]] : all())
			return false;
		return true;
	}

	size_t memory_usage() const { return store_.capacity() * sizeof(uint32_t); }

	// remove all clauses that satisfy the predicate. Invalidates all CRef's.
	void prune(util::function_view<bool(Clause const &)> f);
	void prune_black();

	// Remove all clauses_, keeping allocated memory
	void clear();
};

static_assert(sizeof(Lit) == 4);
static_assert(sizeof(Clause) % sizeof(Lit) == 0);

} // namespace dawn

template <> struct fmt::formatter<dawn::Lit>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Lit a, FormatContext &ctx) const
	{
		// NOTE: '-elim' and '-undef' should never happen, just for debugging
		if (a.proper())
			return fmt::format_to(ctx.out(), "{}", a.toDimacs());
		else if (a == dawn::Lit::undef())
			return fmt::format_to(ctx.out(), "undef");
		else if (a == dawn::Lit::one())
			return fmt::format_to(ctx.out(), "true");
		else if (a == dawn::Lit::zero())
			return fmt::format_to(ctx.out(), "false");
		else if (a == dawn::Lit::elim())
			return fmt::format_to(ctx.out(), "elim");
		else if (a == dawn::Lit::elim().neg())
			return fmt::format_to(ctx.out(), "-elim");
		else if (a == dawn::Lit::undef().neg())
			return fmt::format_to(ctx.out(), "-undef");
		else
			assert(false);
	}
};

template <> struct fmt::formatter<dawn::Clause>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Clause const &cl, FormatContext &ctx) const
	{
		return fmt::format_to(ctx.out(), "{}", fmt::join(cl.lits(), " "));
	}
};

namespace util {
template <class> struct is_contiguously_hashable;
template <> struct is_contiguously_hashable<dawn::Lit> : std::true_type
{};
} // namespace util
