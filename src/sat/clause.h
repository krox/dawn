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
	// "removed" clause. Actual removal with the next call to `prune`
	black = 0,

	// reducible clause. Might be kept for a while depending a local searcher
	// heuristics.
	red = 1,

	// also reducible, but estimated to be good enough to keep around
	//   - worth to spend inprocessing time on (i.e. vivification)
	//   - communicated across threads
	green = 2,

	// irreducible clause. Only these have to be satisfied
	blue = 3,
};

inline Color min(Color a, Color b) { return a < b ? a : b; }
inline Color max(Color a, Color b) { return a > b ? a : b; }

class Clause
{
  public:
	// 4 byte header. Might be extended in the future.
	// (as a comparison: Minisat uses 4 bytes header plus optionally 4 bytes
	// footer. Cryptominisat seems to use 28 bytes header by default)
	uint16_t size_;
	Color color;
	uint8_t reserved_;

	// array of Lits
	// Lit _lits[]; // not valid C++

	Clause() {}
	Clause(const Clause &) = delete;

	// array-like access to literals
	std::span<Lit> lits() { return std::span<Lit>{(Lit *)(this + 1), size_}; }
	std::span<const Lit> lits() const
	{
		return std::span<const Lit>{(Lit *)(this + 1), size_};
	}

	// make Clause usable as span<Lit> without calling '.lits()' explicitly
	uint16_t size() const { return size_; }
	Lit &operator[](size_t i) { return lits()[i]; }
	const Lit &operator[](size_t i) const { return lits()[i]; }
	operator std::span<Lit>() { return lits(); }
	operator std::span<const Lit>() const { return lits(); }
	auto begin() { return lits().begin(); }
	auto begin() const { return lits().begin(); }
	auto end() { return lits().end(); }
	auto end() const { return lits().end(); }

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
	// NOTE: this is unsafe, because the clause does not know its own capacity.
	//       only use right after succesfully removing another literal.
	void add_literal_unchecked(Lit a)
	{
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
			color = Color::black;
		else
			size_ = (uint16_t)s;
	}
};

// Reference to a clause inside a ClauseStorage object.
// Technically just a (31 bit) index into an array.
class CRef
{
	// NOTE: highest bit is used for bit-packing in 'Watch' and 'Reason'
	uint32_t _val;

  public:
	CRef() = default;
	constexpr explicit CRef(uint32_t val) : _val(val) {}

	static constexpr CRef undef() { return CRef{UINT32_MAX}; }

	constexpr operator uint32_t() const { return _val; }

	constexpr bool proper() const { return _val <= (UINT32_MAX >> 1); }
};

#define CREF_MAX (UINT32_MAX >> 1)

class ClauseStorage
{
  private:
	util::vector<Lit> store_;
	std::vector<CRef> clauses_;

  public:
	// add a new clause, no checking of lits done
	CRef add_clause(std::span<const Lit> lits, Color color)
	{
		if (lits.size() > UINT16_MAX)
			throw std::runtime_error("clause to long for storage");

		// allocate space for the new clause
		store_.reserve_with_spare(store_.size() + lits.size() +
		                          sizeof(Clause) / sizeof(Lit));
		if (store_.size() > CREF_MAX)
			throw std::runtime_error("clause storage overflow");
		auto r = CRef((uint32_t)store_.size());
		Clause &cl = *(Clause *)(store_.end());
		store_.set_size_unsafe(store_.size() + lits.size() +
		                       sizeof(Clause) / sizeof(Lit));

		// copy it over
		cl.size_ = (uint16_t)lits.size();
		cl.color = color;
		for (size_t i = 0; i < lits.size(); ++i)
			cl[i] = lits[i];

		clauses_.push_back(r);
		return r;
	}

	CRef add_binary(Lit a, Lit b)
	{
		return add_clause(std::array<Lit, 2>{a, b}, Color::blue);
	}

	Clause &operator[](CRef i) { return *(Clause *)&store_[i]; }

	const Clause &operator[](CRef i) const { return *(Clause *)&store_[i]; }

	std::span<const CRef> crefs() const { return clauses_; }
	auto crefs_reverse() const { return util::reverse(clauses_); }

	auto all()
	{
		auto deref = [this](CRef i) -> auto & { return (*this)[i]; };
		return util::transform(crefs(), deref);
	}

	auto all() const
	{
		auto deref = [this](CRef i) -> auto & { return (*this)[i]; };
		return util::transform(crefs(), deref);
	}

	auto all_reverse() const
	{
		auto deref = [this](CRef i) -> auto & { return (*this)[i]; };
		return util::transform(crefs_reverse(), deref);
	}

	auto enumerate()
	{
		auto deref = [this](CRef i) {
			return std::make_tuple(i, std::ref((*this)[i]));
		};
		return util::transform(crefs(), deref);
	}

	auto enumerate() const
	{
		auto deref = [this](CRef i) {
			return std::make_tuple(i, std::ref((*this)[i]));
		};
		return util::transform(crefs(), deref);
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

	size_t memory_usage() const
	{
		return store_.capacity() * sizeof(uint32_t) +
		       clauses_.capacity() * sizeof(CRef);
	}

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
