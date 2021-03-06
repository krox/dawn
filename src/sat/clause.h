/**
 * Basic definitions and Clause Storage.
 */

#pragma once

#include "util/span.h"
#include <cstdint>
#include <functional>
#include <tuple>
#include <vector>

namespace dawn {

/**
 * A literal is a variable number + sign. Also there are some special lits:
 * one, zero, undef, elim,
 */
class Lit
{
	uint32_t val_;

  public:
	/** constructors */
	constexpr Lit() : val_(-3) {}
	explicit constexpr Lit(uint32_t val) : val_(val) {}
	constexpr Lit(int var, bool s) : val_(2 * var + (s ? 1 : 0)) {}

	/** special values of Lit */
	static constexpr Lit zero() { return Lit{(uint32_t)-1}; }
	static constexpr Lit one() { return Lit{(uint32_t)-2}; }
	static constexpr Lit undef() { return Lit{(uint32_t)-4}; }
	static constexpr Lit elim() { return Lit{(uint32_t)-6}; }
	static constexpr Lit fixed(bool sign) { return one() ^ sign; }

	/** basic accesors and properties */
	constexpr operator int() const { return (int)val_; }
	constexpr int var() const { return val_ >> 1; }
	constexpr bool sign() const { return (val_ & 1) != 0; }
	constexpr bool proper() const { return (int32_t)val_ >= 0; }
	constexpr bool fixed() const { return (val_ & ~1) == (uint32_t)-2; }

	/** IO in dimacs convention */
	constexpr static Lit fromDimacs(int x)
	{
		return Lit(x > 0 ? 2 * x - 2 : -2 * x - 1);
	}
	constexpr int toDimacs() const { return sign() ? -var() - 1 : var() + 1; }

	/** misc */
	constexpr bool operator==(Lit b) const { return val_ == b.val_; }

	constexpr Lit neg() const { return Lit(val_ ^ 1); }
	constexpr Lit operator^(bool sign) const { return Lit(val_ ^ sign); }
};

/**
 * - removes duplicates and Lit::zero()
 * - returns -1 for tautologies and Lit::one()
 * - otherwiese, returns new size
 */
inline int normalizeClause(util::span<Lit> lits)
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

class Clause
{
  public:
	// 4 byte header
	uint16_t size_;
	uint8_t flags_;
	uint8_t glue;

	// array of Lits
	// Lit _lits[]; // not valid C++

	Clause() {}
	Clause(const Clause &) = delete;

	/** array-like access to literals */
	util::span<Lit> lits() { return util::span<Lit>{(Lit *)(this + 1), size_}; }
	util::span<const Lit> lits() const
	{
		return util::span<const Lit>{(Lit *)(this + 1), size_};
	}

	/** make Clause usable as span<Lit> without calling '.lits()' explicitly */
	uint16_t size() const { return size_; }
	Lit &operator[](size_t i) { return lits()[i]; }
	const Lit &operator[](size_t i) const { return lits()[i]; }
	operator util::span<Lit>() { return lits(); }
	operator util::span<const Lit>() const { return lits(); }
	auto begin() { return lits().begin(); }
	auto begin() const { return lits().begin(); }
	auto end() { return lits().end(); }
	auto end() const { return lits().end(); }

	/** flags */
	bool isRemoved() const { return (flags_ & 1) != 0; }
	void remove() { flags_ |= 1; }
	bool irred() const { return (flags_ & 2) != 0; }
	void makeIrred() { flags_ |= 2; }
	void makeRed() { flags_ &= ~2; }

	/** remove a literal from this clause. returns false if not found */
	bool removeLiteral(Lit a)
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

	/** remove two literals from this clause, only if both are found */
	bool removeLitarals(Lit a, Lit b)
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

	/**
	 * Add a literal to the clause.
	 * NOTE: this is unsafe, because the clause does not know its own capacity.
	 *       only use right after succesfully removing another literal.
	 */
	void addLiteralUnchecked(Lit a)
	{
		size_ += 1;
		lits()[size_ - 1] = a;
	}

	/** check if this clause contains some literal */
	bool contains(Lit a) const
	{
		for (Lit b : lits())
			if (a == b)
				return true;
		return false;
	}

	bool contains_variable(int v) const
	{
		for (Lit b : lits())
			if (b.var() == v)
				return true;
		return false;
	}

	/**
	 * - remove duplicate/fixed lits
	 * - remove clause if tautological
	 */
	void normalize()
	{
		if (int s = normalizeClause(lits()); s == -1)
			remove();
		else
			size_ = (uint16_t)s;
	}
};

/**
 * Reference to a clause inside a ClauseStorage object.
 * Technically just a (31 bit) index into an array.
 */
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
	std::vector<uint32_t> store;
	std::vector<CRef> clauses;

  public:
	/** add a new clause, no checking of lits done */
	CRef addClause(util::span<const Lit> lits, bool irred)
	{
		if (lits.size() > UINT16_MAX)
		{
			fmt::print("ERROR: clause to long for storage\n");
			exit(-1);
		}

		Clause header;
		header.size_ = (uint16_t)lits.size();
		header.flags_ = 0;
		header.glue = (uint8_t)std::min((size_t)255,
		                                lits.size()); // may decrease later
		if (irred)
			header.makeIrred();
		auto index = store.size();
		if (index > CREF_MAX)
		{
			fmt::print("ERROR: clause storage full\n");
			exit(-1);
		}

		store.push_back(*(uint32_t *)&header);
		for (auto l : lits)
			store.push_back(l);

		auto r = CRef((uint32_t)index);
		clauses.push_back(r);
		return r;
	}

	CRef addBinary(Lit a, Lit b)
	{
		return addClause(std::array<Lit, 2>{a, b}, true);
	}

	Clause &operator[](CRef i) { return *(Clause *)&store[i]; }

	const Clause &operator[](CRef i) const { return *(Clause *)&store[i]; }

	struct iterator
	{
		ClauseStorage &cs_;
		std::vector<CRef>::iterator it_;

	  public:
		iterator(ClauseStorage &cs, std::vector<CRef>::iterator it)
		    : cs_(cs), it_(it)
		{
			while (it_ != cs.clauses.end() && cs[*it_].isRemoved())
				++it_;
		}

		std::tuple<CRef, Clause &> operator*()
		{
			return std::make_tuple(*it_, std::ref(cs_[*it_]));
		}

		void operator++()
		{
			++it_;
			while (it_ != cs_.clauses.end() && cs_[*it_].isRemoved())
				++it_;
		}

		bool operator!=(const iterator &r) const { return it_ != r.it_; }
	};

	iterator begin() { return iterator(*this, clauses.begin()); }

	iterator end() { return iterator(*this, clauses.end()); }

	struct const_iterator
	{
		const ClauseStorage &cs_;
		std::vector<CRef>::const_iterator it_;

	  public:
		const_iterator(const ClauseStorage &cs,
		               std::vector<CRef>::const_iterator it)
		    : cs_(cs), it_(it)
		{
			while (it_ != cs_.clauses.end() && cs_[*it_].isRemoved())
				++it_;
		}

		std::tuple<CRef, const Clause &> operator*()
		{
			return std::make_tuple(*it_, std::ref(cs_[*it_]));
		}

		void operator++()
		{
			++it_;
			while (it_ != cs_.clauses.end() && cs_[*it_].isRemoved())
				++it_;
		}

		bool operator!=(const const_iterator &r) const { return it_ != r.it_; }
	};

	const_iterator begin() const
	{
		return const_iterator(*this, clauses.begin());
	}

	const_iterator end() const { return const_iterator(*this, clauses.end()); }

	/** number of (non-removed) clauses */
	size_t count() const
	{
		size_t r = 0;
		for (auto _ [[maybe_unused]] : clauses)
			++r;
		return r;
	}

	size_t memory_usage() const
	{
		return store.capacity() * sizeof(uint32_t) +
		       clauses.capacity() * sizeof(CRef);
	}

	/**
	 * Actually remove clauses that are marked as such by moving all
	 * remaining clauses closer together. Invalidates all CRef's.
	 */
	void compactify();

	/**
	 * Remove all clauses (but keep allocated memory). Invalidates all
	 * CRef's.
	 */
	void clear();
};

static_assert(sizeof(Lit) == 4);
static_assert(sizeof(Clause) == 4);

} // namespace dawn

template <> struct fmt::formatter<dawn::Lit>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Lit a, FormatContext &ctx)
	{
		// NOTE: '-elim' and '-undef' should never happen, just for debugging
		if (a.proper())
			return format_to(ctx.out(), "{}", a.toDimacs());
		else if (a == dawn::Lit::undef())
			return format_to(ctx.out(), "undef");
		else if (a == dawn::Lit::one())
			return format_to(ctx.out(), "true");
		else if (a == dawn::Lit::zero())
			return format_to(ctx.out(), "false");
		else if (a == dawn::Lit::elim())
			return format_to(ctx.out(), "elim");
		else if (a == dawn::Lit::elim().neg())
			return format_to(ctx.out(), "-elim");
		else if (a == dawn::Lit::undef().neg())
			return format_to(ctx.out(), "-undef");
		else
			assert(false);
	}
};

template <> struct fmt::formatter<dawn::Clause>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Clause const &cl, FormatContext &ctx)
	{
		auto it = ctx.out();
		for (size_t i = 0; i < cl.size(); ++i)
			it = format_to(it, i == 0 ? "{}" : " {}", cl[i]);
		return it;
	}
};

template <> struct std::hash<dawn::Lit>
{
	std::size_t operator()(dawn::Lit const &l) const noexcept { return (int)l; }
};
