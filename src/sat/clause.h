/**
 * Basic definitions and Clause Storage.
 */
#ifndef SAT_CLAUSE_H
#define SAT_CLAUSE_H

#include <cstdint>
#include <functional>
#include <iostream>
#include <tuple>
#include <vector>

/**
 * A literal is a variable number + sign. Also there are some special lits:
 * one, zero, undef, elim,
 */
class Lit
{
	uint32_t val_;

  public:
	/** constructors */
	Lit() : val_(-3) {}
	explicit constexpr Lit(uint32_t val) : val_(val) {}
	Lit(uint32_t var, bool s) : val_(2 * var + (s ? 1 : 0)) {}

	/** special values of Lit */
	static constexpr Lit zero() { return Lit{(uint32_t)-1}; }
	static constexpr Lit one() { return Lit{(uint32_t)-2}; }
	static constexpr Lit undef() { return Lit{(uint32_t)-3}; }
	static constexpr Lit elim() { return Lit{(uint32_t)-4}; }

	/** basic accesors and properties */
	constexpr operator uint32_t() const { return val_; }
	constexpr uint32_t var() const { return val_ >> 1; }
	bool sign() const { return (val_ & 1) != 0; }
	bool proper() const { return (int32_t)val_ >= 0; }
	bool fixed() const { return (val_ & ~1) == (uint32_t)-2; }

	/** IO in dimacs convention */
	static Lit fromDimacs(int x) { return Lit(x > 0 ? 2 * x - 2 : -2 * x - 1); }

	int toDimacs() const { return sign() ? -var() - 1 : var() + 1; }

	friend std::ostream &operator<<(std::ostream &stream, Lit l);

	/** misc */
	bool operator==(Lit b) const { return val_ == b.val_; }

	Lit neg() const { return Lit(val_ ^ 1); }
};

class Clause
{
  public:
	// 4 byte header
	uint16_t size_;
	uint8_t flags_;
	uint8_t reserved_;

	// array of Lits
	// Lit _lits[]; // not valid C++

	Lit *lits_() { return (Lit *)(this + 1); }
	const Lit *lits_() const { return (const Lit *)(this + 1); }

	Clause() {}
	Clause(const Clause &) = delete;

	/** array-like access to literals */
	uint16_t size() const { return size_; }
	Lit &operator[](size_t i) { return lits_()[i]; }
	const Lit &operator[](size_t i) const { return lits_()[i]; }
	typedef Lit *iterator;
	typedef const Lit *const_iterator;
	iterator begin() { return &lits_()[0]; }
	iterator end() { return &lits_()[size_]; }
	const_iterator begin() const { return lits_(); }
	const_iterator end() const { return lits_() + size_; }

	/** flags */
	bool isRemoved() const { return (flags_ & 1) != 0; }
	void remove() { flags_ |= 1; }
};

/** Reference to a clause inside a ClauseStorage object. */
class CRef
{
	// NOTE: highest bit is used for bit-packing in 'Watch' and 'Reason'
	uint32_t _val;

  public:
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
	CRef addClause(const std::vector<Lit> &lits)
	{
		if (lits.size() > UINT16_MAX)
		{
			std::cerr << "ERROR: clause to long for storage" << std::endl;
			exit(-1);
		}

		Clause header;
		header.size_ = (uint16_t)lits.size();
		header.flags_ = 0;
		auto index = store.size();
		if (index > CREF_MAX)
		{
			std::cerr << "ERROR: clause storage full" << std::endl;
			exit(-1);
		}

		store.push_back(*(uint32_t *)&header);
		for (auto l : lits)
			store.push_back(l);

		auto r = CRef((uint32_t)index);
		clauses.push_back(r);
		return r;
	}

	Clause &operator[](CRef i) { return *(Clause *)&store[i]; }

	const Clause &operator[](CRef i) const { return *(Clause *)&store[i]; }

	struct iterator
	{
		ClauseStorage &cs;
		std::vector<CRef>::iterator it;

	  public:
		iterator(ClauseStorage &cs, std::vector<CRef>::iterator it)
		    : cs(cs), it(it)
		{}

		std::tuple<CRef, Clause &> operator*()
		{
			return std::make_tuple(*it, std::ref(cs[*it]));
		}

		void operator++() { ++it; }

		bool operator!=(const iterator &r) const { return it != r.it; }
	};

	iterator begin()
	{
		iterator it(*this, clauses.begin());
		while (it != end() && std::get<1>(*it).isRemoved())
			++it;
		return it;
	}

	iterator end() { return iterator(*this, clauses.end()); }

	struct const_iterator
	{
		const ClauseStorage &cs;
		std::vector<CRef>::const_iterator it;

	  public:
		const_iterator(const ClauseStorage &cs,
		               std::vector<CRef>::const_iterator it)
		    : cs(cs), it(it)
		{}

		std::tuple<CRef, const Clause &> operator*()
		{
			return std::make_tuple(*it, std::ref(cs[*it]));
		}

		void operator++() { ++it; }

		bool operator!=(const const_iterator &r) const { return it != r.it; }
	};

	const_iterator begin() const
	{
		return const_iterator(*this, clauses.begin());
	}

	const_iterator end() const { return const_iterator(*this, clauses.end()); }
};

static_assert(sizeof(Lit) == 4);
static_assert(sizeof(Clause) == 4);

std::ostream &operator<<(std::ostream &stream, const Clause &clause);
std::ostream &operator<<(std::ostream &stream, const ClauseStorage &clauses);

#endif
