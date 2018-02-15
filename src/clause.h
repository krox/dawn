/**
 * Basic definitions and Clause Storage.
 */
#ifndef CLAUSE_H
#define CLAUSE_H

#include <cstdint>
#include <vector>
#include <iostream>
#include <tuple>
#include <functional>

/**
 * A literal is a variable number + sign. Also there are some special lits:
 * one, zero, undef, elim,
 */
class Lit
{
	uint32_t _val;

public:
	/** constructors */
	Lit() : _val(-3) {}
	explicit constexpr Lit(uint32_t val) : _val(val) {}
	Lit(uint32_t var, bool s) : _val(2*var+(s?1:0)) {}

	/** basic accesors and properties */
	operator uint32_t() const { return _val; }
	uint32_t var() const { return _val >> 1; }
	bool sign() const { return (_val&1) != 0; }
	bool proper() const { return (int32_t)_val >= 0; }
	bool fixed() const { return (_val&~1) == (uint32_t)-2; }

	/** IO in dimacs convention */
	static Lit fromDimacs(int x)
	{
		return Lit(x>0?2*x-2:-2*x-1);
	}

	int toDimacs() const
	{
		return sign()?-var()-1:var()+1;
	}

	friend std::ostream& operator<<(std::ostream& stream, Lit l);

	/** misc */
	bool operator==(Lit b) const
	{
		return _val == b._val;
	}

	Lit neg() const
	{
		return Lit(_val^1);
	}
};

/** special values of Lit */
#define LIT_ZERO Lit((uint32_t)-1)
#define LIT_ONE Lit((uint32_t)-2)
#define LIT_UNDEF Lit((uint32_t)-3)
#define LIT_ELIM Lit((uint32_t)-4)

class Clause
{
public:
	// 4 byte header
	uint16_t _size;
	uint8_t _flags;
	uint8_t _reserved;

	// array of Lits
	Lit _lits[0];

	Clause() {}
	Clause(const Clause&) = delete;

	uint16_t size() const
	{
		return _size;
	}

	Lit& operator[](size_t i)
	{
		return _lits[i];
	}

	const Lit& operator[](size_t i) const
	{
		return _lits[i];
	}

	typedef Lit* iterator;
	typedef const Lit* const_iterator;
	iterator begin() { return &_lits[0]; }
	iterator end() { return &_lits[_size]; }
	const_iterator begin() const { return &_lits[0]; }
	const_iterator end() const { return &_lits[_size]; }
};

/** Reference to a clause inside a ClauseStorage object. */
class CRef
{
	// NOTE: highest bit is used for bit-packing in 'Watch' and 'Reason'
	uint32_t _val;
public:
	constexpr explicit CRef(uint32_t val)
		:_val(val)
	{}

	operator uint32_t() const
	{
		return _val;
	}
};

#define CREF_MAX (UINT32_MAX>>1)
#define CREF_UNDEF CRef(UINT32_MAX)

class ClauseStorage
{
private:
	std::vector<uint32_t> store;
	std::vector<CRef> clauses;

public:

	/** add a new clause, no checking of lits done */
	CRef addClause(const std::vector<Lit>& lits)
	{
		if(lits.size() > UINT16_MAX)
		{
			std::cerr << "ERROR: clause to long for storage" << std::endl;
			exit(-1);
		}

		Clause header;
		header._size = (uint16_t)lits.size();
		header._flags = 0;
		auto index = store.size();
		if(index > CREF_MAX)
		{
			std::cerr << "ERROR: clause storage full" << std::endl;
			exit(-1);
		}
		store.reserve(store.size()+1+lits.size());
		store.push_back(*(uint32_t*)&header);
		for(auto l : lits)
			store.push_back(l);

		auto r = CRef((uint32_t)index);
		clauses.push_back(r);
		return r;
	}

	Clause& operator[](CRef i)
	{
		return *(Clause*)&store[i];
	}

	const Clause& operator[](CRef i) const
	{
		return *(Clause*)&store[i];
	}

	struct iterator
	{
		ClauseStorage& cs;
		std::vector<CRef>::iterator it;
	public:
		iterator(ClauseStorage& cs, std::vector<CRef>::iterator it)
			: cs(cs), it(it)
		{}

		std::tuple<CRef, Clause&> operator*()
		{
			return std::make_tuple(*it, std::ref(cs[*it]));
		}

		void operator++()
		{
			++it;
		}

		bool operator!=(const iterator& r) const
		{
			return it != r.it;
		}
	};

	iterator begin()
	{
		return iterator(*this, clauses.begin());
	}

	iterator end()
	{
		return iterator(*this, clauses.end());
	}

	struct const_iterator
	{
		const ClauseStorage& cs;
		std::vector<CRef>::const_iterator it;
	public:
		const_iterator(const ClauseStorage& cs, std::vector<CRef>::const_iterator it)
			: cs(cs), it(it)
		{}

		std::tuple<CRef,const Clause&> operator*()
		{
			return std::make_tuple(*it, std::ref(cs[*it]));
		}

		void operator++()
		{
			++it;
		}

		bool operator!=(const const_iterator& r) const
		{
			return it != r.it;
		}
	};

	const_iterator begin() const
	{
		return const_iterator(*this, clauses.begin());
	}

	const_iterator end() const
	{
		return const_iterator(*this, clauses.end());
	}
};

static_assert(sizeof(Lit) == 4);
static_assert(sizeof(Clause) == 4);

std::ostream& operator<<(std::ostream& stream, const ClauseStorage& clauses);

#endif
