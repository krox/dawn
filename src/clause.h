/**
 * Basic definitions and Clause Storage.
 */
#ifndef CLAUSE_H
#define CLAUSE_H

#include <cstdint>
#include <vector>
#include <iostream>

/**
 * A literal is a variable number + sign. Also there are some special lits:
 * one, zero, undef, elim,
 */
class Lit
{
	uint32_t _val;

public:
	/** constructors */
	inline Lit() : _val(-3) {}
	inline constexpr Lit(uint32_t val) : _val(val) {}
	inline Lit(uint32_t var, bool s) : _val(2*var+(s?1:0)) {}

	/** basic accesors and properties */
	inline uint32_t toInt() const { return _val; }
	inline uint32_t var() const { return toInt() >> 1; }
	inline bool sign() const { return (toInt()&1) != 0; }
	inline bool proper() const { return (int32_t)toInt() >= 0; }
	inline bool fixed() const { return (toInt()&~1) == (uint32_t)-2; }

	/** IO in dimacs convention */
	inline static Lit fromDimacs(int x)
	{
		return Lit(x>0?2*x-2:-2*x-1);
	}

	inline int toDimacs() const
	{
		return sign()?-var()-1:var()+1;
	}

	friend std::ostream& operator<<(std::ostream& stream, Lit l);

	/** misc */
	inline bool operator==(Lit b) const
	{
		return _val == b._val;
	}

	inline Lit neg() const
	{
		return Lit(toInt()^1);
	}
};

/** special values of Lit */
inline constexpr Lit zero = {(uint32_t)-1};
inline constexpr Lit one = {(uint32_t)-2};
inline constexpr Lit undef = {(uint32_t)-3};
inline constexpr Lit elim = {(uint32_t)-4};

class Clause
{
public:
	// 4 byte header
	uint16_t _size;
	uint8_t _flags;
	uint8_t _reserved;

	// array of Lits
	Lit lits[0];

	Clause() {}
	Clause(const Clause&) = delete;

	uint16_t size() const
	{
		return _size;
	}
};

/** Reference to a clause inside a ClauseStorage object. */
class CRef
{
public:
	// NOTE: highest bit is used for bit-packing in 'Watch' and 'Reason'
	uint32_t _val;
	CRef(uint32_t val)
		:_val(val)
	{}
};


#define CREF_MAX (UINT32_MAX>>1)

class ClauseStorage
{
	std::vector<uint32_t> store;

public:
	std::vector<CRef> clauses;

	/** add a new clause, no checking of lits done */
	inline CRef addClause(const std::vector<Lit>& lits)
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
			store.push_back(l.toInt());

		auto r = CRef((uint32_t)index);
		clauses.push_back(r);
		return r;
	}

	inline Clause& operator[](CRef i)
	{
		return *(Clause*)&store[i._val];
	}

	inline const Clause& operator[](CRef i) const
	{
		return *(Clause*)&store[i._val];
	}

	friend std::ostream& operator<<(std::ostream& stream, const ClauseStorage& clauses);
};

static_assert(sizeof(Lit) == 4);
static_assert(sizeof(Clause) == 4);

#endif
