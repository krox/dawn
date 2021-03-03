#pragma once

#include "clause.h"
#include "fmt/format.h"
#include "fmt/os.h"
#include "util/bit_vector.h"
#include <vector>

namespace dawn {

struct Solution
{
	util::bit_vector assign;

	Solution() : assign(0) {}

	explicit Solution(int n) : assign(2 * n) {}

	Solution(util::bit_vector assign) : assign(std::move(assign)) {}

	/** get/set varCount */
	int varCount() const;
	void varCount(int n);

	/** set a literal */
	void set(Lit a);

	/** check that each variable is either true or false */
	bool valid() const;

	/** check if a clause is satisfied in the assignment */
	bool satisfied(Lit a) const;
	bool satisfied(Lit a, Lit b) const;
	bool satisfied(Lit a, Lit b, Lit c) const;
	bool satisfied(util::span<const Lit> cl) const;
	bool satisfied(ClauseStorage const &cls) const;
};

inline int Solution::varCount() const { return (int)(assign.size() / 2); }

inline void Solution::varCount(int n) { assign.resize(2 * n); }

inline void Solution::set(Lit a) { assign[a] = true; }

inline bool Solution::valid() const
{
	for (int i = 0; i < (int)assign.size(); i += 2)
		if (assign[i] == assign[i + 1])
			return false;
	return true;
}

inline bool Solution::satisfied(Lit a) const { return assign[a]; }

inline bool Solution::satisfied(Lit a, Lit b) const
{
	return assign[a] || assign[b];
}

inline bool Solution::satisfied(Lit a, Lit b, Lit c) const
{
	return assign[a] || assign[b] || assign[c];
}

inline bool Solution::satisfied(util::span<const Lit> cl) const
{
	for (Lit lit : cl)
		if (assign[lit])
			return true;
	return false;
}

inline bool Solution::satisfied(ClauseStorage const &cls) const
{
	for (auto [ci, cl] : cls)
	{
		(void)ci;
		if (!satisfied(cl))
			return false;
	}
	return true;
}

} // namespace dawn
