#pragma once

#include "clause.h"
#include "fmt/format.h"
#include "fmt/os.h"
#include "util/bit_vector.h"
#include <vector>

namespace dawn {

// partial assignment of variables with some convenience functions
class Assignment
{
	// invariant: variables can be un-assgined, but not contradictory
	util::bit_vector assign_;

  public:
	Assignment() = default;

	explicit Assignment(int n) : assign_(2 * n) {}

	Assignment(util::bit_vector a) noexcept : assign_(std::move(a))
	{
		assert(assign_.size() % 2 == 0);
		for (int i = 0; i < var_count(); ++i)
			assert(!(assign_[2 * i] && assign_[2 * i + 1]));
	}

	// number of variables
	int var_count() const noexcept;

	// set/unset a variable (assuming it was previously unset/set)
	void set(Lit a) noexcept;
	void unset(Lit a) noexcept;

	// set a variable (overwrite previous assignment if any)
	void force_set(Lit a) noexcept;

	// returns true if all variables have been assigned
	bool complete() const noexcept;

	// check if a clause is currently satisfied
	bool satisfied(Lit a) const noexcept;
	bool satisfied(Lit a, Lit b) const noexcept;
	bool satisfied(Lit a, Lit b, Lit c) const noexcept;
	bool satisfied(util::span<const Lit> cl) const noexcept;
	bool satisfied(ClauseStorage const &cls) const noexcept;
};

inline int Assignment::var_count() const noexcept
{
	return (int)(assign_.size() / 2);
}

inline void Assignment::set(Lit a) noexcept
{
	assert(!assign_[a] && !assign_[a.neg()]);
	assign_[a] = true;
}

inline void Assignment::unset(Lit a) noexcept
{
	assert(assign_[a]);
	assign_[a] = false;
}

inline void Assignment::force_set(Lit a) noexcept
{
	assign_[a] = true;
	assign_[a.neg()] = false;
}

inline bool Assignment::complete() const noexcept
{
	return (int)assign_.count() == var_count();
}

inline bool Assignment::satisfied(Lit a) const noexcept { return assign_[a]; }

inline bool Assignment::satisfied(Lit a, Lit b) const noexcept
{
	return assign_[a] || assign_[b];
}

inline bool Assignment::satisfied(Lit a, Lit b, Lit c) const noexcept
{
	return assign_[a] || assign_[b] || assign_[c];
}

inline bool Assignment::satisfied(util::span<const Lit> cl) const noexcept
{
	for (Lit lit : cl)
		if (assign_[lit])
			return true;
	return false;
}

inline bool Assignment::satisfied(ClauseStorage const &cls) const noexcept
{
	for (auto &cl : cls.all())
		if (!satisfied(cl))
			return false;
	return true;
}

} // namespace dawn

template <> struct fmt::formatter<dawn::Assignment>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Assignment const &a, FormatContext &ctx)
	{
		auto it = ctx.out();
		bool first = true;
		for (int i = 0; i < a.var_count() * 2; ++i)
			if (a.satisfied(dawn::Lit(i)))
			{
				it = format_to(it, first ? "{}" : " {}", dawn::Lit(i));
				first = false;
			}
		return it;
	}
};
