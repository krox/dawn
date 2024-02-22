#pragma once

#include "clause.h"
#include "fmt/format.h"
#include "fmt/os.h"
#include "util/bit_vector.h"
#include <vector>

namespace dawn {

class lbool
{
	// 0=undef, 1=true, 2=false
	uint8_t v_ = 0;

  public:
	static constexpr lbool unchecked(uint8_t v)
	{
		lbool b;
		b.v_ = v;
		return b;
	}

	lbool() = default;
	constexpr explicit lbool(bool b) noexcept : v_(1 << !b) {}
	constexpr explicit operator bool() const noexcept { return v_ == 1; }

	constexpr bool operator==(lbool b) const noexcept { return v_ == b.v_; }
	constexpr bool operator!=(lbool b) const noexcept { return v_ != b.v_; }
	constexpr bool operator==(bool b) const noexcept
	{
		return *this == lbool(b);
	}
	constexpr bool operator!=(bool b) const noexcept
	{
		return *this != lbool(b);
	}

	constexpr lbool operator~() const noexcept
	{
		return unchecked((0b011000 >> (v_ * 2)) & 3);
	}

	constexpr lbool operator&(lbool b) const noexcept
	{
		return unchecked((0b101010100100100000 >> (v_ * 2 + b.v_ * 6)) & 3);
	}

	constexpr lbool operator|(lbool b) const noexcept
	{
		return unchecked((0b100100010101000100 >> (v_ * 2 + b.v_ * 6)) & 3);
	}

	constexpr lbool operator^(lbool b) const noexcept
	{
		return unchecked((0b100100011000000000 >> (v_ * 2 + b.v_ * 6)) & 3);
	}

	constexpr lbool operator^(bool b) const noexcept
	{
		return unchecked((0b011000100100 >> (v_ * 2 + b * 6)) & 3);
	}

	constexpr void operator&=(lbool b) noexcept { *this = *this & b; }
	constexpr void operator^=(lbool b) noexcept { *this = *this | b; }
	constexpr void operator|=(lbool b) noexcept { *this = *this ^ b; }
	constexpr void operator|=(bool b) noexcept { *this = *this ^ b; }
};

constexpr lbool lundef = lbool::unchecked(0);
constexpr lbool ltrue = lbool::unchecked(1);
constexpr lbool lfalse = lbool::unchecked(2);

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
	// TODO: this should not exist I think
	void force_set(Lit a) noexcept;

	// returns true if all variables have been assigned
	bool complete() const noexcept;

	// current value of a variable
	lbool operator()(int v) const noexcept;

	// current value of clause
	lbool operator()(Lit a) const noexcept;
	lbool operator()(Lit a, Lit b) const noexcept;
	lbool operator()(Lit a, Lit b, Lit c) const noexcept;
	lbool operator()(std::span<const Lit> cl) const noexcept;

	// backward-compatibility...
	bool operator[](Lit a) const noexcept { return assign_[a]; }

	// check if a clause is currently satisfied
	bool satisfied(Lit a) const noexcept;
	bool satisfied(Lit a, Lit b) const noexcept;
	bool satisfied(Lit a, Lit b, Lit c) const noexcept;
	bool satisfied(std::span<const Lit> cl) const noexcept;
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

inline lbool Assignment::operator()(int v) const noexcept
{
	static_assert(sizeof(*assign_.data()) == 8);
	return lbool::unchecked((assign_.data()[v >> 5] >> ((v >> 5) * 2)) & 3);
}

inline lbool Assignment::operator()(Lit a) const noexcept
{
	return (*this)(a.var()) ^ a.sign();
}

inline lbool Assignment::operator()(Lit a, Lit b) const noexcept
{
	return (*this)(a) | (*this)(b);
}

inline lbool Assignment::operator()(Lit a, Lit b, Lit c) const noexcept
{
	return (*this)(a) | (*this)(b) | (*this)(c);
}

inline lbool Assignment::operator()(std::span<const Lit> cl) const noexcept
{
	auto r = lfalse;
	for (auto a : cl)
		r |= (*this)(a);
	return r;
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

inline bool Assignment::satisfied(std::span<const Lit> cl) const noexcept
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
				if (!first)
					*it++ = ' ';
				it = fmt::format_to(it, "{}", dawn::Lit(i));
				first = false;
			}
		return it;
	}
};
