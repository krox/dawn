#pragma once

// helper functions to create sat instances from binary integer expressions

#include "sat/cnf.h"

namespace dawn {

template <int N> struct Register
{
	std::array<Lit, N> lits_;
	Cnf &sat_;

	Register(Cnf &sat, uint32_t value = 0) : sat_(sat)
	{
		for (int i = 0; i < N; ++i)
			lits_[i] = Lit::fixed(!((value >> i) & 1));
	}

	static Register unknown(Cnf &sat)
	{
		auto r = Register(sat);
		for (int i = 0; i < N; ++i)
			r.lits_[i] = Lit(sat.add_var(), false);
		return r;
	}

	Register(Register const &other) = default;
	Register &operator=(Register const &other)
	{
		assert(&sat_ == &other.sat_);
		lits_ = other.lits_;
		return *this;
	}
};

Lit make_and(Cnf &sat, Lit a, Lit b)
{
	if (a == Lit::zero() || b == Lit::zero())
		return Lit::zero();
	if (a == Lit::one())
		return b;
	if (b == Lit::one())
		return a;

	Lit r = Lit(sat.add_var(), false);
	sat.add_and_clause_safe(r, a, b);
	return r;
}

Lit make_or(Cnf &sat, Lit a, Lit b)
{
	return make_and(sat, a.neg(), b.neg()).neg();
}

Lit make_xor(Cnf &sat, Lit a, Lit b)
{
	if (a.fixed())
		return b ^ !a.sign();
	if (b.fixed())
		return a ^ !b.sign();

	Lit r = Lit(sat.add_var(), false);
	sat.add_xor_clause_safe(r, a, b);
	return r;
}

Lit make_xor(Cnf &sat, Lit a, Lit b, Lit c)
{
	if (a.fixed())
		return make_xor(sat, b, c) ^ !a.sign();
	if (b.fixed())
		return make_xor(sat, a, c) ^ !b.sign();
	if (c.fixed())
		return make_xor(sat, a, b) ^ !c.sign();

	Lit r = Lit(sat.add_var(), false);
	sat.add_xor_clause_safe(r, a, b, c);
	return r;
}

Lit make_maj(Cnf &sat, Lit a, Lit b, Lit c)
{
	if (a == Lit::zero())
		return make_and(sat, b, c);
	if (b == Lit::zero())
		return make_and(sat, a, c);
	if (c == Lit::zero())
		return make_and(sat, a, b);
	if (a == Lit::one())
		return make_or(sat, b, c);
	if (b == Lit::one())
		return make_or(sat, a, c);
	if (c == Lit::one())
		return make_or(sat, a, b);

	Lit r = Lit(sat.add_var(), false);
	sat.add_maj_clause_safe(r, a, b, c);
	return r;
}

Lit make_ite(Cnf &sat, Lit a, Lit b, Lit c)
{
	if (a == Lit::one())
		return b;
	if (a == Lit::zero())
		return c;
	// plenty more special cases missing...

	Lit r = Lit(sat.add_var(), false);
	sat.add_ite_clause_safe(r, a, b, c);
	return r;
}

template <int N>
Register<N> operator&(Register<N> const &a, Register<N> const &b)
{
	assert(&a.sat_ == &b.sat_);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = make_and(a.sat_, a.lits_[i], b.lits_[i]);
	return r;
}

template <int N>
Register<N> operator|(Register<N> const &a, Register<N> const &b)
{
	assert(&a.sat_ == &b.sat_);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = make_or(a.sat_, a.lits_[i], b.lits_[i]);
	return r;
}

template <int N>
Register<N> make_xor(Register<N> const &a, Register<N> const &b)
{
	assert(&a.sat_ == &b.sat_);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = make_xor(a.sat_, a.lits_[i], b.lits_[i]);
	return r;
}

template <int N>
Register<N> make_xor(Register<N> const &a, Register<N> const &b,
                     Register<N> const &c)
{
	assert(&a.sat_ == &b.sat_ && &a.sat_ == &c.sat_);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = make_xor(a.sat_, a.lits_[i], b.lits_[i], c.lits_[i]);
	return r;
}

template <int N>
Register<N> operator^(Register<N> const &a, Register<N> const &b)
{
	return make_xor(a, b);
}

template <int N> Register<N> operator~(Register<N> const &a)
{
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = a.lits_[i].neg();
	return r;
}

template <int N>
Register<N> maj(Register<N> const &a, Register<N> const &b,
                Register<N> const &c)
{
	assert(&a.sat_ == &b.sat_ && &a.sat_ == &c.sat_);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = make_maj(a.sat_, a.lits_[i], b.lits_[i], c.lits_[i]);
	return r;
}

template <int N>
Register<N> ite(Register<N> const &a, Register<N> const &b,
                Register<N> const &c)
{
	assert(&a.sat_ == &b.sat_ && &a.sat_ == &c.sat_);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = make_ite(a.sat_, a.lits_[i], b.lits_[i], c.lits_[i]);
	return r;
}

template <int N> Register<N> operator>>(Register<N> const &a, int shift)
{
	assert(0 <= shift && shift < N);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N - shift; ++i)
		r.lits_[i] = a.lits_[(i + shift) % N];
	for (int i = N - shift; i < N; ++i)
		r.lits_[i] = Lit::zero();
	return r;
}

template <int N> Register<N> operator<<(Register<N> const &a, int shift)
{
	assert(0 <= shift && shift < N);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < shift; ++i)
		r.lits_[i] = Lit::zero();
	for (int i = shift; i < N; ++i)
		r.lits_[i] = a.lits_[(i - shift) % N];
	return r;
}

template <int N> Register<N> rotr(Register<N> const &a, int shift)
{
	assert(0 <= shift && shift < N);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = a.lits_[(i + shift) % N];
	return r;
}

template <int N> Register<N> rotl(Register<N> const &a, int shift)
{
	assert(0 <= shift && shift < N);
	auto r = Register<N>(a.sat_);
	for (int i = 0; i < N; ++i)
		r.lits_[i] = a.lits_[(i - shift + N) % N];
	return r;
}

template <int N>
Register<N> operator+(Register<N> const &a, Register<N> const &b)
{
	assert(&a.sat_ == &b.sat_);
	auto r = Register<N>(a.sat_);
	Lit carry = Lit::zero();
	for (int i = 0; i < N; ++i)
	{
		r.lits_[i] = make_xor(a.sat_, a.lits_[i], b.lits_[i], carry);
		carry = make_maj(a.sat_, a.lits_[i], b.lits_[i], carry);
	}
	return r;
}

template <int N> Register<N> operator+(Register<N> const &a, uint32_t b)
{
	return a + Register<N>(a.sat_, b);
}

template <int N> Register<N> &operator+=(Register<N> &a, Register<N> const &b)
{
	a = a + b;
	return a;
}

template <int N> void equal(Register<N> const &a, Register<N> const &b)
{
	for (int i = 0; i < N; ++i)
	{
		a.sat_.add_clause_safe({{a.lits_[i].neg(), b.lits_[i]}});
		a.sat_.add_clause_safe({{a.lits_[i], b.lits_[i].neg()}});
	}
}

} // namespace dawn
