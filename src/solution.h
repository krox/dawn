#ifndef SOLUTION_H
#define SOLUTION_H

class Solution
{
	std::vector<bool> assign;

public:
	Solution()
		: assign(0)
	{}

	Solution(std::vector<bool> assign)
		: assign(std::move(assign))
	{}

	/** get/set varCount */
	bool empty() const;
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
	bool satisfied(const std::vector<Lit>& cl) const;

	/** output in dimacs format */
	friend std::ostream& operator<<(std::ostream& stream, const Solution& sol);
};

inline bool Solution::empty() const
{
	return assign.empty();
}

inline int Solution::varCount() const
{
	return (int)(assign.size()/2);
}

inline void Solution::varCount(int n)
{
	assign.resize(2*n);
}

inline void Solution::set(Lit a)
{
	assign[a] = true;
}

inline bool Solution::valid() const
{
	for(int i = 0; i < (int)assign.size(); i += 2)
		if(assign[i] == assign[i+1])
			return false;
	return true;
}

inline bool Solution::satisfied(Lit a) const
{
	return assign[a];
}

inline bool Solution::satisfied(Lit a, Lit b) const
{
	return assign[a] || assign[b];
}

inline bool Solution::satisfied(Lit a, Lit b, Lit c) const
{
	return assign[a] || assign[b] || assign[c];
}

inline bool Solution::satisfied(const std::vector<Lit>& cl) const
{
	for(Lit lit : cl)
		if(assign[lit])
			return true;
	return false;
}

inline std::ostream& operator<<(std::ostream& stream, const Solution& sol)
{
	stream << "v";
	for(int i = 0; i < (int)sol.assign.size(); ++i)
		if(sol.assign[i])
			stream << " " << Lit(i);
	stream << " 0" << std::endl;
	return stream;
}

#endif
