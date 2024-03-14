#pragma once

#include "sat/sat.h"

namespace dawn {

/** heap of variables with quick access to the most 'active' one */
class ActivityHeap
{
	double activity_inc_ = 1.0;
	std::vector<double> activity_;
	std::vector<int> arr_;
	std::vector<int>
	    location_; // -1 for vars that are not in the heap currently

	static constexpr int parent(int i) { return (i - 1) / 2; }
	static constexpr int left(int i) { return 2 * i + 1; }
	static constexpr int right(int i) { return 2 * i + 2; }

	bool pred(int x, int y) const { return activity_[x] > activity_[y]; }

	int smaller_child(int i) const
	{
		if (right(i) < (int)arr_.size() && pred(arr_[right(i)], arr_[left(i)]))
			return right(i);
		else
			return left(i);
	}

	void percolate_up(int i)
	{
		auto x = arr_[i];

		for (int p = parent(i); i != 0 && pred(x, arr_[p]);
		     i = p, p = parent(i))
		{
			arr_[i] = arr_[p];
			location_[arr_[i]] = i;
		}

		arr_[i] = x;
		location_[x] = i;
	}

	void percolate_down(int i)
	{
		auto x = arr_[i];

		for (int c = smaller_child(i); c < (int)size() && pred(arr_[c], x);
		     i = c, c = smaller_child(i))
		{
			arr_[i] = arr_[c];
			location_[arr_[i]] = i;
		}

		arr_[i] = x;
		location_[x] = i;
	}

  public:
	ActivityHeap(int var_count) : activity_(var_count), location_(var_count, -1)
	{
		arr_.reserve(var_count);
		for (int i = 0; i < var_count; i++)
			push(i);
	}

	/** returns true if heap is empty */
	bool empty() const { return arr_.empty(); }

	/** returns number of elements in the heap */
	size_t size() const { return arr_.size(); }

	/** check if a var is currently present in th heap */
	bool contains(int var) const { return location_[var] != -1; }

	/** Removes most active variable from heap and returns it. */
	int pop()
	{
		assert(!empty());
		int r = arr_.front();
		location_[r] = -1;
		arr_.front() = arr_.back();
		arr_.pop_back();
		if (!empty())
			percolate_down(0);
		return r;
	}

	/** Add a variable to the queue. If it is already in, update it. */
	void push(int var)
	{
		if (contains(var))
		{
			percolate_up(location_[var]);
			percolate_down(location_[var]);
		}
		else
		{
			arr_.push_back(var);
			percolate_up((int)size() - 1);
		}
	}

	// increase activity of a variable. updates heap if necessary.
	void bump_variable_activity(int var)
	{
		activity_[var] += activity_inc_;

		if (contains(var))
		{
			percolate_up(location_[var]);
			percolate_down(location_[var]);
		}
	}

	// decrease activity of all variables by a factor
	// (technically, we increase the activity_inc_ by a factor)
	void decay_variable_activity()
	{
		// this number should be customizable
		activity_inc_ *= 1.05;

		// scale everything down if neccessary
		if (activity_inc_ > 1e100)
		{
			activity_inc_ *= 1e-100;
			for (double &value : activity_)
				value *= 1e-100;
		}
	}
};

} // namespace dawn
