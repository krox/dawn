#pragma once

#include "sat/sat.h"

namespace dawn {

/** heap of variables with quick access to the most 'active' one */
class ActivityHeap
{
	Sat &sat;
	std::vector<int> arr;
	std::vector<int> location; // -1 for vars that are not in the heap currently

	static constexpr int parent(int i) { return (i - 1) / 2; }
	static constexpr int left(int i) { return 2 * i + 1; }
	static constexpr int right(int i) { return 2 * i + 2; }

	bool pred(int x, int y) const { return sat.activity[x] > sat.activity[y]; }

	int smallerChild(int i) const
	{
		if (right(i) < (int)arr.size() && pred(arr[right(i)], arr[left(i)]))
			return right(i);
		else
			return left(i);
	}

	void percolateUp(int i)
	{
		auto x = arr[i];

		for (int p = parent(i); i != 0 && pred(x, arr[p]); i = p, p = parent(i))
		{
			arr[i] = arr[p];
			location[arr[i]] = i;
		}

		arr[i] = x;
		location[x] = i;
	}

	void percolateDown(int i)
	{
		auto x = arr[i];

		for (int c = smallerChild(i); c < (int)size() && pred(arr[c], x);
		     i = c, c = smallerChild(i))
		{
			arr[i] = arr[c];
			location[arr[i]] = i;
		}

		arr[i] = x;
		location[x] = i;
	}

  public:
	ActivityHeap(Sat &sat) : sat(sat), location(sat.varCount(), -1)
	{
		arr.reserve(sat.varCount());
	}

	/** returns true if heap is empty */
	bool empty() const { return arr.empty(); }

	/** returns number of elements in the heap */
	size_t size() const { return arr.size(); }

	/** check if a var is currently present in th heap */
	bool contains(int var) const { return location[var] != -1; }

	/** Removes most active variable from heap and returns it. */
	int pop()
	{
		assert(!empty());
		int r = arr.front();
		location[r] = -1;
		arr.front() = arr.back();
		arr.pop_back();
		if (!empty())
			percolateDown(0);
		return r;
	}

	/** Add a variable to the queue. If it is already in, update it. */
	void push(int var)
	{
		if (contains(var))
		{
			percolateUp(location[var]);
			percolateDown(location[var]);
		}
		else
		{
			arr.push_back(var);
			percolateUp((int)size() - 1);
		}
	}

	/** Notifiy the heap that the activity of var has changed. Does nothing if
	 * not currently in the heap. */
	void update(int var)
	{
		if (contains(var))
		{
			percolateUp(location[var]);
			percolateDown(location[var]);
		}
	}
};

} // namespace dawn
