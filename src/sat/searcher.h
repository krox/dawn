#pragma once

#include "sat/cnf.h"
#include "sat/propengine.h"
#include <thread>

namespace dawn {

// core of a CDCL solver, running in a separate thread
//   * constructor copies the CNF formula
class Searcher
{
	Cnf cnf_;
	PropEngine p_;
	std::jthread thread_;

	void main(std::stop_token stoken)
	{
		while (!stoken.stop_requested())
		{
			// something
		}
	}

  public:
	// creating the searcher copies the cnf formula
	Searcher(Cnf cnf)
	    : cnf_(std::move(cnf)), p_(cnf_),
	      thread_([this](std::stop_token stoken) { main(stoken); })
	{}

	void start() {}

	// request the search to stop
	void request_stop() { thread_.request_stop(); }
};
} // namespace dawn