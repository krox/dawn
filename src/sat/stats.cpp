#include "sat/stats.h"

#include "fmt/format.h"

void Stats::dump()
{
	fmt::print("c ============================ time stats "
	           "=============================\n");
	fmt::print("c SCC        {:#6.2f} s ({:#4.1f} %)\n", swSCC.secs(),
	           100. * swSCC.secs() / swTotal.secs());
	fmt::print("c cleanup    {:#6.2f} s ({:#4.1f} %)\n", swCleanup.secs(),
	           100. * swCleanup.secs() / swTotal.secs());
	fmt::print("c probing    {:#6.2f} s ({:#4.1f} %)\n", swProbing.secs(),
	           100. * swProbing.secs() / swTotal.secs());
	fmt::print("c searchInit {:#6.2f} s ({:#4.1f} %)\n", swSearchInit.secs(),
	           100. * swSearchInit.secs() / swTotal.secs());
	fmt::print("c search     {:#6.2f} s ({:#4.1f} %)\n", swSearch.secs(),
	           100. * swSearch.secs() / swTotal.secs());
	fmt::print("c total      {:#6.2f} s\n", swTotal.secs());
}
