#include "sat/stats.h"

#include "fmt/format.h"

static void dumpHistogram(const util::IntHistogram &h)
{
	if (h.underflow())
		fmt::print("<{:#2}: {:#12}\n", h.min(), h.underflow());
	for (int i = h.min(); i < h.max(); ++i)
		if (h.count(i))
			fmt::print("{:#3}: {:#12}\n", i, h.count(i));
	if (h.overflow())
		fmt::print(">{:#2}: {:#12}\n", h.max() - 1, h.overflow());
}

void Stats::dump()
{
	if (watchStats)
	{
		fmt::print("c ======================= binlist size histogram "
		           "=======================\n");
		dumpHistogram(binHistogram);
		fmt::print("c ===================== watchlist size histogram "
		           "======================\n");
		dumpHistogram(watchHistogram);
	}

	fmt::print("c ========================= propagation stats "
	           "=========================\n");
	fmt::print("c watchlist size: {:#10.2f}\n", watchHistogram.mean());
	fmt::print("c binary props:   {:#10}\n", nBinProps);
	fmt::print("c binary confls:  {:#10}\n", nBinConfls);
	fmt::print("c long props:     {:#10} ({:#4.1f} % of watches)\n", nLongProps,
	           100. * nLongProps / watchHistogram.sum());
	fmt::print("c long confls:    {:#10} ({:#4.1f} % of watches)\n",
	           nLongConfls, 100. * nLongConfls / watchHistogram.sum());
	fmt::print("c clauses learnt: {:#10}\n", nLearnt);

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
