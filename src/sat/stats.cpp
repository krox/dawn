#include "sat/stats.h"

#include "fmt/format.h"

namespace dawn {

static void dumpHistogram(const util::IntHistogram &h)
{
	for (int i = 0; i <= h.max(); ++i)
		if (h.bin(i))
			fmt::print("{:#3}: {:#12}\n", i, h.bin(i));
	fmt::print("average: {:#12.2f}\n", h.mean());
}

void Stats::dump()
{
	if (watch_stats)
	{
		fmt::print("c ======================= binlist size histogram "
		           "=======================\n");
		dumpHistogram(binHistogram);
		fmt::print("c ===================== watchlist size histogram "
		           "======================\n");
		dumpHistogram(watchHistogram);
		fmt::print("c =================== visited clause size histogram "
		           "===================\n");
		dumpHistogram(clauseSizeHistogram);
	}

	fmt::print("c ========================= propagation stats "
	           "=========================\n");
	fmt::print("c watchlist size: {:#10.2f}\n", watchHistogram.mean());
	int64_t nBinTotal = nBinSatisfied + nBinProps + nBinConfls;
	fmt::print("c binary sat.:    {:#10} ({:#4.1f} % of bins)\n", nBinSatisfied,
	           100. * nBinSatisfied / nBinTotal);
	fmt::print("c binary props:   {:#10} ({:#4.1f} % of bins)\n", nBinProps,
	           100. * nBinProps / nBinTotal);
	fmt::print("c binary confls:  {:#10} ({:#4.1f} % of bins)\n", nBinConfls,
	           100. * nBinConfls / nBinTotal);
	fmt::print("c long sat.:      {:#10} ({:#4.1f} % of watches)\n",
	           nLongSatisfied, 100. * nLongSatisfied / watchHistogram.sum());
	fmt::print("c long shift:     {:#10} ({:#4.1f} % of watches)\n",
	           nLongShifts, 100. * nLongShifts / watchHistogram.sum());
	fmt::print("c long props:     {:#10} ({:#4.1f} % of watches)\n", nLongProps,
	           100. * nLongProps / watchHistogram.sum());
	fmt::print("c long confls:    {:#10} ({:#4.1f} % of watches)\n",
	           nLongConfls, 100. * nLongConfls / watchHistogram.sum());
	fmt::print("c clauses learnt: {:#10} ({:#4.1f} % shortened by otf)\n",
	           nLearnt, 100. * nLitsOtfRemoved / nLitsLearnt);

	fmt::print("c ============================ time stats "
	           "=============================\n");
	fmt::print("c parser       {:#6.2f} s ({:#4.1f} %)\n", swParsing.secs(),
	           100. * swParsing.secs() / swTotal.secs());
	fmt::print("c cleanup      {:#6.2f} s ({:#4.1f} %)\n", swCleanup.secs(),
	           100. * swCleanup.secs() / swTotal.secs());
	fmt::print("c probing      {:#6.2f} s ({:#4.1f} %)\n", swProbing.secs(),
	           100. * swProbing.secs() / swTotal.secs());
	fmt::print("c subsume      {:#6.2f} s ({:#4.1f} %)\n", swSubsume.secs(),
	           100. * swSubsume.secs() / swTotal.secs());
	fmt::print("c vivification {:#6.2f} s ({:#4.1f} %)\n",
	           swVivification.secs(),
	           100. * swVivification.secs() / swTotal.secs());
	fmt::print("c BVE          {:#6.2f} s ({:#4.1f} %)\n", swBVE.secs(),
	           100. * swBVE.secs() / swTotal.secs());
	fmt::print("c BCE          {:#6.2f} s ({:#4.1f} %)\n", swBCE.secs(),
	           100. * swBCE.secs() / swTotal.secs());
	fmt::print("c BVA          {:#6.2f} s ({:#4.1f} %)\n", swBVA.secs(),
	           100. * swBVA.secs() / swTotal.secs());
	fmt::print("c search init  {:#6.2f} s ({:#4.1f} %)\n", swSearchInit.secs(),
	           100. * swSearchInit.secs() / swTotal.secs());
	fmt::print("c search       {:#6.2f} s ({:#4.1f} %)\n", swSearch.secs(),
	           100. * swSearch.secs() / swTotal.secs());
	fmt::print("c total        {:#6.2f} s\n", swTotal.secs());
}

} // namespace dawn
