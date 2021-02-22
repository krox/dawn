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
	fmt::print("c hyper-binaries: {:#10}\n", nLhbr);
	fmt::print("c clauses learnt: {:#10} ({:#4.1f} % shortened by otf)\n",
	           nLearnt, 100. * nLitsOtfRemoved / nLitsLearnt);

	fmt::print("c ============================ time stats "
	           "=============================\n");
	fmt::print("c SCC          {:#6.2f} s ({:#4.1f} %)\n", swSCC.secs(),
	           100. * swSCC.secs() / swTotal.secs());
	fmt::print("c cleanup      {:#6.2f} s ({:#4.1f} %)\n", swCleanup.secs(),
	           100. * swCleanup.secs() / swTotal.secs());
	fmt::print("c probing      {:#6.2f} s ({:#4.1f} %)\n", swProbing.secs(),
	           100. * swProbing.secs() / swTotal.secs());
	fmt::print("c subsume bin  {:#6.2f} s ({:#4.1f} %)\n", swSubsumeBin.secs(),
	           100. * swSubsumeBin.secs() / swTotal.secs());
	fmt::print("c subsume long {:#6.2f} s ({:#4.1f} %)\n", swSubsumeLong.secs(),
	           100. * swSubsumeLong.secs() / swTotal.secs());
	fmt::print("c vivification {:#6.2f} s ({:#4.1f} %)\n",
	           swVivification.secs(),
	           100. * swVivification.secs() / swTotal.secs());
	fmt::print("c search init  {:#6.2f} s ({:#4.1f} %)\n", swSearchInit.secs(),
	           100. * swSearchInit.secs() / swTotal.secs());
	fmt::print("c search       {:#6.2f} s ({:#4.1f} %)\n", swSearch.secs(),
	           100. * swSearch.secs() / swTotal.secs());
	fmt::print("c total        {:#6.2f} s\n", swTotal.secs());
}
