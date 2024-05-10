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

void PropStats::dump(bool with_histograms)
{
	if (with_histograms)
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
}

PropStats &operator+=(PropStats &a, const PropStats &b)
{
	a.binHistogram += b.binHistogram;
	a.watchHistogram += b.watchHistogram;
	a.clauseSizeHistogram += b.clauseSizeHistogram;
	a.nBinSatisfied += b.nBinSatisfied;
	a.nBinProps += b.nBinProps;
	a.nBinConfls += b.nBinConfls;
	a.nLongSatisfied += b.nLongSatisfied;
	a.nLongShifts += b.nLongShifts;
	a.nLongProps += b.nLongProps;
	a.nLongConfls += b.nLongConfls;
	a.nLitsLearnt += b.nLitsLearnt;
	a.nLitsOtfRemoved += b.nLitsOtfRemoved;
	return a;
}

void PropStats::clear() { *this = PropStats{}; }

} // namespace dawn
