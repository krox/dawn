#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/searcher.h"
#include "sat/solver.h"
#include "sat/subsumption.h"
#include "sat/vivification.h"
#include "util/ring_buffer.h"
#include <string>

#include "ftxui/component/captured_mouse.hpp"
#include "ftxui/component/component.hpp"
#include "ftxui/component/component_base.hpp"
#include "ftxui/component/screen_interactive.hpp"
#include "ftxui/dom/elements.hpp"

using namespace dawn;
using namespace ftxui;

namespace {

// CLI options of "dawn ui" command
struct Options
{
	std::string cnfFile;
};

class Log
{
	util::fixed_ring_buffer<std::string> msgs_;

  public:
	Log() : msgs_(10) {}
	void add(std::string_view msg) { msgs_.emplace_back(msg); }

	Element element()
	{
		std::vector<Element> elems;
		for (auto &msg : msgs_)
			elems.push_back(text(msg));
		return vbox(std::move(elems));
	}
};

Element make_element(util::IntHistogram const &hist)
{
	std::vector<Element> elems;
	int64_t very_long = 0;
	for (int l = 0; l <= hist.max(); ++l)
	{
		if (l > 10)
			very_long += hist.bin(l);
		else if (hist.bin(l))
			elems.push_back(text(fmt::format("{:>3}: {}", l, hist.bin(l))));
	}
	if (very_long)
		elems.push_back(text(fmt::format(">10: {}", very_long)));
	elems.push_back(text(fmt::format("max: {}", hist.max())));
	elems.push_back(text(fmt::format("avg: {:.2f}", hist.mean())));
	return vbox(std::move(elems));
}

void run_ui_command(Options opt)
{
	Log log;
	auto screen = ScreenInteractive::FitComponent();
	auto logger = Logger("ui");

	Logger::set_sink([&](std::string_view msg) {
		log.add(msg);
		screen.PostEvent(Event::Custom);
	});

	auto [originalClauses, varCount] = parseCnf(opt.cnfFile);
	Sat sat = Sat(varCount, originalClauses); // clauses are copied here!

	SolverConfig config;
	config.max_learnt = 1000;

	auto run_searcher = [&]() {
		auto result = Searcher(sat).run_epoch(10000, {});
		if (std::get_if<Assignment>(&result))
		{
			logger.info("SATISFIABLE\n");
			assert(!sat.contradiction);
		}
		else if (auto *learnts = std::get_if<ClauseStorage>(&result))
		{
			logger.info("learnt {} clauses", learnts->count());
			for (auto &cl : learnts->all())
				sat.add_clause(cl, cl.color);
		}
		else
			assert(false);

		if (sat.contradiction)
		{
			logger.info("UNSATISFIABLE\n");
		}
	};

	// The tree of components. This defines how to navigate using the keyboard.
	std::vector<Component> buttons;
	buttons.push_back(Button("Search", run_searcher));
	buttons.push_back(Button("UP+SCC", [&] {
		cleanup(sat);
		logger.info("cleanup ran");
	}));
	buttons.push_back(Button("subsume", [&] {
		run_subsumption(sat);
		cleanup(sat);
	}));
	buttons.push_back(Button("vivify", [&] { run_vivification(sat, {}, {}); }));
	buttons.push_back(Button("clean >10", [&] {
		sat.clauses.prune([](Clause const &cl) {
			return cl.color != dawn::Color::blue && cl.size() > 10;
		});
	}));
	buttons.push_back(Button("Quit", [&] { screen.Exit(); }));

	auto all_buttons = Container::Horizontal(buttons);

	auto dom = [&] {
		auto left = vbox({
		    log.element(),
		    separator(),
		    all_buttons->Render(),
		});
		auto right = vbox({
		    text("nvars = " + std::to_string(sat.var_count())),
		    make_element(sat.clause_histogram()),
		});
		return hbox({
		           left,
		           separator(),
		           right,
		       }) |
		       border;
	};

	screen.Loop(Renderer(all_buttons, dom));
}
} // namespace

void setup_ui_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	// input/output
	app.add_option("input", opt->cnfFile, "input CNF in dimacs format")
	    ->type_name("<filename>");

	app.callback([opt]() { run_ui_command(*opt); });
}