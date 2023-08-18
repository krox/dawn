#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include "sat/subsumption.h"
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
		auto p = PropEngine(sat);
		auto sol = p.search(1000);
		if (sol)
		{
			logger.info("SATISFIABLE\n");
			assert(!sat.contradiction);
		}
		if (sat.contradiction)
		{
			logger.info("UNSATISFIABLE\n");
		}
	};

	// The tree of components. This defines how to navigate using the keyboard.
	std::vector<Component> buttons;
	buttons.push_back(Button("Search", run_searcher));
	buttons.push_back(Button("UP+SCC", [&] {
		int n = cleanup(sat);
		logger.info("removed {} clauses", n);
	}));
	buttons.push_back(Button("subsume", [&] { run_subsumption(sat); }));
	buttons.push_back(Button("clean >10", [&] {
		for (auto &cl : sat.clauses.all())
			if (!cl.irred() && cl.size() > 10)
				cl.remove();
		sat.clauses.compactify();
	}));
	buttons.push_back(Button("Quit", [&] { screen.Exit(); }));

	auto all_buttons = Container::Horizontal(buttons);

	auto dom = [&] {
		return vbox({
		           log.element(),
		           separator(),
		           text("nvars = " + std::to_string(sat.var_count())),
		           make_element(sat.clause_histogram()),
		           separator(),
		           all_buttons->Render(),
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