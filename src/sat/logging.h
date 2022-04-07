#pragma once

#include "fmt/format.h"
#include "util/hash_map.h"
#include "util/stopwatch.h"
#include <mutex>

namespace dawn {

// simple logging facitily built upon fmtlib
//     * log level can be set globally or per component, both are stored in
//       global variables
//     * logger construction is (slightly) slow due to memory allocation and
//       mutexes, so reusing is good for performance
//     * logging itself should never throw (so it can be used in destructors and
//       any other precarious situation), so it is marked 'noexcept'.
//       TODO: actually handle any errors (from formatting or filesystem or
//       such) more gracefully than calling std::terminate
//
// Intended usage:
//    // at the beginning of main()
//    Logger::set_level(Logger::Level::info);
//    Logger::set_level("my class", Logger::Level::debug);
//
//    // in a class constructor or similar
//    log = Logger("my class");
//
//    // during actual work
//    log.info("some message {}", 42);
//    log.debug("some more verbose message {}", 21+21);

class Logger
{
  public:
	enum class Level
	{
		// These are the levels from the spdlog library. They seem reasonable,
		// though not all are actually used in this project. (Errors generally
		// abort the whole program without trying to carry on)
		off,
		critical,
		err,
		warn,
		info,
		debug,
		trace
	};

  private:
	inline static Level g_default_level_ = Level::info;
	inline static util::hash_map<std::string, Level> g_custom_level_;
	inline static std::mutex g_mutex_;

  public:
	static void set_level(Level level)
	{
		auto lock = std::scoped_lock(g_mutex_);
		g_default_level_ = level;
		g_custom_level_.clear();
	}

	static void set_level(std::string_view name, Level level)
	{
		auto lock = std::scoped_lock(g_mutex_);
		g_custom_level_[std::string(name)] = level;
	}

  private:
	std::string name_;
	Level level_;
	util::Stopwatch sw;

	void do_log(std::string_view str, fmt::format_args &&args) const noexcept
	{
		fmt::print("c [{:12} {:#6.2f}] {}\n", name_, sw.secs(),
		           fmt::vformat(str, std::move(args)));
	}

  public:
	explicit Logger(std::string name) : name_(std::move(name))
	{
		sw.start();
		auto lock = std::scoped_lock(g_mutex_);
		if (g_custom_level_.count(name_))
			level_ = g_custom_level_[name_];
		else
			level_ = g_default_level_;
	}

	template <class... Args>
	void trace(std::string_view str, Args &&...args) const noexcept
	{
		if (level_ >= Level::trace)
			do_log(str, fmt::make_format_args(std::forward<Args>(args)...));
	}

	template <class... Args>
	void debug(std::string_view str, Args &&...args) const noexcept
	{
		if (level_ >= Level::debug)
			do_log(str, fmt::make_format_args(std::forward<Args>(args)...));
	}

	template <class... Args>
	void info(std::string_view str, Args &&...args) const noexcept
	{
		if (level_ >= Level::info)
			do_log(str, fmt::make_format_args(std::forward<Args>(args)...));
	}

	template <class... Args>
	void warn(std::string_view str, Args &&...args) const noexcept
	{
		if (level_ >= Level::warn)
			do_log(str, fmt::make_format_args(std::forward<Args>(args)...));
	}

	template <class... Args>
	void err(std::string_view str, Args &&...args) const noexcept
	{
		if (level_ >= Level::err)
			do_log(str, fmt::make_format_args(std::forward<Args>(args)...));
	}

	template <class... Args>
	void critical(std::string_view str, Args &&...args) const noexcept
	{
		if (level_ >= Level::critical)
			do_log(str, fmt::make_format_args(std::forward<Args>(args)...));
	}
};

} // namespace dawn