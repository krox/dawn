#pragma once

#include "sat/sat.h"

namespace dawn {

struct redshift_config
{};

void run_redshift(Sat &, redshift_config const &);

} // namespace dawn