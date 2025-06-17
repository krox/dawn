#pragma once

#include "sat/cnf.h"

namespace dawn {

struct redshift_config
{};

void run_redshift(Cnf &, redshift_config const &);

} // namespace dawn