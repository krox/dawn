#include "sat/assignment.h"

namespace dawn {

static_assert(bool(ltrue));
static_assert(!static_cast<bool>(lfalse));
static_assert(!static_cast<bool>(lundef));
static_assert(lbool(true) == ltrue);
static_assert(lbool(false) == lfalse);
static_assert(~ltrue == lfalse);
static_assert(~lfalse == ltrue);

static_assert((ltrue & ltrue) == ltrue);
static_assert((ltrue & lfalse) == lfalse);
static_assert((ltrue & lundef) == lundef);
static_assert((lfalse & ltrue) == lfalse);
static_assert((lfalse & lfalse) == lfalse);
static_assert((lfalse & lundef) == lfalse);
static_assert((lundef & ltrue) == lundef);
static_assert((lundef & lfalse) == lfalse);
static_assert((lundef & lundef) == lundef);

static_assert((ltrue | ltrue) == ltrue);
static_assert((ltrue | lfalse) == ltrue);
static_assert((ltrue | lundef) == ltrue);
static_assert((lfalse | ltrue) == ltrue);
static_assert((lfalse | lfalse) == lfalse);
static_assert((lfalse | lundef) == lundef);
static_assert((lundef | ltrue) == ltrue);
static_assert((lundef | lfalse) == lundef);
static_assert((lundef | lundef) == lundef);

static_assert((ltrue ^ ltrue) == lfalse);
static_assert((ltrue ^ lfalse) == ltrue);
static_assert((ltrue ^ lundef) == lundef);
static_assert((lfalse ^ ltrue) == ltrue);
static_assert((lfalse ^ lfalse) == lfalse);
static_assert((lfalse ^ lundef) == lundef);
static_assert((lundef ^ ltrue) == lundef);
static_assert((lundef ^ lfalse) == lundef);
static_assert((lundef ^ lundef) == lundef);

static_assert((ltrue ^ true) == lfalse);
static_assert((ltrue ^ false) == ltrue);
static_assert((lfalse ^ true) == ltrue);
static_assert((lfalse ^ false) == lfalse);
static_assert((lundef ^ true) == lundef);
static_assert((lundef ^ false) == lundef);

} // namespace dawn
