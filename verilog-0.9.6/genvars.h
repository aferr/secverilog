#ifndef __GENVARS_H__
#define __GENVARS_H__ 1

#include "PGenerate.h"
#include "compiler.h"
#include "netlist.h"
#include "netmisc.h"
#include "pform.h"

void collect_used_genvars(std::set<perm_string> &res, Predicate &pred,
                          TypeEnv &env);

void collect_used_genvars(std::set<perm_string> &res, SecType *typ,
                          TypeEnv &env);

void start_dump_genvar_quantifiers(SexpPrinter &printer,
                                   std::set<perm_string> &vars, TypeEnv &env);

void end_dump_genvar_quantifiers(SexpPrinter &printer,
                                 std::set<perm_string> &vars);

#endif
