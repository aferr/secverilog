#include <stdexcept>
#include <utility>
#ifndef __PATH_ASSIGN_H__
#define __PATH_ASSIGN_H__ 1
#include "PExpr.h"
#include "StringHeap.h"
#include "sectypes.h"

#include <map>
#include <vector>

/**
 * @param m The module to analyze
 * @return A map from variable names to expressions that represent the
 * conditions under which each variable is assigned during a given clock cycle.
 */
PathAnalysis get_paths(Module &m, TypeEnv &env);

/**
 * Dump a constraint to the solver to check that the given
 * variable is definitely assigned - this is true whenever
 * at least one branch condition in the analysis is true.
 * @param p an S-Exp printer used to generate z3 output
 * @param paths a path analyis returned from get_paths
 * @param var the name of the variable from paths to check
 */
void dump_is_def_assign(SexpPrinter &p, PathAnalysis &paths, perm_string var);
/**
 * Dump constraints to the solver to check that every variable
 * is assigned on AT MOST one path.
 * @param p an S-Exp printer used to generate z3 output
 * @param paths a path analyis returned from get_paths
 * @param vars the set of variable names from paths to dump
 */
void dump_no_overlap_anal(SexpPrinter &p, PathAnalysis &paths,
                          set<perm_string> &vars);

/**
 * @param varname PEIdent* to check for definite assignment.
 * @param paths The path analysis data structure use to compute the result.
 * @return True if varname is assigned on all program paths, else false.
 */
bool isDefinitelyAssigned(PEIdent *varname, PathAnalysis &paths);

/**
 * Based on all of the given variable assignments,
 * for each assignment that is into an array (e.g., arr[x])
 * (not bit-selection - it must be on variables of array type)
 * return the set of index variables that are used in these assignments.
 *
 * @param array_name The name of the array to consider
 * @param paths The analysis to use
 * @return A set of index names
 */
std::set<perm_string> getArrayIndices(perm_string array_name,
                                      PathAnalysis &paths);

/**
 * Dump the conditions that we are on one of the paths in {@param paths}
 */
void dump_on_paths(SexpPrinter &p, const std::vector<Predicate> &paths);
#endif
