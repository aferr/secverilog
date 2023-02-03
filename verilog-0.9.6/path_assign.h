#include "PExpr.h"
#include "StringHeap.h"
#ifndef __PATH_ASSIGN_H__
#define __PATH_ASSIGN_H__ 1

#include <map>
#include <vector>


using PathAnalysis = std::map<perm_string, std::vector<PExpr>>;


/**
 * @param m The module to analyze
 * @return A map from variable names to expressions that represent the conditions
 * under which each variable is assigned during a given clock cycle.
 */
PathAnalysis get_paths(Module &m);
//TODO you'll probably need to pass some typing information to this analysis also


/**
 * @param varname Variable to check for definite assignment.
 * @param paths The path analysis data structure use to compute the result.
 * @return True if varname is assigned on all program paths, else false.
 */
bool isDefinitelyAssigned(perm_string varname, PathAnalysis &paths);

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
std::set<perm_string> getArrayIndices(perm_string array_name, PathAnalysis &paths);

#endif
