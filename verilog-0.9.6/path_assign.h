#include "PExpr.h"
#include "StringHeap.h"
#ifndef __PATH_ASSIGN_H__
#define __PATH_ASSIGN_H__ 1


#include <map>
#include <vector>


std::map<perm_string, std::vector<PExpr>> get_paths(Module &m);


#endif
