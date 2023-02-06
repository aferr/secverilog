#include "path_assign.h"
#include "Module.h"
#include "Statement.h"

PathAnalysis
get_paths(Module &m, TypeEnv &env)
{
  PathAnalysis paths;
  for (auto b : m.behaviors)
    {
      Predicate emptyPred;
      b->statement()->collect_assign_paths(paths, env, emptyPred);
    }


  // debug printing of paths
  for(auto &p : paths)
    {
      std::cout << p.first << ":\n";
      for(auto &pred : p.second)
	{
	  std::cout << pred;
	}
    }
  
  return paths;
}




void Statement::collect_assign_paths(PathAnalysis &, TypeEnv &, Predicate &) {}

void PAssign_::collect_assign_paths(PathAnalysis &paths, TypeEnv &, Predicate &pred)
{
  paths[lval()->get_name()].push_back(pred);
}


void PBlock::collect_assign_paths(PathAnalysis &paths, TypeEnv &env, Predicate &pred)
{
  for (uint i = 0; i < list_.count(); ++i)
    list_[i]->collect_assign_paths(paths, env, pred);
}


void PCAssign::collect_assign_paths(PathAnalysis &paths, TypeEnv &, Predicate &pred)
{
  paths[lval_->get_name()].push_back(pred);
}


void PCondit::collect_assign_paths(PathAnalysis &paths, TypeEnv &env, Predicate &pred)
{
  auto oldPred = pred;
  if (if_ != NULL)
    {
      absintp(pred, env, true, true);
      if_->collect_assign_paths(paths, env, pred);
      pred.hypotheses = oldPred.hypotheses;
    }
  if(else_ != NULL)
    {
      absintp(pred, env, false, true);
      else_->collect_assign_paths(paths, env, pred);
      pred.hypotheses = oldPred.hypotheses;
    }
}

void PEventStatement::collect_assign_paths(PathAnalysis &paths, TypeEnv &env, Predicate &pred)
{
  statement_->collect_assign_paths(paths, env, pred);
}
