#include "path_assign.h"
#include "Module.h"
#include "PExpr.h"
#include "PGenerate.h"
#include "Statement.h"
#include "compiler.h"
#include "ivl_target.h"
#include "sectypes.h"
#include "sexp_printer.h"
#include <algorithm>

static inline void collectPathsBehavior(PathAnalysis &p, PProcess &b,
                                        TypeEnv &env) {
  if (b.type() != IVL_PR_INITIAL) {
    Predicate emptyPred;
    emptyPred.hypotheses.insert(new Hypothesis(new PEBoolean(true)));
    b.statement()->collect_assign_paths(p, env, emptyPred);
  }
}

static inline void collectPathsGenerate(PathAnalysis &p, const PGenerate &gen,
                                        TypeEnv &env) {
  for (auto g : gen.generate_schemes)
    collectPathsGenerate(p, *g, env);
  for (auto b : gen.behaviors)
    collectPathsBehavior(p, *b, env);
}

PathAnalysis get_paths(Module &m, TypeEnv &env) {
  PathAnalysis paths;
  for (auto g : m.generate_schemes)
    collectPathsGenerate(paths, *g, env);
  for (auto b : m.behaviors)
    collectPathsBehavior(paths, *b, env);

  // debug printing of paths
  if (debug_typecheck)
    for (auto &p : paths) {
      std::cerr << p.first << ":\n";
      std::cerr << p.second.size() << "\n";
      for (auto &pred : p.second) {
        std::cerr << pred;
      }
    }
  return paths;
}

void dump_no_overlap_anal(SexpPrinter &p, PathAnalysis &paths) {
  for (auto &[var, paths] : paths) {
    p.singleton("push");
    p.startList("assert");
    p.startList("or");
    if (paths.size() <= 1)
      p.printAtom("false");
    for (auto i = paths.cbegin(); i != paths.cend(); ++i) {
      for (auto j = i + 1; j != paths.cend(); ++j) {
        // p.startList("not");
        p.startList("and");
        p << *i << *j;
        // p.endList();
        p.endList();
      }
    }
    p.endList();
    p.endList();
    p.startList("echo");
    std::string msg = std::string("\"checking paths of ") + var.str() + "\"";
    p.printAtom(msg);
    p.endList();
    p.singleton("check-sat");
    p.singleton("pop");
  }
}

bool isDefinitelyAssigned(PEIdent *varname, PathAnalysis &paths) {
  return true;
}

void Statement::collect_assign_paths(PathAnalysis &, TypeEnv &, Predicate &) {}

void PAssign_::collect_assign_paths(PathAnalysis &paths, TypeEnv &,
                                    Predicate &pred) {
  paths[lval()->get_name()].push_back(pred);
}

void PBlock::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                  Predicate &pred) {
  for (uint i = 0; i < list_.count(); ++i)
    list_[i]->collect_assign_paths(paths, env, pred);
}

void PCAssign::collect_assign_paths(PathAnalysis &paths, TypeEnv &,
                                    Predicate &pred) {
  paths[lval_->get_name()].push_back(pred);
}

void PCondit::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                   Predicate &pred) {
  auto oldPred = pred;
  if (if_ != NULL) {
    absintp(pred, env, true, true);
    if_->collect_assign_paths(paths, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
  if (else_ != NULL) {
    absintp(pred, env, false, true);
    else_->collect_assign_paths(paths, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
}

void PEventStatement::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                           Predicate &pred) {
  statement_->collect_assign_paths(paths, env, pred);
}
