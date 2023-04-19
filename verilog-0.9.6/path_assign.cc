#include "path_assign.h"
#include "Module.h"
#include "PExpr.h"
#include "PGenerate.h"
#include "Statement.h"
#include "StringHeap.h"
#include "compiler.h"
#include "genvars.h"
#include "ivl_target.h"
#include "sectypes.h"
#include "sexp_printer.h"
#include <ranges>

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

void dump_is_def_assign(SexpPrinter &p, PathAnalysis &path_analysis,
                        perm_string varname) {

  if (!path_analysis.contains(varname) || path_analysis[varname].empty()) {
    p << "false";
    return;
  }
  dump_on_paths(p, path_analysis[varname]);
}

void dump_on_paths(SexpPrinter &p, const std::vector<Predicate> &paths) {
  p.inList("or", [&]() {
    std::for_each(paths.begin(), paths.end(), [&p](auto &path) { p << path; });
  });
}

void dump_no_overlap_anal(SexpPrinter &p, Module &m, TypeEnv &env,
                          set<perm_string> &vars) {
  p.inList("echo", [&]() { p.printAtom("\"Starting assigned-once checks\""); });
  auto isDepVar =
      [&vars](const std::pair<perm_string, std::vector<Predicate>> &pred) {
        auto str       = std::string(pred.first);
        auto brack_idx = str.find_first_of('[');
        if (brack_idx == 0)
          brack_idx = str.size();
        auto lit = perm_string::literal(str.substr(0, brack_idx).c_str());
        return vars.contains(lit);
      };
  for (auto &[var, paths] : std::ranges::filter_view(env.analysis, isDepVar)) {
    auto str           = std::string(var);
    auto brack_idx     = str.find_first_of('[');
    auto brack_end_idx = str.find_first_of(']');
    std::set<perm_string> genvar_idx_used;
    if (brack_idx != brack_end_idx) {
      // evil perm_string heap hack (leaks memory)
      auto idxpr = perm_string::literal(
          (new std::string(
               str.substr(brack_idx + 1, brack_end_idx - brack_idx - 1)))
              ->c_str());
      if (m.genvars.contains(idxpr)) {
        genvar_idx_used.insert(idxpr);
      }
    }
    // for (auto &[var, paths] : path_analysis) {

    p.singleton("push");

    p.inList("assert", [&]() {
      start_dump_genvar_quantifiers(p, genvar_idx_used, env);

      p.inList("or", [&]() {
        if (paths.size() <= 1)
          p.printAtom("false");
        for (auto i = paths.cbegin(); i != paths.cend(); ++i) {
          for (auto j = i + 1; j != paths.cend(); ++j) {
            p.inList("and", [&]() { p << *i << *j; });
          }
        }
      });
      end_dump_genvar_quantifiers(p, genvar_idx_used);
    });
    std::string msg = std::string("\"checking paths of ") + var.str() + "\"";
    p.inList("echo", [&]() { p.printAtom(msg); });
    p.singleton("check-sat");
    p.singleton("pop");
  }
  p.inList("echo", [&]() { p.printAtom("\"Ending assigned-once checks\""); });
}

bool isDefinitelyAssigned(PEIdent *varname, PathAnalysis &paths) {
  return true;
}

void Statement::collect_assign_paths(PathAnalysis &, TypeEnv &, Predicate &) {}

void PAssign_::collect_assign_paths(PathAnalysis &paths, TypeEnv &,
                                    Predicate &pred) {
  paths[lval()->get_full_name()].push_back(pred);
}

void PBlock::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                  Predicate &pred) {
  for (uint i = 0; i < list_.count(); ++i)
    list_[i]->collect_assign_paths(paths, env, pred);
}

void PCAssign::collect_assign_paths(PathAnalysis &paths, TypeEnv &,
                                    Predicate &pred) {
  paths[lval_->get_full_name()].push_back(pred);
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

void PForStatement::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                         Predicate &pred) {
  auto oldPred = pred;
  if (statement_) {
    absintp(pred, env);
    statement_->collect_assign_paths(paths, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
}

void PEventStatement::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                           Predicate &pred) {
  statement_->collect_assign_paths(paths, env, pred);
}
