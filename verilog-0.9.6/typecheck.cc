/*
 * Copyright (c) 1998-2013 Danfeng Zhang (zhangdf@cs.cornell.edu)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#include "PExpr.h"
#include "StringHeap.h"
#include "config.h"

/*
 * Type-checking takes a list of modules, and generates a Z3 file to be solved
 * by Z3.
 */

#include "PEvent.h"
#include "PGate.h"
#include "PGenerate.h"
#include "PSpec.h"
#include "compiler.h"
#include "genvars.h"
#include "ivl_assert.h"
#include "netlist.h"
#include "netmisc.h"
#include "parse_api.h"
#include "parse_misc.h"
#include "path_assign.h"
#include "pform.h"
#include "sectypes.h"
#include "sexp_printer.h"
#include "util.h"
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <ranges>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <type_traits>
#include <typeinfo>

#define ASSUME_NAME "assume"

void output_type_families(SexpPrinter &printer, char *depfun);
void output_lattice(SexpPrinter &out, char *lattice);

void printDecl(SexpPrinter &out, const char *expr) {
  out.startList("declare-fun");
  out << expr << "()"
      << "Int";
  out.endList();
}
void printBounds(SexpPrinter &out, const char *expr, PWire *def) {
  if (def) {
    out.startList("assert");
    out.startList("<=");
    out << "0" << expr;
    out.endList();
    out.endList();

    out.startList("assert");
    out.startList("<=");
    out << expr << std::to_string((1 << (def->getRange() + 1)) - 1);
    out.endList();
    out.endList();
  }
}

void printDeclaration(SexpPrinter &out, const char *expr, PWire *def) {
  printDecl(out, expr);
  printBounds(out, expr, def);
}

/**
 * Type-check parameters, which are constants.
 */
void LexicalScope::typecheck_parameters_(SexpPrinter &printer,
                                         TypeEnv &env) const {
  typedef map<perm_string, param_expr_t>::const_iterator parm_iter_t;
  if (debug_typecheck) {
    for (parm_iter_t cur = parameters.begin(); cur != parameters.end(); cur++) {
      cerr << "check parameter " << (*cur).first << " " << (*cur).second.type
           << endl;
    }
  }
  // parameters can only be assigned to constants. So the label must be LOW
  for (parm_iter_t cur = parameters.begin(); cur != parameters.end(); cur++) {
    env.varsToType[(*cur).first] = ConstType::BOT;
    if (debug_typecheck) {
      cerr << " param " << (*cur).first << " has type ";
      cerr << env.varsToType[(*cur).first] << endl;
    }
  }
}

/**
 * These are constants. Set them to the bottom type.
 */
void LexicalScope::typecheck_localparams_(SexpPrinter &printer,
                                          TypeEnv &env) const {
  typedef map<perm_string, param_expr_t>::const_iterator parm_iter_t;
  if (debug_typecheck) {

    if (dynamic_cast<const PScope *>(this)) {
      const PScope *ps = dynamic_cast<const PScope *>(this);
      cerr << "typecheck_localparams for " << ps->pscope_name() << endl;
    } else {
      cerr << "checking localparams for a non-pscope lexscope" << endl;
    }
    for (parm_iter_t cur = localparams.begin(); cur != localparams.end();
         cur++) {
      cerr << "check localparam ";
      if ((*cur).second.msb)
        cerr << "[" << *(*cur).second.msb << ":" << *(*cur).second.lsb << "] ";
      cerr << (*cur).first << " = ";
      if ((*cur).second.expr)
        cerr << *(*cur).second.expr << ";" << endl;
      else
        cerr << "/* ERROR */;" << endl;
    }
  }
  for (parm_iter_t cur = localparams.begin(); cur != localparams.end(); cur++) {
    env.varsToType[(*cur).first] = ConstType::BOT;
    if (debug_typecheck) {
      cerr << " localparam " << (*cur).first << " has type ";
      cerr << *env.varsToType[(*cur).first] << endl;
    }
  }
}

//-----------------------------------------------------------------------------
// Next Cycle Transformation
//-----------------------------------------------------------------------------

void Module::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) {
  // This transformation moves all assignments to sequential logic into
  // assignments to next-cycle objects.
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    if (debug_typecheck) {
      cerr << "NextCycleTransform:: " << typeid(*behav).name() << endl;
    }
    (*behav)->next_cycle_transform(printer, env);
  }
  /*
   * This is deleted since we don't really need to transform
   * the program, we just want to rename variables -> which we should
   * realy just do during constraint generation, skip all the nonsense
   * of re-writing the AST.
   */
  // typedef set<perm_string>::const_iterator seqvar_iter_t;
  // for (seqvar_iter_t cur = env.seqVars.begin(); cur != env.seqVars.end();
  //      cur++) {
  //   behaviors.push_back(gen_assign_next_block(*cur));
  // }

  // transform the code in the generate blocks too
  typedef list<PGenerate *>::const_iterator genscheme_iter_t;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->next_cycle_transform(printer, env);
  }
}

PProcess *Module::gen_assign_next_block(perm_string id) {
  // make the assignment in an always@(*) block
  PEventStatement *event_expr = new PEventStatement();
  PEIdent *nexted_id          = new PEIdent(nextify_perm_string(id));
  PEIdent *unnexted_id        = new PEIdent(id);
  PAssign *asgn               = new PAssign(unnexted_id, nexted_id);

  event_expr->set_statement(asgn);

  PProcess *ret = new PProcess(IVL_PR_ALWAYS, event_expr);
  return ret;
}

void PProcess::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) const {
  if (statement_ == NULL)
    return;
  if (debug_typecheck)
    cerr << "NextCycleTransform:: " << typeid(*statement_).name() << endl;
  statement_->next_cycle_transform(printer, env);
}

bool PProcess::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                      Predicate &pred) {
  if (statement_ == NULL)
    return false;
  if (debug_typecheck)
    cerr << "collect_dep_invariants:: " << typeid(*statement_).name() << endl;
  return statement_->collect_dep_invariants(printer, env, pred);
}

void PProcess::collectAssigned(set<perm_string> &s) const {
  if (statement_ == NULL || (type_ == IVL_PR_INITIAL))
    return;
  if (debug_typecheck)
    cerr << "collectAssigned:: " << typeid(*statement_).name() << endl;
  statement_->collectAssigned(s);
}

void PProcess::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  if (statement_ == NULL)
    return;
  if (debug_typecheck)
    cerr << "collect_index_exprs:: " << typeid(*statement_).name() << endl;
  statement_->collect_index_exprs(exprs, env);
}

Statement *Statement::next_cycle_transform(SexpPrinter &, TypeEnv &env) {
  return this;
}

bool Statement::collect_dep_invariants(SexpPrinter &, TypeEnv &env,
                                       Predicate &pred) {
  return false;
}

void Statement::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  return;
}

Statement *PEventStatement::next_cycle_transform(SexpPrinter &printer,
                                                 TypeEnv &env) {
  statement_ = statement_->next_cycle_transform(printer, env);
  return this;
}

void PEventStatement::collect_index_exprs(set<perm_string> &exprs,
                                          TypeEnv &env) {
  if (debug_typecheck)
    cerr << "collect_index_exprs:: " << typeid(*statement_).name() << endl;
  statement_->collect_index_exprs(exprs, env);
}

bool PEventStatement::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                             Predicate &pred) {
  if (debug_typecheck)
    cerr << "collect_dep_invariants:: " << typeid(*statement_).name() << endl;
  return statement_->collect_dep_invariants(printer, env, pred);
}

Statement *PBlock::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) {
  for (uint i = 0; i < list_.count(); i++) {
    if (debug_typecheck)
      cerr << "NextCycleTransform:: " << typeid(*list_[i]).name() << endl;
    list_[i] = list_[i]->next_cycle_transform(printer, env);
  }
  return this;
}

void PBlock::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  for (uint i = 0; i < list_.count(); i++) {
    if (debug_typecheck)
      cerr << "collect_index_exprs:: " << typeid(list_[i]).name() << endl;
    list_[i]->collect_index_exprs(exprs, env);
  }
}

bool PBlock::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                    Predicate &pred) {
  bool result = false;
  for (uint i = 0; i < list_.count(); i++) {
    if (debug_typecheck)
      cerr << "collect_dep_invariants:: " << typeid(list_[i]).name() << endl;
    result |= list_[i]->collect_dep_invariants(printer, env, pred);
  }
  return result;
}

Statement *PCondit::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) {
  if (if_ != NULL)
    if_ = if_->next_cycle_transform(printer, env);
  if (else_ != NULL)
    else_ = else_->next_cycle_transform(printer, env);
  return this;
}

void PCondit::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  if (debug_typecheck) {
    cerr << "collect_index_exprs on if" << endl;
  }
  if (if_ != NULL) {
    if_->collect_index_exprs(exprs, env);
  }
  if (else_ != NULL) {
    else_->collect_index_exprs(exprs, env);
  }
  expr_->collect_index_exprs(exprs, env);
  // also collect all the identifiers in the condition:
  // expr_->collect_idens(exprs);
}

bool PCondit::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                     Predicate &pred) {
  if (debug_typecheck)
    cerr << "collect_dep_invariants on if" << endl;
  Predicate oldPred = pred;
  bool result       = false;
  if (if_ != NULL) {
    absintp(pred, env, true, true);
    result |= if_->collect_dep_invariants(printer, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
  if (else_ != NULL) {
    absintp(pred, env, false, true);
    result |= else_->collect_dep_invariants(printer, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
  if (result) {
    expr_->collect_idens(env.dep_exprs);
  }
  return result;
}

void PCAssign::collectAssigned(set<perm_string> &s) const {
  if (debug_typecheck)
    cerr << "skipping collectAssigned on pcassign" << endl;
  return;
}
void PCAssign::collect_index_exprs(set<perm_string> &exprs, TypeEnv &) {
  if (debug_typecheck)
    cerr << "skipping collect_index_exprs on pcassign" << endl;
}

bool PCAssign::collect_dep_invariants(SexpPrinter &, TypeEnv &env,
                                      Predicate &pred) {
  if (debug_typecheck)
    cerr << "skipping collect_dep_invariants on pcassign" << endl;
  return false;
}

// This is the only rule where something actually happens. Only the left
// hand-side of the assignment is transformed.
Statement *PAssignNB::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) {
  if (debug_typecheck)
    cerr << "Nextify " << *lval_ << endl;
  assert(lval_);
  lval_ = lval_->next_cycle_transform(printer, env);
  return this;
}

void PAssign_::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  if (debug_typecheck) {
    cerr << "collect_index_exprs on passign" << endl;
    cerr << "on " << *rval() << " gets " << *lval() << endl;
  }
  rval()->collect_index_exprs(exprs, env);
  lval()->collect_index_exprs(exprs, env);
}

bool PAssign_::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                      Predicate &pred) {
  if (debug_typecheck) {
    cerr << "collect_dep_invariants on passign" << endl;
    cerr << "lval is: " << *lval() << endl;
  }
  // make sure basetype implies lhs has only 1 value per cycle (i.e. not a com
  // reg)
  BaseType *bt  = lval()->check_base_type(printer, env.varsToBase);
  bool isOkType = bt->isNextType(); // TODO check if declared as Wire
  // if lhs appears in dependent type and is correct basetype
  if (isOkType &&
      (env.dep_exprs.find(lval()->get_name()) != env.dep_exprs.end())) {
    bool hasPreds = !pred.hypotheses.empty();
    std::set<perm_string> genvars;
    collect_used_genvars(genvars, pred, env);
    lval()->collect_used_genvars(genvars, env);
    rval()->collect_used_genvars(genvars, env);
    printer.startList("assert");
    start_dump_genvar_quantifiers(printer, genvars, env);
    if (hasPreds) {
      printer.startList("=>");
      printer << pred;
    }
    printer.startList("=");
    lval()->dumpz3(printer);
    rval()->dumpz3(printer);
    printer.endList(); // end "="
    if (hasPreds) {
      printer.endList(); // end "=>"
    }
    end_dump_genvar_quantifiers(printer, genvars);
    printer.endList(); // end "assert"
    // also collect rhs variables in the dep_exprs to define them in z3 file
    rval()->collect_idens(env.dep_exprs);
    return true;
  } else {
    SecType *ltyp = lval()->typecheck(printer, env);
    bool isRecDep = ltyp->isDepType() && ltyp->hasExpr(lval()->get_name());
    // cerr << lval()->get_name() << " is recdep " << isRecDep << endl;
    if (isRecDep) {
      // also add idens on rhs to depexprs so we know to print them
      rval()->collect_idens(env.dep_exprs);
    }
    if (debug_typecheck) {
      cerr << "skipping collect_dep_invariants on " << *lval() << endl;
    }
    return false;
  }
}

Statement *PCAssign::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) {
  lval_ = lval_->next_cycle_transform(printer, env);
  return this;
}

PExpr *PExpr::next_cycle_transform(SexpPrinter &, TypeEnv &env) { return this; }

PExpr *PEIdent::next_cycle_transform(SexpPrinter &printer, TypeEnv &env) {

  BaseType *bt = check_base_type(printer, env.varsToBase);
  if (bt == NULL) {
    cerr << "WARN: null basetype: " << peek_tail_name(path()).str() << endl;
  }
  assert(bt);
  // if bt is seqtype, make it into next cycle version
  if (bt->isSeqType()) {
    name_component_t topName     = path().back();
    perm_string nextName         = nextify_perm_string(topName.name);
    name_component_t *newTopName = new name_component_t(nextName);
    newTopName->index            = topName.index;
    pform_name_t newPath;
    list<name_component_t>::const_iterator stop = path().end();
    --stop;
    for (list<name_component_t>::const_iterator it = path().begin(); it != stop;
         ++it) {
      newPath.push_back(*it);
    }
    newPath.push_back(*newTopName);
    if (debug_typecheck) {
      cerr << "Nextify " << path() << " to " << newPath << endl;
    }
    return new PEIdent(newPath);
  }
  return this;
}

PEIdent *PEIdent::get_this_cycle_name() {
  name_component_t topName     = path().back();
  perm_string lastName         = un_nextify_perm_string(topName.name);
  name_component_t *newTopName = new name_component_t(lastName);
  newTopName->index            = topName.index;
  pform_name_t newPath;
  list<name_component_t>::const_iterator stop = path().end();
  --stop;
  for (list<name_component_t>::const_iterator it = path().begin(); it != stop;
       ++it) {
    newPath.push_back(*it);
  }
  newPath.push_back(*newTopName);
  if (debug_typecheck) {
    cerr << "Nextify " << path() << " to " << newPath << endl;
  }
  return new PEIdent(newPath);
}

void PGenerate::next_cycle_transform(SexpPrinter &printer, TypeEnv env) {
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    if (debug_typecheck)
      cerr << "NextCycleTransform:: " << typeid(**behav).name() << endl;
    (*behav)->next_cycle_transform(printer, env);
  }
}

// PCallTask
// PCase
// PCAssign
// PDeassign
// PDelayStatement
// PDisable
// PEventStatement
// PForce
// PForever
// PForStatement
// PNoop
// PRepeat
// PRelease
// PTrigger
// PWhile

/**
 * Do nothing for now.
 */
void LexicalScope::typecheck_events_(SexpPrinter &printer, TypeEnv &env) const {
  if (debug_typecheck) {
    for (map<perm_string, PEvent *>::const_iterator cur = events.begin();
         cur != events.end(); cur++) {
      PEvent *ev = (*cur).second;
      cerr << ev->name() << ev->get_fileline() << endl;
    }
  }
}

/**
 * Get the security labels for wires.
 */
void LexicalScope::typecheck_wires_(SexpPrinter &printer, TypeEnv &env) const {
  // Iterate through and display all the wires.
  for (map<perm_string, PWire *>::const_iterator wire = wires.begin();
       wire != wires.end(); wire++) {
    (*wire).second->typecheck(printer, env.varsToType, env.varsToBase,
                              env.seqVars);
  }
}

/*
 * Type-check a wire.
 */
void PWire::typecheck(SexpPrinter &printer,
                      map<perm_string, SecType *> &varsToType,
                      map<perm_string, BaseType *> &varsToBase,
                      set<perm_string> &seqVars) const {
  if (debug_typecheck) {
    cerr << "PWire::check " << type_;

    switch (port_type_) {
    case NetNet::PIMPLICIT:
      cerr << " implicit input";
      break;
    case NetNet::PINPUT:
      cerr << " input";
      break;
    case NetNet::POUTPUT:
      cerr << " output";
      break;
    case NetNet::PINOUT:
      cerr << " inout";
      break;
    case NetNet::NOT_A_PORT:
      break;
    }

    cerr << " " << data_type_;

    if (signed_) {
      cerr << " signed";
    }

    if (discipline_) {
      cerr << " discipline<" << discipline_->name() << ">";
    }

    if (port_set_) {
      if (port_msb_ == 0) {
        cerr << " port<scalar>";
      } else {
        cerr << " port[" << *port_msb_ << ":" << *port_lsb_ << "]";
      }
    }
    if (net_set_) {
      if (net_msb_ == 0) {
        cerr << " net<scalar>";
      } else {
        cerr << " net[" << *net_msb_ << ":" << *net_lsb_ << "]";
      }
    }

    cerr << " " << name_;

    // If the wire has indices, dump them.
    if (lidx_ || ridx_) {
      cerr << "[";
      if (lidx_)
        cerr << *lidx_;
      if (ridx_)
        cerr << ":" << *ridx_;
      cerr << "]";
    }

    cerr << ";" << endl;
  }
  varsToType[basename()] = sectype_;
  varsToBase[basename()] = basetype_;
  if (sectype_ == NULL) {
    cerr << "WARN: Found NULL sectype for " << basename().str() << ", using BOT"
         << endl;
    varsToType[basename()] = ConstType::BOT;
  }
  if (debug_typecheck) {
    cerr << "updating typeEnv for " << basename();
    cerr << " with sectype: " << *(varsToType[basename()]);
    cerr << " and basetype: " << varsToBase[basename()]->name() << endl;
  }
  if (basetype_->isSeqType() &&
      (port_type_ == NetNet::NOT_A_PORT || port_type_ == NetNet::POUTPUT))
    seqVars.insert(basename());
}

void Module::dumpExprDefs(SexpPrinter &printer, set<perm_string> exprs) const {
  for (auto &expr : exprs) {
    map<perm_string, PWire *>::const_iterator cur = wires.find(expr);
    if (cur != wires.end()) {
      PWire *def = (*cur).second;
      // assume wires are either arrays or ints
      if (def->get_isarray()) {
        printer.inList("declare-fun", [&]() {
          printer << expr.str() << "()";
          printer.inList("Array", [&]() {
            printer << "Int"
                    << "Int";
          });
        });

        // printer.startList("declare-fun");
        // printer << expr.str() << "()";
        // printer.startList("Array");
        // printer << "Int"
        //         << "Int";
        // printer.endList();
        // printer.endList();

        printer.startList("assert");
        printer.startList("forall");
        printer.startList();
        printer.startList("x");
        printer << "Int";
        printer.endList();
        printer.endList();
        printer.startList("<=");
        printer << "0";
        printer.startList("select");
        printer << expr.str() << "x";
        printer.endList();
        printer.endList();
        printer.endList();
        printer.endList();

        printer.startList("assert");
        printer.startList("forall");
        printer.startList();
        printer.startList("x");
        printer << "Int";
        printer.endList();
        printer.endList();
        printer.startList("<=");
        printer.startList("select");
        printer << expr.str() << "x";
        printer.endList();
        printer << std::to_string((1 << (def->getRange() + 1)) - 1);
        printer.endList();
        printer.endList();
        printer.endList();
      } else {
        printDeclaration(printer, expr.str(), def);
      }
    } else {
      // in this case, its probably a genvar, do nothing
      if (debug_typecheck) {
        cerr << "couldn't find wire for " << expr << endl;
      }
    }
  }
}
PExpr *getInstantiatedAssumption(PGModule *mod,
                                 map<perm_string, Module *> modlist) {
  map<perm_string, Module *>::const_iterator tmp =
      modlist.find(mod->get_type());
  Module *moddef = (tmp != modlist.end()) ? (*tmp).second : NULL;
  if (moddef) {
    PExpr *assume = moddef->getAssumptions();
    if (assume) {
      map<perm_string, perm_string> pinSubst;
      mod->fillPinMap(pinSubst, moddef);
      return assume->subst(pinSubst);
    }
  }
  return NULL;
}

/**
 * Collect all expressions that  appears in dependent types.
 * Need to also collect all identifiers that appear in
 * index expressions of quantified types.
 */
void Module::CollectDepExprs(SexpPrinter &printer, TypeEnv &env,
                             map<perm_string, Module *> modules) const {
  set<perm_string> exprs;
  PExpr *assumption = getAssumptions();
  // Need all identifiers in our module assumptions to be defined
  if (assumption) {
    assumption->collect_idens(exprs);
  }
  for (std::map<perm_string, SecType *>::iterator iter = env.varsToType.begin();
       iter != env.varsToType.end(); iter++) {
    SecType *st = iter->second;
    st->collect_dep_expr(exprs);
  }

  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    (*behav)->collect_index_exprs(exprs, env);
  }
  for (list<PGenerate *>::const_iterator cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->collect_index_exprs(exprs, env);
  }

  for (list<PGate *>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign *pgassign = dynamic_cast<PGAssign *>(*gate);
    PGModule *pgmodule = dynamic_cast<PGModule *>(*gate);
    if (pgassign != NULL) {
      pgassign->collect_index_exprs(exprs, env);
    }
    if (pgmodule) {
      PExpr *modAssume = getInstantiatedAssumption(pgmodule, modules);
      if (modAssume) {
        modAssume->collect_idens(exprs);
      }
    }
  }

  for (std::set<perm_string>::iterator expr = exprs.begin();
       expr != exprs.end(); expr++) {
    env.dep_exprs.insert(*expr);
  }

  // declare the expressions as variables in z3 file
  printer.addComment("variables to be solved");
  dumpExprDefs(printer, env.dep_exprs);
}

/**
 * Generate invariants about the next cycle values of labels.
 * Only generate if expr is in a dependent label.
 * Returns true if any invariants were generated
 */
bool Module::CollectDepInvariants(SexpPrinter &printer, TypeEnv &env) const {
  printer.addComment("invariants about dependent variables");
  set<perm_string> oldDeps = env.dep_exprs;
  // collect invariants and print them after definining new variables
  stringstream invs;
  SexpPrinter tmp_printer(invs, printer.margin);
  for (auto behav : behaviors) {
    Predicate emptyPred;
    behav->collect_dep_invariants(tmp_printer, env, emptyPred);
  }
  for (auto gate : gates_) {
    PGAssign *pgassign = dynamic_cast<PGAssign *>(gate);
    if (pgassign != NULL) {
      pgassign->collect_dep_invariants(tmp_printer, env);
    }
  }
  for (auto cur : generate_schemes) {
    if (debug_typecheck)
      cerr << "collecting dep invariants on generate scheme" << endl;
    cur->collect_dep_invariants(tmp_printer, env);
  }

  if (debug_typecheck)
    cerr << "done collecting dep invariants on generate schemes" << endl;

  set<perm_string> newDeps;
  std::set_difference(env.dep_exprs.begin(), env.dep_exprs.end(),
                      oldDeps.begin(), oldDeps.end(),
                      std::inserter(newDeps, newDeps.end()));
  if (debug_typecheck)
    cerr << "calculated newDeps" << endl;

  auto tmp = newDeps;
  for (auto v : tmp) {
    if (env.varsToBase.contains(v) && env.varsToBase.at(v)->isSeqType()) {
      newDeps.insert(nextify_perm_string(v));
    }
  }

  if (debug_typecheck)
    cerr << "starting unassigned path assertions" << endl;

  // variables that show up on a path need to be declared
  set<perm_string> pathVariables;
  // auto portVars =
  //     std::ranges::transform_view(ports, [](auto &port) { return port->name;
  //     });

  for (auto &p : env.analysis) {
    for (auto &pred : p.second) {
      for (auto h : pred.hypotheses) {
        h->bexpr_->collect_idens(pathVariables);
      }
    }
  }
  // set<perm_string> pathVariables = pathVariables;
  //  std::set_intersection(
  //      pathVariables.begin(), pathVariables.end(), portVars.begin(),
  //      portVars.end(),
  //      std::inserter(pathVariables, pathVariables.end()));

  for (auto &de : env.dep_exprs) {
    pathVariables.erase(de);
  }

  set<perm_string> newVars;
  std::set_union(newDeps.begin(), newDeps.end(), pathVariables.begin(),
                 pathVariables.end(), std::inserter(newVars, newVars.end()));
  dumpExprDefs(printer, newVars);

  auto outStr = invs.str();
  printer.writeRawLine(outStr);

varloop:
  for (auto &depVar : std::ranges::filter_view(env.dep_exprs, [&](auto &v) {
         return env.varsToBase.contains(v) && env.varsToBase.at(v) &&
                env.varsToBase.at(v)->isSeqType();
       })) {

    auto wire      = wires.find(depVar);
    auto def       = wire->second;
    auto nextified = nextify_perm_string(depVar);

    if (def->get_isarray()) {
      auto all_relevant =
          std::ranges::filter_view(env.analysis,
                                   [depVar](auto &v) {
                                     auto str       = std::string(v.first);
                                     auto brack_idx = str.find_first_of('[');
                                     if (brack_idx == 0)
                                       brack_idx = str.size();
                                     auto lit = perm_string::literal(
                                         str.substr(0, brack_idx).c_str());
                                     return lit == depVar;
                                   }) |
          std::views::transform([](auto &v) {
            std::regex regex("\\[([^\\[]*)\\]");
            auto str = std::string(v.first);
            std::smatch match;
            if (std::regex_search(str, match, regex)) {
              return std::make_pair(match[1].str(), v.second);
            } else {
              auto msg = new std::string("Attempted to assign whole array: ");
              *msg += str;
              throw std::runtime_error(*msg);
            }
          });

      int range = def->getArrayRange();

      printer.inList("assert", [&]() {
        printer.inList("forall", [&]() {
          printer << "((_i Int))";
          printer.inList("=>", [&]() {
            printer.inList("and", [&]() {
              std::string range_str("(<= 0 _i) (< _i ");
              range_str += std::to_string(range) + ")";
              printer << range_str;
              printer.inList("not", [&]() {
                printer.inList("or", [&]() {
                  if (!all_relevant.empty()) {
                    for (const auto &a : all_relevant) {
                      auto lit = perm_string::literal(a.first.c_str());
                      if (env.genVarVals.contains(lit)) {
                        auto lst = env.genVarVals[lit];
                        printer.inList("and", [&]() {
                          printer.inList("or", [&]() {
                            for (auto value : lst)
                              printer.inList("=", [&]() {
                                printer << "_i" << std::to_string(value);
                              });
                          });
                          std::map<perm_string, perm_string> mp{
                              {lit, perm_string::literal("_i")}};
                          for (const auto &path : std::ranges::transform_view(
                                   a.second, [&mp](auto &pred) {
                                     return *pred.subst(mp);
                                   })) {
                            printer << path;
                          }
                        });
                      } else {
                        // non genvars are treated normally
                        printer.inList("and", [&]() {
                          printer.inList("=",
                                         [&]() { printer << "_i" << a.first; });
                          printer.inList("not", [&]() {
                            printer.inList("or", [&]() {
                              for (const auto &path : a.second)
                                printer << path;
                            });
                          });
                        });
                      }
                    }
                  } else {
                    printer << "false";
                  }
                });
              });
            });
            auto i_str = "_i";
            printer.inList("=", [&]() {
              printer.inList("select",
                             [&]() { printer << nextified.str() << i_str; });
              printer.inList("select",
                             [&]() { printer << depVar.str() << i_str; });
            });
          });
        });
      });
      // }
    } else {
      auto &branches = env.analysis[depVar];
      if (!branches.empty()) {
        printer.inList("assert", [&]() {
          printer.inList("=>", [&]() {
            printer.inList("not", [&]() {
              printer.inList("or", [&]() {
                for (auto &path : branches)
                  printer << path;
              });
            });
            printer.inList(
                "=", [&]() { printer << nextified.str() << depVar.str(); });
          });
        });
      }
    }
  }

  return !outStr.empty();
}

PExpr *Module::getAssumptions() const {
  try {
    return attributes.at(perm_string::literal(ASSUME_NAME));
  } catch (const std::out_of_range &oor) {
    return NULL;
  }
}

void makeAssumptions(Module *mod, SexpPrinter &printer, TypeEnv &env) {
  PExpr *assumeAttr = mod->getAssumptions();
  if (assumeAttr) {
    if (debug_typecheck)
      cerr << "Found assume attribute in module" << endl;
    printer.addComment("Input module assertions");
    printer.startList("assert");
    assumeAttr->dumpz3(printer);
    printer.endList();
  }
}

void checkUnassignedPaths(SexpPrinter &printer, TypeEnv &env, Module &m) {
  for (auto v : env.seqVars) {
    auto sectype = env.varsToType[v];
    if (debug_typecheck) {
      cerr << "checking unassigned paths of " << v << endl;
      cerr << "sectype is: " << *sectype << endl;
    }

    if (sectype->isDepType()) {
      if (debug_typecheck)
        cerr << "type of " << v << " is dependent\n";
      auto wire = m.wires[v];

      std::string note("checking unassigned paths of ");
      note += v.str();
      if (wire->get_isarray()) {
        if (debug_typecheck)
          cerr << v << " is an array\n";
        // do array stuff;
        auto all_relevant_view =
            std::ranges::filter_view(env.analysis,
                                     [v](auto &var) {
                                       auto str       = std::string(var.first);
                                       auto brack_idx = str.find_first_of('[');
                                       if (brack_idx == 0)
                                         brack_idx = str.size();
                                       auto lit = perm_string::literal(
                                           str.substr(0, brack_idx).c_str());
                                       return lit == v;
                                     }) |
            std::views::transform([](auto &var) {
              std::regex regex("\\[([^\\[]*)\\]");
              auto str = std::string(var.first);
              std::smatch match;
              if (std::regex_search(str, match, regex)) {

                // auto lit = perm_string::literal(match[1].str().c_str());
                return std::make_pair(match[1].str(), var.second);
              }
              throw std::runtime_error("failed to match");
            });
        std::vector all_relevant_vec(all_relevant_view.begin(),
                                     all_relevant_view.end());
        auto all_relevant =
            std::ranges::filter_view(all_relevant_vec, [&env](auto &pr) {
              auto lit = perm_string::literal(pr.first.c_str());
              return !env.genVarVals.contains(lit);
            });
        int range = wire->getArrayRange(); // 1 << (def->getRange() + 1);

        std::vector filtered_relevant(all_relevant.begin(), all_relevant.end());
        if (debug_typecheck) {
          std::cerr << "range is 0-" << range << endl;
          std::cerr << "all relevant size: " << filtered_relevant.size()
                    << endl;
        }

        if (!filtered_relevant.empty()) {
          for (int i = 0; i < range; ++i) {
            printer.singleton("push");
            printer.inList("echo", [&]() {
              printer.printString((note + "[") + std::to_string(i) + "]");
            });
            printer.inList("assert", [&]() {
              printer.inList("not", [&]() {
                printer.inList("or", [&]() {
                  if (debug_typecheck)
                    cerr << "back here..." << endl;
                  for (const auto &a : filtered_relevant) {
                    if (debug_typecheck)
                      cerr << "index: " << i << ", index var: " << a.first
                           << endl;
                    printer.inList("and", [&]() {
                      printer.inList("=", [&]() {
                        printer << std::to_string(i) << a.first;
                      });
                      dump_on_paths(printer, a.second);
                    });
                  }
                });
              });
            });
            if (debug_typecheck)
              cerr << "got here..." << endl;

            std::stringstream ss;
            SexpPrinter tmp(ss, 99999);
            sectype->dump(tmp);
            auto quantified = dynamic_cast<QuantType *>(sectype);

            if (debug_typecheck)
              cerr << "and here..." << endl;

            auto idx = new PENumber(new verinum(i));
            auto applied =
                dynamic_cast<QuantType *>(quantified->apply_index(idx));
            if (debug_typecheck)
              cerr << "here?" << endl;

            idx               = new PENumber(new verinum(i));
            auto next_sectype = dynamic_cast<QuantType *>(
                quantified->next_cycle(env)->apply_index(idx));

            if (debug_typecheck) {
              cerr << "this_inner: " << *applied->getInnerType() << endl
                   << "next inner: " << *next_sectype->getInnerType() << endl;
            }

            Predicate empty;
            Constraint c(next_sectype, applied, env.invariants, &empty);
            set<perm_string> empty_genvars;
            dump_constraint(printer, c, empty_genvars, env);

            printer.singleton("check-sat");
            printer.singleton("pop");
          }
        }

      } else {
        if (debug_typecheck)
          cerr << v << " is not an array\n";
        printer.singleton("push");
        printer.inList("echo", [&]() { printer.printString(note); });

        printer.inList("assert", [&]() {
          printer.inList(
              "not", [&]() { dump_is_def_assign(printer, env.analysis, v); });
        });

        auto next_sectype = sectype->next_cycle(env);
        Predicate empty;
        Constraint c(next_sectype, sectype, env.invariants, &empty);
        set<perm_string> empty_genvars;
        dump_constraint(printer, c, empty_genvars, env);
        printer.singleton("check-sat");
        printer.singleton("pop");
      }
    }
  }
}

/**
 * Type-check a module.
 */
void Module::typecheck(SexpPrinter &printer, TypeEnv &env,
                       map<perm_string, Module *> modules, char *depfun,
                       char *latfile) {
  if (debug_typecheck) {
    cerr << "Module::check " << mod_name() << endl;
    for (unsigned idx = 0; idx < ports.size(); idx += 1) {
      port_t *cur = ports[idx];
      if (cur == 0) {
        cerr << "    unconnected" << endl;
        continue;
      }
      cerr << "Port::check " << cur->name << "(" << *cur->expr[0];
      for (unsigned wdx = 1; wdx < cur->expr.size(); wdx += 1) {
        cerr << ", " << *cur->expr[wdx];
      }
      cerr << ")" << endl;
    }
  }

  if (debug_typecheck)
    cerr << "typechecking module parameters" << endl;
  typecheck_parameters_(printer, env);
  if (debug_typecheck)
    cerr << "typechecking localparams" << endl;
  typecheck_localparams_(printer, env);

  typedef map<perm_string, LineInfo *>::const_iterator genvar_iter_t;
  for (genvar_iter_t cur = genvars.begin(); cur != genvars.end(); cur++) {
    // genvars are bottom
    env.varsToType[(*cur).first] = ConstType::BOT;
  }

  typedef map<perm_string, PExpr *>::const_iterator specparm_iter_t;
  for (specparm_iter_t cur = specparams.begin(); cur != specparams.end();
       cur++) {
    throw "specparams not supported";
  }

  typedef list<Module::named_expr_t>::const_iterator parm_hiter_t;
  for (parm_hiter_t cur = defparms.begin(); cur != defparms.end(); cur++) {
    throw "defparams not supported";
  }

  typecheck_events_(printer, env);

  // Iterate through and display all the wires (including registers).
  if (debug_typecheck)
    cerr << "typechecking wires" << endl;
  typecheck_wires_(printer, env);

  auto analysis = get_paths(*this, env);
  env.analysis  = analysis;

  if (debug_typecheck)
    cerr << "next-cycle transform" << endl;
  next_cycle_transform(printer, env);

  if (debug_typecheck)
    cerr << "collecting dependands" << endl;
  CollectDepExprs(printer, env, modules);
  if (debug_typecheck)
    cerr << "generating input invariant assumptions" << endl;
  makeAssumptions(this, printer, env);

  typedef list<PGenerate *>::const_iterator genscheme_iter_t;
  if (debug_typecheck)
    cerr << "collecting definite assignments" << endl;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->collectAssigned(env);
  }
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    set<perm_string> s;
    (*behav)->collectAssigned(s);
    env.defAssigned[(*behav)] = s;
  }

  if (debug_typecheck)
    cerr << "collecting genvar values" << endl;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->fill_genvar_vals(mod_name(), env.genVarVals);
  }
  if (debug_typecheck) {
    cerr << "genvar possible values" << endl;
    for (auto &g : env.genVarVals) {
      cerr << "genvar: " << g.first << "->" << endl;
      cerr << "(";
      for (auto &e : g.second) {
        cerr << e << ", ";
      }
      cerr << ")" << endl;
    }
  }

  if (debug_typecheck)
    cerr << "collecting dependent invariants" << endl;
  bool foundInvs = CollectDepInvariants(printer, env);

  if (overlap_check)
    dump_no_overlap_anal(printer, *this, env, env.seqVars);

  // TODO probably delete this
  //  remove an invariant if some variable does not show up
  if (0) {
    if (debug_typecheck)
      cerr << "optimizing invariants" << endl;
    for (set<Equality *>::iterator invite = env.invariants->invariants.begin();
         invite != env.invariants->invariants.end();) {
      set<perm_string> vars, diff;
      (*invite)->left->collect_dep_expr(vars);
      (*invite)->right->collect_dep_expr(vars);

      set<Equality *>::iterator current = invite++;

      // if the invariant has free variables, then remove it
      for (set<perm_string>::iterator varite = vars.begin();
           varite != vars.end(); varite++) {
        if (env.dep_exprs.find(*varite) == env.dep_exprs.end()) {
          env.invariants->invariants.erase(current);
          break;
        }
      }
    }
  }
  // end TODO of delete

  printer.lineBreak();
  if (foundInvs) {
    // Only check base conditions if we actually _have_ base conditions
    // Otherwise the solver tends to hang
    printer.startList("echo");
    printer << "\"Start base conditions are satisfiable? (should be sat)\"";
    printer.endList();
    printer.singleton("check-sat");
    printer.lineBreak();
    printer.startList("echo");
    printer << "\"End base conditions are satisfiable?\"";
    printer.endList();
  } else {
    printer.startList("echo");
    printer << "\"Skipping base conditions check\"";
    printer.endList();
  }

  if (debug_typecheck)
    cerr << "outputting lattice" << endl;
  output_lattice(printer, latfile);
  if (debug_typecheck)
    cerr << "outputting type families" << endl;
  output_type_families(printer, depfun);

  printer.addComment("assertions to be verified");

  if (debug_typecheck) {
    cerr << "checking generates" << endl;
  }
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->typecheck(printer, env, modules);
  }

  checkUnassignedPaths(printer, env, *this);

  // Dump the task definitions.
  if (debug_typecheck) {
    cerr << "dump tasks" << endl;
    typedef map<perm_string, PTask *>::const_iterator task_iter_t;
    for (task_iter_t cur = tasks.begin(); cur != tasks.end(); cur++) {
      cerr << "PTask ignored" << endl;
    }
  }

  // Dump the function definitions.
  if (debug_typecheck) {
    cerr << "dump functions" << endl;
    typedef map<perm_string, PFunction *>::const_iterator func_iter_t;
    for (func_iter_t cur = funcs.begin(); cur != funcs.end(); cur++) {
      cerr << "PFunction" << endl;
    }
  }

  // Iterate through and display all the gates.
  if (debug_typecheck)
    cerr << "checking gates" << endl;
  for (list<PGate *>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign *pgassign = dynamic_cast<PGAssign *>(*gate);
    PGModule *pgmodule = dynamic_cast<PGModule *>(*gate);

    // make sure the parameters has same label as module declaration
    if (pgmodule != NULL) {
      pgmodule->typecheck(printer, env, modules);
    } else if (pgassign != NULL) {
      Predicate pred;
      set<perm_string> empty;
      pgassign->typecheck(printer, env, pred, empty);
    }
  }

  // The code above should collect a typing environment for all variables.
  // The following code performs intra-process type checking.
  if (debug_typecheck)
    cerr << "checking processes" << endl;
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    (*behav)->typecheck(printer, env, env.defAssigned[(*behav)]);
  }

  if (debug_typecheck)
    cerr << "checking AProcesses" << endl;
  for (list<AProcess *>::const_iterator idx = analog_behaviors.begin();
       idx != analog_behaviors.end(); idx++) {
    throw "Analog behaviors not supported";
  }

  if (debug_typecheck)
    cerr << "checking PSpecPaths" << endl;
  for (list<PSpecPath *>::const_iterator spec = specify_paths.begin();
       spec != specify_paths.end(); spec++) {
    throw "Specify paths not supported";
  }
}

/**
 * Type-check a process.
 */
void PProcess::typecheck(SexpPrinter &printer, TypeEnv &env,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PProcess:check "
         << " /* " << get_fileline() << " */" << endl;
  }

  // initial is not synthesizable, just ignore them
  if (type_ != IVL_PR_INITIAL) {
    Predicate emptypred;
    if (debug_typecheck) {
      cerr << "pprocess checking statement of type ";
      cerr << typeid(*statement_).name() << endl;
    }
    PProcess *x = const_cast<PProcess *>(this);
    statement_->typecheck(printer, env, emptypred, env.defAssigned[x]);
  }
}

/**
 * Do nothing.
 */
void AContrib::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "AContrib::check ";
    cerr << *lval_ << " <+ " << *rval_ << endl;
  }
  throw "AContrib";
}

/**
 * Generate constraints for an assignment
 * lhs <= rhs
 *
 * pred: A predication on hardware state that holds when the assignment
 * occurs. For example, (x==1). note: The line of code in the source file.
 * This information is used to trace a security violation back to SecVerilog
 * source code. details. env: A typing environment.
 */
void typecheck_assignment_constraint(SexpPrinter &printer, SecType *lhs,
                                     SecType *rhs, Predicate pred, string note,
                                     PEIdent *checkDefAssign, TypeEnv &env) {
  std::set<perm_string> genvars;
  collect_used_genvars(genvars, pred, env);
  collect_used_genvars(genvars, lhs, env);
  collect_used_genvars(genvars, rhs, env);
  printer.lineBreak();
  printer.singleton("push");
  if (checkDefAssign) {
    printer.startList("assert");
    // TODO make the genvars get selected based on defAssign analysis
    // for only this assertion
    start_dump_genvar_quantifiers(printer, genvars, env);
    printer.startList("not");
    dump_is_def_assign(printer, env.analysis, checkDefAssign->get_full_name());
    printer.endList();
    end_dump_genvar_quantifiers(printer, genvars);
    printer.endList();
  }
  Constraint c = Constraint(lhs, rhs, env.invariants, &pred);
  dump_constraint(printer, c, genvars, env);

  printer.addComment(note);
  printer.startList("echo");
  printer << (string("\"") + note + "\"");
  printer.endList();
  printer.singleton("check-sat");
  printer.singleton("pop");
}

/**
 * Type-check an assignment (either noblocking or blocking).
 */
void typecheck_assignment(SexpPrinter &printer, PExpr *lhs, PExpr *rhs,
                          TypeEnv &env, Predicate precond, Predicate postcond,
                          unsigned int lineno, string note, bool is_blocking,
                          set<perm_string> &defAssgns) {
  // when the RHS is a PETernary expression, i.e. e1?e2:e3, we first
  // translate to the equivalent statements
  PETernary *ternary = dynamic_cast<PETernary *>(rhs);
  if (ternary == NULL) {
    SecType *ltype, *rtype, *ltype_orig;
    BaseType *lbase;
    PEIdent *lident = dynamic_cast<PEIdent *>(lhs);
    lbase           = lhs->check_base_type(printer, env.varsToBase);
    if (lident != NULL) {
      // if lhs is v[x], only want to put type(v) in the type
      ltype_orig = lident->typecheckName(printer, env, false);
      // want next cycle version if is NextType
      ltype = lident->typecheckName(printer, env, lbase->isNextType());
    } else {
      auto msg = new std::string("Assigned to non identifier on LHS: ");
      *msg += lhs->get_name().str();
      throw std::runtime_error(*msg);
    }

    rtype = new JoinType(rhs->typecheck(printer, env), env.pc);
    if (lident != NULL) {
      // if lhs is v[x], want to include type(x) in the rhs type
      rtype = new JoinType(rtype, lident->typecheckIdx(printer, env));
    }
    if (debug_typecheck) {
      cerr << "line no" << lineno << endl;
      cerr << "pctype: " << *env.pc << endl;
      cerr << "ltype: " << *ltype << endl;
      cerr << "rtype: " << *rtype << endl;
      cerr << "lbase: " << lbase->name() << endl;
      cerr << "lhs: " << *lhs << endl;
      cerr << "rhs: " << *rhs << endl;
      cerr << "precond: " << precond << endl;
      cerr << "postcond: " << postcond << endl;
    }

    // is com type and has reflexive label
    bool isRecursiveCom =
        !lbase->isNextType() && ltype->hasExpr(lhs->get_name());
    if (isRecursiveCom && is_blocking) { // the is_blocking check should be
                                         // redundant, but just in case :)
      // declare a fresh variable to represent new value of lhs
      printer.singleton("push");
      string tmpname(lhs->get_name());
      tmpname.append(to_string(lineno));
      perm_string newname = perm_string::literal(tmpname.c_str());
      printDecl(printer, newname.str());
      auto wire_ite = env.module->wires.find(lhs->get_name());
      if (wire_ite != env.module->wires.end()) {
        PWire *def = (*wire_ite).second;
        printBounds(printer, newname.str(), def);
      }
      // assume new value for rhs
      Predicate newcond = precond;
      newcond.hypotheses.insert(new Hypothesis(new PEIdent(newname), rhs));
      // replace lhsname in ltype
      typecheck_assignment_constraint(printer,
                                      ltype->subst(lhs->get_name(), newname),
                                      rtype, newcond, note, NULL, env);
      // NSU check if not definitely assigned:
      if (!defAssgns.contains(lhs->get_name())) {
        string newNote = note + "--No-sensitive-upgrade-check;";
        Predicate emptyPred;
        typecheck_assignment_constraint(printer, ltype_orig, env.pc, emptyPred,
                                        newNote, NULL, env);
      }
      printer.singleton("pop");
      printer.lineBreak();
    } else {
      // is seq type or non rec dep com
      typecheck_assignment_constraint(printer, ltype, rtype, precond, note,
                                      NULL, env);
      // need no-sensitive-upgrade check when:
      //   - lident has a recursive dep type
      //   - lident is not definitely assigned
      //   - lident is a NEXT type (i.e., it's a register assignment)
      if ((ltype_orig->isDepType() && lbase->isNextType())) {
        PEIdent *origName = lident->get_this_cycle_name();
        // is recursive if ltype contains lident
        if (ltype_orig->hasExpr(origName->get_name())) {
          // either  isDefAssigned(lident) OR forall contexts.
          //  (leq pc ltype_orig)
          //  rtype also flows to cur cycle label of lident in any context
          string newNote = note + "--No-sensitive-upgrade-check;";
          Predicate emptyPred;
          typecheck_assignment_constraint(printer, ltype_orig, env.pc,
                                          emptyPred, newNote, origName, env);
        }
      }
    }
  } else {
    ternary->translate(lhs, is_blocking)
        ->typecheck(printer, env, precond, defAssgns);
  }
}

void PGAssign::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  pin(0)->collect_index_exprs(exprs, env);
  pin(1)->collect_index_exprs(exprs, env);
}

bool PGAssign::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env) {
  if (debug_typecheck) {
    cerr << "collect_dep_invariants on pgassign" << endl;
  }
  PExpr *l      = pin(0);
  PEIdent *lval = dynamic_cast<PEIdent *>(l);
  PExpr *rval   = pin(1);
  if (!lval) {
    cerr << "Skipping assign to non identifier in gate when collecting "
            "dep invariants"
         << endl;
    return false;
  }
  if (env.dep_exprs.find(lval->get_name()) != env.dep_exprs.end()) {
    std::set<perm_string> genvars;
    lval->collect_used_genvars(genvars, env);
    rval->collect_used_genvars(genvars, env);
    printer.startList("assert");
    start_dump_genvar_quantifiers(printer, genvars, env);
    printer.startList("=");
    lval->dumpz3(printer);
    rval->dumpz3(printer);
    printer.endList(); // end "="
    end_dump_genvar_quantifiers(printer, genvars);
    printer.endList(); // end "assert"
    // also collect rhs variables in the dep_exprs to define them in z3
    // file
    rval->collect_idens(env.dep_exprs);
    return true;
  } else {
    return false;
  }
}

/**
 * Type-check a blocking assignment.
 */
void PGAssign::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "assign " << *pin(0) << " = " << *pin(1) << ";" << endl;
  }

  stringstream ss;
  ss << "assign " << *pin(0) << " = " << *pin(1) << " @" << get_fileline();
  Predicate post;
  typecheck_assignment(printer, pin(0), pin(1), env, pred, post, get_lineno(),
                       ss.str(), true, defAssgn);
}

void check_assumption(SexpPrinter &printer, PExpr *assume, perm_string mname,
                      perm_string mtype) {
  printer.lineBreak();
  printer.singleton("push");
  printer.startList("assert");
  printer.startList("not");
  assume->dumpz3(printer);
  printer.endList();
  printer.endList();
  printer.startList("echo");
  printer << "\"checking assumptions for" << mname.str() << "of type module"
          << mtype.str() << "\"";
  printer.endList();
  printer.singleton("check-sat");
  printer.singleton("pop");
}

void PGModule::fillPinMap(map<perm_string, perm_string> &pinSubst,
                          Module *moddef) {
  map<perm_string, PWire *> mwires = moddef->wires;
  for (unsigned idx = 0; idx < get_pin_count(); idx += 1) {
    map<perm_string, PWire *>::const_iterator ite =
        mwires.find(get_pin_name(idx));
    if (ite != mwires.end()) {
      PWire *port = (*ite).second;
      if (port->get_port_type() == NetNet::PINPUT ||
          port->get_port_type() == NetNet::PINOUT) {
        pinSubst[get_pin_name(idx)] = get_param(idx)->get_name();
      } else {
        pinSubst[get_pin_name(idx)] = get_pin_name(idx);
      }
    }
  }
}

void PGModule::fillParamMap(map<perm_string, perm_string> &paraSubst,
                            Module *moddef) {
  map<perm_string, PWire *> mwires = moddef->wires;
  for (unsigned idx = 0; idx < get_pin_count(); idx += 1) {
    map<perm_string, PWire *>::const_iterator ite =
        mwires.find(get_pin_name(idx));
    PWire *port = (*ite).second;
    if (port->get_port_type() == NetNet::POUTPUT ||
        port->get_port_type() == NetNet::PINOUT) {
      paraSubst[get_param(idx)->get_name()] = get_pin_name(idx);
    } else {
      paraSubst[get_param(idx)->get_name()] = get_param(idx)->get_name();
    }
  }
}

/**
 * Type-check a module instantiation.
 */
void PGModule::typecheck(SexpPrinter &printer, TypeEnv &env,
                         map<perm_string, Module *> modules) {
  if (debug_typecheck)
    cerr << "pc context for module instantiation?" << endl;

  this->pin_count();
  this->get_pin_count();
  map<perm_string, Module *>::const_iterator cur = modules.find(get_type());
  map<perm_string, PWire *> mwires;
  if (cur != modules.end()) {
    mwires            = ((*cur).second)->wires;
    unsigned pincount = get_pin_count();
    map<perm_string, perm_string> pinSubst;
    map<perm_string, perm_string> paraSubst;
    fillPinMap(pinSubst, (*cur).second);
    fillParamMap(paraSubst, (*cur).second);

    // Check that assumptions of this module MUST be satisfied:
    // negate assumption and look for unsat
    // Also substitute the original pin names for the instantiated pins
    PExpr *assume = getInstantiatedAssumption(this, modules);
    if (assume) {
      check_assumption(printer, assume->subst(pinSubst), get_name(),
                       get_type());
    }

    for (unsigned idx = 0; idx < pincount; idx += 1) {
      map<perm_string, PWire *>::const_iterator ite =
          mwires.find(get_pin_name(idx));
      if (ite != mwires.end()) {
        PExpr *param = get_param(idx);
        if (param != NULL) {
          printer.lineBreak();
          printer.singleton("push");
          // the direction (input, output) determines def or use should be
          // more restrictive: def <= use for outputs use <= def for
          // inputs
          PWire *port               = (*ite).second;
          NetNet::PortType porttype = port->get_port_type();

          SecType *paramType = param->typecheck(printer, env);
          SecType *pinType   = port->get_sec_type();
          for (std::map<perm_string, perm_string>::iterator substiter =
                   pinSubst.begin();
               substiter != pinSubst.end(); ++substiter)
            pinType =
                pinType->subst(substiter->first, pinSubst[substiter->first]);
          for (std::map<perm_string, perm_string>::iterator substiter =
                   paraSubst.begin();
               substiter != paraSubst.end(); ++substiter)
            paramType =
                paramType->subst(substiter->first, paraSubst[substiter->first]);
          // declare the free variables in pinType when necessary
          set<perm_string> vars;
          pinType->collect_dep_expr(vars);
          for (set<perm_string>::iterator varsite = vars.begin();
               varsite != vars.end(); varsite++) {
            if (env.dep_exprs.find(*varsite) == env.dep_exprs.end()) {
              printer.startList("declare-fun");
              printer << varsite->str() << "()"
                      << "Int";
              printer.endList();
              map<perm_string, PWire *>::const_iterator decl =
                  mwires.find(*varsite);
              // get the range of the free variables
              if (decl != mwires.end()) {
                PWire *def = (*decl).second;
                printer.startList("assert");
                printer.startList("<=");
                printer << "0" << varsite->str();
                printer.endList();
                printer.endList();
                printer.startList("assert");
                printer.startList("<=");
                printer << varsite->str()
                        << std::to_string((1 << (def->getRange() + 1)) - 1);
                printer.endList();
                printer.endList();
              }
            }
          }

          if (porttype == NetNet::PINPUT || porttype == NetNet::PINOUT) {
            SecType *rhs = paramType;
            SecType *lhs = pinType;
            Predicate pred;
            Constraint c = Constraint(lhs, rhs, env.invariants, &pred);
            // TODO genvars properly
            std::set<perm_string> genvars;
            dump_constraint(printer, c, genvars, env);
            // debugging information
            std::stringstream tmp;
            tmp << "Instantiate parameter " << get_pin_name(idx)
                << " in module " << get_type() << " @" << get_fileline()
                << endl;
            printer.addComment(tmp.str());
            tmp.str("");
            tmp.clear();
            printer.startList("echo");
            tmp << "\"parameter " << get_pin_name(idx) << " for module "
                << get_type() << " @" << get_fileline() << "\"";
            printer << tmp.str();
            printer.endList();
            printer.singleton("check-sat");
            printer.singleton("pop");
          } else if (porttype == NetNet::POUTPUT ||
                     porttype == NetNet::PINOUT) {
            SecType *rhs = pinType;
            SecType *lhs = paramType;
            Predicate pred;
            Constraint c = Constraint(lhs, rhs, env.invariants, &pred);
            // TODO genvars properly
            std::set<perm_string> genvars;
            dump_constraint(printer, c, genvars, env);
            // debugging information
            std::stringstream tmp;
            tmp << "Instantiate parameter " << get_pin_name(idx)
                << " in module " << get_type() << " @" << get_fileline()
                << endl;
            printer.addComment(tmp.str());
            tmp.str("");
            tmp.clear();
            printer.startList("echo");
            tmp << "\"parameter " << get_pin_name(idx) << " for module "
                << get_type() << " @" << get_fileline() << "\"";
            printer << tmp.str();
            printer.endList();
            printer.singleton("check-sat");
            printer.singleton("pop");
          }
        } else {
          cerr << "parameter " << *param << " is not found" << endl;
        }
      } else {
        cerr << "PWire " << get_pin_name(idx) << " is not found" << endl;
      }
    }
  }
}

/**
 * Type-check an assignment statement.
 */
void PAssign::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                        set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PAssign::check " << *lval() << " = ";
    if (delay_)
      cerr << "#" << *delay_ << " ";
    if (count_)
      cerr << "repeat(" << *count_ << ") ";
    if (event_)
      cerr << *event_ << " ";
    cerr << *rval() << ";" << endl;
  }

  auto ident = dynamic_cast<PEIdent *>(lval_);
  if (ident && env.varsToBase.contains(ident->get_name()) &&
      env.varsToBase[ident->get_name()]->isSeqType()) {
    auto msg = new std::string("tried to use blocking assign on seq var: ");
    *msg += ident->get_name().str();
    *msg += " on line ";
    *msg += get_fileline();
    throw std::runtime_error(*msg);
  }

  stringstream ss;
  ss << *lval() << " = " << *rval() << " @" << get_fileline();

  Predicate precond = pred;
  absintp(pred, env);
  typecheck_assignment(printer, lval_, rval_, env, precond, pred, get_lineno(),
                       ss.str(), true, defAssgn);
}

/**
 * Type-check a nonblocking assignment.
 */
void PAssignNB::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                          set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PAssignNB::check " << *lval() << " <= ";
    if (delay_)
      cerr << "#" << *delay_ << " ";
    if (count_)
      cerr << "repeat(" << *count_ << ") ";
    if (event_)
      cerr << *event_ << " ";
    cerr << *rval() << ";" << endl;
  }

  auto ident = dynamic_cast<PEIdent *>(lval_);
  if (ident && env.varsToBase.contains(ident->get_name()) &&
      !env.varsToBase[ident->get_name()]->isNextType() &&
      !env.varsToBase[ident->get_name()]->isSeqType()) {
    auto msg =
        new std::string("tried to use nonblocking assign on nonseq var: ");
    *msg += ident->get_name().str();
    *msg += " on line ";
    *msg += get_fileline();
    throw std::runtime_error(*msg);
  }

  stringstream ss;
  ss << *lval() << " <= " << *rval() << " @" << get_fileline();

  Predicate precond = pred;
  absintp(pred, env);
  typecheck_assignment(printer, lval_, rval_, env, precond, pred, get_lineno(),
                       ss.str(), false, defAssgn);
}

/**
 * Type-check a block of code.
 */
void PBlock::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                       set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PBlock::check "
         << "begin";
    if (pscope_name() != 0)
      cerr << " : " << pscope_name();
    cerr << endl;
  }

  if (pscope_name() != 0) {
    typecheck_parameters_(printer, env);

    typecheck_localparams_(printer, env);

    typecheck_events_(printer, env);

    typecheck_wires_(printer, env);
  }

  set<Hypothesis *> before = pred.hypotheses;
  for (unsigned idx = 0; idx < list_.count(); idx += 1) {
    if (list_[idx])
      list_[idx]->typecheck(printer, env, pred, defAssgn);
  }
}

/**
 * Do nothing.
 */
void PCallTask::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                          set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PCallTask::check " << path_;

    if (parms_.count() > 0) {
      cerr << "(";
      if (parms_[0])
        cerr << *parms_[0];

      for (unsigned idx = 1; idx < parms_.count(); idx += 1) {
        cerr << ", ";
        if (parms_[idx])
          cerr << *parms_[idx];
      }
      cerr << ")";
    }
    cerr << endl;
  }
  // throw "PCallTask";
  cerr << "PCallTask is ignored" << endl;
}

/**
 * Type-check a case statement.
 */
void PCase::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                      set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PCase::check ";

    cerr << " (" << *expr_ << ") " << endl;

    for (unsigned idx = 0; idx < items_->count(); idx += 1) {
      PCase::Item *cur = (*items_)[idx];

      if (cur->expr.count() != 0) {
        cerr << "case item " << *cur->expr[0];

        for (unsigned e = 1; e < cur->expr.count(); e += 1)
          cerr << ", " << *cur->expr[e];

        cerr << ":";
      }
    }
  }

  for (unsigned idx = 0; idx < items_->count(); idx += 1) {
    PCase::Item *cur = (*items_)[idx];
    SecType *oldpc   = env.pc;
    bool need_hypo =
        env.dep_exprs.find(expr_->get_name()) != env.dep_exprs.end();
    env.pc = new JoinType(expr_->typecheck(printer, env), oldpc);
    env.pc = env.pc->simplify();

    Predicate oldh = pred;
    if (need_hypo) {
      if (cur->expr.count() != 0) {
        for (unsigned e = 0; e < cur->expr.count(); e += 1)
          pred.hypotheses.insert(new Hypothesis(expr_, cur->expr[e]));
      }
    }

    if (cur->stat) {
      cur->stat->typecheck(
          printer, env, pred /* add case condition to assumptions */, defAssgn);
    }

    pred   = oldh;
    env.pc = oldpc;
  }
}

/**
 * Type-check a branch.
 */
void PCondit::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                        set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PCondit::check "
         << "if (" << *expr_ << ")" << endl;

    cerr << "depvars currently in scope:" << endl;
    for (set<perm_string>::iterator depite = env.dep_exprs.begin();
         depite != env.dep_exprs.end(); depite++) {
      cerr << *depite << endl;
    }
  }

  SecType *oldpc             = env.pc;
  set<Hypothesis *> beforeif = pred.hypotheses;

  // generate fresh variables for that used in the current pc
  SecType *etype =
      expr_->typecheck(printer, env); //->freshVars(get_lineno(), subst);
  env.pc = new JoinType(etype, oldpc);
  env.pc = env.pc->simplify();

  if (if_) {
    absintp(pred, env, true, false);
    if_->typecheck(printer, env, pred, defAssgn);
  }

  Predicate afterif = pred;
  pred.hypotheses   = beforeif;

  if (else_) {
    absintp(pred, env, false, false);
    else_->typecheck(printer, env, pred, defAssgn);
  }
  Predicate afterelse = pred;
  // at the merge point, we assume no assumptions are valid anymore
  env.pc = oldpc;
  pred.hypotheses.clear();
  merge(afterif, afterelse, pred);
}

/**
 * Do nothing.
 */
void PCAssign::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PCAssign::check "
         << "assign " << *lval_ << " = " << *expr_ << endl;
  }
  throw "PCAssign";
}

/**
 * Do nothing.
 */
void PDeassign::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                          set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PDeassign::check " << *lval_ << "; " << endl;
  }
  throw "PDeassign";
}

/**
 * Do nothing.
 */
void PDelayStatement::typecheck(SexpPrinter &printer, TypeEnv &env,
                                Predicate &pred,
                                set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PDelayStatement::check "
         << "#" << *delay_;
    if (statement_) {
      cerr << endl;
    } else {
      cerr << " /* noop */;" << endl;
    }
  }
  throw "PDelay";
}

/**
 * Do nothing.
 */
void PDisable::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PDisable::check " << scope_ << ";" << endl;
  }
  throw "PDisable";
}

/**
 * Type-check an event.
 */
void PEventStatement::typecheck(SexpPrinter &printer, TypeEnv &env,
                                Predicate &pred,
                                set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    if (expr_.count() == 0) {
      cerr << "PEventStatement::check "
           << "@* ";
    } else {
      cerr << "PEventStatement::check "
           << "@(" << *(expr_[0]);
      if (expr_.count() > 1) {
        for (unsigned idx = 1; idx < expr_.count(); idx += 1) {
          cerr << " or " << *(expr_[idx]);
        }
      }
      cerr << ")";
    }

    if (statement_) {
      cerr << endl;
    } else {
      cerr << " ;" << endl;
    }
  }

  SecType *oldpc = env.pc;
  // taint pc by the label of trigger event
  if (expr_.count() != 0) {
    env.pc = new JoinType(env.pc, expr_[0]->expr()->typecheck(printer, env));
    for (unsigned idx = 1; idx < expr_.count(); idx += 1)
      env.pc =
          new JoinType(env.pc, expr_[idx]->expr()->typecheck(printer, env));
  }
  if (debug_typecheck) {
    cerr << "New PC is: " << *env.pc << endl;
  }
  statement_->typecheck(printer, env, pred, defAssgn);
  env.pc = oldpc;
}

/**
 * Do nothing.
 */
void PForce::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                       set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PForce::check " << *lval_ << " = " << *expr_ << ";" << endl;
  }
  throw "PForce";
}

/**
 * Do nothing.
 */
void PForever::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PForever::check " << endl;
  }
  throw "PForever";
}

Statement *PForStatement::next_cycle_transform(SexpPrinter &printer,
                                               TypeEnv &env) {
  // only transform body
  if (debug_typecheck) {
    cerr << "PForStatement::next_cycle_transform" << endl;
  }
  if (statement_) {
    statement_ = statement_->next_cycle_transform(printer, env);
  }
  return this;
}

void PForStatement::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  if (debug_typecheck) {
    cerr << "collect_index_exprs on for" << endl;
  }
  expr1_->collect_index_exprs(exprs, env);
  expr2_->collect_index_exprs(exprs, env);
  cond_->collect_index_exprs(exprs, env);
  statement_->collect_index_exprs(exprs, env);
}

bool PForStatement::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                           Predicate &pred) {
  if (debug_typecheck)
    cerr << "collect_dep_invariants on for" << endl;
  Predicate oldPred = pred;
  bool result       = false;
  absintp(pred, env);
  if (statement_) {
    result = statement_->collect_dep_invariants(printer, env, pred);
  }
  pred.hypotheses = oldPred.hypotheses;
  if (result) {
    cond_->collect_idens(env.dep_exprs);
  }
  return result;
}

void PForStatement::typecheck(SexpPrinter &printer, TypeEnv &env,
                              Predicate &pred,
                              set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PForStatement::check "
         << "for (" << *name1_ << " = " << *expr1_ << "; " << *cond_ << "; "
         << *name2_ << " = " << *expr2_ << ")" << endl;
  }
  Predicate precond = pred;
  stringstream note;
  note << *name1_ << " = " << *expr1_ << " @" << get_fileline();
  typecheck_assignment(printer, name1_, expr1_, env, precond, pred,
                       get_lineno(), note.str(), true, defAssgn);
  note.clear();

  note << *name2_ << " = " << *expr2_ << " @" << get_fileline();
  typecheck_assignment(printer, name2_, expr2_, env, precond, pred,
                       get_lineno(), note.str(), true, defAssgn);

  SecType *oldpc    = env.pc;
  SecType *condType = cond_->typecheck(printer, env);
  env.pc            = new JoinType(condType, oldpc);
  env.pc            = env.pc->simplify();

  statement_->typecheck(printer, env, pred, defAssgn);

  env.pc = oldpc;
}

/**
 * Type-check a generate statement.
 * Use a copy of env to avoid duplicated definitions.
 */
void PGenerate::typecheck(SexpPrinter &printer, TypeEnv env,
                          map<perm_string, Module *> modules) {
  if (debug_typecheck) {
    dump(cerr, 0);
  }

  typecheck_parameters_(printer, env);
  typecheck_localparams_(printer, env);
  if (defparms.size() > 0) {
    cerr << "PGenerate::defparms are ignored" << endl;
  }
  typecheck_events_(printer, env);
  // Iterate through and display all the wires (including registers).
  typecheck_wires_(printer, env);
  printer.lineBreak();
  printer.addComment("assertions to be verified");
  printer.lineBreak();

  if (debug_typecheck) {
    cerr << "Current PC is: " << *env.pc << endl;
  }

  for (list<PGate *>::const_iterator gate = gates.begin(); gate != gates.end();
       gate++) {
    PGAssign *pgassign = dynamic_cast<PGAssign *>(*gate);
    PGModule *pgmodule = dynamic_cast<PGModule *>(*gate);

    set<perm_string> defassgn;
    // make sure the parameters has same label as module declaration
    if (pgmodule != NULL) {
      pgmodule->typecheck(printer, env, modules);
    } else if (pgassign != NULL) {
      Predicate pred;
      pgassign->typecheck(printer, env, pred, defassgn);
    }
  }

  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    (*idx)->typecheck(printer, env, env.defAssigned[(*idx)]);
  }

  for (list<AProcess *>::const_iterator idx = analog_behaviors.begin();
       idx != analog_behaviors.end(); idx++) {
    throw "AProcess";
  }

  typedef map<perm_string, LineInfo *>::const_iterator genvar_iter_t;
  for (genvar_iter_t cur = genvars.begin(); cur != genvars.end(); cur++) {
    throw "genvars";
  }

  for (list<PGenerate *>::const_iterator idx = generate_schemes.begin();
       idx != generate_schemes.end(); idx++) {
    (*idx)->typecheck(printer, env, modules);
  }
}

void PGenerate::collectAssigned(TypeEnv &env) const {
  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    if (debug_typecheck) {
      cerr << "collectAssigned for behavior: " << (*idx) << endl;
    }
    set<perm_string> s;
    (*idx)->collectAssigned(s);
    env.defAssigned[(*idx)] = s;
  }
}

void PGenerate::collect_index_exprs(set<perm_string> &exprs, TypeEnv &env) {
  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    if (debug_typecheck) {
      cerr << "collect_index_exprs for behavior: " << (*idx) << endl;
    }
    (*idx)->collect_index_exprs(exprs, env);
  }
}

void PGenerate::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env) {
  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    if (debug_typecheck) {
      cerr << "collect_dep_invariants for behavior: " << (*idx) << endl;
    }
    Predicate emptyPred;
    (*idx)->collect_dep_invariants(printer, env, emptyPred);
    if (debug_typecheck) {
      cerr << "done collect_dep_invariants for behavior: " << (*idx) << endl;
    }
  }
}

/**
 * Do nothing.
 */
void PNoop::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                      set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "check PNoop " << endl;
  }
  throw "PNoop";
}

/**
 * Do nothing.
 */
void PRelease::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PRelease::check " << *lval_ << ";" << endl;
  }
  throw "PRelease";
}

/**
 * Do nothing.
 */
void PRepeat::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                        set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PRepeat::check (" << *expr_ << ")" << endl;
  }
  throw "PRepeat";
}

/**
 * Do nothing.
 */
void PTrigger::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                         set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PTrigger::check"
         << "-> " << event_ << ";" << endl;
  }
  throw "PTrigger";
}

/**
 * Do nothing.
 */
void PWhile::typecheck(SexpPrinter &printer, TypeEnv &env, Predicate &pred,
                       set<perm_string> &defAssgn) const {
  if (debug_typecheck) {
    cerr << "PWhile::check (" << *cond_ << ")" << endl;
  }
  throw "PWhile";
}

struct root_elem {
  Module *mod;
  NetScope *scope;
};

// TODO C++26 should introduce std::embed
const char *default_lattice =
#include "default_lattice.lat"
    ;

/**
 * SecVerilog by default declares a minimal lattice with only bottom and top:
 *                   HIGH
 *
 *                   LOW
 *
 * Programmers can define their own lattice structure in a Z3 file,
 * by using the [-l lattice_file] option to SecVerilog. This will not
 * overwrite the existing bottom and top, and can only specify other, new
 * elements.
 */
void output_lattice(SexpPrinter &out, char *lattice) {
  out.lineBreak();
  out.writeRawLine(default_lattice);

  // append the user-defined lattice
  if (lattice) {
    out.lineBreak();
    string line;
    ifstream infile(lattice);
    while (getline(infile, line)) {
      out.writeRawLine(line);
    }
  }
}

/**
 * SecVerilog by default declares a simple type-level function "LH",
 * which maps 0 to LOW and 1 to HIGH.
 *
 * Programmers can define their own function in a Z3 file,
 * using the [-F depfun_file] option to SecVerilog.
 */
void output_type_families(SexpPrinter &printer, char *depfun) {
  printer.lineBreak();
  printer.addComment("function that maps 0 to LOW; 1 to HIGH");
  printer.singleton("declare-fun LH (Int) Label");
  printer.singleton("assert (= (LH 0) LOW)");
  printer.singleton("assert (= (LH 1) HIGH)");

  // append the user-defined type-level functions
  if (depfun) {
    string line;
    ifstream infile(depfun);
    while (getline(infile, line)) {
      printer.writeRawLine(line);
    }
  }
}

/*
 * This function is the root of all type checking. The input is the list
 * of root module names. The function locates the Module definitions
 * for each root, does the type check.
 */
void typecheck(map<perm_string, Module *> modules, char *lattice_file_name,
               char *depfun_file_name) {
  // Scan the root modules by name, and output the name.
  for (map<perm_string, Module *>::const_iterator mod = modules.begin();
       mod != modules.end(); mod++) {

    // Get the module definition for this root instance.
    Module *rmod = (*mod).second;

    // Typing environment \G and assumptions \A for type
    // checking typing rules have the form \G, \A |- C, where
    // \G is a map from Verilog vars to security lables, and
    // \A is a conjunction of predicates on PWire
    map<perm_string, SecType *> *varsToType = new map<perm_string, SecType *>();
    map<perm_string, BaseType *> *varsToBase =
        new map<perm_string, BaseType *>();
    TypeEnv *env = new TypeEnv(*varsToType, *varsToBase, ConstType::BOT, rmod);

    ofstream z3file;
    string z3filename = string(rmod->file_name().str());
    size_t pos        = z3filename.find_first_of('.');
    if (pos != string::npos) {
      z3filename = z3filename.substr(0, pos);
    }
    z3file.open((z3filename + ".z3").c_str());
    SexpPrinter printer(z3file, 80);
    try {
      rmod->typecheck(printer, *env, modules, depfun_file_name,
                      lattice_file_name);
    } catch (char const *str) {
      cerr << "Unimplemented " << str << endl;
    } catch (Sexception &exn) {
      cerr << "Error with sexpifying: " << exn.what() << endl;
    }
    z3file.close();
  }
}
