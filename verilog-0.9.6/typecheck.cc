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
#include "ivl_assert.h"
#include "netlist.h"
#include "netmisc.h"
#include "parse_api.h"
#include "parse_misc.h"
#include "path_assign.h"
#include "pform.h"
#include "sexp_printer.h"
#include "util.h"
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <typeinfo>

#define ASSUME_NAME "assume"

void output_type_families(SexpPrinter &printer, char *depfun);

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
  typedef set<perm_string>::const_iterator seqvar_iter_t;
  for (seqvar_iter_t cur = env.seqVars.begin(); cur != env.seqVars.end();
       cur++) {
    behaviors.push_back(gen_assign_next_block(*cur));
  }
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

void PProcess::collect_index_exprs(set<perm_string> &exprs,
                                   map<perm_string, SecType *> &env) {
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

void Statement::collect_index_exprs(set<perm_string> &exprs,
                                    map<perm_string, SecType *> &env) {
  return;
}

Statement *PEventStatement::next_cycle_transform(SexpPrinter &printer,
                                                 TypeEnv &env) {
  statement_ = statement_->next_cycle_transform(printer, env);
  return this;
}

void PEventStatement::collect_index_exprs(set<perm_string> &exprs,
                                          map<perm_string, SecType *> &env) {
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
      cerr << "NextCycleTransform:: " << typeid(list_[i]).name() << endl;
    list_[i] = list_[i]->next_cycle_transform(printer, env);
  }
  return this;
}

void PBlock::collect_index_exprs(set<perm_string> &exprs,
                                 map<perm_string, SecType *> &env) {
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

void PCondit::collect_index_exprs(set<perm_string> &exprs,
                                  map<perm_string, SecType *> &env) {
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

void PCAssign::collect_index_exprs(set<perm_string> &exprs,
                                   map<perm_string, SecType *> &env) {
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
  assert(lval_);
  lval_ = lval_->next_cycle_transform(printer, env);
  return this;
}

void PAssign_::collect_index_exprs(set<perm_string> &exprs,
                                   map<perm_string, SecType *> &env) {
  if (debug_typecheck) {
    cerr << "collect_index_exprs on passign" << endl;
    cerr << "on " << *rval() << " gets " << *lval() << endl;
  }
  rval()->collect_index_exprs(exprs, env);
  lval()->collect_index_exprs(exprs, env);
}

bool PAssign_::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env,
                                      Predicate &pred) {
  if (debug_typecheck)
    cerr << "collect_dep_invariants on passign" << endl;
  PEIdent *rident   = dynamic_cast<PEIdent *>(rval());
  bool isNextAssign = false;
  if (rident != NULL) {
    BaseType *rtyp = rident->check_base_type(printer, env.varsToBase);
    if (rtyp) {
      isNextAssign = rtyp->isNextType();
    }
  }
  // make sure basetype is appropriate
  lval()->check_base_type(printer, env.varsToBase);
  // if lhs appears in dependent type, and  this is not the generated assignment
  // (x = x_next_)
  if ((env.dep_exprs.find(lval()->get_name()) != env.dep_exprs.end()) &&
      !isNextAssign) {
    bool hasPreds = !pred.hypotheses.empty();
    printer.startList("assert");
    if (hasPreds) {
      printer.startList("=>");
      printer << pred;
    }
    printer.startList("=");
    lval()->dumpz3(printer);
    rval()->dumpz3(printer);
    printer.endList();
    if (hasPreds) {
      printer.endList();
    }
    printer.endList();
    // also collect rhs variables in the dep_exprs to define them in z3 file
    rval()->collect_idens(env.dep_exprs);
    return true;
  } else {
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
      cout << "Nextify " << path() << " to " << newPath << endl;
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
    cout << "Nextify " << path() << " to " << newPath << endl;
  }
  return new PEIdent(newPath);
}

void PGenerate::next_cycle_transform(SexpPrinter &printer, TypeEnv env) {
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    if (debug_typecheck)
      cerr << "NextCycleTransform:: " << typeid(*behav).name() << endl;
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
    cout << "PWire::check " << type_;

    switch (port_type_) {
    case NetNet::PIMPLICIT:
      cout << " implicit input";
      break;
    case NetNet::PINPUT:
      cout << " input";
      break;
    case NetNet::POUTPUT:
      cout << " output";
      break;
    case NetNet::PINOUT:
      cout << " inout";
      break;
    case NetNet::NOT_A_PORT:
      break;
    }

    cout << " " << data_type_;

    if (signed_) {
      cout << " signed";
    }

    if (discipline_) {
      cout << " discipline<" << discipline_->name() << ">";
    }

    if (port_set_) {
      if (port_msb_ == 0) {
        cout << " port<scalar>";
      } else {
        cout << " port[" << *port_msb_ << ":" << *port_lsb_ << "]";
      }
    }
    if (net_set_) {
      if (net_msb_ == 0) {
        cout << " net<scalar>";
      } else {
        cout << " net[" << *net_msb_ << ":" << *net_lsb_ << "]";
      }
    }

    cout << " " << name_;

    // If the wire has indices, dump them.
    if (lidx_ || ridx_) {
      cout << "[";
      if (lidx_)
        cout << *lidx_;
      if (ridx_)
        cout << ":" << *ridx_;
      cout << "]";
    }

    cout << ";" << endl;
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
  for (std::set<perm_string>::iterator ite = exprs.begin(); ite != exprs.end();
       ite++) {
    perm_string temp                              = *ite;
    map<perm_string, PWire *>::const_iterator cur = wires.find(temp);
    if (cur != wires.end()) {
      PWire *def = (*cur).second;
      // assume wires are either arrays or ints
      if (def->get_isarray()) {
        printer.startList("declare-fun");
        printer << ite->str() << "()";
        printer.startList("Array");
        printer << "Int"
                << "Int";
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
        printer << "0";
        printer.startList("select");
        printer << ite->str() << "x";
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
        printer << ite->str() << "x";
        printer.endList();
        printer << std::to_string((1 << (def->getRange() + 1)) - 1);
        printer.endList();
        printer.endList();
        printer.endList();
      } else {
        printer.startList("declare-fun");
        printer << ite->str() << "()"
                << "Int";
        printer.endList();

        printer.startList("assert");
        printer.startList("<=");
        printer << "0" << ite->str();
        printer.endList();
        printer.endList();

        printer.startList("assert");
        printer.startList("<=");
        printer << ite->str()
                << std::to_string((1 << (def->getRange() + 1)) - 1);
        printer.endList();
        printer.endList();
      }
    } else {
      // in this case, its probably a genvar, just declare it as an unbound int
      if (debug_typecheck) {
        cout << "couldn't find wire for " << temp << endl;
      }
      printer.startList("declare-fun");
      printer << temp.str() << "()"
              << "Int";
      printer.endList();
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
    (*behav)->collect_index_exprs(exprs, env.varsToType);
  }
  for (list<PGenerate *>::const_iterator cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->collect_index_exprs(exprs, env.varsToType);
  }

  for (list<PGate *>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign *pgassign = dynamic_cast<PGAssign *>(*gate);
    PGModule *pgmodule = dynamic_cast<PGModule *>(*gate);
    if (pgassign != NULL) {
      pgassign->collect_index_exprs(exprs, env.varsToType);
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
 * Only generate if expr is in a dependent label but skip the automatic
 * next_cycle_transform assignment
 * Returns true if any invariants were generated
 */
bool Module::CollectDepInvariants(SexpPrinter &printer, TypeEnv &env) const {
  printer.addComment("invariants about dependent variables");
  set<perm_string> oldDeps = env.dep_exprs;
  // collect invariants and print them after definining new variables
  stringstream invs;
  SexpPrinter tmp_printer(invs, printer.margin);
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    Predicate emptyPred;
    (*behav)->collect_dep_invariants(tmp_printer, env, emptyPred);
  }
  for (list<PGate *>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign *pgassign = dynamic_cast<PGAssign *>(*gate);
    if (pgassign != NULL) {
      pgassign->collect_dep_invariants(tmp_printer, env);
    }
  }

  set<perm_string> newDeps;
  std::set_difference(env.dep_exprs.begin(), env.dep_exprs.end(),
                      oldDeps.begin(), oldDeps.end(),
                      std::inserter(newDeps, newDeps.end()));
  dumpExprDefs(printer, newDeps);
  auto outStr = invs.str();
  printer.writeRawLine(outStr);
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

/**
 * Type-check a module.
 */
void Module::typecheck(SexpPrinter &printer, TypeEnv &env,
                       map<perm_string, Module *> modules, char *depfun) {

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
    cerr << "outputting type families" << endl;
  output_type_families(printer, depfun);
  if (debug_typecheck)
    cerr << "generating input invariant assumptions" << endl;
  makeAssumptions(this, printer, env);
  if (debug_typecheck)
    cerr << "collecting dependent invariants" << endl;
  bool foundInvs = CollectDepInvariants(printer, env);

  dump_no_overlap_anal(printer, analysis, env.dep_exprs);

  // TODO probably delete this
  //  remove an invariant if some variable does not show up
  if (debug_typecheck)
    cerr << "optimizing invariants" << endl;
  for (set<Equality *>::iterator invite = env.invariants->invariants.begin();
       invite != env.invariants->invariants.end();) {
    set<perm_string> vars, diff;
    (*invite)->left->collect_dep_expr(vars);
    (*invite)->right->collect_dep_expr(vars);

    set<Equality *>::iterator current = invite++;

    // if the invariant has free variables, then remove it
    for (set<perm_string>::iterator varite = vars.begin(); varite != vars.end();
         varite++) {
      if (env.dep_exprs.find(*varite) == env.dep_exprs.end()) {
        env.invariants->invariants.erase(current);
        break;
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

  printer.addComment("assertions to be verified");
  if (debug_typecheck)
    cerr << "checking generates" << endl;
  typedef list<PGenerate *>::const_iterator genscheme_iter_t;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->typecheck(printer, env, modules);
  }

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
      pgassign->typecheck(printer, env, pred);
    }
  }

  // The code above should collect a typing environment for all variables.
  // The following code performs intra-process type checking.
  if (debug_typecheck)
    cerr << "checking processes" << endl;
  for (list<PProcess *>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    (*behav)->typecheck(printer, env);
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
void PProcess::typecheck(SexpPrinter &printer, TypeEnv &env) const {
  if (debug_typecheck) {
    cout << "PProcess:check "
         << " /* " << get_fileline() << " */" << endl;
  }

  // initial is not synthesizable, just ignore them
  if (type_ != IVL_PR_INITIAL) {
    Predicate emptypred;
    if (debug_typecheck) {
      cerr << "pprocess checking statement of type ";
      cerr << typeid(*statement_).name() << endl;
    }
    statement_->typecheck(printer, env, emptypred);
  }
}

/**
 * Do nothing.
 */
void AContrib::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate &pred) const {
  if (debug_typecheck) {
    cout << "AContrib::check ";
    cout << *lval_ << " <+ " << *rval_ << endl;
  }
  throw "AContrib";
}

/**
 * Generate constraints for an assignment
 * lhs <= rhs
 *
 * pred: A predication on hardware state that holds when the assignment occurs.
 *       For example, (x==1).
 * note: The line of code in the source file. This information is used to trace
 *       a security violation back to SecVerilog source code.
 * details. env: A typing environment.
 */
void typecheck_assignment_constraint(SexpPrinter &printer, SecType *lhs,
                                     SecType *rhs, Predicate pred, string note,
                                     PEIdent *checkDefAssign, TypeEnv *env) {
  printer.lineBreak();
  printer.singleton("push");
  if (checkDefAssign) {
    printer.startList("assert");
    printer.startList("not");
    dump_is_def_assign(printer, env->analysis, checkDefAssign);
    printer.endList();
    printer.endList();
  }
  Constraint *c = new Constraint(lhs, rhs, env->invariants, &pred);
  printer << *c;
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
                          TypeEnv *env, Predicate precond, Predicate postcond,
                          unsigned int lineno, string note) {
  // when the RHS is a PETernary expression, i.e. e1?e2:e3, we first translate
  // to the equivalent statements
  PETernary *ternary = dynamic_cast<PETernary *>(rhs);
  if (ternary == NULL) {
    SecType *ltype, *rtype, *ltype_orig;
    BaseType *lbase;
    PEIdent *lident = dynamic_cast<PEIdent *>(lhs);
    if (lident != NULL) {
      // if lhs is v[x], only want to put type(v) in the type
      ltype_orig = lident->typecheckName(printer, env->varsToType);
    } else {
      ltype_orig = lhs->typecheck(printer, env->varsToType);
    }
    lbase = lhs->check_base_type(printer, env->varsToBase);
    // If ltype is sequential, substitute its free variables with the
    // next-cycle version of that variable.
    if (lbase->isNextType()) {
      ltype = ltype_orig->next_cycle(env);
    } else {
      ltype = ltype_orig;
    }
    rtype = new JoinType(rhs->typecheck(printer, env->varsToType), env->pc);
    if (lident != NULL) {
      // if lhs is v[x], want to include type(x) in the rhs type
      rtype =
          new JoinType(rtype, lident->typecheckIdx(printer, env->varsToType));
    }
    if (lbase->isSeqType()) {
      // Sequential logic is actually checked by the next cycle logic
      // generated by the next cycle transformation. This must be the
      // trusted, compiler-generated assignment
      rtype = ConstType::BOT;
    }
    if (debug_typecheck) {
      cerr << "line no" << lineno << endl;
      cerr << "pctype: " << *env->pc << endl;
      cerr << "ltype: " << *ltype << endl;
      cerr << "rtype: " << *rtype << endl;
      cerr << "lbase: " << lbase->name() << endl;
      cerr << "lhs: " << *lhs << endl;
      cerr << "rhs: " << *rhs << endl;
      cerr << "precond: " << precond << endl;
      cerr << "postcond: " << postcond << endl;
    }

    typecheck_assignment_constraint(printer, ltype, rtype, precond, note, NULL,
                                    env);
    // need no-sensitive-upgrade check when:
    //   - lident has a recursive dep type
    //   - lident is not definitely assigned
    //   - lident is a NEXT type (i.e., it's a register assignment)
    if (ltype_orig->isDepType() && lbase->isNextType()) {
      PEIdent *origName = lident->get_this_cycle_name();
      // is recursive if ltype contains lident
      if (ltype_orig->hasExpr(origName->get_name())) {
        // either  isDefAssigned(lident) OR forall contexts. (leq pc ltype_orig)
        //  rtype also flows to cur cycle label of lident in any context
        string newNote = note.append("--No-sensitive-upgrade-check;");
        Predicate emptyPred;
        typecheck_assignment_constraint(printer, ltype_orig, env->pc, emptyPred,
                                        newNote, origName, env);
      }
    }
  } else {
    ternary->translate(lhs)->typecheck(printer, *env, precond);
  }
}

void PGAssign::collect_index_exprs(set<perm_string> &exprs,
                                   map<perm_string, SecType *> &env) {
  pin(0)->collect_index_exprs(exprs, env);
  pin(1)->collect_index_exprs(exprs, env);
}

bool PGAssign::collect_dep_invariants(SexpPrinter &printer, TypeEnv &env) {
  if (debug_typecheck)
    cerr << "collect_dep_invariants on pgassign" << endl;
  PExpr *l      = pin(0);
  PEIdent *lval = dynamic_cast<PEIdent *>(l);
  PExpr *rval   = pin(1);
  if (!lval) {
    cerr << "Skipping assign to non identifier in gate when collecting dep "
            "invariants"
         << endl;
    return false;
  }
  if (env.dep_exprs.find(lval->get_name()) != env.dep_exprs.end()) {
    printer.startList("assert");
    printer.startList("=");
    lval->dumpz3(printer);
    rval->dumpz3(printer);
    printer.endList();
    printer.endList();
    // also collect rhs variables in the dep_exprs to define them in z3 file
    rval->collect_idens(env.dep_exprs);
    return true;
  } else {
    return false;
  }
}

/**
 * Type-check a blocking assignment.
 */
void PGAssign::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate pred) const {
  if (debug_typecheck) {
    cout << "assign " << *pin(0) << " = " << *pin(1) << ";" << endl;
  }

  stringstream ss;
  ss << "assign " << *pin(0) << " = " << *pin(1) << " @" << get_fileline();
  Predicate post;
  typecheck_assignment(printer, pin(0), pin(1), &env, pred, post, get_lineno(),
                       ss.str());
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
    cout << "pc context for module instantiation?" << endl;

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
          // the direction (input, output) determines def or use should be more
          // restrictive: def <= use for outputs use <= def for inputs
          PWire *port               = (*ite).second;
          NetNet::PortType porttype = port->get_port_type();

          SecType *paramType = param->typecheck(printer, env.varsToType);
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
            Constraint *c = new Constraint(lhs, rhs, env.invariants, &pred);
            printer << *c;
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
            Constraint *c = new Constraint(lhs, rhs, env.invariants, &pred);
            printer << *c;
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
void PAssign::typecheck(SexpPrinter &printer, TypeEnv &env,
                        Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PAssign::check " << *lval() << " = ";
    if (delay_)
      cout << "#" << *delay_ << " ";
    if (count_)
      cout << "repeat(" << *count_ << ") ";
    if (event_)
      cout << *event_ << " ";
    cout << *rval() << ";" << endl;
  }

  stringstream ss;
  ss << *lval() << " = " << *rval() << " @" << get_fileline();

  Predicate precond = pred;
  absintp(pred, env);
  typecheck_assignment(printer, lval_, rval_, &env, precond, pred, get_lineno(),
                       ss.str());
}

/**
 * Type-check a nonblocking assignment.
 */
void PAssignNB::typecheck(SexpPrinter &printer, TypeEnv &env,
                          Predicate &pred) const {
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

  stringstream ss;
  ss << *lval() << " <= " << *rval() << " @" << get_fileline();

  Predicate precond = pred;
  absintp(pred, env);
  typecheck_assignment(printer, lval_, rval_, &env, precond, pred, get_lineno(),
                       ss.str());
}

/**
 * Type-check a block of code.
 */
void PBlock::typecheck(SexpPrinter &printer, TypeEnv &env,
                       Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PBlock::check "
         << "begin";
    if (pscope_name() != 0)
      cout << " : " << pscope_name();
    cout << endl;
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
      list_[idx]->typecheck(printer, env, pred);
  }
}

/**
 * Do nothing.
 */
void PCallTask::typecheck(SexpPrinter &printer, TypeEnv &env,
                          Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PCallTask::check " << path_;

    if (parms_.count() > 0) {
      cout << "(";
      if (parms_[0])
        cout << *parms_[0];

      for (unsigned idx = 1; idx < parms_.count(); idx += 1) {
        cout << ", ";
        if (parms_[idx])
          cout << *parms_[idx];
      }
      cout << ")";
    }
    cout << endl;
  }
  // throw "PCallTask";
  cout << "PCallTask is ignored" << endl;
}

/**
 * Type-check a case statement.
 */
void PCase::typecheck(SexpPrinter &printer, TypeEnv &env,
                      Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PCase::check ";

    cout << " (" << *expr_ << ") " << endl;

    for (unsigned idx = 0; idx < items_->count(); idx += 1) {
      PCase::Item *cur = (*items_)[idx];

      if (cur->expr.count() != 0) {
        cout << "case item " << *cur->expr[0];

        for (unsigned e = 1; e < cur->expr.count(); e += 1)
          cout << ", " << *cur->expr[e];

        cout << ":";
      }
    }
  }

  for (unsigned idx = 0; idx < items_->count(); idx += 1) {
    PCase::Item *cur = (*items_)[idx];
    SecType *oldpc   = env.pc;
    bool need_hypo =
        env.dep_exprs.find(expr_->get_name()) != env.dep_exprs.end();
    env.pc = new JoinType(expr_->typecheck(printer, env.varsToType), oldpc);
    env.pc = env.pc->simplify();

    Predicate oldh = pred;
    if (need_hypo) {
      if (cur->expr.count() != 0) {
        for (unsigned e = 0; e < cur->expr.count(); e += 1)
          pred.hypotheses.insert(new Hypothesis(expr_, cur->expr[e]));
      }
    }

    if (cur->stat) {
      cur->stat->typecheck(printer, env,
                           pred /* add case condition to assumptions */);
    }

    pred   = oldh;
    env.pc = oldpc;
  }
}

/**
 * Type-check a branch.
 */
void PCondit::typecheck(SexpPrinter &printer, TypeEnv &env,
                        Predicate &pred) const {
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
  SecType *etype = expr_->typecheck(
      printer, env.varsToType); //->freshVars(get_lineno(), subst);
  env.pc = new JoinType(etype, oldpc);
  env.pc = env.pc->simplify();

  if (if_) {
    absintp(pred, env, true, false);
    if_->typecheck(printer, env, pred);
  }

  Predicate afterif = pred;
  pred.hypotheses   = beforeif;

  if (else_) {
    absintp(pred, env, false, false);
    else_->typecheck(printer, env, pred);
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
void PCAssign::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PCAssign::check "
         << "assign " << *lval_ << " = " << *expr_ << endl;
  }
  throw "PCAssign";
}

/**
 * Do nothing.
 */
void PDeassign::typecheck(SexpPrinter &printer, TypeEnv &env,
                          Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PDeassign::check " << *lval_ << "; " << endl;
  }
  throw "PDeassign";
}

/**
 * Do nothing.
 */
void PDelayStatement::typecheck(SexpPrinter &printer, TypeEnv &env,
                                Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PDelayStatement::check "
         << "#" << *delay_;
    if (statement_) {
      cout << endl;
    } else {
      cout << " /* noop */;" << endl;
    }
  }
  throw "PDelay";
}

/**
 * Do nothing.
 */
void PDisable::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PDisable::check " << scope_ << ";" << endl;
  }
  throw "PDisable";
}

/**
 * Type-check an event.
 */
void PEventStatement::typecheck(SexpPrinter &printer, TypeEnv &env,
                                Predicate &pred) const {
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
    env.pc = new JoinType(env.pc,
                          expr_[0]->expr()->typecheck(printer, env.varsToType));
    for (unsigned idx = 1; idx < expr_.count(); idx += 1)
      env.pc = new JoinType(
          env.pc, expr_[idx]->expr()->typecheck(printer, env.varsToType));
  }
  if (debug_typecheck) {
    cerr << "New PC is: " << *env.pc << endl;
  }
  statement_->typecheck(printer, env, pred);
  env.pc = oldpc;
}

/**
 * Do nothing.
 */
void PForce::typecheck(SexpPrinter &printer, TypeEnv &env,
                       Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PForce::check " << *lval_ << " = " << *expr_ << ";" << endl;
  }
  throw "PForce";
}

/**
 * Do nothing.
 */
void PForever::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PForever::check " << endl;
  }
  throw "PForever";
}

/**
 * Do nothing.
 */
void PForStatement::typecheck(SexpPrinter &printer, TypeEnv &env,
                              Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PForStatement::check "
         << "for (" << *name1_ << " = " << *expr1_ << "; " << *cond_ << "; "
         << *name2_ << " = " << *expr2_ << ")" << endl;
  }
  throw "PForStatement";
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

    // make sure the parameters has same label as module declaration
    if (pgmodule != NULL) {
      pgmodule->typecheck(printer, env, modules);
    } else if (pgassign != NULL) {
      Predicate pred;
      pgassign->typecheck(printer, env, pred);
    }
  }

  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    (*idx)->typecheck(printer, env);
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

void PGenerate::collect_index_exprs(set<perm_string> &exprs,
                                    map<perm_string, SecType *> &env) {
  for (list<PProcess *>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    if (debug_typecheck) {
      cout << "collect_index_exprs for behavior: " << (*idx) << endl;
    }
    (*idx)->collect_index_exprs(exprs, env);
  }
}

/**
 * Do nothing.
 */
void PNoop::typecheck(SexpPrinter &printer, TypeEnv &env,
                      Predicate &pred) const {
  if (debug_typecheck) {
    cout << "check PNoop " << endl;
  }
  throw "PNoop";
}

/**
 * Do nothing.
 */
void PRelease::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PRelease::check " << *lval_ << ";" << endl;
  }
  throw "PRelease";
}

/**
 * Do nothing.
 */
void PRepeat::typecheck(SexpPrinter &printer, TypeEnv &env,
                        Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PRepeat::check (" << *expr_ << ")" << endl;
  }
  throw "PRepeat";
}

/**
 * Do nothing.
 */
void PTrigger::typecheck(SexpPrinter &printer, TypeEnv &env,
                         Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PTrigger::check"
         << "-> " << event_ << ";" << endl;
  }
  throw "PTrigger";
}

/**
 * Do nothing.
 */
void PWhile::typecheck(SexpPrinter &printer, TypeEnv &env,
                       Predicate &pred) const {
  if (debug_typecheck) {
    cout << "PWhile::check (" << *cond_ << ")" << endl;
  }
  throw "PWhile";
}

struct root_elem {
  Module *mod;
  NetScope *scope;
};

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
void output_lattice(ostream &out, char *lattice) {
  out << "; this part encodes a partial order on labels" << endl;
  out << "(declare-sort Label)" << endl;
  out << "(declare-fun leq (Label Label) Bool)" << endl;
  out << "(declare-fun join (Label Label) Label)" << endl;
  out << "(declare-fun meet (Label Label) Label)" << endl;

  out << "(assert (forall ((x Label)) (leq x x)))" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x "
         "y) (leq y z)) (leq x z))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label)) (implies (and (leq x y) (leq y "
         "x)) (= x y))))"
      << endl;

  out << endl << "; axioms for join" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (leq (join "
         "x y) z) (and (leq x z) (leq y z)))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x "
         "z) (leq y z)) (leq (join x y) z))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label)) (and (leq x (join x y)) (leq y "
         "(join x y)))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label)) (= (join x y) (join y x))))"
      << endl;

  out << endl << "; axioms for meet" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (leq x "
         "(meet y z)) (and (leq x y) (leq x z)))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x "
         "y) (leq x z)) (leq x (meet y z)))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label)) (and (leq (meet x y) x) (leq "
         "(meet x y) y))))"
      << endl;
  out << "(assert (forall ((x Label) (y Label)) (= (meet x y) (meet y x))))"
      << endl;

  out << endl << "; lattice elements" << endl;
  out << "(declare-fun LOW () Label)" << endl;
  out << "(declare-fun HIGH () Label)" << endl;

  out << endl << "; lattice structure" << endl;
  out << "(assert (forall ((x Label)) (leq LOW x)))" << endl;
  out << "(assert (forall ((x Label)) (leq x HIGH)))" << endl;
  out << "(assert (not (= HIGH LOW))) ; the lattice cannot clapse" << endl;

  // append the user-defined lattice
  if (lattice) {
    out << endl;
    string line;
    ifstream infile(lattice);
    while (getline(infile, line)) {
      out << line << endl;
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
    output_lattice(z3file, lattice_file_name);
    SexpPrinter printer(z3file, 80);
    try {
      rmod->typecheck(printer, *env, modules, depfun_file_name);
    } catch (char const *str) {
      cerr << "Unimplemented " << str << endl;
    } catch (Sexception &exn) {
      cerr << "Error with sexpifying: " << exn.what() << endl;
    }
    z3file.close();
  }
}
