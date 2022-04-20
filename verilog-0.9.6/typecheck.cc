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

# include "config.h"

/*
 * Type-checking takes a list of modules, and generates a Z3 file to be solved by Z3.
 */

# include  <typeinfo>
# include  <cstdlib>
# include  <sstream>
# include  <fstream>
# include  <algorithm>
# include  "pform.h"
# include  "PEvent.h"
# include  "PGenerate.h"
# include  "PGate.h"
# include  "PSpec.h"
# include  "netlist.h"
# include  "netmisc.h"
# include  "util.h"
# include  "parse_api.h"
# include  "compiler.h"
# include  "ivl_assert.h"
# include  "parse_misc.h"

void output_type_families(ostream& out, char* depfun);
extern bool check_write;

/**
 * Type-check parameters, which are constants.
 */
void LexicalScope::typecheck_parameters_(ostream&out, TypeEnv& env) const {
  typedef map<perm_string, param_expr_t>::const_iterator parm_iter_t;
  if (debug_typecheck) {
    for (parm_iter_t cur = parameters.begin();
	 cur != parameters.end();
	 cur++) {
      cout << "check parameter " << (*cur).first << " " << (*cur).second.type << endl;
    }
  }
  // parameters can only be assigned to constants. So the label must be LOW
  for (parm_iter_t cur = parameters.begin(); cur != parameters.end(); cur++) {
    env.varsToType[(*cur).first] = ConstType::BOT;
    if (debug_typecheck) {
      cerr << " param " << (*cur).first << " has type ";
      cerr << env.varsToType[(*cur).first] << endl ;
    }
  }
}

/**
 * These are constants. Set them to the bottom type.
 */
void LexicalScope::typecheck_localparams_(ostream&out, TypeEnv& env) const {
  typedef map<perm_string, param_expr_t>::const_iterator parm_iter_t;
  if (debug_typecheck) {

    if(dynamic_cast<const PScope*>(this)) {
      const PScope* ps = dynamic_cast<const PScope*>(this);
      fprintf(stderr, "typecheck_localparams for %s\n", ps->pscope_name().str());
    } else {
      fprintf(stderr, "checking localparams for a non-pscope lexscope\n");
    }

    for (parm_iter_t cur = localparams.begin();
	 cur != localparams.end();
	 cur++) {
      out << "check localparam ";
      if ((*cur).second.msb)
	out << "[" << *(*cur).second.msb << ":" << *(*cur).second.lsb
	    << "] ";
      out << (*cur).first << " = ";
      if ((*cur).second.expr)
	out << *(*cur).second.expr << ";" << endl;
      else
	out << "/* ERROR */;" << endl;
    }
  }
  for (parm_iter_t cur = localparams.begin();
       cur != localparams.end(); cur++) {
    env.varsToType[(*cur).first] = ConstType::BOT;
    if (debug_typecheck) {
      cerr << " localparam " << (*cur).first << " has type ";
      cerr << *env.varsToType[(*cur).first] << endl ;
    }
  }
}

//-----------------------------------------------------------------------------
// Next Cycle Transformation
//-----------------------------------------------------------------------------

void Module::next_cycle_transform(ostream&out, TypeEnv&env) {
  // This transformation moves all assignments to sequential logic into 
  // assignments to next-cycle objects.
  for (list<PProcess*>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    if(debug_typecheck) 
      fprintf(stderr, "NextCycleTransform:: %s\n", typeid(*behav).name());
    (*behav)->next_cycle_transform(out, env);
  }
  typedef set<perm_string>::const_iterator seqvar_iter_t;
  for (seqvar_iter_t cur = env.seqVars.begin();
       cur != env.seqVars.end(); cur++) {
    behaviors.push_back(gen_assign_next_block(*cur));
  }
  // transform the code in the generate blocks too
  typedef list<PGenerate*>::const_iterator genscheme_iter_t;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->next_cycle_transform(out, env);
  }

}

PProcess* Module::gen_assign_next_block(perm_string id){
  //make the assignment in an always@(*) block
  PEventStatement* event_expr = new PEventStatement();
  PEIdent*nexted_id = new PEIdent(nextify_perm_string(id));
  PEIdent*unnexted_id = new PEIdent(id);
  PAssign*asgn = new PAssign(unnexted_id, nexted_id);

  event_expr->set_statement(asgn);

  PProcess*ret = new PProcess(IVL_PR_ALWAYS, event_expr);
  return ret;
}

void PProcess::next_cycle_transform(ostream&out, TypeEnv&env) const {
  if(statement_ == NULL) return;
  if(debug_typecheck) 
    fprintf(stderr, "NextCycleTransform:: %s\n", typeid(*statement_).name());
  statement_->next_cycle_transform(out, env);
}

bool PProcess::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  if(statement_ == NULL) return false;
  if(debug_typecheck) 
    fprintf(stderr, "collect_dep_invariants:: %s\n", typeid(*statement_).name());
  return statement_->collect_dep_invariants(out, env, pred);
}

void PProcess::collect_index_exprs(set<perm_string>&exprs, map<perm_string, SecType*>&env) {
  if(statement_ == NULL) return;
  if(debug_typecheck) 
    fprintf(stderr, "collect_index_exprs:: %s\n", typeid(*statement_).name());
  statement_->collect_index_exprs(exprs, env);
}

Statement* Statement::next_cycle_transform(ostream&out, TypeEnv&env) {
  return this;
}

bool Statement::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  return false;
}

void Statement::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  return;
}

Statement* PEventStatement::next_cycle_transform(ostream&out, TypeEnv&env) {
  statement_ = statement_->next_cycle_transform(out,env);
  return this;
}

void PEventStatement::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  if (debug_typecheck) fprintf(stderr, "collect_index_exprs:: %s\n", typeid(*statement_).name());  
  statement_->collect_index_exprs(exprs, env);
}

bool PEventStatement::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  if (debug_typecheck) fprintf(stderr, "collect_dep_invariants:: %s\n", typeid(*statement_).name());
  return statement_->collect_dep_invariants(out,env, pred);
}

Statement* PBlock::next_cycle_transform(ostream&out, TypeEnv&env) {
  for(uint i=0; i<list_.count(); i++) {
    if(debug_typecheck) 
      fprintf(stderr, "NextCycleTransform:: %s\n", typeid(list_[i]).name());
    list_[i]=list_[i]->next_cycle_transform(out, env);
  }
  return this;
}

void PBlock::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  for(uint i=0; i<list_.count(); i++) {
    if(debug_typecheck) 
      fprintf(stderr, "collect_index_exprs:: %s\n", typeid(list_[i]).name());
    list_[i]->collect_index_exprs(exprs, env);
  }
}

bool PBlock::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  bool result = false;
  for(uint i=0; i<list_.count(); i++) {
    if(debug_typecheck) 
      fprintf(stderr, "collect_dep_invariants:: %s\n", typeid(list_[i]).name());
    result |= list_[i]->collect_dep_invariants(out, env, pred);
  }
  return result;
}

Statement* PCondit::next_cycle_transform(ostream&out, TypeEnv&env) {
  if(if_ != NULL)
    if_   = if_->next_cycle_transform(out, env);
  if(else_ != NULL)
    else_ = else_->next_cycle_transform(out, env);
  return this;
}

void PCondit::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  if (debug_typecheck) fprintf(stderr, "collect_index_exprs on if\n");
  if (if_ != NULL) {
    if_->collect_index_exprs(exprs, env);
  }
  if(else_ != NULL) {
    else_->collect_index_exprs(exprs, env);
  }
  expr_->collect_index_exprs(exprs, env);
}

bool PCondit::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  if (debug_typecheck) fprintf(stderr, "collect_dep_invariants on if\n");
  Predicate oldPred = pred;
  bool result = false;
  if (if_ != NULL) {
    absintp(pred, env, true, true);
    result |= if_->collect_dep_invariants(out, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
  if(else_ != NULL) {
    absintp(pred, env, false, true);
    result |= else_->collect_dep_invariants(out, env, pred);
    pred.hypotheses = oldPred.hypotheses;
  }
  if(result) {
    expr_->collect_idens(env.dep_exprs);
  }
  return result;
}

void PCAssign::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  if (debug_typecheck) fprintf(stderr, "skipping collect_index_exprs on pcassign\n");  
}

bool PCAssign::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  if (debug_typecheck) fprintf(stderr, "skipping collect_dep_invariants on pcassign\n");
  return false;
}

// This is the only rule where something actually happens. Only the left 
// hand-side of the assignment is transformed.
Statement* PAssignNB::next_cycle_transform(ostream&out, TypeEnv&env) {
  assert(lval_);
  lval_ = lval_->next_cycle_transform(out, env);
  return this;
}

void PAssign_::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  if (debug_typecheck) fprintf(stderr, "collect_index_exprs on passign\n");
  rval()->collect_index_exprs(exprs, env);
  lval()->collect_index_exprs(exprs, env);
}

bool PAssign_::collect_dep_invariants(ostream&out, TypeEnv&env, Predicate&pred) {
  if (debug_typecheck) fprintf(stderr, "collect_dep_invariants on passign\n");  
  PEIdent* rident = dynamic_cast<PEIdent*>(rval());
  bool isNextAssign = false;
  if (rident != NULL) {
    BaseType *rtyp = rident->check_base_type(out, env.varsToBase);
    if (rtyp) {
      isNextAssign = rtyp->isNextType();
    }
  }
  BaseType *ltyp = lval()->check_base_type(out, env.varsToBase);
  bool isLeftSeq = ltyp->isNextType() || ltyp->isSeqType();
  //if lhs appears in dependent type, and is a seq or next type and this is not the generated assignment (x = x_next_)
  if ((env.dep_exprs.find(lval()->get_name()) != env.dep_exprs.end()) &&
      isLeftSeq && !isNextAssign) {
    
    bool hasPreds = !pred.hypotheses.empty();
    out << "(assert ";
    if (hasPreds) {
      out << "(=> " << pred << " ";
    }
    out << "(= ";
    lval()->dumpz3(out);
    out << " ";
    rval()->dumpz3(out);
    out << ")";
    if (hasPreds) {
      out << ")";
    }
    out << ")" << endl;
    //also collect rhs variables in the dep_exprs to define them in z3 file
    rval()->collect_idens(env.dep_exprs);
    return true;
  } else {
    return false;
  }
}


Statement* PCAssign::next_cycle_transform(ostream&out, TypeEnv&env) {
  lval_ = lval_->next_cycle_transform(out, env);
  return this;
}

PExpr* PExpr::next_cycle_transform(ostream&out, TypeEnv&env) { return this; }

PExpr* PEIdent::next_cycle_transform(ostream&out, TypeEnv&env) {
  
  BaseType*bt = check_base_type(out,env.varsToBase);
  assert(bt);
  // if bt is seqtype, make it into next cycle version
  if(bt == NULL) {
    fprintf(stderr, "WARN: null basetype: %s",
	    peek_tail_name(path()).str());
    return this;
  }
  if(bt->isSeqType()) {
    name_component_t topName = path().back();
    perm_string nextName = nextify_perm_string(topName.name);
    name_component_t* newTopName = new name_component_t(nextName);
    newTopName->index = topName.index;
    pform_name_t newPath;
    list<name_component_t>::const_iterator stop = path().end();
    --stop;
    for (list<name_component_t>::const_iterator it = path().begin(); it != stop; ++it) {
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

void PGenerate::next_cycle_transform(ostream&out, TypeEnv env) {
  for (list<PProcess*>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    if(debug_typecheck) 
      fprintf(stderr, "NextCycleTransform:: %s\n", typeid(*behav).name());
    (*behav)->next_cycle_transform(out, env);
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
void LexicalScope::typecheck_events_(ostream&out, TypeEnv& env) const {
  if (debug_typecheck) {
    for (map<perm_string, PEvent*>::const_iterator cur = events.begin();
	 cur != events.end();
	 cur++) {
      PEvent*ev = (*cur).second;
      out << "check event " << ev->name() << "; // " << ev->get_fileline()
	  << endl;
    }
  }
}

/**
 * Get the security labels for wires.
 */
void LexicalScope::typecheck_wires_(ostream&out, TypeEnv& env) const {
  // Iterate through and display all the wires.
  for (map<perm_string, PWire*>::const_iterator wire = wires.begin();
       wire != wires.end();
       wire++) {
    (*wire).second->typecheck(out, env.varsToType, env.varsToBase, env.seqVars);
  }
}

/*
 * Type-check a wire.
 */
void PWire::typecheck(ostream&out, map<perm_string, SecType*>& varsToType,
		      map<perm_string, BaseType*>& varsToBase,
		      set<perm_string>& seqVars) const {
  //void PWire::typecheck(ostream&out, TypeEnv&env) const {
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
	out << *lidx_;
      if (ridx_)
	out << ":" << *ridx_;
      cout << "]";
    }

    cout << ";" << endl;
  }
  varsToType[basename()] = sectype_;
  varsToBase[basename()] = basetype_;
  if(sectype_ == NULL) {
    fprintf(stderr, "WARN: Found NULL sectype for %s, using BOT",
	    basename().str());
    varsToType[basename()] = ConstType::BOT;
  }
  if(debug_typecheck) {
    cerr << "updating typeEnv for " << basename();
    cerr << " with sectype: " << *(varsToType[basename()]);
    cerr << " and basetype: " << varsToBase[basename()]->name() << endl;
  }
  if(basetype_->isSeqType() &&
     (port_type_ == NetNet::NOT_A_PORT ||
      port_type_ == NetNet::POUTPUT) ) seqVars.insert(basename());
}

void Module::dumpExprDefs(ostream&out, set<perm_string>exprs) const {
  for (std::set<perm_string>::iterator ite = exprs.begin();
       ite != exprs.end(); ite++) {
    out << "(declare-fun " << (*ite) << " () Int)" << endl;
    perm_string temp = *ite;
    map<perm_string, PWire*>::const_iterator cur = wires.find(temp);
    if (cur != wires.end()) {
      PWire* def = (*cur).second;
      out << "(assert (<= 0  " << (*ite) << "))" << endl;
      out << "(assert (<= " << (*ite) << " "
	  << (1 << (def->getRange() + 1)) - 1 << "))" << endl;
    }
  }  
}
/**
 * Collect all expressions that  appears in dependent types.
 * Need to also collect all identifiers that appear in
 * index expressions of quantified types.
 */
void Module::CollectDepExprs(ostream&out, TypeEnv & env) const {
  set<perm_string> exprs;
  for (std::map<perm_string, SecType*>::iterator iter =
	 env.varsToType.begin(); iter != env.varsToType.end(); iter++) {
    SecType* st = iter->second;
    st->collect_dep_expr(exprs);
  }

  for (list<PProcess*>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    (*behav)->collect_index_exprs(exprs, env.varsToType);
  }
  for (list<PGate*>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign* pgassign = dynamic_cast<PGAssign*>(*gate);
    if (pgassign != NULL) {
      pgassign->collect_index_exprs(exprs, env.varsToType);
    }
  }
  
  for (std::set<perm_string>::iterator expr = exprs.begin();
       expr != exprs.end(); expr++) {
    env.dep_exprs.insert(*expr);
  }
  
					   
  // check write labels, skipped for most hardware designs
  if (check_write)
    env.dep_exprs.insert(perm_string::literal("WriteLabel"));
  // declare the expressions as variables in z3 file
  out << endl << "; variables to be solved" << endl;

  dumpExprDefs(out, env.dep_exprs);  
}

/**
 * Generate invariants about the next cycle values of labels.
 * Only generate if expr is in a dependent label but skip the automatic next_cycle_transform assignment
 */
void Module::CollectDepInvariants(ostream&out, TypeEnv & env) const {
  out << "; invariants about dependent variables" << endl;
  set<perm_string> oldDeps = env.dep_exprs;
  //collect invariants and print them after definining new variables
  stringstream invs;
  for (list<PProcess*>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    Predicate emptyPred;
    (*behav)->collect_dep_invariants(invs, env, emptyPred);
  }
  for (list<PGate*>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign* pgassign = dynamic_cast<PGAssign*>(*gate);
    if (pgassign != NULL) {
      pgassign->collect_dep_invariants(invs, env);
    }
  }
  
  set<perm_string> newDeps;
  std::set_difference(env.dep_exprs.begin(), env.dep_exprs.end(),
		      oldDeps.begin(), oldDeps.end(), std::inserter(newDeps, newDeps.end()));
  dumpExprDefs(out, newDeps);
  out << invs.str();
}


/**
 * Type-check a module.
 */
void Module::typecheck(ostream&out, TypeEnv& env,
		       map<perm_string, Module*> modules, char* depfun) {
  if (debug_typecheck) {
    cout << "Module::check " << mod_name() << endl;

    for (unsigned idx = 0; idx < ports.size(); idx += 1) {
      port_t*cur = ports[idx];

      if (cur == 0) {
	cout << "    unconnected" << endl;
	continue;
      }

      cout << "Port::check " << cur->name << "(" << *cur->expr[0];
      for (unsigned wdx = 1; wdx < cur->expr.size(); wdx += 1) {
	cout << ", " << *cur->expr[wdx];
      }

      cout << ")" << endl;
    }
  }
    
  typecheck_parameters_(out, env);
  if(debug_typecheck) fprintf(stderr, "typechecking localparams\n");
  typecheck_localparams_(out, env);

  typedef map<perm_string, LineInfo*>::const_iterator genvar_iter_t;
  for (genvar_iter_t cur = genvars.begin(); cur != genvars.end(); cur++) {
    // genvars must be public
    env.varsToType[(*cur).first] = ConstType::BOT;
  }

  typedef map<perm_string, PExpr*>::const_iterator specparm_iter_t;
  for (specparm_iter_t cur = specparams.begin(); cur != specparams.end();
       cur++) {
    throw "specparm";
  }

  typedef list<Module::named_expr_t>::const_iterator parm_hiter_t;
  for (parm_hiter_t cur = defparms.begin(); cur != defparms.end(); cur++) {
    throw "defparam";
  }

  typecheck_events_(out, env);

  // Iterate through and display all the wires (including registers).
  if(debug_typecheck) fprintf(stderr, "typechecking wires\n");
  typecheck_wires_(out, env);

  if(debug_typecheck) fprintf(stderr, "next-cycle transform \n");
  next_cycle_transform(out,env);

  if(debug_typecheck) fprintf(stderr, "collecting dependands\n");
  CollectDepExprs(out, env);
  if(debug_typecheck) fprintf(stderr, "outputting type families\n");
  output_type_families(out, depfun);
  if(debug_typecheck) fprintf(stderr, "collecting dependent invariants\n");
  CollectDepInvariants(out, env);
  // remove an invariant if some variable does not show up
  if(debug_typecheck) fprintf(stderr, "optimizing invariants\n");
  for (set<Equality*>::iterator invite = env.invariants->invariants.begin();
       invite != env.invariants->invariants.end();) {
    set<perm_string> vars, diff;
    (*invite)->left->collect_dep_expr(vars);
    (*invite)->right->collect_dep_expr(vars);

    set<Equality*>::iterator current = invite++;

    // if the invariant has free variables, then remove it
    for (set<perm_string>::iterator varite = vars.begin();
	 varite != vars.end(); varite++) {
      if (env.dep_exprs.find(*varite) == env.dep_exprs.end()) {
	env.invariants->invariants.erase(current);
	break;
      }
    }
  }
  out << endl << "; assertions to be verified" << endl;

  if(debug_typecheck) fprintf(stderr, "checking generates\n");
  typedef list<PGenerate*>::const_iterator genscheme_iter_t;
  for (genscheme_iter_t cur = generate_schemes.begin();
       cur != generate_schemes.end(); cur++) {
    (*cur)->typecheck(out, env, modules);
  }

  // Dump the task definitions.
  if(debug_typecheck) fprintf(stderr, "dump tasks\n");
  typedef map<perm_string, PTask*>::const_iterator task_iter_t;
  for (task_iter_t cur = tasks.begin(); cur != tasks.end(); cur++) {
    cerr << "PTask ignored" << endl;
  }

  // Dump the function definitions.
  if(debug_typecheck) fprintf(stderr, "dump functions\n");
  typedef map<perm_string, PFunction*>::const_iterator func_iter_t;
  for (func_iter_t cur = funcs.begin(); cur != funcs.end(); cur++) {
    cerr << "PFunction" << endl;
  }

  // Iterate through and display all the gates.
  if(debug_typecheck) fprintf(stderr, "checking gates\n");
  for (list<PGate*>::const_iterator gate = gates_.begin();
       gate != gates_.end(); gate++) {
    PGAssign* pgassign = dynamic_cast<PGAssign*>(*gate);
    PGModule* pgmodule = dynamic_cast<PGModule*>(*gate);

    // make sure the parameters has same label as module declaration
    if (pgmodule != NULL) {
      pgmodule->typecheck(out, env, modules);
    } else if (pgassign != NULL) {
      Predicate pred;
      pgassign->typecheck(out, env, pred);
    }
  }

  // The code above should collect a typing environment for all variables.
  // The following code performs intra-process type checking.
  if(debug_typecheck) fprintf(stderr, "checking processes\n");
  for (list<PProcess*>::const_iterator behav = behaviors.begin();
       behav != behaviors.end(); behav++) {
    (*behav)->typecheck(out, env);
  }

  if(debug_typecheck) fprintf(stderr, "checking AProcesses\n");
  for (list<AProcess*>::const_iterator idx = analog_behaviors.begin();
       idx != analog_behaviors.end(); idx++) {
    throw "AProcess";
  }

  if(debug_typecheck) fprintf(stderr, "checking PSpecPaths\n");
  for (list<PSpecPath*>::const_iterator spec = specify_paths.begin();
       spec != specify_paths.end(); spec++) {
    throw "PSpecPath";
  }
}

/**
 * Type-check a process.
 */
void PProcess::typecheck(ostream&out, TypeEnv& env) const {
  if (debug_typecheck) {
    cout << "PProcess:check " << " /* " << get_fileline() << " */" << endl;
  }

  // initial is not synthesizable, just ignore them
  if (type_ != IVL_PR_INITIAL) {
    Predicate emptypred;
    if(debug_typecheck) {
      cerr << "pprocess checking statement of type ";
      cerr << typeid(*statement_).name() << endl;
    }
    statement_->typecheck(out, env, emptypred);
  }
}

/**
 * Do nothing.
 */
void AContrib::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
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
 * vardecl: Fresh variable generated for an assingment. See rule (T-ASSIGN-REC)
 *       in the paper "A Hardware Design Language for Timing-Sensitive
 *       Information-Flow Security" by Zhang et al. at ASPLOS'15 for more details.
 * env: A typing environment.
 */
void typecheck_assignment_constraint(ostream& out, SecType* lhs, SecType* rhs,
				     Predicate pred, string note, string vardecl, TypeEnv* env) {
  out << endl << "(push)" << endl;
  out << vardecl;
  Constraint* c = new Constraint(lhs, rhs, env->invariants, &pred);
  out << *c;
  out << "    ; " << note << endl;
  out << "(echo \"" << note << "\")" << endl;
  out << "(check-sat)" << endl;
  out << "(pop)" << endl << endl;

  // check restrictions on write labels
  if (check_write) {
    out << endl << "(push)" << endl;
    out << vardecl;
    c = new Constraint(lhs, IndexType::WL, env->invariants, &pred);
    out << *c;
    out << "    ; check write label " << note << endl;
    out << "(check-sat)" << endl;
    out << "(pop)" << endl << endl;
  }
}

/**
 * Type-check an assignment (either noblocking or blocking).
 */
void typecheck_assignment(ostream& out, PExpr* lhs, PExpr* rhs, TypeEnv* env,
			  Predicate precond, Predicate postcond, unsigned int lineno, string note) {
  // when the RHS is a PETernary expression, i.e. e1?e2:e3, we first translate to the equivalent statements
  PETernary* ternary = dynamic_cast<PETernary*>(rhs);
  if (ternary == NULL) {
    SecType* ltype, *rtype;
    BaseType* lbase;
    PEIdent* lident = dynamic_cast<PEIdent*>(lhs);
    if (lident != NULL) {
      //lhs is v[x], only want to put type(v) in the type
      ltype = lident->typecheckName(out, env->varsToType);
    } else {
      ltype = lhs->typecheck(out, env->varsToType);
    }
    lbase = lhs->check_base_type(out, env->varsToBase);
        
    //If ltype is sequential, substitute its free variables with the 
    //next-cycle version of that variable.
    if(lbase->isNextType()){
      ltype  = ltype->next_cycle(env);
    }
    rtype = new JoinType(rhs->typecheck(out, env->varsToType), env->pc);
    if (lident != NULL) {
      //lhs is v[x], want to include type(x) in the rhs type
      rtype = new JoinType(rtype, lident->typecheckIdx(out, env->varsToType));
    }
    if(lbase->isSeqType()){
      // Sequential logic is actually checked by the next cycle logic 
      // generated by the next cycle transformation. This must be the 
      // trusted, compiler-generated assignment
      rtype = ConstType::BOT;
    }


    if(debug_typecheck){
      cout << "line no" << lineno << endl;
      cout << "ltype: " << *ltype << endl;
      cout << "rtype: " << *rtype << endl;
      cout << "lbase: " << lbase->name() << endl;
      cout << "lhs: " << *lhs << endl;
      cout << "rhs: " << *rhs << endl;
      cout << "precond: " << precond << endl;
      cout << "postcond: " << postcond << endl;
    }

    // if nothing depends on LHS, simple case
    if (!lhs->typecheck(out, env->varsToType)->hasExpr(lhs->get_name())) {
      typecheck_assignment_constraint(out, ltype, rtype, precond, note,
				      "", env);
    } else {
      // declare a fresh variable
      stringstream ss, vardecl;
      ss << lhs->get_name() << lineno;
      const std::string* tmp = new string(ss.str());
      perm_string newname = perm_string::literal(tmp->c_str());
      vardecl << "(declare-fun " << newname << " () Int)" << endl;
      map<perm_string, PWire*>::const_iterator cur =
	env->module->wires.find(lhs->get_name());
      if (cur != env->module->wires.end()) {
	PWire* def = (*cur).second;
	vardecl << "(assert (<= 0  " << newname << "))" << endl;
	vardecl << "(assert (<= " << newname << " "
		<< (1 << (def->getRange() + 1)) - 1 << "))" << endl;
      }
      // add assumption v' = [[e]] if [[e]] is not bottom
      // perform no-sensitive-upgrade check if the variable being assigned to
      // might not be assigned to in other paths.
      set<perm_string>::iterator aiter = env->aliveVars.find(
							     lhs->get_name());
      if (aiter != env->aliveVars.end()) {
	rtype = env->pc;
	typecheck_assignment_constraint(out, ltype, rtype, precond,
					"no-sensitive-upgrade check " + note, "", env);
      }

      PENumber* number = dynamic_cast<PENumber*>(rhs);
      if (number != NULL
	  || env->dep_exprs.find(rhs->get_name())
	  != env->dep_exprs.end()) {
	precond.hypotheses.insert(
				  new Hypothesis(new PEIdent(newname), rhs));
      }
      typecheck_assignment_constraint(out,
				      ltype->subst(lhs->get_name(), newname), rtype, precond,
				      note, vardecl.str(), env);
    }
  } else {
    ternary->translate(lhs)->typecheck(out, *env, precond);
  }
}

void PGAssign::collect_index_exprs(set<perm_string>& exprs, map<perm_string, SecType*>&env) {
  pin(0)->collect_index_exprs(exprs, env);
  pin(1)->collect_index_exprs(exprs, env);
}

bool PGAssign::collect_dep_invariants(ostream&out, TypeEnv&env) {
  if (debug_typecheck) fprintf(stderr, "collect_dep_invariants on pgassign\n");
  PExpr* l = pin(0);
  PEIdent* lval = dynamic_cast<PEIdent*>(l);
  PExpr* rval = pin(1);
  if (!lval) {
    cerr << "Skipping assign to non identifier in gate" << endl;
    return false;
  }
  if (env.dep_exprs.find(lval->get_name()) != env.dep_exprs.end()) {    
    out << "(assert ";
    out << "(= ";
    lval->dumpz3(out);
    out << " ";
    rval->dumpz3(out);
    out << ")";
    out << ")" << endl;
    //also collect rhs variables in the dep_exprs to define them in z3 file
    rval->collect_idens(env.dep_exprs);
    return true;
  } else {
    return false;
  }  
}

/**
 * Type-check a blocking assignment.
 */
void PGAssign::typecheck(ostream&out, TypeEnv& env, Predicate pred) const {
  if (debug_typecheck) {
    cout << "assign " << *pin(0) << " = " << *pin(1) << ";" << endl;
  }

  stringstream ss;
  ss << "assign " << *pin(0) << " = " << *pin(1) << " @" << get_fileline();
  Predicate post;
  typecheck_assignment(out, pin(0), pin(1), &env, pred, post, get_lineno(),
		       ss.str());
}

/**
 * Type-check a module instantiation.
 */
void PGModule::typecheck(ostream&out, TypeEnv& env,
			 map<perm_string, Module*> modules) {
  cout << "pc context for module instantiation?" << endl;
  this->pin_count();
  this->get_pin_count();
  map<perm_string, Module*>::const_iterator cur = modules.find(get_type());
  map<perm_string, PWire*> mwires;
  if (cur != modules.end()) {
    mwires = ((*cur).second)->wires;
    unsigned pincount = get_pin_count();
    if (pincount != 0) {
      // collect name maps
      map<perm_string, perm_string> pinSubst;
      map<perm_string, perm_string> paraSubst;
      for (unsigned idx = 0; idx < pincount; idx += 1) {
	map<perm_string, PWire*>::const_iterator ite = mwires.find(
								   get_pin_name(idx));
	if (ite != mwires.end()) {
	  PWire* port = (*ite).second;
	  if (port->get_port_type() == NetNet::PINPUT
	      || port->get_port_type() == NetNet::PINOUT) {
	    pinSubst[get_pin_name(idx)] =
	      get_param(idx)->get_name();
	  } else {
	    pinSubst[get_pin_name(idx)] = get_pin_name(idx);
	  }

	  if (port->get_port_type() == NetNet::POUTPUT
	      || port->get_port_type() == NetNet::PINOUT) {
	    paraSubst[get_param(idx)->get_name()] = get_pin_name(
								 idx);
	  } else {
	    paraSubst[get_param(idx)->get_name()] =
	      get_param(idx)->get_name();
	  }
	}
      }
      for (unsigned idx = 0; idx < pincount; idx += 1) {
	map<perm_string, PWire*>::const_iterator ite = mwires.find(
								   get_pin_name(idx));
	if (ite != mwires.end()) {
	  PExpr* param = get_param(idx);
	  if (param != NULL) {
	    out << endl << "(push)" << endl;
	    // the direction (input, output) determines def or use should be more restrictive:
	    // def <= use for outputs
	    // use <= def for inputs
	    PWire* port = (*ite).second;
	    NetNet::PortType porttype = port->get_port_type();

	    SecType* paramType = param->typecheck(out,
						  env.varsToType);
	    SecType* pinType = port->get_sec_type();
	    for (std::map<perm_string, perm_string>::iterator substiter =
		   pinSubst.begin(); substiter != pinSubst.end();
		 ++substiter)
	      pinType = pinType->subst(substiter->first,
				       pinSubst[substiter->first]);
	    for (std::map<perm_string, perm_string>::iterator substiter =
		   paraSubst.begin(); substiter != paraSubst.end();
		 ++substiter)
	      paramType = paramType->subst(substiter->first,
					   paraSubst[substiter->first]);

	    // declare the free variables in pinType when necessary
	    set<perm_string> vars;
	    pinType->collect_dep_expr(vars);
	    for (set<perm_string>::iterator varsite = vars.begin();
		 varsite != vars.end(); varsite++) {
	      if (env.dep_exprs.find(*varsite)
		  == env.dep_exprs.end()) {
		out << "(declare-fun " << (*varsite)
		    << " () Int)" << endl;
		map<perm_string, PWire*>::const_iterator decl =
		  mwires.find(*varsite);
		// get the range of the free variables
		if (decl != mwires.end()) {
		  PWire* def = (*decl).second;
		  out << "(assert (<= 0  " << (*varsite)
		      << "))" << endl;
		  out << "(assert (<= " << (*varsite) << " "
		      << (1 << (def->getRange() + 1)) - 1
		      << "))" << endl;
		}
	      }
	    }

	    if (porttype == NetNet::PINPUT
		|| porttype == NetNet::PINOUT) {
	      SecType* rhs = paramType;
	      SecType* lhs = pinType;
	      Predicate pred;
	      Constraint* c = new Constraint(lhs, rhs,
					     env.invariants, &pred);
	      out << *c;
	      // debugging information
	      out << "    ; Instantiate parameter "
		  << get_pin_name(idx) << " in module "
		  << get_type() << " @" << get_fileline()
		  << endl;
	      out << "(echo \"parameter " << get_pin_name(idx)
		  << " for module " << get_type() << " @" << get_fileline()
		  << "\")" << endl;
	      out << "(check-sat)" << endl;	      
	      out << "(pop)" << endl << endl;
	    } else if (porttype == NetNet::POUTPUT
		       || porttype == NetNet::PINOUT) {
	      SecType* rhs = pinType;
	      SecType* lhs = paramType;
	      Predicate pred;
	      Constraint* c = new Constraint(lhs, rhs,
					     env.invariants, &pred);
	      out << *c;
	      // debugging information
	      out << "    ; Instantiate parameter "
		  << get_pin_name(idx) << " in module "
		  << get_type() << " @" << get_fileline()
		  << endl;
	      out << "(echo \"parameter " << get_pin_name(idx)
		  << " for module " << get_type() << " @" << get_fileline()
		  << "\")" << endl;	      
	      out << "(check-sat)" << endl;
	      out << "(pop)" << endl << endl;
	    }
	  } else {
	    cerr << "parameter " << *param << " is not found"
		 << endl;
	  }
	} else {
	  cerr << "PWire " << get_pin_name(idx) << " is not found"
	       << endl;
	}
      }
    }
  }
}

/**
 * Type-check an assignment statement.
 */
void PAssign::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
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
  typecheck_assignment(out, lval_, rval_, &env, precond, pred, get_lineno(),
		       ss.str());
}

/**
 * Type-check a nonblocking assignment.
 */
void PAssignNB::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PAssignNB::check " << *lval() << " <= ";
    if (delay_)
      cout << "#" << *delay_ << " ";
    if (count_)
      cout << "repeat(" << *count_ << ") ";
    if (event_)
      cout << *event_ << " ";
    cout << *rval() << ";" << endl;
  }

  stringstream ss;
  ss << *lval() << " <= " << *rval() << " @" << get_fileline();

  Predicate precond = pred;
  absintp(pred, env);
  typecheck_assignment(out, lval_, rval_, &env, precond, pred, get_lineno(),
		       ss.str());
}

/**
 * Type-check a block of code.
 */
void PBlock::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PBlock::check " << "begin";
    if (pscope_name() != 0)
      cout << " : " << pscope_name();
    cout << endl;
  }

  if (pscope_name() != 0) {
    typecheck_parameters_(out, env);

    typecheck_localparams_(out, env);

    typecheck_events_(out, env);

    typecheck_wires_(out, env);
  }

  set<Hypothesis*> before = pred.hypotheses;
  for (unsigned idx = 0; idx < list_.count(); idx += 1) {
    if (list_[idx])
      list_[idx]->typecheck(out, env, pred);
  }
}

/**
 * Do nothing.
 */
void PCallTask::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
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
  //throw "PCallTask";
  cout << "PCallTask is ignored" << endl;
}

/**
 * Type-check a case statement.
 */
void PCase::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PCase::check ";

    cout << " (" << *expr_ << ") " << endl;

    for (unsigned idx = 0; idx < items_->count(); idx += 1) {
      PCase::Item*cur = (*items_)[idx];

      if (cur->expr.count() != 0) {
	cout << "case item " << *cur->expr[0];

	for (unsigned e = 1; e < cur->expr.count(); e += 1)
	  cout << ", " << *cur->expr[e];

	cout << ":";
      }
    }
  }

  for (unsigned idx = 0; idx < items_->count(); idx += 1) {
    PCase::Item*cur = (*items_)[idx];
    SecType* oldpc = env.pc;
    bool need_hypo = env.dep_exprs.find(expr_->get_name())
      != env.dep_exprs.end();
    env.pc = new JoinType(expr_->typecheck(out, env.varsToType), oldpc);
    env.pc = env.pc->simplify();

    Predicate oldh = pred;
    if (need_hypo) {
      if (cur->expr.count() != 0) {
	for (unsigned e = 0; e < cur->expr.count(); e += 1)
	  pred.hypotheses.insert(new Hypothesis(expr_, cur->expr[e]));
      }
    }

    if (cur->stat) {
      cur->stat->typecheck(out, env,
			   pred /* add case condition to assumptions */);
    }

    pred = oldh;
    env.pc = oldpc;
  }
}

/**
 * Type-check a branch.
 */
void PCondit::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cerr << "PCondit::check " << "if (" << *expr_ << ")" << endl;

    cerr << "depvars currently in scope:" << endl;
    for (set<perm_string>::iterator depite = env.dep_exprs.begin();
	 depite != env.dep_exprs.end(); depite++) {
      cerr << *depite << endl;
    }

  }

  SecType* oldpc = env.pc;
  set<Hypothesis*> beforeif = pred.hypotheses;
  set<perm_string> oldalive = env.aliveVars;

  // generate fresh variables for that used in the current pc
  SecType* etype = expr_->typecheck(out, env.varsToType); //->freshVars(get_lineno(), subst);
  env.pc = new JoinType(etype, oldpc);
  env.pc = env.pc->simplify();

  // the commented out code takes a snapshot of the pc environment before executing the commands
  // in branches, in the hope of improving expressiveness. However, this feature seems useless
  // in real applications.
  //	for (map<perm_string, perm_string>::iterator ite=subst.begin(); ite != subst.end(); ite++) {
  //		perm_string oldname = (*ite).first;
  //		perm_string newname = (*ite).second;
  //    	out << "(declare-fun " << newname << " () Int)" << endl;
  //    	map<perm_string,PWire*>::const_iterator cur = env.module->wires.find(oldname);
  //    	if (cur != env.module->wires.end()) {
  //    		PWire* def = (*cur).second;
  //    		out << "(assert (<= 0  " << newname << "))" << endl;
  //    		out << "(assert (<= " << newname << " " << pow(2,def->getRange()+1)-1 << "))" << endl;
  //        }
  //	}

  // calculate the alternative modified variables for if and else branch
  set<PExpr*, ExprComparator> modified;

  mustmodify(modified, env.dep_exprs);

  for (set<perm_string>::iterator depite = env.dep_exprs.begin();
       depite != env.dep_exprs.end(); depite++) {
    bool add = true;
    for (set<PExpr*, ExprComparator>::iterator exprite = modified.begin();
	 exprite != modified.end(); exprite++) {
      if ((*exprite)->get_name() == *depite) {
	add = false;
	break;
      }
    }
    if (add)
      env.aliveVars.insert(*depite);
  }

  if (if_) {
    absintp(pred, env, true, false);
    if_->typecheck(out, env, pred);
  }

  Predicate afterif = pred;
  pred.hypotheses = beforeif;

  if (else_) {
    absintp(pred, env, false, false);
    else_->typecheck(out, env, pred);
  }
  Predicate afterelse = pred;
  // at the merge point, we assume no assumptions are valid anymore
  env.pc = oldpc;
  env.aliveVars = oldalive;
  pred.hypotheses.clear();
  merge(afterif, afterelse, pred);
  
}

/**
 * Do nothing.
 */
void PCAssign::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PCAssign::check " << "assign " << *lval_ << " = " << *expr_
	 << endl;
  }
  throw "PCAssign";
}

/**
 * Do nothing.
 */
void PDeassign::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PDeassign::check " << *lval_ << "; " << endl;
  }
  throw "PDeassign";
}

/**
 * Do nothing.
 */
void PDelayStatement::typecheck(ostream&out, TypeEnv& env,
				Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PDelayStatement::check " << "#" << *delay_;
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
void PDisable::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PDisable::check " << scope_ << ";" << endl;
  }
  throw "PDisable";
}

/**
 * Type-check an event.
 */
void PEventStatement::typecheck(ostream&out, TypeEnv& env,
				Predicate& pred) const {
  if (debug_typecheck) {
    if (expr_.count() == 0) {
      cerr << "PEventStatement::check " << "@* ";
    } else {
      cerr << "PEventStatement::check" << "@(" << *(expr_[0]);
      if (expr_.count() > 1)
	for (unsigned idx = 1; idx < expr_.count(); idx += 1)
	  cerr << " or " << *(expr_[idx]);
      cerr << ")";
    }

    if (statement_) {
      cerr << endl;
    } else {
      cerr << " ;" << endl;
    }
  }

  SecType* oldpc = env.pc;
  // taint pc by the label of trigger event
  if (expr_.count() != 0) {
    env.pc = new JoinType(env.pc,
			  expr_[0]->expr()->typecheck(out, env.varsToType));
    for (unsigned idx = 1; idx < expr_.count(); idx += 1)
      env.pc = new JoinType(env.pc,
			    expr_[idx]->expr()->typecheck(out, env.varsToType));
  }
  statement_->typecheck(out, env, pred);
  env.pc = oldpc;
}

/**
 * Do nothing.
 */
void PForce::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PForce::check " << *lval_ << " = " << *expr_ << ";" << endl;
  }
  throw "PForce";
}

/**
 * Do nothing.
 */
void PForever::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PForever::check " << endl;
  }
  throw "PForever";
}

/**
 * Do nothing.
 */
void PForStatement::typecheck(ostream&out, TypeEnv& env,
			      Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PForStatement::check " << "for (" << *name1_ << " = "
	 << *expr1_ << "; " << *cond_ << "; " << *name2_ << " = "
	 << *expr2_ << ")" << endl;
  }
  throw "PForStatement";
}

/**
 * Type-check a generate statement.
 * Use a copy of env to avoid duplicated definitions.
 */
void PGenerate::typecheck(ostream&out, TypeEnv env,
			  map<perm_string, Module*> modules) {
  if (debug_typecheck) {
    dump(cout, 0);
  }

  typecheck_parameters_(out, env);
  typecheck_localparams_(out, env);
  if (defparms.size() > 0) {
    cout << "PGenerate::defparms are ignored" << endl;
  }
  typecheck_events_(out, env);
  // Iterate through and display all the wires (including registers).
  typecheck_wires_(out, env);
  out << endl << "; assertions to be verified" << endl;

  for (list<PGate*>::const_iterator gate = gates.begin(); gate != gates.end();
       gate++) {
    PGAssign* pgassign = dynamic_cast<PGAssign*>(*gate);
    PGModule* pgmodule = dynamic_cast<PGModule*>(*gate);

    // make sure the parameters has same label as module declaration
    if (pgmodule != NULL) {
      pgmodule->typecheck(out, env, modules);
    } else if (pgassign != NULL) {
      Predicate pred;
      pgassign->typecheck(out, env, pred);
    }
  }

  for (list<PProcess*>::const_iterator idx = behaviors.begin();
       idx != behaviors.end(); idx++) {
    (*idx)->typecheck(out, env);
  }

  for (list<AProcess*>::const_iterator idx = analog_behaviors.begin();
       idx != analog_behaviors.end(); idx++) {
    throw "AProcess";
  }

  typedef map<perm_string, LineInfo*>::const_iterator genvar_iter_t;
  for (genvar_iter_t cur = genvars.begin(); cur != genvars.end(); cur++) {
    throw "genvars";
  }

  for (list<PGenerate*>::const_iterator idx = generate_schemes.begin();
       idx != generate_schemes.end(); idx++) {
    (*idx)->typecheck(out, env, modules);
  }
}

/**
 * Do nothing.
 */
void PNoop::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "check PNoop " << endl;
  }
  throw "PNoop";
}

/**
 * Do nothing.
 */
void PRelease::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PRelease::check " << *lval_ << ";" << endl;
  }
  throw "PRelease";
}

/**
 * Do nothing.
 */
void PRepeat::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PRepeat::check (" << *expr_ << ")" << endl;
  }
  throw "PRepeat";
}

/**
 * Do nothing.
 */
void PTrigger::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
  if (debug_typecheck) {
    cout << "PTrigger::check" << "-> " << event_ << ";" << endl;
  }
  throw "PTrigger";
}

/**
 * Do nothing.
 */
void PWhile::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const {
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
 * SecVerilog by default declares a "dimand" lattice with four security labels as follows:
 *                   HIGH
 *             D1            D2
 *                   LOW
 *
 * Programmers can define their own lattice structure in a Z3 file,
 * by using the [-l lattice_file] option to SecVerilog.
 */
void output_lattice(ostream& out, char* lattice) {
  out << "; this part encodes a partial order on labels" << endl;
  out << "(declare-sort Label)" << endl;
  out << "(declare-fun leq (Label Label) Bool)" << endl;
  out << "(declare-fun join (Label Label) Label)" << endl;
  out << "(declare-fun meet (Label Label) Label)" << endl;

  out << "(assert (forall ((x Label)) (leq x x)))" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x y) (leq y z)) (leq x z))))" << endl;
  out << "(assert (forall ((x Label) (y Label)) (implies (and (leq x y) (leq y x)) (= x y))))" << endl;

  out << endl << "; axioms for join" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (leq (join x y) z) (and (leq x z) (leq y z)))))" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x z) (leq y z)) (leq (join x y) z))))" << endl;
  out << "(assert (forall ((x Label) (y Label)) (and (leq x (join x y)) (leq y (join x y)))))" << endl;
  out << "(assert (forall ((x Label) (y Label)) (= (join x y) (join y x))))" << endl;

  out << endl << "; axioms for meet" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (leq x (meet y z)) (and (leq x y) (leq x z)))))" << endl;
  out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x y) (leq x z)) (leq x (meet y z)))))" << endl;
  out << "(assert (forall ((x Label) (y Label)) (and (leq (meet x y) x) (leq (meet x y) y))))" << endl;
  out << "(assert (forall ((x Label) (y Label)) (= (meet x y) (meet y x))))" << endl;

  out << endl << "; lattice elements" << endl;
  out << "(declare-fun LOW () Label)" << endl;
  out << "(declare-fun HIGH () Label)" << endl;
  out << "(declare-fun D1 () Label)" << endl;
  out << "(declare-fun D2 () Label)" << endl;

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
void output_type_families(ostream& out, char* depfun) {
  out << endl << "; function that maps 0 to LOW; 1 to HIGH" << endl;
  out << "(declare-fun LH (Int) Label)" << endl;
  out << "(assert (= (LH 0) LOW))" << endl;
  out << "(assert (= (LH 1) HIGH))" << endl;

  // append the user-defined type-level functions
  if (depfun) {
    string line;
    ifstream infile(depfun);
    while (getline(infile, line)) {
      out << line << endl;
    }
  }
}

/*
 * This function is the root of all type checking. The input is the list
 * of root module names. The function locates the Module definitions
 * for each root, does the type check.
 */
void typecheck(map<perm_string, Module*> modules,
	       char* lattice_file_name, char* depfun_file_name) {

  // Scan the root modules by name, and output the name.
  for (map<perm_string, Module*>::const_iterator mod = modules.begin();
       mod != modules.end(); mod++) {

    // Get the module definition for this root instance.
    Module *rmod = (*mod).second;

    // Typing environment \G and assumptions \A for type
    // checking typing rules have the form \G, \A |- C, where
    // \G is a map from Verilog vars to security lables, and
    // \A is a conjunction of predicates on PWire
    map<perm_string, SecType*> *varsToType =
      new map<perm_string, SecType*>();
    map<perm_string, BaseType*> *varsToBase=
      new map<perm_string, BaseType*>();
    TypeEnv* env = new TypeEnv(*varsToType, *varsToBase, ConstType::BOT, rmod);

    ofstream z3file;
    string z3filename = string(rmod->file_name().str());
    size_t pos = z3filename.find_first_of('.');
    if (pos != string::npos)
      z3filename = z3filename.substr(0, pos);
    z3file.open((z3filename + ".z3").c_str());
    output_lattice(z3file, lattice_file_name);
    try {
      rmod->typecheck(z3file, *env, modules, depfun_file_name);
    } catch (char const* str) {
      cerr << "Unimplemented " << str << endl;
    }
    z3file.close();
  }
}
