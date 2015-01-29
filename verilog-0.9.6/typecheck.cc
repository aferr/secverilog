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
 * Type-check takes as input a complete parse tree and the name of a
 * root module, and generates Z3 constraints.
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

SecType* typecheck_subst(perm_string lname, SecType* ltype, PExpr* rhs, TypeEnv* env);
SecType* typecheck_subst(perm_string lname, SecType* ltype, PWire* rhs, TypeEnv* env);
void output_type_families(ostream& out);
extern bool check_write;

void LexicalScope::typecheck_parameters_(ostream&out, TypeEnv& env) const
{
      typedef map<perm_string,param_expr_t>::const_iterator parm_iter_t;
      if (debug_typecheck) {
    	  for (parm_iter_t cur = parameters.begin()
    		  ; cur != parameters.end() ; cur ++) {
	          cout << "check parameter " << (*cur).first << " " << (*cur).second.type << endl;
          }
      }
      // parameters can only be assigned to constants. So the label must be LOW
	  for (parm_iter_t cur = parameters.begin()
		  ; cur != parameters.end() ; cur ++) {
		  env.varsToType[(*cur).first] = ConstType::BOT;
	  }
}

void LexicalScope::typecheck_localparams_(ostream&out, TypeEnv& env) const
{
      typedef map<perm_string,param_expr_t>::const_iterator parm_iter_t;
      for (parm_iter_t cur = localparams.begin()
		 ; cur != localparams.end() ; cur ++) {
	    out << "check localparam ";
	    if ((*cur).second.msb)
		  out << "[" << *(*cur).second.msb << ":"
		      << *(*cur).second.lsb << "] ";
	    out << (*cur).first << " = ";
	    if ((*cur).second.expr)
		  out << *(*cur).second.expr << ";" << endl;
	    else
		  out << "/* ERROR */;" << endl;
      }
}

void LexicalScope::typecheck_events_(ostream&out, TypeEnv& env) const
{
      for (map<perm_string,PEvent*>::const_iterator cur = events.begin()
		 ; cur != events.end() ;  cur ++ ) {
	    PEvent*ev = (*cur).second;
	    out << "check event " << ev->name() << "; // "
		<< ev->get_fileline() << endl;
      }
}

void LexicalScope::typecheck_wires_(ostream&out, TypeEnv& env) const
{
      // Iterate through and display all the wires.
      for (map<perm_string,PWire*>::const_iterator wire = wires.begin()
		 ; wire != wires.end() ; wire ++ ) {

	    (*wire).second->typecheck(out, env.varsToType);
      }
}

void PWire::typecheck(ostream&out, map<perm_string, SecType*>& varsToType) const
{
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
	    if (lidx_) out << *lidx_;
	    if (ridx_) out << ":" << *ridx_;
	    cout << "]";
      }

      cout << ";" << endl;
	}

	varsToType[basename()] = sectype_;
}

void Module::CollectDepExprs(ostream&out, TypeEnv & env) const
{
    // collect all expressions that  appears in dependent types
    for (std::map<perm_string, SecType*>::iterator iter = env.varsToType.begin()
    		 ; iter != env.varsToType.end() ; iter ++) {
    	SecType* st = iter->second;
    	set<perm_string> exprs;
    	st->collect_dep_expr(exprs);
        for (std::set<perm_string>::iterator expr = exprs.begin()
        		 ; expr != exprs.end() ; expr ++) {
            env.dep_exprs.insert(*expr);
    	}
    }

    if (check_write)
    	env.dep_exprs.insert(perm_string::literal("WriteLabel"));
    // declare the expressions as variables in z3 file
    out << endl << "; variables to be solved" << endl;

    for ( std::set<perm_string>::iterator ite = env.dep_exprs.begin();
    			ite != env.dep_exprs.end();
    			ite ++) {
    	out << "(declare-fun " << (*ite) << " () Int)" << endl;
    	perm_string temp = *ite;
    	map<perm_string,PWire*>::const_iterator cur = wires.find(temp);
    	if (cur != wires.end()) {
    		PWire* def = (*cur).second;
    		out << "(assert (<= 0  " << (*ite) << "))" << endl;
    		out << "(assert (<= " << (*ite) << " " << pow(2,def->getRange()+1)-1 << "))" << endl;
        }
//    	out << "(assert (or (= (Par " << (*ite) << ") LOW) (= (Par " << (*ite) << ") HIGH)))" << endl;
    }
}

void Module::typecheck(ostream&out, TypeEnv& env, map<perm_string,Module*> modules) const
{
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
    typecheck_localparams_(out, env);

    typedef map<perm_string,LineInfo*>::const_iterator genvar_iter_t;
    for (genvar_iter_t cur = genvars.begin()
		 ; cur != genvars.end() ; cur++) {
    	// genvars must be public
    	env.varsToType[(*cur).first] = ConstType::BOT;
    }

    typedef map<perm_string,PExpr*>::const_iterator specparm_iter_t;
    for (specparm_iter_t cur = specparams.begin()
		 ; cur != specparams.end() ; cur ++) {
	    throw "specparm";
    }


    typedef list<Module::named_expr_t>::const_iterator parm_hiter_t;
    for (parm_hiter_t cur = defparms.begin()
		 ; cur != defparms.end() ;  cur ++) {
	    throw "defparam";
    }

    typecheck_events_(out, env);

	// Iterate through and display all the wires (including registers).
    typecheck_wires_(out, env);
    CollectDepExprs(out, env);
    output_type_families(out);
    // remove an invariant if some variable does not show up
    for (set<Equality*>::iterator invite = env.invariants->invariants.begin(); invite != env.invariants->invariants.end(); ) {
    	set<perm_string> vars, diff;
    	(*invite)->left->collect_dep_expr(vars);
    	(*invite)->right->collect_dep_expr(vars);

    	set<Equality*>::iterator current = invite++;

    	// if the invariant has free variables, then remove it
    	for (set<perm_string>::iterator varite = vars.begin(); varite!=vars.end(); varite++) {
    		if (env.dep_exprs.find(*varite) == env.dep_exprs.end()) {
    	    	env.invariants->invariants.erase(current);
    	    	break;
    		}
    	}
    }
    out << endl << "; assertions to be verified" << endl;

    typedef list<PGenerate*>::const_iterator genscheme_iter_t;
    for (genscheme_iter_t cur = generate_schemes.begin()
		 ; cur != generate_schemes.end() ; cur++) {
    	(*cur)->typecheck(out, env, modules);
    }

    // Dump the task definitions.
    typedef map<perm_string,PTask*>::const_iterator task_iter_t;
    for (task_iter_t cur = tasks.begin()
		 ; cur != tasks.end() ; cur ++) {
	    out << "PTask ignored" << endl;
    }


	// Dump the function definitions.
    typedef map<perm_string,PFunction*>::const_iterator func_iter_t;
    for (func_iter_t cur = funcs.begin()
		 ; cur != funcs.end() ; cur ++) {
	    cerr << "PFunction" << endl;
    }


	// Iterate through and display all the gates
    for (list<PGate*>::const_iterator gate = gates_.begin()
		 ; gate != gates_.end()
		 ; gate ++ ) {
    	PGAssign* pgassign = dynamic_cast<PGAssign*>(*gate);
    	PGModule* pgmodule = dynamic_cast<PGModule*>(*gate);

    	// make sure the parameters has same label as module declaration
    	if (pgmodule != NULL) {
    		pgmodule->typecheck(out, env, modules);
    	}
    	else if (pgassign != NULL) {
    		Predicate pred;
    		pgassign->typecheck(out, env, pred);
    	}
    }

    // the code above should collect a typing environment for all variables
    // the following code performs intra-process type checking
    for (list<PProcess*>::const_iterator behav = behaviors.begin()
		 ; behav != behaviors.end()
		 ; behav ++ ) {

	    (*behav)->typecheck(out, env);
    }

    for (list<AProcess*>::const_iterator idx = analog_behaviors.begin()
		 ; idx != analog_behaviors.end() ;  idx++) {
    	throw "AProcess";
    }

    for (list<PSpecPath*>::const_iterator spec = specify_paths.begin()
		 ; spec != specify_paths.end()
		 ; spec ++ ) {
    	throw "PSpecPath";
    }
}

void PProcess::typecheck(ostream&out, TypeEnv& env) const
{
	if (debug_typecheck) {
		cout << "PProcess:check " << " /* " << get_fileline() << " */" << endl;
	}
	//dump_attributes_map(out, attributes, ind+2);

	// initial is not synthesizable, just ignore them
	if (type_ != IVL_PR_INITIAL) {
		//	out << endl << "(push)" << endl;
		Predicate emptypred;
		statement_->typecheck(out, env, emptypred);
		//	out << "(check-sat)" << endl;
		//	out << "(pop)" << endl << endl;
	}
}

void AContrib::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
		cout << "AContrib::check ";
		cout << *lval_ << " <+ " << *rval_ << endl;
	}
	throw "AContrib";
}

// this function returns a new type for the variable on LHS after assignments
SecType* typecheck_subst(perm_string lname, SecType* ltype, PExpr* rhs, TypeEnv* env) {
	PENumber* number = dynamic_cast<PENumber*>(rhs);
	bool need_subst = false;
	for (std::set<perm_string>::iterator ite = env->dep_exprs.begin();
			ite != env->dep_exprs.end(); ite++) {
		if (rhs->contains_expr(*ite))
			need_subst = true;
	}
	if (number != NULL) {
		need_subst = true;
	}
	if (need_subst) {
		ltype = ltype->subst(lname, rhs->get_name());
	}
	return ltype;
}

SecType* typecheck_subst(perm_string lname, SecType* ltype, PWire* rhs, TypeEnv* env) {
	for (std::set<perm_string>::iterator ite = env->dep_exprs.begin();
			ite != env->dep_exprs.end(); ite++) {
		if (rhs->basename() == (*ite))
			ltype = ltype->subst(lname, rhs->basename());
	}
	return ltype;
}

void typecheck_assignment_constraint (ostream& out, SecType* lhs, SecType* rhs, Predicate pred, string note, string vardecl, TypeEnv* env) {
	out << endl << "(push)" << endl;
	out << vardecl;

  // For now, just add lhs and rhs declared bounds
  //
  lhs->give_name("lhs");
  rhs->give_name("rhs");

  QFuncDefs* d = new QFuncDefs();
  if(lhs->has_defs()){
      d->defs.insert(lhs);
  }
  if(rhs->has_defs()){
      d->defs.insert(rhs);
  }

  QBounds *b = new QBounds();
  lhs->add_bounds(b);
  rhs->add_bounds(b);

	Constraint* c = new Constraint(lhs, rhs, env->invariants, &pred);
  c->def = d;
  c->bound = b;
	out << *c;
	out << "    ; " << note << endl;
	out << "(check-sat)" << endl;
	out << "(pop)" << endl << endl;
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

void freshvariant (TypeEnv& env, Predicate& precond, Predicate postcond, map<perm_string, perm_string>& subst, unsigned int lineno) {
	for (set<perm_string>::iterator ite = env.dep_exprs.begin(); ite != env.dep_exprs.end(); ite++) {
		stringstream ss;
		ss << (*ite) << lineno;
	    const std::string* tmp = new string(ss.str());
		perm_string newname = perm_string::literal(tmp->c_str());
		subst[(*ite)] = newname;
	}
	Predicate* freshpost = postcond.subst(subst);
	precond.hypotheses.insert(freshpost->hypotheses.begin(), freshpost->hypotheses.end());
}

void typecheck_assignment(ostream& out, PExpr* lhs, PExpr* rhs, TypeEnv* env,
		Predicate precond, Predicate postcond, unsigned int lineno, string note) {
	// when the RHS is a PETernary expression, i.e. e1?e2:e3, we first translate to the equivalent statements
	PETernary* ternary = dynamic_cast<PETernary*>(rhs);
	if (ternary == NULL) {
		SecType* ltype, *rtype;
		ltype = lhs->typecheck(out, env->varsToType);
		rtype = new JoinType(rhs->typecheck(out, env->varsToType), env->pc);

		// if nothing depends on LHS, simple case
		if (!lhs->typecheck(out, env->varsToType)->hasExpr(lhs->get_name())) {
			typecheck_assignment_constraint(out, ltype, rtype, precond, note, "", env);
		}
		else {
//			map<perm_string, perm_string> subst;
//			freshvariant(*env, precond, postcond, subst, lineno);
//			for (map<perm_string, perm_string>::iterator ite = subst.begin();
//				ite != subst.end(); ite++) {
//				perm_string oldname = (*ite).first;
//				perm_string newname = (*ite).second;
//				out << "(declare-fun " << newname << " () Int)" << endl;
//				map<perm_string, PWire*>::const_iterator cur =
//						env->module->wires.find(oldname);
//				if (cur != env->module->wires.end()) {
//				PWire* def = (*cur).second;
//				out << "(assert (<= 0  " << newname << "))" << endl;
//				out << "(assert (<= " << newname << " "
//						<< pow(2, def->getRange() + 1) - 1 << "))" << endl;
//				}
//			}
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
						<< pow(2, def->getRange() + 1) - 1 << "))" << endl;
			}
			// add assumption v' = [[e]] if [[e]] is not bottom
			// check alternative branch if necessary
			set<perm_string>::iterator aiter = env->aliveVars.find(lhs->get_name());
			if (aiter != env->aliveVars.end()) {
				rtype = env->pc;
				typecheck_assignment_constraint(out, ltype, rtype, precond, "alive check "+note, "", env);
			}

			PENumber* number = dynamic_cast<PENumber*>(rhs);
			if (number != NULL || env->dep_exprs.find(rhs->get_name()) != env->dep_exprs.end()) {
				precond.hypotheses.insert(new Hypothesis(new PEIdent(newname), rhs));
			}
			typecheck_assignment_constraint(out, ltype->subst(lhs->get_name(), newname),
					rtype, precond, note, vardecl.str(), env);
		}
	}
	else {
		ternary->translate(lhs)->typecheck(out, *env, precond);
	}
}

void PGAssign::typecheck(ostream&out, TypeEnv& env, Predicate pred) const
{
	if (debug_typecheck) {
	    cout << "assign " << *pin(0) << " = " << *pin(1) << ";" << endl;
	}

	stringstream ss;
	ss << "assign " << *pin(0) << " = " << *pin(1) << " @" << get_fileline();
	Predicate post;
	typecheck_assignment(out, pin(0), pin(1), &env, pred, post, get_lineno(), ss.str());
}

void PGModule::typecheck(ostream&out, TypeEnv& env, map<perm_string,Module*> modules)
{
	cout << "pc context for module instantiation?" << endl;
	this->pin_count();
	this->get_pin_count();
	map<perm_string,Module*>::const_iterator cur = modules.find(get_type());
	map<perm_string,PWire*> mwires;
	if (cur != modules.end()) {
        mwires = ((*cur).second)->wires;
		unsigned pincount = get_pin_count();
		if (pincount != 0) {
			// collect name maps
			map<perm_string,perm_string> pinSubst;
			map<perm_string,perm_string> paraSubst;
			for (unsigned idx = 0; idx < pincount; idx += 1) {
				map<perm_string,PWire*>::const_iterator ite = mwires.find(get_pin_name(idx));
				if (ite != mwires.end()) {
					PWire* port = (*ite).second;
					if (port->get_port_type() == NetNet::PINPUT || port->get_port_type() == NetNet::PINOUT) {
						pinSubst[get_pin_name(idx)] = get_param(idx)->get_name();
					}
					else {
						pinSubst[get_pin_name(idx)] = get_pin_name(idx);
					}

					if (port->get_port_type() == NetNet::POUTPUT || port->get_port_type() == NetNet::PINOUT) {
						paraSubst[get_param(idx)->get_name()] = get_pin_name(idx);
					}
					else {
						paraSubst[get_param(idx)->get_name()] = get_param(idx)->get_name();
					}
				}
			}
			for (unsigned idx = 0; idx < pincount; idx += 1) {
				map<perm_string,PWire*>::const_iterator ite = mwires.find(get_pin_name(idx));
				if (ite != mwires.end()) {
					PExpr* param =  get_param(idx);
					if (param != NULL) {
						out << endl << "(push)" << endl;
						// the direction (input, output) determines def or use should be more restrictive:
						// def <= use for outputs
						// use <= def for inputs
						PWire* port = (*ite).second;
						NetNet::PortType porttype = port->get_port_type();

						SecType* paramType = param->typecheck(out, env.varsToType);
						SecType* pinType = port->get_sec_type();
	    				for(std::map<perm_string,perm_string>::iterator substiter = pinSubst.begin(); substiter != pinSubst.end(); ++substiter)
	    					pinType = pinType->subst(substiter->first, pinSubst[substiter->first]);
	    				for(std::map<perm_string,perm_string>::iterator substiter = paraSubst.begin(); substiter != paraSubst.end(); ++substiter)
	    					paramType = paramType->subst(substiter->first, paraSubst[substiter->first]);

	    				// declare the free variables in pinType when necessary
	    				set<perm_string> vars;
	    				pinType->collect_dep_expr(vars);
	    				for (set<perm_string>::iterator varsite = vars.begin();
	    						varsite!=vars.end(); varsite++) {
	    					if (env.dep_exprs.find(*varsite) == env.dep_exprs.end()) {
	    						out << "(declare-fun " << (*varsite) << " () Int)" << endl;
	    						map<perm_string, PWire*>::const_iterator decl =
	    								mwires.find(*varsite);
	    						// get the range of the free variables
	    						if (decl != mwires.end()) {
	    							PWire* def = (*decl).second;
	    							out << "(assert (<= 0  " << (*varsite) << "))" << endl;
	    							out << "(assert (<= " << (*varsite) << " "
	    									<< pow(2, def->getRange() + 1) - 1 << "))" << endl;
	    						}
	    					}
	    				}

						if (porttype == NetNet::PINPUT || porttype == NetNet::PINOUT) {
							SecType* rhs = paramType;
							SecType* lhs = pinType;
							Predicate pred;
							Constraint* c = new Constraint(lhs, rhs, env.invariants, &pred);
							out << *c;
							// debugging information
							out << "    ; Instantiate parameter " << get_pin_name(idx)
							    << " in module " << get_type() << " @" << get_fileline() << endl;
							out << "(check-sat)" << endl;
							out << "(pop)" << endl << endl;
						}
						else if (porttype == NetNet::POUTPUT || porttype == NetNet::PINOUT){
							SecType* rhs = pinType;
							SecType* lhs = paramType;
							Predicate pred;
							Constraint* c = new Constraint(lhs, rhs, env.invariants, &pred);
							out << *c;
							// debugging information
							out << "    ; Instantiate parameter " << get_pin_name(idx)
								<< " in module " << get_type() << " @" << get_fileline() << endl;
							out << "(check-sat)" << endl;
							out << "(pop)" << endl << endl;
						}
					}
					else {
						cerr << "parameter " << *param << " is not found" << endl;
					}
				}
				else {
					cerr << "PWire " << get_pin_name(idx) << " is not found" << endl;
				}
			}
		}
	}
}

void PAssign::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PAssign::check " << *lval() << " = ";
      if (delay_) cout << "#" << *delay_ << " ";
      if (count_) cout << "repeat(" << *count_ << ") ";
      if (event_) cout << *event_ << " ";
      cout << *rval() << ";" << endl;
	}

	stringstream ss;
	ss << *lval() << " = " << *rval() << " @" << get_fileline();

	Predicate precond = pred;
	absintp(pred, env);
	typecheck_assignment(out, lval_, rval_, &env, precond, pred, get_lineno(), ss.str());
}

void PAssignNB::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
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
	typecheck_assignment(out, lval_, rval_, &env, precond, pred, get_lineno(), ss.str());
}

void PBlock::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
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

void PCallTask::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
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

void PCase::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
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
		bool need_hypo = env.dep_exprs.find(expr_->get_name()) != env.dep_exprs.end();
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
			cur->stat->typecheck(out, env, pred /* add case condition to assumptions */);
		}

//		if (need_hypo) {
//			if (cur->expr.count() != 0) {
//				for (unsigned e = 0; e < cur->expr.count(); e += 1) {
//					env.hypotheses.pop_back();
//				}
//			}
//		}
		pred = oldh;
		env.pc = oldpc;
	}
}

void PCondit::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PCondit::check " << "if (" << *expr_ << ")" << endl;
	}

	SecType* oldpc = env.pc;
	set<Hypothesis*> beforeif = pred.hypotheses;
//	map<perm_string, perm_string> subst;
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
			depite!=env.dep_exprs.end(); depite++) {
		bool add = true;
		for (set<PExpr*, ExprComparator>::iterator exprite = modified.begin();
			exprite != modified.end(); exprite++) {
			if ((*exprite)->get_name()==*depite) {
				add = false;
				break;
			}
		}
		if (add)
			env.aliveVars.insert(*depite);
	}

	if (if_) {
		absintp(pred, env, true);
//		env.dupHypotheses(subst);
		if_->typecheck(out, env, pred);
	}
	Predicate afterif = pred;
	pred.hypotheses = beforeif;
    if (else_) {
		absintp(pred, env, false);
//		env.dupHypotheses(subst);
	    else_->typecheck(out, env, pred);
    }
	Predicate afterelse = pred;
    // at the merge point, we assume no assumptions are valid anymore
    env.pc = oldpc;
    env.aliveVars = oldalive;
    pred.hypotheses.clear();
    merge(afterif, afterelse, pred);
    // remove predicates over pc variables
//    for (map<perm_string, perm_string>::iterator mite = subst.begin(); mite != subst.end(); mite++) {
//		set<Hypothesis*>::iterator hypoite = env.hypotheses.begin();
//		while (hypoite != env.hypotheses.end()) {
//			if ((*hypoite)->matches((*mite).second)) {
//				env.hypotheses.erase(hypoite);
//			}
//			hypoite++;
//		}
//    }
//    env.hypotheses = beforeif;
}

void PCAssign::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
		cout << "PCAssign::check " << "assign " << *lval_ << " = " << *expr_ << endl;
	}
	throw "PCAssign";
}

void PDeassign::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PDeassign::check " << *lval_ << "; " << endl;
	}
	throw "PDeassign";
}

void PDelayStatement::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PDelayStatement::check " << "#" << *delay_;
      if (statement_) {
	    cout << endl;
	  } else {
	    cout << " /* noop */;" << endl;
      }
	}
	throw "PDelay";
/*
	if (statement_)
	    statement_->typecheck(out, env);
*/
}

void PDisable::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PDisable::check " << scope_ << ";" << endl;
	}
	throw "PDisable";
}

void PEventStatement::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      if (expr_.count() == 0) {
	    cout << "PEventStatement::check " << "@* ";
      } else {
	    cout << "PEventStatement::check" << "@(" << *(expr_[0]);
	    if (expr_.count() > 1)
		  for (unsigned idx = 1 ;  idx < expr_.count() ;  idx += 1)
			cout << " or " << *(expr_[idx]);
	    cout << ")";
      }

      if (statement_) {
	    cout << endl;
	  } else {
	    cout << " ;" << endl;
      }
	}

	SecType* oldpc = env.pc;
	// taint pc by the label of trigger event
    if (expr_.count() != 0) {
	    env.pc = new JoinType(env.pc, expr_[0]->expr()->typecheck(out, env.varsToType));
		for (unsigned idx = 1 ;  idx < expr_.count() ;  idx += 1)
		    env.pc = new JoinType(env.pc, expr_[idx]->expr()->typecheck(out, env.varsToType));
    }
    statement_->typecheck(out, env, pred);
    env.pc = oldpc;
}

void PForce::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PForce::check " << *lval_ << " = " << *expr_
	  << ";" << endl;
	}
	throw "PForce";
}

void PForever::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PForever::check " << endl;
	}
	throw "PForever";
//    statement_->typecheck(out, env);
}

void PForStatement::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PForStatement::check " << "for (" << *name1_ << " = " << *expr1_
	  << "; " << *cond_ << "; " << *name2_ << " = " << *expr2_ <<
	    ")" << endl;
	}
	throw "PForStatement";
//    statement_->typecheck(out, env);
}

// use a copy of env to avoid duplicated definitions
void PGenerate::typecheck(ostream&out, TypeEnv env, map<perm_string,Module*> modules)
{
	if (debug_typecheck) {
	   dump(cout, 0);
	}

	typecheck_parameters_(out, env);
    typecheck_localparams_(out, env);
    if (defparms.size()>0) {
    	cout << "PGenerate::defparms are ignored" << endl;
    }
    typecheck_events_(out, env);
	// Iterate through and display all the wires (including registers).
    typecheck_wires_(out, env);
    out << endl << "; assertions to be verified" << endl;

    for (list<PGate*>::const_iterator gate = gates.begin()
		 ; gate != gates.end() ;  gate++) {
    	PGAssign* pgassign = dynamic_cast<PGAssign*>(*gate);
    	PGModule* pgmodule = dynamic_cast<PGModule*>(*gate);

    	// make sure the parameters has same label as module declaration
    	if (pgmodule != NULL) {
    		pgmodule->typecheck(out, env, modules);
    	}
    	else if (pgassign != NULL) {
    		Predicate pred;
    		pgassign->typecheck(out, env, pred);
    	}
    }

    for (list<PProcess*>::const_iterator idx = behaviors.begin()
		 ; idx != behaviors.end() ;  idx++) {
	    (*idx)->typecheck(out, env);
    }

    for (list<AProcess*>::const_iterator idx = analog_behaviors.begin()
		 ; idx != analog_behaviors.end() ;  idx++) {
    	throw "AProcess";
    }

    typedef map<perm_string,LineInfo*>::const_iterator genvar_iter_t;
    for (genvar_iter_t cur = genvars.begin()
		 ; cur != genvars.end() ; cur++) {
	    throw "genvars";
    }

    for (list<PGenerate*>::const_iterator idx = generate_schemes.begin()
		 ; idx != generate_schemes.end() ;  idx++) {
	    (*idx)->typecheck(out, env, modules);
    }
}

void PNoop::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
		cout << "check PNoop " << endl;
	}
	throw "PNoop";
}

void PRelease::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
		cout << "PRelease::check " << *lval_ << ";" << endl;
	}
	throw "PRelease";
}

void PRepeat::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
		cout << "PRepeat::check (" << *expr_ << ")" << endl;
	}
	throw "PRepeat";
//    statement_->typecheck(out, env);
}

void PTrigger::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
		cout << "PTrigger::check" << "-> " << event_ << ";" << endl;
	}
	throw "PTrigger";
}

void PWhile::typecheck(ostream&out, TypeEnv& env, Predicate& pred) const
{
	if (debug_typecheck) {
      cout << "PWhile::check (" << *cond_ << ")" << endl;
	}
	throw "PWhile";
//    statement_->typecheck(out, env);
}

struct root_elem {
      Module *mod;
      NetScope *scope;
};

// output the encoding of a lattice with two lables HIGH and LOW
void output_lattice(ostream& out)
{
	out << "; this part encodes a partial order on labels" << endl;
    out << "(declare-sort Label)" << endl;
	out << "(declare-fun leq (Label Label) Bool)" << endl;
	out << "(declare-fun join (Label Label) Label)" << endl;
	out << "(declare-fun meet (Label Label) Label)" << endl;

	out << "(assert (forall ((x Label)) (leq x x)))" << endl;
	out << "(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x y) (leq y z)) (leq x z))))" << endl;
	out << "(assert (forall ((x Label) (y Label)) (implies (and (leq x y) (leq y x)) (= x y))))" << endl;

	out << endl << "; lattice elements" << endl;
	out << "(declare-fun LOW () Label)" << endl;
	out << "(declare-fun HIGH () Label)" << endl;
	out << "(declare-fun D1 () Label)" << endl;
	out << "(declare-fun D2 () Label)" << endl;

	out << endl << "; lattice structure" << endl;
	out << "(assert (forall ((x Label)) (leq LOW x)))" << endl;
	out << "(assert (forall ((x Label)) (leq x HIGH)))" << endl;
	out << "(assert (not (= HIGH LOW))) ; the lattice cannot clapse" << endl;
	out << "(assert (leq D1 D2))" << endl;
	out << "(assert (not (= LOW D1)))" << endl;
	out << "(assert (not (= LOW D2)))" << endl;

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
}

// output the encoding of a lattice with two lables HIGH and LOW
void output_type_families(ostream& out)
{
	// TODO: this should be declared in the source code
	out << endl << "; partition function" << endl;
	out << "(declare-fun Par (Int) Label)" << endl;
	out << "(assert (= (Par 0) LOW))" << endl;
	out << "(assert (= (Par 1) HIGH))" << endl;
	out << "(assert (= (Par 2) HIGH))" << endl;
	out << "(assert (= (Par 3) HIGH))" << endl;

	out << "(declare-fun Way (Int) Label)" << endl;
	out << "(assert (= (Way 0) LOW))" << endl;
	out << "(assert (= (Way 1) LOW))" << endl;
	out << "(assert (= (Way 2) HIGH))" << endl;
	out << "(assert (= (Way 3) HIGH))" << endl;

	out << "(declare-fun Domain (Int) Label)" << endl;
	out << "(assert (= (Domain 0) D1))" << endl;
	out << "(assert (= (Domain 1) D2))" << endl;
	out << "(assert (= (Domain 2) HIGH)) ; shouldn't be used" << endl;
	out << "(assert (= (Domain 3) HIGH))" << endl;

	if (check_write) {
		out << "(declare-fun BusPar (Int) Label)" << endl;
		out << "(assert (= (BusPar 0) (Par ReadLabel)))" << endl;
		out << "(assert (= (BusPar 1) HIGH))" << endl;
	}
}

/*
 * This function is the root of all type checking. The input is the list
 * of root module names. The function locates the Module definitions
 * for each root, does the type check
 * For now, this function only prints out the entire module.
 */
void typecheck(list<perm_string>roots, map<perm_string,Module*> modules)
{
      svector<root_elem*> root_elems(roots.size());
      int errors = 0;

	  // Scan the root modules by name, and output the name
      for (list<perm_string>::const_iterator root = roots.begin()
		 ; root != roots.end()
		 ; root++) {

	    // Look for the root module in the list.
	    map<perm_string,Module*>::const_iterator mod = pform_modules.find(*root);
	    if (mod == pform_modules.end()) {
		  cerr << "error: Unable to find the root module \""
		       << (*root) << "\" in the Verilog source." << endl;
		  cerr << "     : Perhaps ``-s " << (*root)
		       << "'' is incorrect?" << endl;
		  errors++;
		  continue;
	    }

	    // Get the module definition for this root instance.
	    Module *rmod = (*mod).second;

	    // type environment \G and assumptions \A for type checking
	    // typing rules have the form \G, \A |- C, where \G is a map from Verilog vars to types, and \A is a conjunction of predicates on PWire
	    map<perm_string, SecType*> *varsToType = new map<perm_string, SecType*>();
	    TypeEnv* env = new TypeEnv(*varsToType, ConstType::BOT, rmod);
	    // add invariant Way way == Par ReadLabel
	    SecType* way = new IndexType(perm_string::literal("Way"), perm_string::literal("way"));
	    SecType* dway = new IndexType(perm_string::literal("Way"), perm_string::literal("dWriteWay"));
	    SecType* iway = new IndexType(perm_string::literal("Way"), perm_string::literal("iWay"));
	    SecType* dsway = new IndexType(perm_string::literal("Way"), perm_string::literal("dStateWay"));
	    SecType* rlbl = new IndexType(perm_string::literal("Par"), perm_string::literal("ReadLabel"));
	    SecType* wlbl = new IndexType(perm_string::literal("Par"), perm_string::literal("WriteLabel"));
	    env->addInvariant(new Equality(way, rlbl));
	    env->addInvariant(new Equality(iway, rlbl));
	    env->addInvariant(new Equality(dway, dsway, true));
	    env->addInvariant(new Equality(dway, rlbl));
	    env->addInvariant(new Equality(rlbl, wlbl));

	    // Make the root scope. This makes a NetScope object and
	    // pushes it into the list of root scopes in the Design.
	    // NetScope*scope = des->make_root_scope(*root);
	    ofstream z3file;
	    z3file.open((string(rmod->mod_name().str())+".z3").c_str());
	    output_lattice(z3file);
	    try {
	      rmod->typecheck(z3file, *env, modules);
	    }
	    catch (char const* str) {
	      cerr << "Unimplemented " << str << endl;
	    }
	    z3file.close();

	    // Look for the root module in the list.
	    //for (map<perm_string,SecType*>::const_iterator iter = env->varsToType.begin(); iter != env->varsToType.end(); ++iter) {
	    //  cout << "@@@" << " " << (*iter).first << " " << *((*iter).second) << endl;
	    //}
      }
}
