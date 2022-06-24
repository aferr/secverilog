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

/*
 * The netlist types, as described in this header file, are intended
 * to be the output from elaboration of the source design. The design
 * can be passed around in this form to the various stages and design
 * processors.
 */
# include  <string>
# include  <sstream>
# include  "PExpr.h"
# include  "sectypes.h"

extern StringHeap lex_strings;
extern perm_string nextify_perm_string(perm_string s);

ConstType* ConstType::TOP = new ConstType(lex_strings.make("HIGH"));
ConstType* ConstType::BOT = new ConstType(lex_strings.make("LOW"));

ConstType::ConstType()
{
	name = lex_strings.make("LOW");
    // setBaseType(new ComType());
}

ConstType::ConstType(perm_string n)
{
	// currently, only support Low and High
	if (n == "Low" || n == "L")
		name = lex_strings.make("LOW");
	else if (n == "High" || n == "H")
		name = lex_strings.make("HIGH");
	else {
		name =n;
	}
}

ConstType::~ConstType()
{
}

bool ConstType::equals(SecType* st)
{
	ConstType* ct = dynamic_cast<ConstType*>(st);
	if (ct!=NULL) {
		return name == ct->name;
	}
	return false;
}

SecType* ConstType::freshVars(unsigned int lineno, map<perm_string, perm_string>& m)
{
	return this;
}
void SecType::emitFlowsTo(ostream&o, SecType* rhs) {
  JoinType* right_join = dynamic_cast<JoinType*>(rhs);
  MeetType* right_meet = dynamic_cast<MeetType*>(rhs);
  QuantType* right_quant = dynamic_cast<QuantType*>(rhs);
  PolicyType* right_policy = dynamic_cast<PolicyType*>(rhs);
  if (right_join) {
    o << "(or ";
    emitFlowsTo(o, right_join->getFirst());
    o << " ";
    emitFlowsTo(o, right_join->getSecond());
    o << ")";
    return;
  }
  if (right_meet) {
    o << "(and ";
    emitFlowsTo(o, right_join->getFirst());
    o << " ";
    emitFlowsTo(o, right_join->getSecond());
    o << ")";
    return;    
  }
  if (right_quant) {
    emitFlowsTo(o, right_quant->getInnerType());
    return;
  }
  if (right_policy) {
    emitFlowsTo(o, right_policy->get_lower());
    return;
  }
  o << "(leq " << *this << " " << *rhs << ")";
}

/* type variables */

VarType::VarType(perm_string varname)
{
	varname_ = varname;
}

VarType::~VarType()
{
}

VarType& VarType::operator= (const VarType& t)
{
	VarType* ret = new VarType(t.varname_);
	return *ret;
}

void VarType::set_type(perm_string varname)
{
	varname_ = varname;
}

perm_string VarType::get_type() const
{
	return varname_;
}

bool VarType::equals(SecType* st)
{
	VarType* vt = dynamic_cast<VarType*>(st);
	if (vt!=NULL) {
		return varname_ == vt->varname_;
	}
	return false;
}

SecType* VarType::freshVars(unsigned int lineno, map<perm_string, perm_string>& m)
{
	stringstream ss;
	ss << varname_ << lineno;
    const std::string* tmp = new string(ss.str());
	perm_string newname = perm_string::literal(tmp->c_str());
	m[varname_] = newname;
	return new VarType(newname);
}

bool VarType::hasExpr(perm_string str)
{
	return varname_ == str;
}

list<perm_string> rllist(1, perm_string::literal("ReadLabel"));
list<perm_string> wllist(1, perm_string::literal("WriteLabel"));
IndexType* IndexType::RL = new IndexType(perm_string::literal("Par"), rllist);
IndexType* IndexType::WL = new IndexType(perm_string::literal("Par"), wllist);

IndexType::IndexType(perm_string name, const list<perm_string>&exprs)
{
	name_ = name;
	exprs_ = exprs;
}

IndexType::~IndexType()
{
}

IndexType& IndexType::operator= (const IndexType& t)
{
	IndexType* ret = new IndexType(t.name_, t.exprs_);
	return *ret;
}

void IndexType::set_type(const perm_string name , list<perm_string>&exprs)
{
	name_ = name;
	exprs_ = exprs;
}

perm_string IndexType::get_name() const
{
	return name_;
}

list<perm_string> IndexType::get_exprs() const
{
	return exprs_;
}

SecType* IndexType::subst(perm_string e1, perm_string e2)
{
  list<perm_string> *substlist = new list<perm_string>;
  for (list<perm_string>::iterator it = exprs_.begin(); it != exprs_.end(); ++it){
    if (*it == e1) {
      substlist->push_back(e2);
    } else {
      substlist->push_back(*it);
    }
  }
  return new IndexType(name_, *substlist);
}

SecType* IndexType::subst(map<perm_string, perm_string> m)
{
  list<perm_string> *substlist = new list<perm_string>;
  for (list<perm_string>::iterator it = exprs_.begin(); it != exprs_.end(); ++it){
    map<perm_string, perm_string>::iterator ite = m.find(*it);    
    if (ite != m.end()) {
      substlist->push_back(ite->second);
    } else {
      substlist->push_back(*it);
    }
  }
  return new IndexType(name_, *substlist); 
}

SecType* IndexType::next_cycle(TypeEnv*env)
{
  list<perm_string> *nextlist = new list<perm_string>;
  for (list<perm_string>::iterator it = exprs_.begin(); it != exprs_.end(); ++it){
    BaseType* fv_base = env->varsToBase[*it];
    if (fv_base->isSeqType()) {
      nextlist->push_back(nextify_perm_string(*it));
    } else {
      nextlist->push_back(*it);
    }
  }
    return new IndexType(name_, *nextlist);
}

bool IndexType::equals(SecType* st)
{
	IndexType* it = dynamic_cast<IndexType*>(st);
	if (it!=NULL) {
		return name_ == it->name_ && exprs_ == it->exprs_;
	}
	return false;
}

bool isConstStr(perm_string s)
{
  const char* chars = s.str();
  int i=0;
  while (chars[i] != '\0') {
    if (chars[i] < '0' || chars[i] > '9') {
      return false;
    }
    i++;
  }
  return true;
}

void IndexType::collect_dep_expr(set<perm_string>& m)
{
  for (list<perm_string>::iterator it = exprs_.begin(); it != exprs_.end(); ++it){
    perm_string ex = *it;
    if (!isConstStr(ex)) {      
      m.insert(ex);
      // If this is a seqtype and so is its free variable, the next-cycle 
      // value of the label is the dependand      
      m.insert(nextify_perm_string(ex));
    }
  }
}

SecType* IndexType::freshVars(unsigned int lineno, map<perm_string, perm_string>& m)
{
  list<perm_string> *substlist = new list<perm_string>;
  for (list<perm_string>::iterator it = exprs_.begin(); it != exprs_.end(); ++it){
	stringstream ss;
	ss << *it << lineno;
	const std::string* tmp = new string(ss.str());
	perm_string newexpr = perm_string::literal(tmp->c_str());
	m[*it] = newexpr;
	substlist->push_back(newexpr);
  }
  return new IndexType(name_, *substlist);
}

bool IndexType::hasExpr(perm_string str)
{
  return (std::find(exprs_.begin(), exprs_.end(), str) != exprs_.end());
}

JoinType::JoinType(SecType* ty1, SecType* ty2)
{
	comp1_ = ty1;
	comp2_ = ty2;
}

JoinType::~JoinType()
{
}

void JoinType::emitFlowsTo(ostream&o, SecType* rhs) {
  o << "(and ";
  getFirst()->emitFlowsTo(o, rhs);
  o << " ";
  getSecond()->emitFlowsTo(o, rhs);
  o << ")";
}

SecType* JoinType::getFirst()
{
	return comp1_;
}

SecType* JoinType::getSecond()
{
	return comp2_;
}

SecType* JoinType::subst(perm_string e1, perm_string e2)
{
	SecType* comp1new = comp1_->subst(e1, e2);
	SecType* comp2new = comp2_->subst(e1, e2);
	if (comp1_!=comp1new || comp2_!=comp2new) {
		return new JoinType(comp1_->subst(e1, e2), comp2_->subst(e1, e2));
	}
	else return this;
}

SecType* JoinType::subst(map<perm_string, perm_string> m)
{
	SecType* comp1new = comp1_->subst(m);
	SecType* comp2new = comp2_->subst(m);
	if (comp1_ != comp1new || comp2_ != comp2new) {
		return new JoinType(comp1_->subst(m), comp2_->subst(m));
	} else
		return this;
}

SecType* JoinType::next_cycle(TypeEnv*env)
{
	SecType* comp1new = comp1_->next_cycle(env);
	SecType* comp2new = comp2_->next_cycle(env);
	if (comp1_ != comp1new || comp2_ != comp2new) {
		return new JoinType(comp1_->next_cycle(env), comp2_->next_cycle(env));
	} else
		return this;
}

JoinType& JoinType::operator= (const JoinType& t)
{
	JoinType* ret = new JoinType(t.comp1_, t.comp2_);
	return *ret;
}

SecType* JoinType::simplify()
{
	if (isBottom()) return ConstType::BOT;
	else if (isTop()) return ConstType::TOP;
	else {
		if (comp1_->isBottom())
			return comp2_->simplify();
		else if (comp2_->isBottom())
			return comp1_->simplify();
		else if (comp1_->hasBottom() || comp2_->hasBottom()) {
			if (comp1_->hasBottom()) comp1_ = comp1_->simplify();
			if (comp2_->hasBottom()) comp2_ = comp2_->simplify();
			return simplify();
		}
	}
	if (comp1_->equals(comp2_))
		return comp1_;
	else
		return this;
}

bool JoinType::equals(SecType* st)
{
	JoinType* ct = dynamic_cast<JoinType*>(st);
	if (ct!=NULL) {
		return comp1_->equals(ct->comp1_) && comp2_->equals(ct->comp2_);
	}
	return false;
}

void JoinType::collect_dep_expr(set<perm_string>& m)
{
	comp1_->collect_dep_expr(m);
	comp2_->collect_dep_expr(m);
}

SecType* JoinType::freshVars(unsigned int lineno, map<perm_string, perm_string>& m)
{
	return new JoinType(comp1_->freshVars(lineno, m), comp2_->freshVars(lineno, m));
}

bool JoinType::hasExpr(perm_string str)
{
	return comp1_->hasExpr(str) || comp2_->hasExpr(str);
}

MeetType::MeetType(SecType* ty1, SecType* ty2)
{
	comp1_ = ty1;
	comp2_ = ty2;
}

MeetType::~MeetType()
{
}

SecType* MeetType::getFirst()
{
	return comp1_;
}

SecType* MeetType::getSecond()
{
	return comp2_;
}

SecType* MeetType::subst(perm_string e1, perm_string e2)
{
	SecType* comp1new = comp1_->subst(e1, e2);
	SecType* comp2new = comp2_->subst(e1, e2);
	if (comp1_!=comp1new || comp2_!=comp2new)
		return new MeetType(comp1_->subst(e1, e2), comp2_->subst(e1, e2));
	else
		return this;
}

SecType* MeetType::subst(map<perm_string, perm_string> m)
{
	SecType* comp1new = comp1_->subst(m);
	SecType* comp2new = comp2_->subst(m);
	if (comp1_ != comp1new || comp2_ != comp2new)
		return new MeetType(comp1_->subst(m), comp2_->subst(m));
	else
		return this;
}

SecType* MeetType::next_cycle(TypeEnv*env)
{
	SecType* comp1new = comp1_->next_cycle(env);
	SecType* comp2new = comp2_->next_cycle(env);
	if (comp1_ != comp1new || comp2_ != comp2new)
		return new MeetType(comp1_->next_cycle(env), comp2_->next_cycle(env));
	else
		return this;
}

MeetType& MeetType::operator= (const MeetType& t)
{
	MeetType* ret = new MeetType(t.comp1_, t.comp2_);
	return *ret;
}

SecType* MeetType::simplify()
{
	if (isBottom()) return ConstType::BOT;
	else if (isTop()) return ConstType::TOP;
	else {
		if (comp1_->isTop())
			return comp2_->simplify();
		else if (comp2_->isTop())
			return comp1_->simplify();
		else if (comp1_->hasTop() || comp2_->hasTop()) {
			if (comp1_->hasTop()) comp1_ = comp1_->simplify();
			if (comp2_->hasTop()) comp2_ = comp2_->simplify();
			return simplify();
		}
	}
	if (comp1_->equals(comp2_))
		return comp1_;
	else
		return this;
}

bool MeetType::equals(SecType* st)
{
	MeetType* ct = dynamic_cast<MeetType*>(st);
	if (ct!=NULL) {
		return comp1_->equals(ct->comp1_) && comp2_->equals(ct->comp2_);
	}
	return false;
}

void MeetType::collect_dep_expr(set<perm_string>& m)
{
	comp1_->collect_dep_expr(m);
	comp2_->collect_dep_expr(m);
}

SecType* MeetType::freshVars(unsigned int lineno, map<perm_string, perm_string>& m)
{
	return new MeetType(comp1_->freshVars(lineno, m), comp2_->freshVars(lineno, m));
}

bool MeetType::hasExpr(perm_string str)
{
	return comp1_->hasExpr(str) || comp2_->hasExpr(str);
}
void MeetType::emitFlowsTo(ostream&o, SecType* rhs) {
  o << "(or ";
  getFirst()->emitFlowsTo(o, rhs);
  o << " ";
  getSecond()->emitFlowsTo(o, rhs);
  o << ")";
}

//---------------------------------------------
// QuantType
//---------------------------------------------
QuantType::QuantType(perm_string index_var, SecType *type)
{
  _index_var = index_var;
  _name = lex_strings.make("TODO");
  _sectype = type;
}

void QuantType::collect_dep_expr(set<perm_string>& m) {
  bool remove_quantvar = m.find(_index_var) == m.end();
  _sectype->collect_dep_expr(m);
  if (remove_quantvar) {
    std::set<perm_string>::iterator it = m.find(_index_var);
    if (it != m.end()) {
      m.erase(it);
      it = m.find(nextify_perm_string(_index_var));
      m.erase(it);
    }
  }
}
//----------------------------------------------
// Policy Type
//----------------------------------------------

PolicyType::PolicyType(SecType *lower,
		       perm_string cond_name, const list<perm_string>&static_exprs, const list<perm_string>&dynamic_exprs,
		       SecType *upper)
{
  _lower = lower;
  _cond_name = cond_name;
  _static = static_exprs;
  _dynamic = dynamic_exprs;
  _upper = upper;
}

SecType* PolicyType::next_cycle(TypeEnv*env)
{
  list<perm_string> *nextlist = new list<perm_string>;
  for (list<perm_string>::iterator it = _dynamic.begin(); it != _dynamic.end(); ++it){
    BaseType* fv_base = env->varsToBase[*it];
    if (fv_base->isSeqType()) {
      nextlist->push_back(nextify_perm_string(*it));
    } else {
      nextlist->push_back(*it);
    }
  }
  return new PolicyType(_lower->next_cycle(env), _cond_name, _static, *nextlist, _upper->next_cycle(env));
}

bool PolicyType::hasExpr(perm_string str) {
  return (std::find(_static.begin(), _static.end(), str) != _static.end())
    || (std::find(_dynamic.begin(), _dynamic.end(), str) != _dynamic.end())
    || _lower->hasExpr(str) || _upper->hasExpr(str);  
}

SecType* PolicyType::subst(perm_string e1, perm_string e2) {
  SecType* nlower = _lower->subst(e1, e2);
  SecType* nupper = _upper->subst(e1, e2);
  list<perm_string> *staticlist = new list<perm_string>;
  for (list<perm_string>::iterator it = _static.begin(); it != _static.end(); ++it){
    if (*it == e1) {
      staticlist->push_back(e2);
    } else {
      staticlist->push_back(*it);
    }
  }
  list<perm_string> *dynamiclist = new list<perm_string>;
  for (list<perm_string>::iterator it = _dynamic.begin(); it != _dynamic.end(); ++it){
    if (*it == e1) {
      dynamiclist->push_back(e2);
    } else {
      dynamiclist->push_back(*it);
    }
  }    
  return new PolicyType(nlower, _cond_name, *staticlist, *dynamiclist, nupper);
}

SecType* PolicyType::subst(map<perm_string, perm_string> m)
{
  SecType* nlower = _lower->subst(m);
  SecType* nupper = _upper->subst(m);  
  list<perm_string> *staticlist = new list<perm_string>;
  for (list<perm_string>::iterator it = _static.begin(); it != _static.end(); ++it){
    map<perm_string, perm_string>::iterator ite = m.find(*it);    
    if (ite != m.end()) {
      staticlist->push_back(ite->second);
    } else {
      staticlist->push_back(*it);
    }
  }
  list<perm_string> *dynamiclist = new list<perm_string>;
  for (list<perm_string>::iterator it = _dynamic.begin(); it != _dynamic.end(); ++it){
    map<perm_string, perm_string>::iterator ite = m.find(*it);    
    if (ite != m.end()) {
      dynamiclist->push_back(ite->second);
    } else {
      dynamiclist->push_back(*it);
    }
  }
  return new PolicyType(nlower, _cond_name, *staticlist, *dynamiclist, nupper);
}
void PolicyType::collect_dep_expr(set<perm_string>& m)
{
  _lower->collect_dep_expr(m);
  _upper->collect_dep_expr(m);
  for (list<perm_string>::iterator it = _static.begin(); it != _static.end(); ++it){
    perm_string ex = *it;
    if (!isConstStr(ex)) {      
      m.insert(ex);
      // If this is a seqtype and so is its free variable, the next-cycle 
      // value of the label is the dependand      
      m.insert(nextify_perm_string(ex));
    }
  }
  for (list<perm_string>::iterator it = _dynamic.begin(); it != _dynamic.end(); ++it){
    perm_string ex = *it;
    if (!isConstStr(ex)) {      
      m.insert(ex);
      // If this is a seqtype and so is its free variable, the next-cycle 
      // value of the label is the dependand      
      m.insert(nextify_perm_string(ex));
    }
  }  
}
void PolicyType::emitFlowsTo(ostream&o, SecType* rhs) {
  PolicyType* right_policy = dynamic_cast<PolicyType*>(rhs);
  ConstType* right_const = dynamic_cast<ConstType*>(rhs);
  VarType* right_var = dynamic_cast<VarType*>(rhs);
  IndexType* right_index = dynamic_cast<IndexType*>(rhs);
  if (right_const || right_var || right_index) {
    get_upper()->emitFlowsTo(o, rhs);
    return;
  }
  if (right_policy) {
    o << "(and ";
    get_lower()->emitFlowsTo(o, right_policy->get_lower());
    o << " ";
    get_upper()->emitFlowsTo(o, right_policy->get_upper());
    o << ")"; //TODO the condition implication part
    return;
  }
  //else do super class behavior
  SecType::emitFlowsTo(o, rhs);

}
////////////////////////////

Hypothesis* Hypothesis::subst(map<perm_string, perm_string> m)
{
	return new Hypothesis(bexpr_->subst(m));
}

bool Hypothesis::matches (perm_string name)
{
	return bexpr_->contains_expr(name);
}

TypeEnv& TypeEnv::operator= (const TypeEnv& e)
{
	TypeEnv* ret = new TypeEnv(e);
	return *ret;
}

Predicate& Predicate::operator= (const Predicate& p)
{
	Predicate* ret = new Predicate();
	ret->hypotheses = p.hypotheses;
	return *ret;
}

Predicate* Predicate::subst(map<perm_string, perm_string> m)
{
	Predicate* ret = new Predicate();
	for (set<Hypothesis*>::iterator ite = hypotheses.begin(); ite != hypotheses.end(); ite ++) {
		ret->hypotheses.insert(new Hypothesis((*ite)->bexpr_->subst(m)));
	}
	return ret;
}

Equality* Equality::subst(map<perm_string, perm_string> m)
{
	Equality* ret = new Equality(left->subst(m), right->subst(m), isleq);
	return ret;
}

void Equality::dump(ostream&out) const
{
	if (isleq)
      out << "leq " << *left << " " << *right;
	else
      out << "= " << *left << " " << *right;
}
