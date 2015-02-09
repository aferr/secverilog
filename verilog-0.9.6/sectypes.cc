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

ConstType* ConstType::TOP = new ConstType(lex_strings.make("HIGH"));
ConstType* ConstType::BOT = new ConstType(lex_strings.make("LOW"));

ConstType::ConstType()
{
	name = lex_strings.make("LOW");
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

IndexType* IndexType::RL = new IndexType(perm_string::literal("Par"), perm_string::literal("ReadLabel"));
IndexType* IndexType::WL = new IndexType(perm_string::literal("Par"), perm_string::literal("WriteLabel"));

IndexType::IndexType(perm_string name, perm_string expr)
{
	name_ = name;
	expr_ = expr;
}

IndexType::~IndexType()
{
}

IndexType& IndexType::operator= (const IndexType& t)
{
	IndexType* ret =  new IndexType(t.name_, t.expr_);
	return *ret;
}

void IndexType::set_type(const perm_string name , perm_string expr)
{
	name_ = name;
	expr_ = expr;
}

perm_string IndexType::get_name() const
{
	return name_;
}

perm_string IndexType::get_expr() const
{
	return expr_;
}

SecType* IndexType::subst(perm_string e1, perm_string e2)
{
	if (expr_ == e1)
		return new IndexType(name_, e2);
	else
		return this;
}

SecType* IndexType::subst(map<perm_string, perm_string> m)
{
	map<perm_string, perm_string>::iterator ite = m.find(expr_);
	if (ite != m.end())
		return subst((*ite).first, (*ite).second);
	else
		return this;
}

bool IndexType::equals(SecType* st)
{
	IndexType* it = dynamic_cast<IndexType*>(st);
	if (it!=NULL) {
		return name_ == it->name_ && expr_ == it->expr_;
	}
	return false;
}

void IndexType::collect_dep_expr(set<perm_string>& m)
{
	// expr_ might be replaced with a constant in a substitution. In this case, do not return expr_
	const char* chars = expr_.str();
	int i=0;
	bool succ = true;
	while (chars[i] != '\0') {
		if (chars[i] < '0' || chars[i] > '9') {
			succ = false;
			break;
		}
		i++;
	}
	if (!succ)
		m.insert(expr_);
}

SecType* IndexType::freshVars(unsigned int lineno, map<perm_string, perm_string>& m)
{
	stringstream ss;
	ss << expr_ << lineno;
    const std::string* tmp = new string(ss.str());
	perm_string newexpr = perm_string::literal(tmp->c_str());
	m[expr_] = newexpr;
	return new IndexType(name_, newexpr);
}

bool IndexType::hasExpr(perm_string str)
{
	return expr_ == str;
}

JoinType::JoinType(SecType* ty1, SecType* ty2)
{
	comp1_ = ty1;
	comp2_ = ty2;
}

JoinType::~JoinType()
{
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
