/*
 * Copyright (c) 1998-2008,2011 Stephen Williams <steve@icarus.com>
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

#include <cassert>
#include <iostream>
#include <sstream>
#include <typeinfo>

//#include "compiler.h"
//#include "config.h"
#include "ivl_target.h"
//#include "Module.h"
#include "netmisc.h"
#include "svector.h"
#include "Statement.h"
#include "StringHeap.h"
#include "verireal.h"

PExpr::PExpr()
{
      expr_type_ = IVL_VT_NO_TYPE;
}

PExpr::~PExpr()
{
}

bool PExpr::has_aa_term(Design*, NetScope*) const
{
      return false;
}

bool PExpr::is_the_same(const PExpr*that) const
{
      return typeid(this) == typeid(that);
}

const perm_string PExpr::get_name() const
{
	stringstream ss;
    dump(ss);
    const std::string* tmp = new string(ss.str());
    return perm_string::literal(tmp->c_str());
}

NetNet* PExpr::elaborate_lnet(Design*des, NetScope*) const
{
      cerr << get_fileline() << ": error: expression not valid in assign l-value: "
	   << *this << endl;
      return 0;
}

NetNet* PExpr::elaborate_bi_net(Design*des, NetScope*) const
{
      cerr << get_fileline() << ": error: "
	   << "expression not valid as argument to inout port: "
	   << *this << endl;
      return 0;
}

bool PExpr::is_collapsible_net(Design*, NetScope*) const
{
      return false;
}

PEBinary::PEBinary(char op, PExpr*l, PExpr*r)
: op_(op), left_(l), right_(r)
{
}

PEBinary::~PEBinary()
{
}

bool PEBinary::has_aa_term(Design*des, NetScope*scope) const
{
      assert(left_ && right_);
      return left_->has_aa_term(des, scope) || right_->has_aa_term(des, scope);
}

bool PEBinary::contains_expr(perm_string that)
{
    assert(left_ && right_);
	return left_->contains_expr(that) || right_->contains_expr(that);
}

bool PEBinary::is_wellformed(set<perm_string> s)
{
	// the following operators are supported:
	// 'e': equlity =
	// '|': or
	// 'a': and
	// 'L' : leq
	// 'n' : !=
	if (op_ == 'e' || op_ == 'o' || op_ == 'L' || op_ == 'n')
		return left_->is_wellformed(s) && right_->is_wellformed(s);
	if (op_ == 'a')
		return left_->is_wellformed(s) || right_->is_wellformed(s);
	else
		return false;
}

PExpr* PEBinary::to_wellformed(set<perm_string> s)
{
	if (op_ == 'e' || op_ == 'o' || op_ == 'L' || op_ == 'n') {
		if (left_->is_wellformed(s) && right_->is_wellformed(s))
			return new PEBinary(op_, left_->to_wellformed(s), right_->to_wellformed(s));
	}
	if (op_ == 'a') {
		if (left_->is_wellformed(s) && right_->is_wellformed(s))
			return new PEBinary(op_, left_->to_wellformed(s), right_->to_wellformed(s));
		else if (left_->is_wellformed(s))
			return left_->to_wellformed(s);
		else if (right_->is_wellformed(s))
			return right_->to_wellformed(s);
	}
	return NULL;
}

bool PEBinary::is_neg_wellformed(set<perm_string> s)
{
	// the following operators are supported:
	// 'e': equlity =
	// '|': or
	// 'a': and
	// 'L' : leq
	// 'n' : !=
	if (op_ == 'e' || op_ == 'a' || op_ == 'L' || op_ == 'n')
		return left_->is_neg_wellformed(s) && right_->is_neg_wellformed(s);
	if (op_ == 'o')
		return left_->is_neg_wellformed(s) || right_->is_neg_wellformed(s);
	else
		return false;
}

PExpr* PEBinary::neg_to_wellformed(set<perm_string> s)
{
	if (op_ == 'e' || op_ == 'a' || op_ == 'L' || op_ == 'n') {
		if (left_->is_neg_wellformed(s) && right_->is_neg_wellformed(s))
			return new PEBinary(op_, left_->neg_to_wellformed(s), right_->neg_to_wellformed(s));
	}
	if (op_ == 'o') {
		if (left_->is_neg_wellformed(s) && right_->is_neg_wellformed(s))
			return new PEBinary(op_, left_->neg_to_wellformed(s), right_->neg_to_wellformed(s));
		else if (left_->is_neg_wellformed(s))
			return left_->neg_to_wellformed(s);
		else if (right_->is_neg_wellformed(s))
			return right_->neg_to_wellformed(s);
	}
	return NULL;
}

PExpr* PEBinary::subst(map<perm_string, perm_string> m)
{
	return new PEBinary(op_, left_->subst(m), right_->subst(m));
}

PEBComp::PEBComp(char op, PExpr*l, PExpr*r)
: PEBinary(op, l, r)
{
      left_width_ = 0;
      right_width_ = 0;
}

PEBComp::~PEBComp()
{
}

PEBLogic::PEBLogic(char op, PExpr*l, PExpr*r)
: PEBinary(op, l, r)
{
      assert(op == 'a' || op == 'o');
}

PEBLogic::~PEBLogic()
{
}

PEBLeftWidth::PEBLeftWidth(char op, PExpr*l, PExpr*r)
: PEBinary(op, l, r)
{
}

PEBLeftWidth::~PEBLeftWidth()
{
}

PEBPower::PEBPower(char op, PExpr*l, PExpr*r)
: PEBLeftWidth(op, l, r)
{
}

PEBPower::~PEBPower()
{
}

PEBShift::PEBShift(char op, PExpr*l, PExpr*r)
: PEBLeftWidth(op, l, r)
{
}

PEBShift::~PEBShift()
{
}

PECallFunction::PECallFunction(const pform_name_t&n, const vector<PExpr *> &parms)
: path_(n), parms_(parms)
{
}

static pform_name_t pn_from_ps(perm_string n)
{
      name_component_t tmp_name (n);
      pform_name_t tmp;
      tmp.push_back(tmp_name);
      return tmp;
}

PECallFunction::PECallFunction(perm_string n, const vector<PExpr*>&parms)
: path_(pn_from_ps(n)), parms_(parms)
{
}

PECallFunction::PECallFunction(perm_string n)
: path_(pn_from_ps(n))
{
}

// NOTE: Anachronism. Try to work all use of svector out.
PECallFunction::PECallFunction(const pform_name_t&n, const svector<PExpr *> &parms)
: path_(n), parms_(vector_from_svector(parms))
{
}

PECallFunction::PECallFunction(perm_string n, const svector<PExpr*>&parms)
: path_(pn_from_ps(n)), parms_(vector_from_svector(parms))
{
}

PECallFunction::~PECallFunction()
{
}

bool PECallFunction::has_aa_term(Design*des, NetScope*scope) const
{
      bool flag = false;
      for (unsigned idx = 0 ; idx < parms_.size() ; idx += 1) {
	    flag = parms_[idx]->has_aa_term(des, scope) || flag;
      }
      return flag;
}

PEConcat::PEConcat(const svector<PExpr*>&p, PExpr*r)
: parms_(p), tested_widths_(p.count()), repeat_(r)
{
}

PEConcat::~PEConcat()
{
      delete repeat_;
}

bool PEConcat::has_aa_term(Design*des, NetScope*scope) const
{
      bool flag = false;
      for (unsigned idx = 0 ; idx < parms_.count() ; idx += 1) {
	    flag = parms_[idx]->has_aa_term(des, scope) || flag;
      }
      if (repeat_)
            flag = repeat_->has_aa_term(des, scope) || flag;

      return flag;
}

PEEvent::PEEvent(PEEvent::edge_t t, PExpr*e)
: type_(t), expr_(e)
{
}

PEEvent::~PEEvent()
{
}

PEEvent::edge_t PEEvent::type() const
{
      return type_;
}

bool PEEvent::has_aa_term(Design*des, NetScope*scope) const
{
      assert(expr_);
      return expr_->has_aa_term(des, scope);
}

PExpr* PEEvent::expr() const
{
      return expr_;
}

PEFNumber::PEFNumber(verireal*v)
: value_(v)
{
}

PEFNumber::~PEFNumber()
{
      delete value_;
}

const verireal& PEFNumber::value() const
{
      return *value_;
}

PEIdent::PEIdent(const pform_name_t&that)
: path_(that)
{
}

PEIdent::PEIdent(perm_string s)
{
      path_.push_back(name_component_t(s));
}

PEIdent::~PEIdent()
{
}

bool PEIdent::has_aa_term(Design*des, NetScope*scope) const
{
      NetNet*       net = 0;
      const NetExpr*par = 0;
      NetEvent*     eve = 0;

      const NetExpr*ex1, *ex2;

      scope = symbol_search(0, des, scope, path_, net, par, eve, ex1, ex2);

      if (scope)
            return scope->is_auto();
      else
            return false;
}

bool PEIdent::is_wellformed(set<perm_string> s)
{
	std::set<perm_string>::iterator ite = s.find(get_name());
	if (ite != s.end())
		return true;
	else
		return false;
}

PExpr* PEIdent::to_wellformed(set<perm_string> s)
{
	std::set<perm_string>::iterator ite = s.find(get_name());
	if (ite != s.end())
		return this;
	else
		return NULL;
}

PExpr* PEIdent::subst(map<perm_string, perm_string> m)
{
	map<perm_string, perm_string>::iterator ite = m.find(get_name());
	if (ite == m.end())
		return this;
	else
		return new PEIdent((*ite).second);
}

PENumber::PENumber(verinum*vp)
: value_(vp)
{
      assert(vp);
}

PENumber::~PENumber()
{
      delete value_;
}

const verinum& PENumber::value() const
{
      return *value_;
}

bool PENumber::is_the_same(const PExpr*that) const
{
      const PENumber*obj = dynamic_cast<const PENumber*>(that);
      if (obj == 0)
	    return false;

      return *value_ == *obj->value_;
}

bool PENumber::is_wellformed(set<perm_string> s)
{
	return true;
}

PExpr* PENumber::to_wellformed(set<perm_string> s)
{
	return this;
}

PEString::PEString(char*s)
: text_(s)
{
}

PEString::~PEString()
{
      delete[]text_;
}

string PEString::value() const
{
      return text_;
}

PETernary::PETernary(PExpr*e, PExpr*t, PExpr*f)
: expr_(e), tru_(t), fal_(f)
{
}

PETernary::~PETernary()
{
}

bool PETernary::has_aa_term(Design*des, NetScope*scope) const
{
      assert(expr_ && tru_ && fal_);
      return expr_->has_aa_term(des, scope)
           || tru_->has_aa_term(des, scope)
           || fal_->has_aa_term(des, scope);
}

// this method translates a PETernary to a if-then-else statement
PCondit* PETernary::translate (PExpr* lhs)
{
	Statement *s1, *s2;
	PETernary* test = dynamic_cast<PETernary*>(tru_);
	if (test == NULL) {
		s1 = new PAssign(lhs, tru_);
		s1->set_file(get_file());
		s1->set_lineno(get_lineno());
	}
	else
		s1 = test->translate(lhs);
	test = dynamic_cast<PETernary*>(fal_);
	if (test == NULL) {
		s2 = new PAssign(lhs, fal_);
		s2->set_file(get_file());
		s2->set_lineno(get_lineno());
	}
	else
		s2 = test->translate(lhs);
	PCondit* ret = new PCondit(expr_, s1, s2);
	ret->set_file(get_file());
	ret->set_lineno(get_lineno());
	return ret;
}

PEUnary::PEUnary(char op, PExpr*ex)
: op_(op), expr_(ex)
{
}

PEUnary::~PEUnary()
{
}

bool PEUnary::has_aa_term(Design*des, NetScope*scope) const
{
      assert(expr_);
      return expr_->has_aa_term(des, scope);
}

bool PEUnary::contains_expr(perm_string that)
{
	return expr_->contains_expr(that);
}

bool PEUnary::is_wellformed(set<perm_string> s)
{
	// only "not" is translated
	return op_ == 'N';
}

PExpr* PEUnary::to_wellformed(set<perm_string> s)
{
	if (op_ == 'N')
		return this;
	else
		return NULL;
}

PExpr* PEUnary::subst(map<perm_string, perm_string> m)
{
	return new PEUnary(op_, expr_->subst(m));
}
