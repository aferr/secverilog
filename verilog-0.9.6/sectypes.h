#ifndef __sectypes_H
#define __sectypes_H
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
 * Security types has the following syntax
 *
 * Basic types ::= High | Low (extend this later)
 * Type vars ::= \alpha
 * Type family (IndexType) ::= f, functions from expressions to types
 * Type ::= Basic types | Type vars | (Type family) e
 *
 * Type environment:
 * \Gamma: vars --> Type
 * \Assumptions: predicates over expressions
 */
# include  <set>
# include  <string>
# include  "StringHeap.h"

class SecType;
class ConstType;
class VarType;
class JoinType;
class IndexType;
struct TypeEnv;

class SecType {

	// Manipulate the types.
    public:
      virtual void dump(ostream&o) {}
      virtual bool hasBottom() {return false;}
      virtual bool isBottom() {return false;}
      virtual bool hasTop() {return false;}
      virtual bool isTop() {return false;};
      virtual SecType* simplify() {return this;}
      virtual bool equals(SecType* st) {return false;}
      virtual SecType* subst(perm_string e1, perm_string e2) {return this;};
      virtual SecType* subst(map<perm_string, perm_string> m) {return this;};
      virtual void collect_dep_expr(set<perm_string>& m) {};
      virtual bool hasExpr(perm_string str) {return false;};
      virtual SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m) {return this;};
    //  BasicType& operator= (const BasicType&);
};

class ConstType : public SecType {

public:

	ConstType();
	ConstType(perm_string name);
	~ConstType();
	void dump(ostream&o) {
		o << name;
	}
	bool hasBottom() {
		return name == "LOW";
	}
	bool hasTop() {
		return name == "HIGH";
	}
	bool isBottom() {
		return name == "LOW";
	}
	bool isTop() {
		return name == "HIGH";
	}
	bool equals(SecType* st);
	SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m);

public:
  static ConstType* TOP;
  static ConstType* BOT;

private:
	perm_string name;
};

/* type variables */
class VarType : public SecType {

    public:
      VarType(perm_string varname);
      ~VarType();
      VarType& operator= (const VarType&);

    public:
	// Manipulate the types.
      void set_type(perm_string varname);
      perm_string get_type() const;
      bool equals(SecType* st);
      SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m);
      bool hasExpr(perm_string str);

    private:
      perm_string varname_;
};

/* Dynamic type */
class IndexType : public SecType {

    public:
	  IndexType(perm_string name, perm_string expr);
      ~IndexType();
      IndexType& operator= (const IndexType&);
      void dump(ostream&o) {
      	o << "(" << name_ << " " << expr_ << ")";
      }
      bool equals(SecType* st);

    public:
	// Manipulate the types.
      void set_type(const perm_string name , perm_string expr);
      perm_string get_name() const;
      perm_string get_expr() const;
      SecType* subst(perm_string e1, perm_string e2);
      SecType* subst(map<perm_string, perm_string> m);
      void collect_dep_expr(set<perm_string>& m);
      SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m);
      bool hasExpr(perm_string str);

    public:
      static IndexType* RL;
      static IndexType* WL;

    private:
      perm_string name_;
      perm_string expr_;
};

/* a CompType can be a join/meet of CompTypes */
class JoinType : public SecType {

    public:
	  JoinType(SecType*, SecType*);
      ~JoinType();
      JoinType& operator= (const JoinType&);
      void dump(ostream&o) {
          o << "(join ";
          comp1_->dump(o);
          o << " ";
          comp2_->dump(o);
          o << ")";
      }
      SecType* getFirst();
      SecType* getSecond();

      bool hasBottom() {return comp1_->hasBottom() || comp2_->hasBottom();}
      bool isBottom() {return comp1_->isBottom() && comp2_->isBottom();}
      bool hasTop() {return comp1_->hasTop() || comp2_->hasTop();}
      bool isTop() {return comp1_->isTop() || comp2_->isTop();}
      SecType* simplify();
      bool equals(SecType* st);
      SecType* subst(perm_string e1, perm_string e2);
      SecType* subst(map<perm_string, perm_string> m);
      void collect_dep_expr(set<perm_string>& m);
      SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m);
      bool hasExpr(perm_string str);

    private:
	  SecType* comp1_;
	  SecType* comp2_;
};

class MeetType : public SecType {

    public:
	  MeetType(SecType*, SecType*);
      ~MeetType();
      MeetType& operator= (const MeetType&);
      void dump(ostream&o) {
          o << "(meet ";
          comp1_->dump(o);
          o << " ";
          comp2_->dump(o);
          o << ")";
      }
      SecType* getFirst();
      SecType* getSecond();

      bool hasBottom() {return comp1_->hasBottom() || comp2_->hasBottom();}
      bool isBottom() {return comp1_->isBottom() || comp2_->isBottom();}
      bool hasTop() {return comp1_->hasTop() || comp2_->hasTop();}
      bool isTop() {return comp1_->isTop() && comp2_->isTop();}
      SecType* simplify();
      bool equals(SecType* st);
      SecType* subst(perm_string e1, perm_string e2);
      SecType* subst(map<perm_string, perm_string> m);
      void collect_dep_expr(set<perm_string>& m);
      SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m);
      bool hasExpr(perm_string str);

    private:
	  SecType* comp1_;
	  SecType* comp2_;
};

/**
 * An equality expression
 */
struct Hypothesis {
	PExpr* bexpr_;

	Hypothesis(PExpr* l, PExpr* r) {
		bexpr_ = new PEBComp('e', l, r);
	}

	Hypothesis(PExpr* bexpr) {
		bexpr_ = bexpr;
	}

	Hypothesis* subst(map<perm_string, perm_string> m);

	bool matches (perm_string name);
};

class HypothesisComparator
{
public:
    bool operator()(const Hypothesis* h1, const Hypothesis* h2)
    {
        return h1->bexpr_->get_name() < h2->bexpr_->get_name();
    }
};

struct Predicate {
	set<Hypothesis*> hypotheses;

    Predicate& operator= (const Predicate&);
	Predicate* subst (map<perm_string, perm_string> m);
};

struct Equality {
	SecType* left;
	SecType* right;
	bool isleq;

	Equality(SecType* l, SecType* r, bool leq = false) {
		left = l;
		right = r;
		isleq = leq;
	}

	void dump(ostream&out) const;
	Equality* subst(map<perm_string, perm_string> m);
};

struct Invariant {
	set<Equality*> invariants;
};

struct TypeEnv {
	map<perm_string, SecType*> varsToType;
	SecType* pc;
    set<perm_string> dep_exprs; // a list of expressions where a dependent type may depend on
    set<perm_string> aliveVars;
    Invariant* invariants;
    Module* module;

	TypeEnv(map<perm_string, SecType*>& m, SecType* pclabel, Module* modu) {
		varsToType = m;
		pc = pclabel;
		module = modu;
		invariants = new Invariant();
	}

	void addInvariant(Equality* inv) {
		invariants->invariants.insert(inv);
	}

    TypeEnv& operator= (const TypeEnv&);
};


struct Constraint {
	SecType* left;
	SecType* right;
	Predicate* pred;
	Invariant* invariant;

	Constraint(SecType* l, SecType* r, Invariant* inv, Predicate* p) {
		left = l;
		right = r;
		pred = p;
		invariant = inv;
	}
};

inline ostream& operator << (ostream&o, SecType&t)
{
	t.dump(o);
    return o;
}


inline ostream& operator << (ostream&o, Predicate& pred)
{
	set<Hypothesis*> l = pred.hypotheses;
	set<Hypothesis*>::iterator i = l.begin();
	if (i != l.end()) {
		o << "(";
		(*i)->bexpr_->dump(o);
		o << ")";
		i++;
	}
	for (; i != l.end() ; i++) {
		o << " ("; (*i)->bexpr_->dump(o); o << ")";
	}
	return o;
}

inline ostream& operator << (ostream&o, Invariant& invs)
{
	set<Equality*> l = invs.invariants;
	set<Equality*>::iterator i = l.begin();
	if (i != l.end()) {
		o << "(";
		(*i)->dump(o);
		o << ")";
		i++;
	}
	for (; i != l.end() ; i++) {
		o << " ("; (*i)->dump(o); o << ")";
	}
	return o;
}

inline ostream& operator << (ostream&o, Constraint&c)
{
	o << "(assert ";
	bool hashypo = c.pred != NULL && c.pred->hypotheses.size() != 0;
	bool hasinv = c.invariant != NULL && c.invariant->invariants.size() != 0;;

	if (hashypo || hasinv)
		o << "(and ";
	if (hashypo)
		o << (*c.pred) << " ";
	if (hasinv)
		o << (*c.invariant);
	o << " (not(leq " << *(c.right->simplify()) << "  "
					<< *(c.left->simplify()) << ")))";
	if (hashypo || hasinv)
		o << ")";
    return o;
}

#endif
