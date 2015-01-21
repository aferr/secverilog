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
 * Type family ::= Par
 * Kind of Par : PWire -> Basic types
 * Type ::= Basic types | Type vars | (Type family) e
 *
 * Type environment:
 * \Gamma: vars --> Type
 * \Assumptions: predicates over expressions
 */
# include  <set>
# include  <string>
# include  "StringHeap.h"
# include "PExpr.h"
# include <sstream>
# include <stdio.h>

class SecType;
class ConstType;
class VarType;
class JoinType;
class IndexType;
struct TypeEnv;
struct CNF;

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
      virtual SecType* apply_index(PExpr *e) { return this; }
      // Upper and lower bounds for quantification. NULL unless has_bounds()
      unsigned long upper;
      unsigned long lower;
      virtual bool has_bounds() { return false; }
      virtual void set_range(PExpr* u, PExpr* l) {}
      perm_string index_var;

     
      //Apply a copy of this type with n as the name for the functiond def. 
      virtual SecType* give_name(std::string n){return this;}
      virtual bool has_defs() { return false; }
      virtual const char * func_def_string() { return ""; }
    
    //  BasicType& operator= (const BasicType&);
};

/* for now, only support two types: L and H */
class ConstType : public SecType {

    public:
      enum TYPES { LOW, HIGH, D1, D2 };

      ConstType();
      ConstType(TYPES t);
      ConstType(perm_string name);
      ~ConstType();
      ConstType& operator= (const ConstType&);
      void dump(ostream&o) {
    	if (type_ == LOW)
    	  o << "LOW";
    	else if (type_ == HIGH)
    	  o << "HIGH";
	    else if (type_ == D1)
	      o << "D1";
	    else if (type_ == D2)
	      o << "D2";
      }
      bool hasBottom() {return type_ == LOW;}
      bool hasTop() {return type_ == HIGH;}
      bool isBottom() {return type_ == LOW;}
      bool isTop() {return type_ == HIGH;}
      bool equals(SecType* st);
      SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m);

    public:
	// Manipulate the types.
      void set_type(TYPES t);
      TYPES get_type() const;

    public:
      static ConstType* TOP;
      static ConstType* BOT;

    private:
      TYPES type_;
};

//-----------------------------------------------------------------------------
// QuantType
//-----------------------------------------------------------------------------
// This type is applied to arrays and acts as a mapping from array elements to 
// types. Syntactically, it specifies an index variable and an expression 
// (possibly) containing that index variable and that evaluates to a type.

class LabelFunc {
    public:
        perm_string label;
        LabelFunc(perm_string l) :
            label(l){};
};

class QuantType : public SecType {
  public:
    QuantType(perm_string index_var, LabelFunc *e);
    ~QuantType();
    // Set upper/lower_bound from the associated array. This is meant to be
    // called by the parent during type checking. This makes it easier to avoid 
    // re-writing the ranges of the array. This will likely require a virtual 
    // set_range in SecType that does nothing and is only overwritten in this 
    // class.
    void set_range(PExpr* u, PExpr* l){
        PENumber* pu = dynamic_cast<PENumber*>(u);
        PENumber* pl = dynamic_cast<PENumber*>(l);
        if( pu == NULL || pl == NULL){
            fprintf(stderr, "error, only constant array bound declarations"
                    " are currently allowed\n");
            exit(1);
        } else {
            unsigned long vu = pu->value().as_ulong();
            unsigned long vl = pl->value().as_ulong();
            if(vu >= vl){ upper = vu; lower = vl; }
            else {upper = vl; lower = vu; }
        }
    }

    virtual bool has_bounds(){return true;}
    virtual bool has_defs(){return true;}

    void dump(ostream&o){
        o << "(" << name.c_str() << " " << index_var.str() << ")";
    }


  public:
    // Connect the indexing expression to the general quantified label to get 
    // the label at the indexing expression.
    SecType* apply_index(PExpr* e);
    bool equals(SecType* st);
 
    SecType * give_name(std::string n){
      QuantType *t = deep_copy();
      t->name = n;
      return t;
    }
  
    const char * func_def_string(){ 
        std::stringstream ss;
        ss.str("");
        //TODO body should be derived from e (third line)
        ss <<   "(declare-fun " << name.c_str() << " (Int) Label)" <<
        endl << "(assert (forall ((x Int))" <<
        endl << "    (= (" << name.c_str() << " x)(Par x))" <<
        endl << "))";
        return ss.str().c_str(); 
    }
 
  private:
    // Index var to be replaced with indexing expression
    // perm_string index_var;
    LabelFunc *expr;
    // Name for declared function.
    std::string name;

    QuantType * deep_copy(){
        QuantType *t = new QuantType(index_var, expr);
        t->lower = lower;
        t->upper = upper;
        t->index_var = index_var;
        t->expr = expr;
        return t;
    }



  //These methods are for development only
  private:
    SecType* apply_index_penumber(PENumber* e);

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

/* type variables */
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

struct CNF {
    list<list<SecType> > cnf_type_;

    CNF& operator= (const CNF&);
    CNF& append (const CNF&);
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
//-----------------------------------------------------------------------------
// Quantified  Type Constraints
//-----------------------------------------------------------------------------
struct QBound{
    unsigned long lower;
    unsigned long upper;
    perm_string qvar;
    QBound(unsigned long u, unsigned long l, perm_string v) :
        lower(l), upper(u), qvar(v) {}
};

struct QBounds{
    set<QBound*> bounds;
};

struct QFuncDefs{
    set<SecType*> defs;
};

inline ostream& operator << (ostream &o, QBound& b){
    o << "(>= "<<b.qvar<<" "<<b.lower<<")(<= "<<b.qvar<<" "<<b.upper<<")";
    return o;
}

struct Constraint {
	SecType* left;
	SecType* right;
	Predicate* pred;
	Invariant* invariant;
    QFuncDefs* def;
    QBounds* bound;

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

inline const char* constraint_inner(Constraint&c)
{
  std::stringstream o;
  o.str("");
    
  bool hashypo = c.pred != NULL && c.pred->hypotheses.size() != 0;
    bool hasinv = c.invariant != NULL && c.invariant->invariants.size() != 0;
 
    if (hashypo || hasinv)
        o << "(and ";
    if (hashypo)
        o << (*c.pred) << " ";
    if (hasinv)
        o << (*c.invariant);
    o << " (leq " << *(c.right->simplify()) << "  "
                    << *(c.left->simplify()) << ")";
 
  return o.str().c_str();
}
 
inline ostream& operator << (ostream&o, Constraint&c)
{
 
  bool hashypo = c.pred != NULL && c.pred->hypotheses.size() != 0;
  bool hasinv = c.invariant != NULL && c.invariant->invariants.size() != 0;
  bool hasbounds = c.bound != NULL && c.bound->bounds.size() != 0;
  bool hasdefs = c.def != NULL && c.def->defs.size() != 0;
 
  //char* inner = constraint_inner(c);
  const char * inner = constraint_inner(c);
 
  if(hasdefs){
    // Define any functions needed
    set<SecType*> defs = c.def->defs;
    set<SecType*>::iterator i = defs.begin();
    for(; i!=defs.end(); i++){
      o << (*i)->func_def_string() << endl;
    }
  }
 
  // Should simplify before this is reached to try to prevent quantification
  if(hasbounds){
    // Quantify over the range of the left and right
    set<QBound*> bounds = c.bound->bounds;
    set<QBound*>::iterator i = bounds.begin();
    // Give quantified variable names
    o << "(assert (not (forall (";
    for(; i != bounds.end(); i++){
      o << "(" << (*i)->qvar<< " Int)";
    }
    o << ")" << endl;
 
    // Give range implications
    i = bounds.begin();
    o << "    (implies (and ";
    for(; i!=bounds.end(); i++) o << (*(*i));
    o << ")"<< endl <<
         "        " << inner << endl << 
         "    )" << endl <<
         ")))";
 
  } else {
    o << "(assert ";
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
  }
  
  return o;
}

#endif
