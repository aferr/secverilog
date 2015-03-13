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
# include "PExpr.h"
# include <sstream>
# include <stdio.h>
# include "QuantExpr.h"

class SecType;
class ConstType;
class VarType;
class JoinType;
class IndexType;
struct TypeEnv;

void CalculateQuantBounds(SecType *st, TypeEnv* env);

struct QBound{
    long lower;
    long upper;
    perm_string qvar;
    QBound(long u, long l, perm_string v) :
        lower(l), upper(u), qvar(v) {}
};

struct QBounds{
    set<QBound*> bounds;
};



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
      virtual void collect_bound_exprs(set<perm_string>* m) {};
      virtual bool hasExpr(perm_string str) {return false;};
      virtual SecType* freshVars(unsigned int lineno, map<perm_string, perm_string>& m) {return this;};
      virtual SecType* apply_index(PExpr *e) { return this; }
      // Upper and lower bounds for quantification. NULL unless has_bounds()
      
      virtual void set_range(PExpr* u, PExpr* l) {}
      perm_string index_var;

      virtual bool has_bounds() { return false; }
      virtual void get_bounds(QBounds* b){}
      virtual void insert_bound(QBound* b){}

     
      //Apply a copy of this type with n as the name for the functiond def. 
      virtual void give_name(perm_string s){}
      virtual bool has_defs() { return false; }
      virtual const char * func_def_string() { return ""; }
    
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

//-----------------------------------------------------------------------------
// QuantType
//-----------------------------------------------------------------------------
// This type is applied to arrays and acts as a mapping from array elements to 
// types. Syntactically, it specifies an index variable and an expression 
// (possibly) containing that index variable and that evaluates to a type.

class QuantType : public SecType {
  public:
    QuantType(perm_string index_var, QuantExpr *e);
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

    virtual bool has_bounds() {
      return (bound!=NULL && bound->bounds.size()>0);
    }

    virtual void get_bounds(QBounds *b){
      if(!has_bounds()) return;
      set<QBound*>::iterator i = bound->bounds.begin();
      for(; i!=(bound->bounds.end()); i++){
        b->bounds.insert(*i);
      }
    }

    virtual void insert_bound(QBound *b){
        bound->bounds.insert(b);
    }

    virtual bool has_defs(){return true;}

    void dump(ostream&o){
        o << "(fun_" << name.str() << " " << index_expr_trans << ")";
    }


  public:
    // Apply the expression that's used to index the quantified type. This 
    // translates the PExpr into QuantExprs that can be translated 
    // into Z3. Then, it creates a deep-copy of this type where the 
    // index_expr_trans 
    // is replaced with that type. This stores the indexing PExpr so that its 
    // bounds can be set in the context of the module where they can be 
    // computed from the range of any PWires in the subtree of that PExpr.
    SecType* apply_index(PExpr* e);
    SecType* apply_index(PENumber* e);
    SecType* apply_index(PEIdent* e);

    bool equals(SecType* st);
 
    void give_name(perm_string s){
      name = s;
    }
    
    const char * func_def_string(){ 
        if( func_def==""){
            std::stringstream b;
            b << "    (= ( fun_" << name.str() << " x)("
              << def_expr << "))";
            const char * body = b.str().c_str();

            std::stringstream ss;
            ss.str("");
            ss <<   "(declare-fun fun_" << name.str() << " (Int) Label)" <<
            endl << "(assert (forall ((x Int))" <<
            endl << body <<
            endl << "))";
            func_def = ss.str().c_str(); 
        }
        return func_def.c_str();
    }

    void collect_bound_exprs(set<perm_string>* m);

 
  private:
    // Index var to be replaced with indexing expression
    // perm_string index_var;
    QuantExpr *def_expr;
    QuantExpr *index_expr_trans;
    PExpr *index_expr;
    QBounds* bound;
    // Name for declared function.
    perm_string name;
    std::string func_def;

    QuantType * deep_copy(){
        QuantType *t = new QuantType(index_var, def_expr);
        t->lower = lower;
        t->upper = upper;
        t->index_var = index_var;
        t->def_expr = def_expr;
        t->index_expr = index_expr;
        t->index_expr_trans = index_expr_trans;
        return t;
    }
    int upper, lower;

    class IndexSwapInVisitor : public QESubVisitor {
        public: 
        IndexSwapInVisitor(perm_string i) : index_var(i) {};
        virtual QuantExpr* visit(IQEVar* e){
            return (e->name == index_var) ? (QuantExpr*) (new IQEIndex()) : 
                (QuantExpr*) e;
        }
        perm_string index_var;
    };
    
    class IndexSwapOutVisitor : public QESubVisitor {
        public: 
        IndexSwapOutVisitor(QuantExpr* e) : expr(e) {};
        virtual QuantExpr* visit(IQEIndex* e){
            return expr;
        }
        QuantExpr* expr;
    };

    class ExprCollector : public QEVisitor {
        public:
        void* visit(IQEVar* e){
            set<perm_string> *s = new set<perm_string>();
            s->insert(e->name);
            return s;
        }
        void* default_val(){
            return new set<perm_string>();
        }
        void* reduce(void* a, void* b){
            set<perm_string> *sa = static_cast<set<perm_string>*>(a);
            set<perm_string> *sb = static_cast<set<perm_string>*>(b);
            for(set<perm_string>::iterator it=sa->begin(); it!=sa->end(); it++){
                sb->insert(*it);
            }
            return b;
        }
    };

  //These methods are for development only
  private:

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

      bool has_defs(){ return comp1_->has_defs() || comp2_->has_defs(); }


      const char * func_def_string(){ 
          if(func_def == ""){
            std::stringstream ss;
            ss.str("");
            ss << comp1_->func_def_string() << endl;
            ss << comp2_->func_def_string();
            func_def = ss.str(); 
          }
          return func_def.c_str();
      }


      virtual void get_bounds(QBounds *b){
        comp1_->get_bounds(b);
        comp2_->get_bounds(b);
      }
      void collect_bound_exprs(set<perm_string>* m){
          comp1_->collect_bound_exprs(m);
          comp1_->collect_bound_exprs(m);
      }
      virtual void insert_bound(QBound *b){
          comp1_->insert_bound(b);
          comp2_->insert_bound(b);
      }

  
    private:
	  SecType* comp1_;
	  SecType* comp2_;
      std::string func_def;
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

      bool has_defs(){ return comp1_->has_defs() || comp2_->has_defs(); }

      virtual void get_bounds(QBounds *b){
        comp1_->get_bounds(b);
        comp2_->get_bounds(b);
      }
      
      virtual void insert_bound(QBound *b){
          comp1_->insert_bound(b);
          comp2_->insert_bound(b);
      }
      void collect_bound_exprs(set<perm_string>* m){
          comp1_->collect_bound_exprs(m);
          comp1_->collect_bound_exprs(m);
      }

      const char * func_def_string(){ 
          if(func_def == ""){
            std::stringstream ss;
            ss.str("");
            ss << comp1_->func_def_string() << endl;
            ss << comp2_->func_def_string();
            func_def = ss.str(); 
          }
          return func_def.c_str();
      }

    private:
	  SecType* comp1_;
	  SecType* comp2_;
      std::string func_def;
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
//-----------------------------------------------------------------------------
// Quantified  Type Constraints
//-----------------------------------------------------------------------------
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

	Constraint(SecType* lhs, SecType* rhs, Invariant* inv, Predicate* p,
      TypeEnv* env) {
		left = lhs;
		right = rhs;
		pred = p;
		invariant = inv;
    def = new QFuncDefs();
    bound = new QBounds();

    if(lhs->has_defs()){
        def->defs.insert(lhs);
    }
    if(rhs->has_defs()){
        def->defs.insert(rhs);
    }
    
    CalculateQuantBounds(lhs, env);
    CalculateQuantBounds(rhs, env);
    lhs->get_bounds(bound);
    rhs->get_bounds(bound);
    
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
         "        " << constraint_inner(c) << endl <<
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
