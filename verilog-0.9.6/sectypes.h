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
#include "PExpr.h"
#include "QuantExpr.h"
#include "StringHeap.h"
#include "basetypes.h"
#include "sexp_printer.h"
#include "verinum.h"
#include <cstdlib>
#include <fstream>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <variant>

class SecType;
class ConstType;
class VarType;
class JoinType;
class MeetType;
class IndexType;
class QuantType;
class PolicyType;
struct TypeEnv;

using str_or_num = variant<perm_string, verinum>;

struct str_or_num_to_string {
  std::string operator()(const perm_string &s) { return s.str(); }
  std::string operator()(const verinum &n) {
    return std::to_string(n.as_long());
  }
};

void dumpZ3Func(SexpPrinter &printer, perm_string name, list<str_or_num> args);

#define CONST_IT(container) container.cbegin(), container.cend()
#define TRANSFORM_IT(src, dest) CONST_IT(src), std::back_inserter(dest)

class SecType {

  // Manipulate the types.
public:
  // BaseType*base_type;
  // void setBaseType(BaseType*b) { base_type = b;}
  // BaseType* getBaseType() { assert(base_type); return base_type; }

  virtual void dump(SexpPrinter &printer) {}
  virtual bool hasBottom() { return false; }
  virtual bool isBottom() { return false; }
  virtual bool hasTop() { return false; }
  virtual bool isTop() { return false; }
  virtual SecType *simplify() { return this; }
  virtual bool equals(SecType *st) { return false; }
  virtual SecType *subst(perm_string e1, perm_string e2) { return this; };
  virtual SecType *subst(map<perm_string, perm_string> m) { return this; };
  virtual SecType *next_cycle(TypeEnv &env) { return this; }
  virtual void collect_dep_expr(set<perm_string> &m){};
  virtual bool isDepType() { return false; };
  virtual bool hasExpr(perm_string str) { return false; };
  virtual SecType *freshVars(unsigned int lineno,
                             map<perm_string, perm_string> &m) {
    return this;
  };
  virtual SecType *apply_index(PExpr *index_val) { return this; }
  virtual SecType *apply_index(perm_string index_var,
                               const str_or_num &index_val) {
    return this;
  }
  //  BasicType& operator= (const BasicType&);
  virtual void emitFlowsTo(SexpPrinter &printer, SecType *rhs);
};

class ConstType : public SecType {

public:
  ConstType();
  ConstType(perm_string name);
  ~ConstType();
  void dump(SexpPrinter &printer) { printer << name.str(); }
  bool hasBottom() { return name == "LOW"; }
  bool hasTop() { return name == "HIGH"; }
  bool isBottom() { return name == "LOW"; }
  bool isTop() { return name == "HIGH"; }
  bool equals(SecType *st);
  SecType *freshVars(unsigned int lineno, map<perm_string, perm_string> &m);

public:
  static ConstType *TOP;
  static ConstType *BOT;

private:
  perm_string name;
};

/* type variables */
class VarType : public SecType {

public:
  VarType(perm_string varname);
  ~VarType();
  VarType &operator=(const VarType &);

public:
  // Manipulate the types.
  void set_type(perm_string varname);
  perm_string get_type() const;
  bool equals(SecType *st);
  SecType *freshVars(unsigned int lineno, map<perm_string, perm_string> &m);
  bool hasExpr(perm_string str);

private:
  perm_string varname_;
};

/* Dynamic type */
class IndexType : public SecType {

public:
  IndexType(perm_string name, const list<str_or_num> &exprs);
  ~IndexType();
  IndexType &operator=(const IndexType &);
  void dump(SexpPrinter &printer) { dumpZ3Func(printer, name_, exprs_); }
  bool equals(SecType *st);

  SecType *apply_index(perm_string index_var, const str_or_num &index_val) {
    list<str_or_num> nexprs;
    std::transform(TRANSFORM_IT(exprs_, nexprs), [&](const str_or_num &n) {
      if (str_or_num(index_var) == n)
        return index_val;
      return n;
    });
    return new IndexType(name_, nexprs);
  }

public:
  // Manipulate the types.
  void set_type(const perm_string name, list<str_or_num> &exprs);
  perm_string get_name() const;
  list<str_or_num> get_exprs() const;
  SecType *subst(perm_string e1, str_or_num &e2);
  SecType *subst(const map<perm_string, str_or_num> &m);
  virtual SecType *next_cycle(TypeEnv &env);
  void collect_dep_expr(set<perm_string> &m);
  SecType *freshVars(unsigned int lineno, map<perm_string, perm_string> &m);
  bool hasExpr(perm_string str);
  bool isDepType() { return true; };

public:
  static IndexType *RL;
  static IndexType *WL;

private:
  perm_string name_;
  list<str_or_num> exprs_;
};

/* a CompType can be a join/meet of CompTypes */
class JoinType : public SecType {

public:
  JoinType(SecType *, SecType *);
  ~JoinType();
  JoinType &operator=(const JoinType &);
  void dump(SexpPrinter &printer) {
    printer.startList();
    printer << "join";
    comp1_->dump(printer);
    comp2_->dump(printer);
    printer.endList();
  }
  SecType *getFirst();
  SecType *getSecond();

  bool hasBottom() { return comp1_->hasBottom() || comp2_->hasBottom(); }
  bool isBottom() { return comp1_->isBottom() && comp2_->isBottom(); }
  bool hasTop() { return comp1_->hasTop() || comp2_->hasTop(); }
  bool isTop() { return comp1_->isTop() || comp2_->isTop(); }
  SecType *simplify();
  bool equals(SecType *st);
  SecType *subst(perm_string e1, perm_string e2);
  SecType *subst(map<perm_string, perm_string> m);
  virtual SecType *next_cycle(TypeEnv &env);
  void collect_dep_expr(set<perm_string> &m);
  SecType *freshVars(unsigned int lineno, map<perm_string, perm_string> &m);
  bool hasExpr(perm_string str);
  virtual void emitFlowsTo(SexpPrinter &printer, SecType *rhs);
  bool isDepType() { return comp1_->isDepType() || comp2_->isDepType(); }

private:
  SecType *comp1_;
  SecType *comp2_;
};

class MeetType : public SecType {

public:
  MeetType(SecType *, SecType *);
  ~MeetType();
  MeetType &operator=(const MeetType &);
  void dump(SexpPrinter &printer) {
    printer.startList();
    printer << "meet";
    comp1_->dump(printer);
    comp2_->dump(printer);
    printer.endList();
  }
  SecType *getFirst();
  SecType *getSecond();

  bool hasBottom() { return comp1_->hasBottom() || comp2_->hasBottom(); }
  bool isBottom() { return comp1_->isBottom() || comp2_->isBottom(); }
  bool hasTop() { return comp1_->hasTop() || comp2_->hasTop(); }
  bool isTop() { return comp1_->isTop() && comp2_->isTop(); }
  SecType *simplify();
  bool equals(SecType *st);
  SecType *subst(perm_string e1, perm_string e2);
  SecType *subst(map<perm_string, perm_string> m);
  virtual SecType *next_cycle(TypeEnv &env);
  void collect_dep_expr(set<perm_string> &m);
  SecType *freshVars(unsigned int lineno, map<perm_string, perm_string> &m);
  bool hasExpr(perm_string str);
  virtual void emitFlowsTo(SexpPrinter &printer, SecType *rhs);
  bool isDepType() { return comp1_->isDepType() || comp2_->isDepType(); }

private:
  SecType *comp1_;
  SecType *comp2_;
};

class QuantType : public SecType {

public:
  QuantType(perm_string index_var, SecType *st);
  ~QuantType();

  void collect_dep_expr(set<perm_string> &m);
  virtual SecType *next_cycle(TypeEnv &env);
  void dump(SexpPrinter &printer) { _sectype->dump(printer); }

  SecType *getInnerType() { return _sectype; }

  SecType *apply_index(PExpr *index_val) {
    // for now only support identifiers and numbers as index_values, if it's
    // anything else, throw an error
    PEIdent *index_id = dynamic_cast<PEIdent *>(index_val);
    str_or_num idx_val;
    if (!index_id) {
      PENumber *index_num = dynamic_cast<PENumber *>(index_val);
      if (!index_num) {
        throw "Quantified types cannot be used with complex index expressions";
      } else {
        idx_val = index_num->value();
      }
    } else {
      // TODO throw error if this itself is indexed
      index_component_t index_idx = index_id->path().back().index.front();
      if (index_idx.sel != index_component_t::SEL_NONE) {
        throw "Index expression must not contain an index";
      }
      idx_val = peek_tail_name(index_id->path());
    }
    SecType *replacedType = _sectype->apply_index(_index_var, idx_val);
    SecType *result       = new QuantType(_index_var, replacedType);
    return result;
  }
  bool isDepType() { return _sectype->isDepType(); }
  bool hasExpr(perm_string str) { return _sectype->hasExpr(str); }

  virtual void emitFlowsTo(SexpPrinter &printer, SecType *rhs) {
    _sectype->emitFlowsTo(printer, rhs);
  }

private:
  perm_string _index_var;
  SecType *_sectype;
  PExpr *_index_expr;
  perm_string _name;
};

/**
 * An equality expression
 */
struct Hypothesis {
  PExpr *bexpr_;

  Hypothesis(PExpr *l, PExpr *r) { bexpr_ = new PEBComp('e', l, r); }

  Hypothesis(PExpr *bexpr) { bexpr_ = bexpr; }

  Hypothesis *subst(map<perm_string, perm_string> m);

  bool matches(perm_string name);
};

class PolicyType : public SecType {

public:
  PolicyType(SecType *lower, perm_string cond_name,
             const list<str_or_num> &static_exprs,
             const list<str_or_num> &dynamic_exprs, SecType *upper);
  ~PolicyType();
  virtual SecType *next_cycle(TypeEnv &env);
  virtual bool hasExpr(perm_string str);
  virtual SecType *subst(perm_string e1, perm_string e2);
  virtual SecType *subst(map<perm_string, perm_string> m);
  virtual void collect_dep_expr(set<perm_string> &m);

  void dump(SexpPrinter &printer) {
    printer.startList();
    printer << "Policy";
    _lower->dump(printer);
    printer.startList();
    printer << _cond_name.str();
    for (auto &v : _static) {
      printer << std::visit(str_or_num_to_string(), v);
    }
    for (auto &v : _dynamic) {
      printer << std::visit(str_or_num_to_string(), v);
    }
    printer.endList();
    _upper->dump(printer);
    printer.endList();
  }

  SecType *apply_index(perm_string index_var, const str_or_num &index_val) {
    SecType *nlower = _lower->apply_index(index_var, index_val);
    SecType *nupper = _upper->apply_index(index_var, index_val);
    list<str_or_num> nstatic;
    list<str_or_num> ndynamic;
    for (auto &s : _static) {
      if (s == str_or_num(index_var)) {
        nstatic.push_back(index_val);
      } else {
        nstatic.push_back(s);
      }
    }
    for (auto &s : _dynamic) {
      if (s == str_or_num(index_var)) {
        ndynamic.push_back(index_val);
      } else {
        ndynamic.push_back(s);
      }
    }
    SecType *result =
        new PolicyType(nlower, _cond_name, nstatic, ndynamic, nupper);
    return result;
  };

  bool isNextType() { return _isNext; }

  SecType *get_lower() { return _lower; }

  SecType *get_upper() { return _upper; }

  perm_string get_cond() { return _cond_name; }

  list<str_or_num> get_static() { return _static; }

  list<str_or_num> get_dynamic() { return _dynamic; }

  list<str_or_num> get_all_args() {
    list<str_or_num> arglist = list<str_or_num>(_static);
    arglist.insert(arglist.end(), _dynamic.begin(), _dynamic.end());
    return arglist;
  }

  virtual void emitFlowsTo(SexpPrinter &printer, SecType *rhs);
  virtual bool equals(SecType *st);
  bool isDepType() { return true; };

private:
  bool _isNext;
  SecType *_lower;
  perm_string _cond_name;
  list<str_or_num> _static;
  list<str_or_num> _dynamic;
  SecType *_upper;
};

class HypothesisComparator {
public:
  bool operator()(const Hypothesis *h1, const Hypothesis *h2) {
    return h1->bexpr_->get_name() < h2->bexpr_->get_name();
  }
};

struct Predicate {
  set<Hypothesis *> hypotheses;

  Predicate &operator=(const Predicate &);
  Predicate *subst(map<perm_string, perm_string> m) const;
};

struct Equality {
  SecType *left;
  SecType *right;
  bool isleq;

  Equality(SecType *l, SecType *r, bool leq = false) {
    left  = l;
    right = r;
    isleq = leq;
  }

  void dump(SexpPrinter &printerut) const;
  Equality *subst(map<perm_string, perm_string> m);
};

struct Invariant {
  set<Equality *> invariants;
};

using PathAnalysis = std::map<perm_string, std::vector<Predicate>>;

struct TypeEnv {
  map<perm_string, SecType *> varsToType;
  map<perm_string, BaseType *> varsToBase;
  SecType *pc;
  set<perm_string>
      dep_exprs; // a list of expressions where a dependent type may depend on
  map<perm_string, list<int>> genVarVals;
  PathAnalysis analysis;
  set<perm_string> seqVars;
  Invariant *invariants;
  Module *module;

  TypeEnv(map<perm_string, SecType *> &m, map<perm_string, BaseType *> &b,
          SecType *pclabel, Module *modu) {
    varsToType = m;
    varsToBase = b;
    pc         = pclabel;
    module     = modu;
    invariants = new Invariant();
  }

  void addInvariant(Equality *inv) { invariants->invariants.insert(inv); }

  TypeEnv &operator=(const TypeEnv &);
};

// TODO real logic for this that handles array
bool isDepExpr(PEIdent *exp, TypeEnv &env) {
  return exp != NULL && env.dep_exprs.contains(exp->get_name());
}
struct Constraint {
  SecType *left;
  SecType *right;
  Predicate *pred;
  Invariant *invariant;

  Constraint(SecType *l, SecType *r, Invariant *inv, Predicate *p) {
    left      = l;
    right     = r;
    pred      = p;
    invariant = inv;
  }
};

inline SexpPrinter &operator<<(SexpPrinter &printer, SecType &t) {
  t.dump(printer);
  return printer;
}

inline ostream &operator<<(ostream &o, SecType &t) {
  SexpPrinter sp(o, 9999, 2, true);
  sp << t;
  return o;
}

inline SexpPrinter &operator<<(SexpPrinter &printer, const Predicate &pred) {
  auto l = pred.hypotheses;
  auto i = l.begin();
  if (l.size() > 1) {
    printer.startList();
    printer << "and";
  }
  if (i != l.end()) {
    (*i)->bexpr_->dumpz3(printer);
    ++i;
  }
  for (; i != l.end(); ++i) {
    (*i)->bexpr_->dumpz3(printer);
  }
  if (l.size() > 1)
    printer.endList();
  return printer;
}

inline ostream &operator<<(ostream &o, Predicate &t) {
  SexpPrinter sp(o, 9999, 2, true);
  sp << t;
  return o;
}

inline SexpPrinter &operator<<(SexpPrinter &printer, Invariant &invs) {
  for (auto inv : invs.invariants) {
    printer.startList();
    inv->dump(printer);
    printer.endList();
  }
  return printer;
}

inline ostream &operator<<(ostream &o, Invariant &t) {
  SexpPrinter sp(o, 9999, 2, true);
  sp << t;
  return o;
}

void dump_constraint(SexpPrinter &printer, Constraint &c,
                     std::set<perm_string> genvars, TypeEnv &env);

#endif
