#include <stdio.h>
#include "verinum.h"
#include "StringHeap.h"
class QEVisitor;
class QESubVisitor;
class BQuantExpr;
//-----------------------------------------------------------------------------
// Abstract Quantified Label Expressions
//-----------------------------------------------------------------------------
class QuantExpr {
  public:
    virtual void dump(ostream&o) = 0;
    virtual QuantExpr* accept(QESubVisitor *v) = 0;
    virtual void* accept(QEVisitor *v) = 0;
};

inline ostream& operator << (ostream &o, QuantExpr *e){
  e->dump(o);
  return o;
}

//-----------------------------------------------------------------------------
// Integer Quantifier Expressions
//-----------------------------------------------------------------------------
class IQuantExpr : public QuantExpr {
};

// A verinum literal
class IQENum : public IQuantExpr {
  public: 
    IQENum(verinum* n);
    IQENum(unsigned long n);
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);

    unsigned long value;
};

// A variable
class IQEVar : public IQuantExpr {
  public:
    IQEVar(perm_string s);
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);

    perm_string name;
};

// The distinguished index varible. This gets substituted out.
class IQEIndex: public IQuantExpr {
  public:
    IQEIndex();
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);
    perm_string name;
};

// A Binary Expression
class IQEBinary : public IQuantExpr {
    public :
    IQEBinary(IQuantExpr *l, IQuantExpr *r, perm_string sym);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);
    IQuantExpr *l;
    IQuantExpr *r;
    perm_string sym;
};

// A Ternary Expression
class IQETernary : public IQuantExpr {
    public :
    IQETernary(BQuantExpr *b, IQuantExpr *e1, IQuantExpr *e2);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);
    BQuantExpr *b;
    IQuantExpr *e1;
    IQuantExpr *e2;
};


//-----------------------------------------------------------------------------
// Binary Quantifier Expressions
//-----------------------------------------------------------------------------
class BQuantExpr : public QuantExpr {
};

class BQETrue : public BQuantExpr{
    public:
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);

    BQETrue();
};

class BQEFalse: public BQuantExpr{
    public:
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);

    BQEFalse();
};

class BQEFromIQE: public BQuantExpr{
    public:
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);

    BQEFromIQE(IQuantExpr *iexp);
    IQuantExpr* iexp;

};

class BQEBinary : public BQuantExpr{
    public:
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);

    BQEBinary(BQuantExpr *l, BQuantExpr *r, perm_string sym);
    BQuantExpr *l;
    BQuantExpr *r;
    perm_string sym;
};

class BQEEq : public BQuantExpr{
    public:
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);
    virtual void dump(ostream&o);

    BQEEq(IQuantExpr *l, IQuantExpr *r);
    IQuantExpr *l;
    IQuantExpr *r;
};

//-----------------------------------------------------------------------------
// Label Quantifier Expressions
//-----------------------------------------------------------------------------
class LQuantExpr : public QuantExpr {
};

// Dependent type applied to a IQE
class LQEDep : public LQuantExpr {
  public:
    LQEDep(perm_string _name, IQuantExpr* _vqe);
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);

    IQuantExpr* vqe;
    perm_string name;
};

class LQEConst : public LQuantExpr {
  public:
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);

    LQEConst(perm_string _name);
    perm_string name;
};

class LQETernary : public LQuantExpr {
  public:
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void* accept(QEVisitor *v);

    LQETernary(BQuantExpr *b, LQuantExpr *l, LQuantExpr *r);
    BQuantExpr *b;
    LQuantExpr *l;
    LQuantExpr *r;
};

//-----------------------------------------------------------------------------
// QEVisitor
//-----------------------------------------------------------------------------
class QEVisitor {
    public:
    virtual void* visit(IQENum* e);
    virtual void* visit(IQEVar* e);
    virtual void* visit(IQEIndex* e);
    virtual void* visit(IQEBinary* e);
    virtual void* visit(IQETernary* e);

    virtual void* visit(BQETrue* e);
    virtual void* visit(BQEFalse* e);
    virtual void* visit(BQEFromIQE* e);
    virtual void* visit(BQEBinary* e);
    virtual void* visit(BQEEq* e);

    virtual void* visit(LQEDep* e);
    virtual void* visit(LQEConst* e);
    virtual void* visit(LQETernary* e);
    virtual void* reduce(void* a, void* b);
    virtual void* reduce(void* vals, ...);
    virtual void* default_val();
};

//-----------------------------------------------------------------------------
// QESubVisitor
//-----------------------------------------------------------------------------
class QESubVisitor {
    public:
    virtual QuantExpr* visit(IQENum* e);
    virtual QuantExpr* visit(IQEVar* e);
    virtual QuantExpr* visit(IQEIndex* e);
    virtual QuantExpr* visit(IQEBinary* e);
    virtual QuantExpr* visit(IQETernary* e);

    virtual QuantExpr* visit(BQETrue* e);
    virtual QuantExpr* visit(BQEFalse* e);
    virtual QuantExpr* visit(BQEFromIQE* e);
    virtual QuantExpr* visit(BQEBinary* e);
    virtual QuantExpr* visit(BQEEq* e);

    virtual QuantExpr* visit(LQEDep* e);
    virtual QuantExpr* visit(LQEConst* e);
    virtual QuantExpr* visit(LQETernary* e);
};
