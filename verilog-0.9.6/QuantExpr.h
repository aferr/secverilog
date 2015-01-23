#include <stdio.h>
#include "verinum.h"
#include "StringHeap.h"
class QESubVisitor;
//-----------------------------------------------------------------------------
// Abstract Quantified Label Expressions
//-----------------------------------------------------------------------------
class QuantExpr {
  public:
    virtual void dump(ostream&o) = 0;
    virtual QuantExpr* accept(QESubVisitor *v) = 0;
};

inline ostream& operator << (ostream &o, QuantExpr *e){
  e->dump(o);
  return o;
}

//-----------------------------------------------------------------------------
// Verinum Quantifier Expressions
//-----------------------------------------------------------------------------
class VQuantExpr : public QuantExpr {
};

// A verinum literal
class VQENum : public VQuantExpr {
  public: 
    VQENum(verinum* n);
    VQENum(unsigned long n);
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);

    unsigned long value;
};

// A variable
class VQEVar : public VQuantExpr {
  public:
    VQEVar(perm_string s);
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);

    perm_string name;
};

// The distinguished index varible. This gets substituted out.
class VQEIndex: public VQuantExpr {
  public:
    VQEIndex();
    virtual QuantExpr* accept(QESubVisitor *v);
    virtual void dump(ostream&o);
    perm_string name;
};


//-----------------------------------------------------------------------------
// Label Quantifier Expressions
//-----------------------------------------------------------------------------
class LQuantExpr : public QuantExpr {
};

// Dependent type applied to a VQE
class LQEDep : public LQuantExpr {
  public:
    LQEDep(perm_string _name, VQuantExpr* _vqe);
    virtual void dump(ostream&o);
    virtual QuantExpr* accept(QESubVisitor *v);

    VQuantExpr* vqe;
    perm_string name;
};

//-----------------------------------------------------------------------------
// QESubVisitor
//-----------------------------------------------------------------------------
class QESubVisitor {
    public:
    virtual QuantExpr* visit(VQENum* e);
    virtual QuantExpr* visit(VQEVar* e);
    virtual QuantExpr* visit(VQEIndex* e);
    virtual QuantExpr* visit(LQEDep* e);
};
