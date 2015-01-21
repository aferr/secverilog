#include <stdio.h>
#include "verinum.h"
#include "StringHeap.h"
//-----------------------------------------------------------------------------
// Abstract Quantified Label Expressions
//-----------------------------------------------------------------------------
class QuantExpr {
  public:
    virtual void dump(ostream&o) = 0;
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
    virtual void dump(ostream&o);

  private:
    unsigned long value;
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

  private:
    VQuantExpr* vqe;
    perm_string name;
};
