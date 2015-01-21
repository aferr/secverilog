#include <stdio.h>
#include "verinum.h"
#include "StringHeap.h"
//-----------------------------------------------------------------------------
// Abstract Quantified Label Expressions
//-----------------------------------------------------------------------------
class QuantExpr {
  public:
  virtual const char * to_z3() = 0;
};

//-----------------------------------------------------------------------------
// Verinum Quantifier Expressions
//-----------------------------------------------------------------------------
class VQuantExpr : public QuantExpr {
};

// A verinum literal
class VQENum : public VQuantExpr {
  public: 
    VQENum(verinum* n);
    virtual const char * to_z3();

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
    virtual const char * to_z3();

  private:
    VQuantExpr* vqe;
    perm_string name;
};
