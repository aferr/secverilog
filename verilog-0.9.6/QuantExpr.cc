# include "QuantExpr.h"
# include <stdio.h>
# include <sstream>

//-----------------------------------------------------------------------------
// Verinum Quantifier Expressions
//-----------------------------------------------------------------------------

VQENum::VQENum(verinum* n) :
  value(n->as_ulong()) {};

VQENum::VQENum(unsigned long n) :
  value(n) {};

void VQENum::dump(ostream& o){
  o << value;
}

QuantExpr* VQENum::accept(QESubVisitor *v){
    return v->visit(this);
}


//-----------------------------------------------------------------------------
// Label Quantifier Expressions
//-----------------------------------------------------------------------------
LQEDep::LQEDep(perm_string _name, VQuantExpr* _vqe) :
  vqe(_vqe), name(_name) {};

void LQEDep::dump(ostream& o){
  o << name.str() << " " << vqe;
}

QuantExpr* LQEDep::accept(QESubVisitor *v){
    return v->visit(this);
}


