# include "QuantExpr.h"
# include <stdio.h>
# include <sstream>

//=============================================================================
// Verinum Quantifier Expressions
//=============================================================================

//-----------------------------------------------------------------------------
// VQENum
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

void* VQENum::accept(QEVisitor *v){
    return v->visit(this);
}

//-----------------------------------------------------------------------------
// VQEVar
//-----------------------------------------------------------------------------
VQEVar::VQEVar(perm_string s) : name(s) {}

void VQEVar::dump(ostream& o){
    o << name.str();
}

QuantExpr* VQEVar::accept(QESubVisitor *v){
    return v->visit(this);
}

void* VQEVar::accept(QEVisitor *v){
    return v->visit(this);
}

//-----------------------------------------------------------------------------
// VQEIndex
//-----------------------------------------------------------------------------
VQEIndex::VQEIndex(){}

QuantExpr* VQEIndex::accept(QESubVisitor *v){
    return v->visit(this);
}

void VQEIndex::dump(ostream& o){
    o << "x";
}
void* VQEIndex::accept(QEVisitor *v){
    return v->visit(this);
}


//=============================================================================
// Label Quantifier Expressions
//=============================================================================

//-----------------------------------------------------------------------------
//LQEDep
//-----------------------------------------------------------------------------
LQEDep::LQEDep(perm_string _name, VQuantExpr* _vqe) :
  vqe(_vqe), name(_name) {};

void LQEDep::dump(ostream& o){
  o << name.str() << " " << vqe;
}

QuantExpr* LQEDep::accept(QESubVisitor *v){
    return v->visit(this);
}
void* LQEDep::accept(QEVisitor *v){
    return v->visit(this);
}


