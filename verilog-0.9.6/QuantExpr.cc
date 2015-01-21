# include "QuantExpr.h"

//-----------------------------------------------------------------------------
// Verinum Quantifier Expressions
//-----------------------------------------------------------------------------

VQENum::VQENum(verinum* n) :
  value(n->as_ulong()) {};

const char* VQENum::to_z3(){
  return (const char*)&value;
}


//-----------------------------------------------------------------------------
// Label Quantifier Expressions
//-----------------------------------------------------------------------------
LQEDep::LQEDep(perm_string _name, VQuantExpr* _vqe) :
  vqe(_vqe), name(_name) {};

const char* LQEDep::to_z3(){
  return "";
}
