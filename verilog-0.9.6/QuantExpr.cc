# include "QuantExpr.h"
# include <stdio.h>
# include <sstream>
# include <iostream>

//=============================================================================
// Integer Quantifier Expressions
//=============================================================================

//-----------------------------------------------------------------------------
// IQENum
//-----------------------------------------------------------------------------
IQENum::IQENum(verinum* n) :
  value(n->as_ulong()) {};

IQENum::IQENum(unsigned long n) :
  value(n) {};

void IQENum::dump(ostream& o){
  o << value;
}

QuantExpr* IQENum::accept(QESubVisitor *v){
    return v->visit(this);
}

void* IQENum::accept(QEVisitor *v){
    return v->visit(this);
}

//-----------------------------------------------------------------------------
// IQEVar
//-----------------------------------------------------------------------------
IQEVar::IQEVar(perm_string s) : name(s) {}

void IQEVar::dump(ostream& o){
    o << name.str();
}

QuantExpr* IQEVar::accept(QESubVisitor *v){
    return v->visit(this);
}

void* IQEVar::accept(QEVisitor *v){
    return v->visit(this);
}

//-----------------------------------------------------------------------------
// IQEIndex
//-----------------------------------------------------------------------------
IQEIndex::IQEIndex(){}

QuantExpr* IQEIndex::accept(QESubVisitor *v){
    return v->visit(this);
}

void IQEIndex::dump(ostream& o){
    o << "x";
}
void* IQEIndex::accept(QEVisitor *v){
    return v->visit(this);
}

//-----------------------------------------------------------------------------
// IQEBinary
//-----------------------------------------------------------------------------
IQEBinary::IQEBinary(IQuantExpr* _l, IQuantExpr* _r, perm_string _sym) :
    l(_l), r(_r), sym(_sym)
{
}

QuantExpr* IQEBinary::accept(QESubVisitor *v){
    return v->visit(this);
}

void IQEBinary::dump(ostream& o){
    o << "(" << sym .str() << " " << l << " " << r << ")";
}

void* IQEBinary::accept(QEVisitor *v){
    return v->visit(this);
}
//-----------------------------------------------------------------------------
// IQETernary
//-----------------------------------------------------------------------------
IQETernary::IQETernary(BQuantExpr* _b, IQuantExpr* _e1, IQuantExpr* _e2) :
    b(_b), e1(_e1), e2(_e2)
{
}

QuantExpr* IQETernary::accept(QESubVisitor *v){
    return v->visit(this);
}

void IQETernary::dump(ostream& o){
    o << "(ite " << b << " " << e1 << " " << e2 << ")";
}

void* IQETernary::accept(QEVisitor *v){
    return v->visit(this);
}


//=============================================================================
// Boolean Quantifier Expressions
//=============================================================================

//-----------------------------------------------------------------------------
// BQETrue
//-----------------------------------------------------------------------------
QuantExpr* BQETrue::accept(QESubVisitor *v){
    return v->visit(this);
}
void*      BQETrue::accept(QEVisitor *v){
    return v->visit(this);
}
void       BQETrue::dump(ostream&o){
    o << "true";
}

BQETrue::BQETrue(){};

//-----------------------------------------------------------------------------
// BQEFalse
//-----------------------------------------------------------------------------
QuantExpr* BQEFalse::accept(QESubVisitor *v){
    return v->visit(this);
}
void*      BQEFalse::accept(QEVisitor *v){
    return v->visit(this);
}
void       BQEFalse::dump(ostream&o){
    o << "false";
}

BQEFalse::BQEFalse(){};

//-----------------------------------------------------------------------------
// BQEFromIQE
//-----------------------------------------------------------------------------
QuantExpr* BQEFromIQE::accept(QESubVisitor *v){
    return v->visit(this);
}
void*      BQEFromIQE::accept(QEVisitor *v){
    return v->visit(this);
}
void       BQEFromIQE::dump(ostream&o){
    o << "(IBOOL " << iexp;
}

BQEFromIQE::BQEFromIQE(IQuantExpr *_iexp) : iexp(_iexp) {};

//-----------------------------------------------------------------------------
// BQEBinary
//-----------------------------------------------------------------------------
QuantExpr* BQEBinary::accept(QESubVisitor *v){
    return v->visit(this);
}
void*      BQEBinary::accept(QEVisitor *v){
    return v->visit(this);
}
void       BQEBinary::dump(ostream&o){
    o << "(" << sym.str() << " " << l << " " << r << ")";
}

BQEBinary::BQEBinary(BQuantExpr *_l, BQuantExpr *_r, perm_string _sym) :
    l(_l), r(_r), sym(_sym)
{};

//-----------------------------------------------------------------------------
// BQEEq
//-----------------------------------------------------------------------------
QuantExpr* BQEEq::accept(QESubVisitor *v){
    return v->visit(this);
}
void*      BQEEq::accept(QEVisitor *v){
    return v->visit(this);
}
void       BQEEq::dump(ostream&o){
    o << "(= " << l << " " << r << ")";
}

BQEEq::BQEEq(IQuantExpr *_l, IQuantExpr *_r) : l(_l), r(_r) {};

//=============================================================================
// Label Quantifier Expressions
//=============================================================================

//-----------------------------------------------------------------------------
//LQEDep
//-----------------------------------------------------------------------------
LQEDep::LQEDep(perm_string _name, IQuantExpr* _vqe) :
  vqe(_vqe), name(_name) {
};

void LQEDep::dump(ostream& o){
  o << name.str() << " " << vqe;
}

QuantExpr* LQEDep::accept(QESubVisitor *v){
    return v->visit(this);
}
void* LQEDep::accept(QEVisitor *v){
    return v->visit(this);
}

//-----------------------------------------------------------------------------
// LQEConst
//-----------------------------------------------------------------------------
LQEConst::LQEConst(perm_string _name) : name(_name)
{
  if(name == perm_string::literal("L")){
    name = perm_string::literal("LOW");
  } else if( name == perm_string::literal("H")){
    name = perm_string::literal("HIGH");
  }
}

void LQEConst::dump(ostream& o){
  o << name.str();
}

QuantExpr* LQEConst::accept(QESubVisitor *v){
  return v->visit(this);
}

void* LQEConst::accept(QEVisitor* v){
  return v->visit(this);
}

//-----------------------------------------------------------------------------
//LQETernary
//-----------------------------------------------------------------------------
LQETernary::LQETernary(BQuantExpr *_b, LQuantExpr *_l, LQuantExpr *_r) :
  b(_b), l(_l), r(_r) {
}

void LQETernary::dump(ostream& o){
  o << "ite " << b << " " << l << " " << r;
}

QuantExpr* LQETernary::accept(QESubVisitor *v){
  return v->visit(this);
}

void* LQETernary::accept(QEVisitor* v){
  return v->visit(this);
}
