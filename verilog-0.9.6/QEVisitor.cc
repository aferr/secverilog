#include "QuantExpr.h"
#include <stdarg.h>

//-----------------------------------------------------------------------------
// Integer Expressions
//-----------------------------------------------------------------------------

void* QEVisitor::visit(IQENum* e){
    return default_val();
}

void* QEVisitor::visit(IQEVar* e){
    return default_val();
}

void* QEVisitor::visit(IQEIndex* e){
    return default_val();
}

void* QEVisitor::visit(IQEBinary* e){
    return reduce(e->l->accept(this), e->r->accept(this));
}

void* QEVisitor::visit(IQETernary* e){
    return reduce(e->b->accept(this),
            e->e1->accept(this),
            e->e2->accept(this));
}

//-----------------------------------------------------------------------------
// Boolean Expressions
//-----------------------------------------------------------------------------
void* QEVisitor::visit(BQETrue* e){
    return default_val();
}
void* QEVisitor::visit(BQEFalse* e){
    return default_val();
}
void* QEVisitor::visit(BQEFromIQE* e){
    return e->iexp->accept(this);
}
void* QEVisitor::visit(BQEBinary* e){
    return reduce(e->l, e->r);
}
void* QEVisitor::visit(BQEEq* e){
    return reduce(e->l, e->r);
}


//-----------------------------------------------------------------------------
// Label Expressions
//-----------------------------------------------------------------------------

void* QEVisitor::visit(LQEDep* e){
    return e->vqe->accept(this);
}

void* QEVisitor::visit(LQEConst* e){
  return default_val();
}

void* QEVisitor::visit(LQETernary* e){
  return reduce(
      e->b->accept(this),
      e->l->accept(this),
      e->r->accept(this));
}

//-----------------------------------------------------------------------------
// Reduce / Default
//-----------------------------------------------------------------------------
void* QEVisitor::reduce(void* a, void* b){
    return default_val();
}

void* QEVisitor::reduce(void* vals, ...){
    va_list argp;
    va_start(argp, vals);

    void* ret = vals;
    void* next;
    while(next = va_arg(argp,void*)){
        ret = reduce( ret, next );
    }
    va_end(argp);
    return ret;
}

void* QEVisitor::default_val(){
    return NULL;
}
