#include "QuantExpr.h"
#include <stdarg.h>

void* QEVisitor::visit(VQENum* e){
    return default_val();
}

void* QEVisitor::visit(VQEVar* e){
    return default_val();
}

void* QEVisitor::visit(VQEIndex* e){
    return default_val();
}

void* QEVisitor::visit(LQEDep* e){
    return e->vqe->accept(this);
}

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
