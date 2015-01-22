# include "QuantExpr.h"

QuantExpr* QESubVisitor::visit(VQENum* e){
    return e;
}
QuantExpr* QESubVisitor::visit(LQEDep* e){
    return new LQEDep(e->name, 
            dynamic_cast<VQuantExpr*>(e->vqe->accept(this))
            );
}
