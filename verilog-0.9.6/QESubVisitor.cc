# include "QuantExpr.h"

QuantExpr* QESubVisitor::visit(VQENum* e){
    return e;
}

QuantExpr* QESubVisitor::visit(VQEVar* e){
    return e;
}

QuantExpr* QESubVisitor::visit(VQEIndex* e){
    return e;
}

QuantExpr* QESubVisitor::visit(VQEBinary* e){
    return new VQEBinary(
            dynamic_cast<VQuantExpr*>(e->l->accept(this)),
            dynamic_cast<VQuantExpr*>(e->r->accept(this)),
            e->sym);
}

QuantExpr* QESubVisitor::visit(VQETernary *e){
    return new VQETernary(
            dynamic_cast<VQuantExpr*>(e->b->accept(this)),
            dynamic_cast<VQuantExpr*>(e->e1->accept(this)),
            dynamic_cast<VQuantExpr*>(e->e2->accept(this)));
}

QuantExpr* QESubVisitor::visit(LQEDep* e){
    return new LQEDep(e->name, 
            dynamic_cast<VQuantExpr*>(e->vqe->accept(this))
            );
}
