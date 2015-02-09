# include "QuantExpr.h"

//-----------------------------------------------------------------------------
// Integer Expressions
//-----------------------------------------------------------------------------
QuantExpr* QESubVisitor::visit(IQENum* e){
    return e;
}

QuantExpr* QESubVisitor::visit(IQEVar* e){
    return e;
}

QuantExpr* QESubVisitor::visit(IQEIndex* e){
    return e;
}

QuantExpr* QESubVisitor::visit(IQEBinary* e){
    return new IQEBinary(
            dynamic_cast<IQuantExpr*>(e->l->accept(this)),
            dynamic_cast<IQuantExpr*>(e->r->accept(this)),
            e->sym);
}

QuantExpr* QESubVisitor::visit(IQETernary *e){
    return new IQETernary(
            dynamic_cast<BQuantExpr*>(e->b->accept(this)),
            dynamic_cast<IQuantExpr*>(e->e1->accept(this)),
            dynamic_cast<IQuantExpr*>(e->e2->accept(this)));
}

//-----------------------------------------------------------------------------
// Boolean Expressions
//-----------------------------------------------------------------------------
QuantExpr* QESubVisitor::visit(BQETrue* e){
    return e;
}
QuantExpr* QESubVisitor::visit(BQEFalse* e){
    return e;
}
QuantExpr* QESubVisitor::visit(BQEFromIQE* e){
    return new BQEFromIQE(
            dynamic_cast<IQuantExpr*>(e->iexp->accept(this)));
}
QuantExpr* QESubVisitor::visit(BQEBinary* e){
    return new BQEBinary(
            dynamic_cast<BQuantExpr*>(e->l->accept(this)),
            dynamic_cast<BQuantExpr*>(e->r->accept(this)),
            e->sym);
}
QuantExpr* QESubVisitor::visit(BQEEq* e){
    return new BQEEq(
            dynamic_cast<IQuantExpr*>(e->l->accept(this)),
            dynamic_cast<IQuantExpr*>(e->r->accept(this)));
}

//-----------------------------------------------------------------------------
// Label Expressions
//-----------------------------------------------------------------------------
QuantExpr* QESubVisitor::visit(LQEDep* e){
    return new LQEDep(e->name, 
            dynamic_cast<IQuantExpr*>(e->vqe->accept(this))
            );
}

QuantExpr* QESubVisitor::visit(LQEConst* e){
    return e;
}

QuantExpr* QESubVisitor::visit(LQETernary* e){
    return new LQETernary(
            dynamic_cast<BQuantExpr*>(e->b->accept(this)),
            dynamic_cast<LQuantExpr*>(e->l->accept(this)),
            dynamic_cast<LQuantExpr*>(e->r->accept(this))
            );
}
