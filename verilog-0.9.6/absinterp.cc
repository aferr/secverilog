/*
 * Copyright (c) 1998-2013 Danfeng Zhang (zhangdf@cs.cornell.edu)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#include <cstdlib>
#include <list>
#include "AStatement.h"
#include "PExpr.h"
#include "sectypes.h"
#include "Statement.h"
#include "StringHeap.h"

/**
 * Invalidate all constraints constraining "name"
 */
void invalidate (Predicate& pred, perm_string name)
{
	set<Hypothesis*>::iterator ite = pred.hypotheses.begin();
	while (ite != pred.hypotheses.end()) {
		Hypothesis* h = (*ite);
		if (h->matches(name))
			pred.hypotheses.erase(ite++);
		else
			++ ite;
	}

}

void AContrib::absintp(Predicate& pred) const
{
	throw "AContrib";
}

/**
 * For blocking assignment, clear predicates on the lhs. Set up a new predicate on lhs if the rhs is a number.
 */
void PAssign::absintp(Predicate& pred, TypeEnv& env) const
{
	invalidate(pred, lval_->get_name());
	PENumber* number = dynamic_cast<PENumber*>(rval_);
	if (number != NULL || env.dep_exprs.find(rval_->get_name()) != env.dep_exprs.end()) {
		if (env.dep_exprs.find(lval_->get_name()) != env.dep_exprs.end())
			pred.hypotheses.insert(new Hypothesis(lval_, rval_));
	}
}

void PAssignNB::absintp(Predicate& pred, TypeEnv& env) const
{
	// do nothing since the update is not visible until the next cycle
}

void PCallTask::absintp(Predicate& pred, TypeEnv& env) const
{
}

/**
 * Do nothing for now. Add more details to improve precision later.
 */
void PCase::absintp(Predicate& pred, TypeEnv& env, unsigned idx) const
{
}

/**
 * Set up a predicate for branches, if the condition is simple.
 */
void PCondit::absintp(Predicate& pred, TypeEnv& env, bool istrue) const
{
	if (istrue && if_) {
		if (expr_->is_wellformed(env.dep_exprs))
			pred.hypotheses.insert(new Hypothesis(expr_->to_wellformed(env.dep_exprs)));
	}
	else if (else_) {
		if (expr_->is_neg_wellformed(env.dep_exprs))
			pred.hypotheses.insert(new Hypothesis(new PEUnary('N', expr_->neg_to_wellformed(env.dep_exprs))));
	}
}

/**
 * Merge point of a branch. Simply take the intersection of two sets.
 */
void PCondit::merge(Predicate& pred1, Predicate& pred2, Predicate& ret) const
{
	std::set_intersection(pred1.hypotheses.begin(), pred1.hypotheses.end(),
			pred2.hypotheses.begin(), pred2.hypotheses.end(),
			inserter(ret.hypotheses, ret.hypotheses.begin()), HypothesisComparator());
}

void PCAssign::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PCAssign";
}

void PDeassign::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PDeassign";
}

void PDelayStatement::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PDelay";
}

void PDisable::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PDisable";
}

void PEventStatement::absintp(Predicate& pred, TypeEnv& env) const
{
}

void PForce::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PForce";
}

void PForever::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PForever";
}

void PForStatement::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PForStatement";
}

void PNoop::absintp(Predicate& pred, TypeEnv& env) const
{
	throw "PNoop";
}

void PRelease::absintp(Predicate& pred, TypeEnv&) const
{
	throw "PRelease";
}

void PRepeat::absintp(Predicate& pred, TypeEnv&) const
{
	throw "PRepeat";
}

void PTrigger::absintp(Predicate& pred, TypeEnv&) const
{
	throw "PTrigger";
}

void PWhile::absintp(Predicate& pred, TypeEnv&) const
{
	throw "PWhile";
}
