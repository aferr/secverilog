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

# include "config.h"

/*
 * This file type-checks expressions.
 */
# include  "PExpr.h"
# include  "sectypes.h"

SecType* PEBinary::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	SecType* ty1 = left_->typecheck(out, varsToType);
	SecType* ty2 = right_->typecheck(out, varsToType);
	return new JoinType(ty1, ty2);
}

SecType* PECallFunction::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
//	throw "PECallFunction";
	cout << "PECallFunction is ignored" << endl;
	return ConstType::BOT;
}

SecType* PEConcat::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	SecType* last = ConstType::BOT;
	if (repeat_!=NULL) {
		last = repeat_->typecheck(out, varsToType);
	}
    for (unsigned idx = 0 ;  idx < parms_.count() ;  idx += 1) {
    	last = new JoinType(last, parms_[idx]->typecheck(out, varsToType));
    }
    return last;
}

SecType* PEEvent::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	throw "PEEvent";
}

// float constants have label Low
SecType* PEFNumber::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}

SecType* PEIdent::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	perm_string name = peek_tail_name(path_);
	map<perm_string,SecType*>::const_iterator find = varsToType.find(name);
	if (find != varsToType.end()) {
		return (*find).second;
	}
	else {
		cout <<  "Unbounded var name: " << name.str() << endl;
		return ConstType::TOP;
	}
}

// integer constants have label Low
SecType* PENumber::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}

// string constants have label Low
SecType* PEString::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}

SecType* PETernary::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
//	SecType* lexp = expr_->typecheck(out, varsToType);
//	SecType* texp = tru_->typecheck(out, varsToType);
//	SecType* fexp = fal_->typecheck(out, varsToType);
//	SecType* rhs = new JoinType(texp, fexp);
//	SecType* ret = new JoinType(lexp, rhs->simplify());
	throw "All PETernary expressions should have been translated already.\n";
}

SecType* PEUnary::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return expr_->typecheck(out, varsToType);
}
