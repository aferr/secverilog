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
# include  "basetypes.h"

SecType* PEBinary::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	SecType* ty1 = left_->typecheck(out, varsToType);
	SecType* ty2 = right_->typecheck(out, varsToType);
	return new JoinType(ty1, ty2);
}
void PEBinary::collect_idens(set<perm_string>&s) const
{
  left_->collect_idens(s);
  right_->collect_idens(s);
}

SecType* PECallFunction::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
//	throw "PECallFunction";
	cout << "PECallFunction is ignored" << endl;
	return ConstType::BOT;
}
void PECallFunction::collect_idens(set<perm_string>&s) const
{
  return;
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
void PEConcat::collect_idens(set<perm_string>&s) const
{
  if (repeat_!= NULL) { repeat_->collect_idens(s); }
  for (unsigned idx = 0 ;  idx < parms_.count() ;  idx += 1) {
    parms_[idx]->collect_idens(s);
  }    
}

SecType* PEEvent::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	throw "PEEvent";
}
void PEEvent::collect_idens(set<perm_string>&s) const
{
  throw "PEEvent";
}
// float constants have label Low
SecType* PEFNumber::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}
void PEFNumber::collect_idens(set<perm_string>&s) const
{
  return;
}
SecType* PEIdent::typecheckName(ostream&out, map<perm_string, SecType*>&varsToType) const {
  perm_string name = peek_tail_name(path_);
  map<perm_string,SecType*>::const_iterator find = varsToType.find(name);
  if (find != varsToType.end()) {
    return (*find).second;
  } else {
    cerr <<  "Unbounded var name: " << name.str() << endl;
    return ConstType::TOP;
  }
}

SecType* PEIdent::typecheckIdx(ostream&out, map<perm_string, SecType*>&varsToType) const {
  SecType* result = ConstType::BOT;
  for (std::list<index_component_t>::const_iterator idxit = path_.back().index.begin();
       idxit != path_.back().index.end(); idxit++) {
    if (idxit->msb != NULL) {
      SecType *tmsb = idxit->msb->typecheck(out, varsToType);
      result = new JoinType(result, tmsb);
    }
    if (idxit->lsb != NULL) {
      SecType *tlsb = idxit->msb->typecheck(out, varsToType);
      result = new JoinType(result, tlsb);
    }
  }
  return result;
}

SecType* PEIdent::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
  //idents are like: varname[bit select]
  //need to join index label with name label
  SecType* namelbl = typecheckName(out, varsToType);
  SecType* idxlbl = typecheckIdx(out, varsToType);
  return new JoinType(namelbl, idxlbl);
}

void PEIdent::collect_idens(set<perm_string>&s) const
{
  s.insert(peek_tail_name(path_));
  for (std::list<index_component_t>::const_iterator idxit = path_.back().index.begin();
	 idxit != path_.back().index.end(); idxit++) {
   if (idxit->msb != NULL) {
     idxit->msb->collect_idens(s);
   }
   if (idxit->lsb != NULL) {
     idxit->lsb->collect_idens(s);
   }
  }
}
// integer constants have label Low
SecType* PENumber::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}
void PENumber::collect_idens(set<perm_string>&s) const
{
  return;
}
// string constants have label Low
SecType* PEString::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}
void PEString::collect_idens(set<perm_string>&s) const
{
  return;
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
void PETernary::collect_idens(set<perm_string>&s) const
{

  expr_->collect_idens(s);
  tru_->collect_idens(s);
  fal_->collect_idens(s);
}

SecType* PEUnary::typecheck(ostream&out, map<perm_string, SecType*>&varsToType) const
{
	return expr_->typecheck(out, varsToType);
}
void PEUnary::collect_idens(set<perm_string>&s) const
{
  expr_->collect_idens(s);
}
SecType* PEDeclassified::typecheck(ostream&out,
        map<perm_string, SecType*>&varsToType) const
{
    return this->type;
}
void PEDeclassified::collect_idens(set<perm_string>&s) const
{
  ex->collect_idens(s);
}

//-----------------------------------------------------------------------------
// Check Base Types
//-----------------------------------------------------------------------------
BaseType* PEConcat::check_base_type(ostream&out,
        map<perm_string, BaseType*>&varsToBase){

    // Default to combinational. Sequential if anything is sequential.
    // Not sure that this actually makes sense...
    //
    // How about: can be all sequential or all combinational but not a mix.
    //
	BaseType* returnType;
	if (repeat_!=NULL) {
		returnType = repeat_->check_base_type(out, varsToBase);
	} else if ( parms_.count() > 0 ){
        returnType = parms_[0]->check_base_type(out, varsToBase);
    }
    assert(returnType);
    for (unsigned idx = 0 ;  idx < parms_.count() ;  idx += 1) {
        //TODO define equality correctly and then just check it here.
        if(parms_[idx]->check_base_type(out, varsToBase)->isSeqType() !=
                returnType->isSeqType()){
            cout << "PEConcat found with multiple base types (com/seq)" << endl;
            assert(false);
        }
    }
    return returnType;
}

BaseType* PEIdent::check_base_type(ostream&out,
        map<perm_string, BaseType*>&varsToBase) {
    return varsToBase[peek_tail_name(path())];
}
