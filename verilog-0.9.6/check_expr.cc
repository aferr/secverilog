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

SecType* PEBinary::typecheck(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const
{
	SecType* ty1 = left_->typecheck(printer, varsToType);
	SecType* ty2 = right_->typecheck(printer, varsToType);
	return new JoinType(ty1, ty2);
}
void PEBinary::collect_idens(set<perm_string>&s) const
{
  left_->collect_idens(s);
  right_->collect_idens(s);
}

SecType* PECallFunction::typecheck(SexpPrinter&, map<perm_string, SecType*>&varsToType) const
{
//	throw "PECallFunction";
	cout << "PECallFunction is ignored" << endl;
	return ConstType::BOT;
}
void PECallFunction::collect_idens(set<perm_string>&s) const
{
  return;
}
SecType* PEConcat::typecheck(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const
{
	SecType* last = ConstType::BOT;
	if (repeat_!=NULL) {
		last = repeat_->typecheck(printer, varsToType);
	}
    for (unsigned idx = 0 ;  idx < parms_.count() ;  idx += 1) {
    	last = new JoinType(last, parms_[idx]->typecheck(printer, varsToType));
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

SecType* PEEvent::typecheck(SexpPrinter&, map<perm_string, SecType*>&varsToType) const
{
	throw "PEEvent";
}
void PEEvent::collect_idens(set<perm_string>&s) const
{
  throw "PEEvent";
}
// float constants have label Low
SecType* PEFNumber::typecheck(SexpPrinter&, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}
void PEFNumber::collect_idens(set<perm_string>&s) const
{
  return;
}
SecType* PEIdent::typecheckName(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const {
  perm_string name = peek_tail_name(path_);
  map<perm_string,SecType*>::const_iterator find = varsToType.find(name);
  if (find != varsToType.end()) {
    SecType* tau = (*find).second;
    //If this is indexed (e.g., v[x]), they type may also be quantified by index (e.g., {|i| F i} )
    //If this selects more than one component (i.e., is not SEL_BIT) then ignore (likely will lead to
    //an error during z3 checking with Quantified types
    //TODO replace more than just the first index component (nested index types works on nested indexes)
    index_component_t index = path().back().index.front();
    if (index.sel == index_component_t::SEL_BIT) {
      tau = tau->apply_index(index.msb);
    }
    return tau;
  } else {
    cerr <<  "Unbounded var name: " << name.str() << endl;
    return ConstType::TOP;
  }
}

SecType* PEIdent::typecheckIdx(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const {
  SecType* result = ConstType::BOT;
  for (std::list<index_component_t>::const_iterator idxit = path_.back().index.begin();
       idxit != path_.back().index.end(); idxit++) {
    if (idxit->msb != NULL) {
      SecType *tmsb = idxit->msb->typecheck(printer, varsToType);
      if (tmsb != ConstType::BOT) {
	result = new JoinType(result, tmsb);
      }
    }
    if (idxit->lsb != NULL) {
      SecType *tlsb = idxit->msb->typecheck(printer, varsToType);
      if (tlsb != ConstType::BOT) {
	result = new JoinType(result, tlsb);
      }
    }
  }
  return result;
}

SecType* PEIdent::typecheck(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const
{
  //idents are like: varname[bit select]
  //need to join index label with name label
  SecType* namelbl = typecheckName(printer, varsToType);
  SecType* idxlbl = typecheckIdx(printer, varsToType);
  return new JoinType(namelbl, idxlbl);
}

void PEIdent::collect_index_exprs(set<perm_string>&s, map<perm_string, SecType*>&varsToType) {
  stringstream ss;
  SexpPrinter tmp(ss, 9999);
  SecType* appliedType = typecheckName(tmp, varsToType);
  appliedType->collect_dep_expr(s);
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
SecType* PENumber::typecheck(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}
void PENumber::collect_idens(set<perm_string>&s) const
{
  return;
}
// string constants have label Low
SecType* PEString::typecheck(SexpPrinter&, map<perm_string, SecType*>&varsToType) const
{
	return ConstType::BOT;
}
void PEString::collect_idens(set<perm_string>&s) const
{
  return;
}
SecType* PETernary::typecheck(SexpPrinter&, map<perm_string, SecType*>&varsToType) const
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

SecType* PEUnary::typecheck(SexpPrinter&printer, map<perm_string, SecType*>&varsToType) const
{
	return expr_->typecheck(printer, varsToType);
}
void PEUnary::collect_idens(set<perm_string>&s) const
{
  expr_->collect_idens(s);
}
SecType* PEDeclassified::typecheck(SexpPrinter&,
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
BaseType* PEConcat::check_base_type(SexpPrinter&printer,
        map<perm_string, BaseType*>&varsToBase){

    // Default to combinational. Sequential if anything is sequential.
    // Not sure that this actually makes sense...
    //
    // How about: can be all sequential or all combinational but not a mix.
    //
  BaseType* returnType = NULL;
  if (repeat_!=NULL) {
    returnType = repeat_->check_base_type(printer, varsToBase);
  } else if ( parms_.count() > 0 ){
    returnType = parms_[0]->check_base_type(printer, varsToBase);
  }
  assert(returnType);
  for (unsigned idx = 0 ;  idx < parms_.count() ;  idx += 1) {
    //TODO define equality correctly and then just check it here.
    if(parms_[idx]->check_base_type(printer, varsToBase)->isSeqType() !=
       returnType->isSeqType()){
      cout << "PEConcat found with multiple base types (com/seq)" << endl;
      assert(false);
    }
  }
  return returnType;
}

BaseType* PEIdent::check_base_type(SexpPrinter&,
        map<perm_string, BaseType*>&varsToBase) {
    return varsToBase[peek_tail_name(path())];
}
