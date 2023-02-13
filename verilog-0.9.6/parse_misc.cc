/*
 * Copyright (c) 1998-1999 Stephen Williams (steve@icarus.com)
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

#include "config.h"

#include "parse_misc.h"
#include <iostream>
#include <list>

extern const char *vl_file;
unsigned error_count     = 0;
unsigned warn_count      = 0;
unsigned long based_size = 0;

std::ostream &operator<<(std::ostream &o, const YYLTYPE &loc) {
  if (loc.text)
    o << loc.text << ":";
  o << loc.first_line;
  return o;
}

named_pexpr_t *nextify_named_pexpr(named_pexpr_t *n) {
  named_pexpr_t *ret = new named_pexpr_t();
  std::string name   = n->name.str();
  ret->name          = lex_strings.make((name + "_next_").c_str());
  ret->parm          = n->parm;
  return ret;
}

perm_string nextify_perm_string(perm_string s) {
  std::string name = s.str();
  return lex_strings.make((name + "_next_").c_str());
}

svector<named_pexpr_t *> *
nextify_named_pexpr_list(svector<named_pexpr_t *> *namelist) {
  svector<named_pexpr_t *> *ret =
      new svector<named_pexpr_t *>(namelist->count());
  for (size_t i = 0; i < ret->count(); i++) {
    (*ret)[i] = nextify_named_pexpr((*namelist)[i]);
  }
  return ret;
}

list<perm_string> *nextify_perm_strings(list<perm_string> *l) {
  list<perm_string> *ret = new list<perm_string>();
  typedef list<perm_string>::const_iterator ps_iter;
  assert(l);
  for (ps_iter cur = l->begin(); cur != l->end(); cur++) {
    perm_string nextified = nextify_perm_string(*cur);
    ret->push_back(nextified);
  }
  return ret;
}

list<perm_string> *nextify_net_decl_names(net_decl_assign_t *nda) {
  list<perm_string> *ret = new list<perm_string>();
  net_decl_assign_t *cur = nda;
  do {
    perm_string nextified = nextify_perm_string(cur->name);
    ret->push_back(nextified);
    cur = nda->next;
  } while (cur != NULL && cur != cur->next);
  return ret;
}

void VLerror(const char *msg) {
  error_count += 1;
  cerr << yylloc.text << ":" << yylloc.first_line << ": " << msg << endl;
}

void VLerror(const YYLTYPE &loc, const char *msg) {
  error_count += 1;
  cerr << loc << ": " << msg << endl;
  based_size = 0; /* Clear the base information if we have an error. */
}

void yywarn(const YYLTYPE &loc, const char *msg) {
  warn_count += 1;
  cerr << loc << ": warning: " << msg << endl;
}

int VLwrap() { return -1; }
