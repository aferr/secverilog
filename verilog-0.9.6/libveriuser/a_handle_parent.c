/*
 * Copyright (c) 2003 Stephen Williams (steve@icarus.com)
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
#ifdef HAVE_CVS_IDENT
#ident "$Id: a_handle_parent.c,v 1.2 2003/06/04 01:56:20 steve Exp $"
#endif

#include  <vpi_user.h>
#include  <acc_user.h>
#include  "priv.h"

handle acc_handle_parent(handle obj)
{
      vpiHandle scope = vpi_handle(vpiScope, obj);

      while (scope && (vpi_get(vpiType, scope) != vpiModule))
	    scope = vpi_handle(vpiScope, scope);

      return scope;
}


handle acc_handle_scope(handle obj)
{
      return vpi_handle(vpiScope, obj);
}

/*
 * $Log: a_handle_parent.c,v $
 * Revision 1.2  2003/06/04 01:56:20  steve
 * 1) Adds configure logic to clean up compiler warnings
 * 2) adds acc_compare_handle, acc_fetch_range, acc_next_scope and
 *    tf_isetrealdelay, acc_handle_scope
 * 3) makes acc_next reentrant
 * 4) adds basic vpiWire type support
 * 5) fills in some acc_object_of_type() and acc_fetch_{full}type()
 * 6) add vpiLeftRange/RigthRange to signals
 *
 * Revision 1.1  2003/03/13 04:35:09  steve
 *  Add a bunch of new acc_ and tf_ functions.
 *
 */

