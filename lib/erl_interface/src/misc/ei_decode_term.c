/*
 * %CopyrightBegin%
 *
 * Copyright Ericsson AB 2001-2010. All Rights Reserved.
 *
 * The contents of this file are subject to the Erlang Public License,
 * Version 1.1, (the "License"); you may not use this file except in
 * compliance with the License. You should have received a copy of the
 * Erlang Public License along with this software. If not, it can be
 * retrieved online at http://www.erlang.org/.
 *
 * Software distributed under the License is distributed on an "AS IS"
 * basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
 * the License for the specific language governing rights and limitations
 * under the License.
 *
 * %CopyrightEnd%
 *

 */
#include <string.h>

#include "eidef.h"
#include "eiext.h"
#include "ei_decode_term.h"
#include "putget.h"

/* Returns 0 on successful encoding, -1 on error, and 1 if the term seems
   alright, but does not fit in the term structure. If it returns 0, the
   index will be incremented, and the term contains the decoded term. */

int ei_decode_ei_term(const char* buf, int* index, ei_term* term)
{
    const char* s = buf + *index, * s0 = s;
    int len, i, n, sign;
    char c;
    double f;

    if (term == NULL) return -1;
    c = term->ei_type = get8(s);
    switch (c) {
    case ERL_SMALL_INTEGER_EXT:
	term->value.i_val = get8(s);
	break;
    case ERL_INTEGER_EXT:
	term->value.i_val = get32be(s);
	break;
    case ERL_FLOAT_EXT:
    case NEW_FLOAT_EXT:
        return ei_decode_double(buf, index, &term->value.d_val);
    case ERL_ATOM_EXT:
	len = get16be(s);
	memcpy(term->value.atom_name, s, len); 
	term->value.atom_name[len] = '\0';
	s += len;
	break;
    case ERL_REFERENCE_EXT:
	/* first the nodename */
	if (get8(s) != ERL_ATOM_EXT) return -1;
	len = get16be(s);
	memcpy(term->value.ref.node, s, len);
	term->value.ref.node[len] = '\0';
	s += len;
        /* now the numbers: num (4), creation (1) */
	term->value.ref.n[0] = get32be(s);
	term->value.ref.len = 1;
	term->value.ref.creation = get8(s) & 0x03;
	break;
    case ERL_NEW_REFERENCE_EXT:
	/* first the integer count */
	term->value.ref.len = get16be(s);
	/* then the nodename */
	if (get8(s) != ERL_ATOM_EXT) return -1;
	len = get16be(s);
	memcpy(term->value.ref.node, s, len);
	term->value.ref.node[len] = '\0';
	s += len;
	/* creation */
	term->value.ref.creation = get8(s) & 0x03;
	/* finally the id integers */
	for (i = 0; (i<term->value.ref.len) && (i<3); i++) {
	    term->value.ref.n[i] = get32be(s);
	}
	if (term->value.ref.len > 3) {
	    s += 4 * (term->value.ref.len - 3);
	}
	break;
    case ERL_PORT_EXT:
	if (get8(s) != ERL_ATOM_EXT) return -1;
	len = get16be(s);
	memcpy(term->value.port.node, s, len);
	term->value.port.node[len] = '\0';
	term->value.port.id = get32be(s) & 0x0fffffff; /* 28 bits */;
	term->value.port.creation = get8(s) & 0x03;
	break;
    case ERL_PID_EXT:
	if (get8(s) != ERL_ATOM_EXT) return -1;
	/* name first */
	len = get16be(s); 
	memcpy(term->value.pid.node, s, len);
	term->value.pid.node[len] = '\0';
	s += len;
	/* now the numbers: num (4), serial (4), creation (1) */
	term->value.pid.num = get32be(s) & 0x7fff; /* 15 bits */
	term->value.pid.serial = get32be(s) & 0x1fff; /* 13 bits */
	term->value.pid.creation = get8(s) & 0x03; /* 2 bits */
	break;
    case ERL_SMALL_TUPLE_EXT:
	term->arity = get8(s);
	break; /*return 0;*/
    case ERL_LARGE_TUPLE_EXT:
	term->arity = get32be(s);
	break; /*return 0;*/
    case ERL_NIL_EXT:
	term->arity = 0;
	break;
    case ERL_STRING_EXT:
	term->size = get16be(s);
	return 0;
    case ERL_LIST_EXT:
	term->arity = get32be(s);
	break; /*return 0;*/
    case ERL_BINARY_EXT:
	term->size = get32be(s);
	return 0;
    case ERL_SMALL_BIG_EXT:
	if ((term->arity = get8(s)) != 4) return -1;
	sign = get8(s);
	/* Little Endian, and n always positive, except for LONG_MIN */
	n = get32le(s);
	if (sign) {
	    /* check for overflow */
	    if ((n - 1) < 0) return -1;
	    n = -n;
	} else {
	    /* check for overflow */
	    if (n < 0) return -1;
	}
	break;
    case ERL_LARGE_BIG_EXT:
	return 0;
    case ERL_PASS_THROUGH:
	return 0;
    case ERL_NEW_CACHE:
	return -1;
    case ERL_CACHED_ATOM:
	return -1;
    default:
	return -1;
    }
    *index += s-s0;
    return 1;
}
