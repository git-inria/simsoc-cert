#ifndef CAML_CONFIG_H
#define CAML_CONFIG_H

#include "int64_init.h"

#define SIZEOF_INT 4 // sizeof(int)
#define SIZEOF_LONG 8 // sizeof(long)
#define SIZEOF_PTR 8 // sizeof(long *)
#define SIZEOF_SHORT 2 // sizeof(short)

#if defined(USE_INT64)
#  define CAML_INT64_EMUL_H
// if SIZEOF_LONG = 8 then
#  define ARCH_INT64_TYPE long
#  define ARCH_UINT64_TYPE unsigned long
// else match  "the longlong.c program"  with 
//   0-1-2)
//     #define ARCH_INT64_TYPE long long
//     #define ARCH_UINT64_TYPE unsigned long long
//   *) No suitable 64-bit integer type found, must use software emulation
//     if SIZEOF_PTR = 8 then failwith "This architecture has 64-bit pointers but no 64-bit integer type" ;
//     #undef ARCH_INT64_TYPE
//     #undef ARCH_UINT64_TYPE
#else
#  define CAML_INT64_NATIVE_H
// match  "the endian.c program"  with
// 0)
//   #define ARCH_BIG_ENDIAN
// 1)
#  undef ARCH_BIG_ENDIAN
// *) failwith TODO
#endif

/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*         Xavier Leroy and Damien Doligez, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id: config.h 10920 2011-01-06 14:20:52Z doligez $ */

/* [...] */

#if SIZEOF_INT == 4
typedef int int32;
typedef unsigned int uint32;
#define ARCH_INT32_PRINTF_FORMAT ""
#elif SIZEOF_LONG == 4
typedef long int32;
typedef unsigned long uint32;
#define ARCH_INT32_PRINTF_FORMAT "l"
#elif SIZEOF_SHORT == 4
typedef short int32;
typedef unsigned short uint32;
#define ARCH_INT32_PRINTF_FORMAT ""
#else
#error "No 32-bit integer type available"
#endif

#if defined(ARCH_INT64_TYPE)
typedef ARCH_INT64_TYPE int64;
typedef ARCH_UINT64_TYPE uint64;
#else
#  ifdef ARCH_BIG_ENDIAN
typedef struct { uint32 h, l; } uint64, int64;
#  else
typedef struct { uint32 l, h; } uint64, int64;
#  endif
#endif

/* [...] */

#endif /* CAML_CONFIG_H */
