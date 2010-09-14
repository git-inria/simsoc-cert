#ifndef COMMON_H
#define COMMON_H

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#define TODO(msg) do {                                                  \
    printf("TODO: " msg " (" __FILE__ ":%d)\n",__LINE__);               \
    abort(); } while (0);
#define ERROR(msg) do {                                                 \
    printf("ERROR: " msg " (" __FILE__ ":%d)\n",__LINE__);              \
    abort(); } while (0);

#define unpredictable() ERROR("simulating something unpredictable")

typedef char bool;
#define true 1
#define false 0

extern bool sl_debug;
extern bool sl_info;
extern bool sl_exec;

#ifdef NDEBUG
#define DEBUG(X) ((void) 0)
#else
#define DEBUG(X) if (sl_debug) {X;}
#endif

#define INFO(X) if (sl_info) {X;}
#define EXEC(X) if (sl_exec) {X;}

#endif /* COMMON_H */
