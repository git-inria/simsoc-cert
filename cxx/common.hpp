#ifndef COMMON_HPP
#define COMMON_HPP

#include <inttypes.h>
#include <stdlib.h>

#include <iostream> // FIXME: replace by stdio.h

#define TODO(msg) do {                                                  \
    std::cout <<std::dec <<"TODO: " <<msg <<" (" __FILE__ ":" <<__LINE__ <<")\n"; \
    abort(); } while (0);
#define ERROR(msg) do {                                                 \
    std::cout <<std::dec <<"ERROR: " <<msg <<" (" __FILE__ ":" <<__LINE__ <<")\n"; \
    abort(); } while (0);

#define unpredictable() ERROR("simulating something unpredictable")

extern bool sl_debug;
extern bool sl_info;
extern bool sl_exec;

#ifdef NDEBUG
#define DEBUG(X) ((void) 0)
#else
#define DEBUG(X) if (sl_debug) {std::cout X;}
#endif

#define INFO(X) if (sl_info) {std::cout X;}
#define EXEC(X) if (sl_exec) {X;}

#endif // COMMON_HPP
