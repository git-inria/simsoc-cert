#ifndef COMMON_HPP
#define COMMON_HPP

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
