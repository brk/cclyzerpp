#ifndef __UNKNOWN_H__
#define __UNKNOWN_H__

#include <iostream>

template <typename T>
static void unknown(const std::string &s, T t) {
  std::cerr << "[warn] Unknown " << s << " " << t << std::endl;
}

#endif
