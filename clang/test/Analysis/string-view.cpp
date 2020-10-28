// RUN: %clang_analyze_cc1 -analyzer-checker=core,cplusplus.StringModeling\
// RUN:   -analyzer-checker=cplusplus.InnerPointer,cplusplus.StringView\
// RUN:   -std=c++17 -analyzer-output=text -verify %s

#include "Inputs/system-header-simulator-cxx.h"

std::basic_string_view::npos = size_type(-1);
/*
char CopyCtorUseAfterClear() {
  std::string S("abc");
  std::string_view V(S);
  std::string_view W(V); // expected-note {{Pointer to inner buffer of 'std::string' obtained here}}
  S.clear(); // expected-note {{Inner buffer of 'std::string' reallocated by call to 'clear'}}
  return W.at(0); // expected-warning {{Inner pointer of container used after re/deallocation}}
  // expected-note@-1 {{Inner pointer of container used after re/deallocation}}
}

char CopyAssignUseAfterClear() {
  std::string S("abc");
  std::string_view V;
  V = S;
  std::string_view W;
  W = V; // expected-note {{Pointer to inner buffer of 'std::string' obtained here}}
  S.clear(); // expected-note {{Inner buffer of 'std::string' reallocated by call to 'clear'}}
  return W[0]; // expected-warning {{Inner pointer of container used after re/deallocation}}
  // expected-note@-1 {{Inner pointer of container used after re/deallocation}}
}

void CopyAssignUseAfterAutomaticFree() {
  std::string_view V;
  std::string_view W;
  {
    std::string S("abc");
    V = S;
    W = V; // expected-note {{Pointer to inner buffer of 'std::string' obtained here}}
  } // expected-note {{Inner buffer of 'std::string' deallocated by call to destructor}}
  W.remove_prefix(1); // expected-warning {{Inner pointer of container used after re/deallocation}}
  // expected-note@-1 {{Inner pointer of container used after re/deallocation}}
}

std::string_view ReturnView() {
  std::string S;
  std::string_view V(S); // expected-note {{Pointer to inner buffer of 'std::string' obtained here}}
  S.clear(); // expected-note {{Inner buffer of 'std::string' reallocated by call to 'clear'}}
  return V; // expected-warning {{Inner pointer of container used after re/deallocation}}
  // expected-note@-1 {{Inner pointer of container used after re/deallocation}}
}
*/
void ViewSubstr() {
  std::string S("abc");
  std::string_view V(S);
  std::string_view W = V.substr(1, 2); // expected-note {{Pointer to inner buffer of 'std::string' obtained here}}
  S.clear(); // expected-note {{Inner buffer of 'std::string' reallocated by call to 'clear'}}
  W.remove_prefix(1); // expected-warning {{Inner pointer of container used after re/deallocation}}
  // expected-note@-1 {{Inner pointer of container used after re/deallocation}}
}
