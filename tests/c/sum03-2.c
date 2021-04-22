// source: sv-benchmarks
#include <assert.h>

#define a (2)
unsigned int __VERIFIER_nondet_uint();

// REQUIRES: unbounded
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() { 
  unsigned int sn=0;
  unsigned int x=0;

  while(1){
    sn = sn + a;
    x++;
    assert(sn==x*a || sn == 0);
  }

  // CHECK-NOT: assertion failed!
  // CHECK: Found errors: 0
}

