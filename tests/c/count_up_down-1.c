// source: sv-comp benchmarks
#include <assert.h>
extern unsigned int __VERIFIER_nondet_uint();

// REQUIRES: bself
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int x=n, y=0;
  while(x>0)
  {
    x--;
    y++;
  }
  assert(y==n);
  // CHECK-NOT: assertion failed!
  // CHECK: Found errors: 0
}

