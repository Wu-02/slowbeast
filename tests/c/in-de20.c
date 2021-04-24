// source: sv-benchmarks
#include <assert.h>

// REQUIRES: bself
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 120 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int x=n, y=0, z;
  while(x>0)
  {
    x--;
    y++;
  }

  z = y;
  while(z>0)
  {
    x++;
    z--;
  }

  assert(x==n);
  // CHECK-NOT: assertion failed!
  // CHECK-NOT: Error found.
  // CHECK: Found errors: 0
  return 0;
}
