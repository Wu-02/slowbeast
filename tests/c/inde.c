#include <assert.h>

// UNSUPPORTED: se
// UNSUPPORTED: bse
// UNSUPPORTED: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 60 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


unsigned __VERIFIER_nondet_uint(void);
int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int x=n, y=0, z;
  while(x>0)
  {
    //assert(n == x + y);
    x--;
    y++;
  }
  assert(x == 0 && (y == 0 || n == y));
  // CHECK-NOT: assertion failed!
  // CHECK-NOT: Error found.
  // CHECK: Found errors: 0
  return 0;
}
