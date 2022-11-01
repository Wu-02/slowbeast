// source: sv-comp benchmarks
#include <assert.h>
extern unsigned int __VERIFIER_nondet_uint();

// REQUIRES: bself
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

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

