#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -se-exit-on-error -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

int main()
{
  int x=__VERIFIER_nondet_int();
  int y=__VERIFIER_nondet_int();
  int z=__VERIFIER_nondet_int();

  while(x<100 && 100<z) 
  {
    _Bool tmp=__VERIFIER_nondet_bool();
    if (tmp)
   {
     x++;
   }
   else
   {
     x--;
     z--;
   }
  }                       
    
  assert(0);    

  // CHECK: Error found.
  // CHECK: Found errors: 1
  return 0;
}


