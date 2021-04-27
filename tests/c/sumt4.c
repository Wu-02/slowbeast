// source: sv-benchmarsk
#include <assert.h>

// REQUIRES: bself
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 60 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


int SIZE = 20000001;
unsigned int __VERIFIER_nondet_uint();
int main() {
  unsigned int n=0,i=0,k=0,j=0,l=0;
  unsigned int v4=0;
  n = __VERIFIER_nondet_uint();
  if (!(n <= SIZE)) return 0;
  while( l < n ) {
	
	  if(!(l%4))
	    v4 = v4 + 1;
	  else if(!(l%3))
	    i = i + 1;
	  else if(!(l%2)) 
		  j = j+1;
	  else 
	    k = k+1;
    l = l+1;
  }
  assert((i+j+k+v4) == l);
  // CHECK-NOT: assertion failed!
  // CHECK: Found errors: 0
  return 0;
}

