#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


int main()
{
  char string_A[2];
  unsigned int i, nc_A;
  
  string_A[0] = 1;
  string_A[1] = 0;

  nc_A = 0;
  while(string_A[nc_A]!='\0')
    nc_A++;

  i=0;
  assert(string_A[i] != 1);

  // CHECK: Error found.
  // CHECK: Found errors: 1
}

