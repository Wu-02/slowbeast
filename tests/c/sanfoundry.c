#include <assert.h>

// UNSUPPORTED: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


unsigned nondet(void);

int main()
{
    unsigned int array[10];
    unsigned int i = 0;
	array[0] = nondet();
    if (array[i] == 0) {
        assert(array[i] == 0);
        // CHECK-NOT: assertion failed!
        // CHECK-NOT: Error found.
        // CHECK: Found errors: 0
    }
  return 0;
}
