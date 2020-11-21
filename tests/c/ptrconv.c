#include <assert.h>

// REQUIRES: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
    int array[10];
    array[0] = 1;
    array[1] = 2;
    int *p = array;
    unsigned long pi = (unsigned long)p;
    pi += sizeof(int);
    p = (int *) pi;
    assert(*p == 2);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}