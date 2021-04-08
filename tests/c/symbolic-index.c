#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s



extern unsigned long input(void);

int main(void) {
    unsigned long n = input();
    int array[10];
    array[0] = 0;
    if (n == 0)
        assert(array[n] == 0);

	// CHECK-NOT: assertion failed!
	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}