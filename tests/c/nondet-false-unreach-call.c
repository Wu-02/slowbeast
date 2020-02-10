#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int a = nondet_int();
	int b = 4;
	assert(a + b == 7);
	// CHECK: assertion failed!
	// CHECK: Found errors: 1
	return 0;
}
