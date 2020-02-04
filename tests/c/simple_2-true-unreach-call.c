#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out  %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int x = nondet_int();
	int n = x;
	x--;
	assert(x == n - 1);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
