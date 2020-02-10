#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out -step=%step %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int array[10];
	array[4] = 1;
	// CHECK-NOT: assertion failed!
	assert(array[4] == 1);
	// CHECK: Found errors: 0
}
