#include <assert.h>


// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out  %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

void __slowbeast_print(int);

int main(void) {
	int a = 3;
	int b = 4;
	__slowbeast_print(a+b);
	assert(a + b == 7);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
	return 0;
}
