#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out  %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int array[10];
	int n = 7;
	array[n+1] = 1;
	assert(array[n] == 1);
	// CHECK: Read from uninitialized memory
	// CHECK: Found errors: 1
}
