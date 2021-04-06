#include <assert.h>

// UNSUPPORTED: bse
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int array[10];
	int n = 7;
	array[n+1] = 1;
	assert(array[n] == 1);
	// CHECK: [memory error] - uninitialized read
	// CHECK: Found errors: 1
}
