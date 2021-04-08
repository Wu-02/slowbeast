#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int x = 3;
	assert((x ^ (x >> 1u)) == 2);
	// CHECK-NOT: assertion failed!
}
