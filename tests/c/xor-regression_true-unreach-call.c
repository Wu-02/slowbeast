#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out -step=%step %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	assert((3 ^ 1) == 2);
	// CHECK-NOT: assertion failed!
}
