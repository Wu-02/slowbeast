#include <assert.h>

int a;

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	assert(a == 0);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
