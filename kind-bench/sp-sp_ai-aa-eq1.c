#include <assert.h>

// REQUIRES: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 10 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int x = nondet_int();
	if (x < 0) {
		return 0;
	}

	while (x > 0) {
		--x;
	}

	for (int i = 0; i < 1; ++i) {
		assert(i == x);
		++x;
	}

	assert(x == 1);

	// CHECK-NOT: assertion failed!
	// CHECK: Enumerating paths done!
	// CHECK: Found errors: 0
}

