#include <assert.h>

// REQUIRES: unbounded
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


int main() {
	int x = nondet_int();
	if (x < 0) {
		return 0;
	}

	while (x > 0) {
		while (x > 10)
			--x;

		--x;
	}

	assert(x == 0);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}

