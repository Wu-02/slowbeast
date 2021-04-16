#include <assert.h>

extern unsigned nondet(void);

// REQUIRES: unbounded
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int x = nondet();
	if (x < 0) {
		return 0;
	}

	int n = 0;
	int y = x;
	int old_diff = x - n;
	while (x > 0) {
		--x;
		++n;
		assert(x - n == old_diff - 2);
		old_diff -= 2;
	}

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
