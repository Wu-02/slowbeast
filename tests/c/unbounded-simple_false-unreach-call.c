#include <assert.h>

// Until we have exit-on-error, we must require kind, because se will
// run indefinitely...
// REQUIRES: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int x = nondet_int();
	if (x < 0)
		return 0;

	while (x > 0) {
		--x;
	}
	assert(x != 0);

	// CHECK: assertion failed!
	// CHECK: Found errors: 1
}
