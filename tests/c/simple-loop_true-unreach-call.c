#include <assert.h>

// -kind does not terminate on this test right now.
// (only with -kind-2 or -kind-basic)
// UNSUPPORTED: kind

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
	int x = nondet_int();
	if (x != 0) {
		return 0;
	}

	for (int i = 0; i < 1; ++i) {
		//assert(x == 0);
		//assert(i == 0);
		++x;
	}

	assert(x == 1);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}

