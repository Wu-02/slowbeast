#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
	int x = 1;
	int i = 0;
	for (; i < 5; ++i) {
		++x;
	}

	assert(x == i);

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
