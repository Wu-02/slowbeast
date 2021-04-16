#include <assert.h>

// UNSUPPORTED: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

void foo2(int y) {
    assert(y + 1 == 5);
}

void foo(int y) {
    foo2(y + 1);
}

int main(void) {
    int x = 2;
    foo(x + 1);

	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}