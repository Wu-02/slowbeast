#include <assert.h>

// UNSUPPORTED: kind
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s



int foo2(int y) {
    return y + 1;
}

int foo(int y) {
    return foo2(y);
}

int main(void) {
    int x = 4;
    int y = foo(x);
    assert(y != 5);

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
