#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

struct A {
    int a;
    int b;
};

int main() {
    struct A s;
    s.a = 1;
    s.b = 2;
    assert(s.a + s.b == 3);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
