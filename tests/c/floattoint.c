#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s



int main() {
    int a = 0;
    float f = (float) a;
    assert(f >= 0.0f && f <= 0.0f);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
