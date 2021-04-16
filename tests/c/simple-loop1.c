#include <assert.h>

// UNSUPPORTED: bse
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

#define N 5
#define M 2
int main(void) {
    int x = nondet();
    __VERIFIER_assume(x == 0);
    int i;
    for (i = 0; i < N; ++i) {
        if (i == 1)
                break;
        ++x;
    }
    assert (x == i);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
