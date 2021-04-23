#include <assert.h>

// REQUIRES: se
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s



int main(void) {
    int x;
    int *p = &x;
    int *q = &x;
    goto L1; // create edge in CFA
L1:
    *p = 1;
    *q = 2;
L2:
    // Can it happen in BSE that we first resolve
    // that x == 2 and then x == 1 since we do not
    // track the order of writes inside one block/edge?

L3:
    assert(x == 2);

    // CHECK-NOT: assertion failed!
    // CHECK-NOT: Error found.
    // CHECK: Found errors: 0
}
