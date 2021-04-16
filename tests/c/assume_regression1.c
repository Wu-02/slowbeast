#include <assert.h>

// REQUIRES: bounded
// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

#define N 5
#define M 2
int main(void) {
        int x = nondet();
        __VERIFIER_assume(x == 1);
        int i;
        for (i = 0; i < N; ++i) {
                assert((i <= M && x - i == 1) || (i > M && x == i));
                // CHECK-NOT: assertion failed!
                // CHECK: Found errors: 0
                if (i == M) {
                        --x;
                }
                ++x;
        }
}
