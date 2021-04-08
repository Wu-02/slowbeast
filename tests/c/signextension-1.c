#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: timeout 30 sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
    unsigned short int allbits = -1;
    short int signedallbits = allbits;
    int signedtosigned = signedallbits;

    assert(signedtosigned != -1);

    // CHECK: Error found.
    // CHECK: Found errors: 1
}

