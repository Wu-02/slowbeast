#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
  unsigned int x = 7;

  while (x > 1) {
    x -= 2;
  }

  assert(x % 2 == 0);

  // CHECK: Error found.
  // CHECK: Found errors: 1
}
