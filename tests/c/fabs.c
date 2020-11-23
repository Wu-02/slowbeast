#include <assert.h>
#include <math.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


// fabs.i from SV-COMP

int main(void) {
  assert(fabs(+3.0) == +3.0);
  assert(fabs(-3.0) == +3.0);
  assert(fabs(-0.0) == -0.0);
  assert(fabs(-0.0) == +0.0);
  assert(fabs(-(__builtin_inff())) == (__builtin_inff()));

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
