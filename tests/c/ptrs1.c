#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main(void) {
    int i = 0;
    if (i > 0)
        abort();

   int array[2];
   int *p = array;
   goto L1;
L1:
   array[0] = 1;
   goto L2;
L2:
   array[1] = 2;
   goto L3;
L3:
   goto L4;
L4:
   assert(*p + *(p + 1) == 3);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
