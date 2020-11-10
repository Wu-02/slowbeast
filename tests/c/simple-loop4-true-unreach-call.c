#include <assert.h>

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out %opts %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s

int main() {
        int x = 1;
        int i;
        for (i = 0; i < 5; ++i) {
                if (i == 1)
                        --x;
                ++x;
        }

        /*
        if (c) {
                ++i;
                ++x;
        }
        */

        assert (x == i);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
