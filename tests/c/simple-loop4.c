#include <assert.h>

// UNSUPPORTED: bse
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main() {
        int x = 1;
        int i;
        for (i = 0; i < 5; ++i) {
                if (i == 1)
                        --x;
                ++x;
        }

        assert (x == i);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
