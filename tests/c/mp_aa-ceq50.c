#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: kind
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main() {
    int i = 0;
    int x = 1;
    while (i < 100) {
        if (i >= 50) {
            i += 2;
        } else {
            ++i;
            ++x;
        }
        if (i == 1)
            --x;
    }
    assert(x == 50);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
