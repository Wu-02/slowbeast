#include <assert.h>

// UNSUPPORTED: bse
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s



int main() {
    int a = 0;
    float f = (float) a;
    assert(f >= 0.0f && f <= 0.0f);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
