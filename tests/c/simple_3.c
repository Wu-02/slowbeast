#include <assert.h>

// UNSUPPORTED: bse
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main(void) {
	int x = 0;
	int i = 0;
	for (; i < 10; ++i) {
		++x;
	}

	assert(x == i);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
