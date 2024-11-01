#include <assert.h>

// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main(void) {
	int x = nondet_int();
	if (x < 0)
		return 0;

	while (x > 0) {
		--x;
	}
	assert(x == 0);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
