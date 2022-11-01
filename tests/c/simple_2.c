#include <assert.h>

// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main(void) {
	int x = nondet_int();
	int n = x;
	x--;
	assert(x == n - 1);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
