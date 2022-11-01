#include <assert.h>

int a;

// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main() {
	assert(a == 0);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
