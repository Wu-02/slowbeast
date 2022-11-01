#include <assert.h>

// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main(void) {
	int x = 1;
	int i = 0;
	for (; i < 2; ++i) {
		++x;
	}

	assert(x == i);

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
