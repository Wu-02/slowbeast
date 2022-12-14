#include <assert.h>

// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

const char *str = "Hello, world!";
int main() {
	assert(str[0] == 'H');
	assert(str[1] == 'e');
	assert(str[2] == 'l');
	assert(str[3] == 'l');

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
