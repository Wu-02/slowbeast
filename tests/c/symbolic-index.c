#include <assert.h>

// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s



extern unsigned long input(void);

int main(void) {
    unsigned long n = input();
    int array[10];
    array[0] = 0;
    if (n == 0)
        assert(array[n] == 0);

	// CHECK-NOT: assertion failed!
	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}
