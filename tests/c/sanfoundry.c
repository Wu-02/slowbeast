#include <assert.h>

// UNSUPPORTED: kind
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s


unsigned nondet(void);

int main()
{
    unsigned int array[10];
    unsigned int i = 0;
	array[0] = nondet();
    if (array[i] == 0) {
        assert(array[i] == 0);
        // CHECK-NOT: assertion failed!
        // CHECK-NOT: Error found.
        // CHECK: Found errors: 0
    }
  return 0;
}
