#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: bself
// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

#define N 5
#define M 2

int x = 0;
void foo(void) {
        int i;
        for (i = 0; i < N; ++i) {
                ++x;
        }
        assert (x == i);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}

int main(void) {
        foo();
}
