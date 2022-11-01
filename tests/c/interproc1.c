#include <assert.h>

// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s



void foo(int y) {
    assert(y == 5);
}

int main(void) {
    int x = 5;
    foo(x);

	// CHECK-NOT: Error found.
	// CHECK: Found errors: 0
}
