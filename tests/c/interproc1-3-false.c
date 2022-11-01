#include <assert.h>

// UNSUPPORTED: kind
// UNSUPPORTED: cfkind
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

void foo2(int y) {
    assert(y + 1 != 5);
}

void foo(int y) {
    foo2(y + 1);
}

int main(void) {
    int x = 2;
    foo(x + 1);

	// CHECK: Error found.
	// CHECK: Found errors: 1
}
