#include <assert.h>

// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

struct A {
    int a;
    int b;
};

int main() {
    struct A s;
    s.a = 1;
    s.b = 2;
    assert(s.a + s.b == 3);

	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
