// REQUIRES: termination
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -check termination -se-exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

#include <assert.h>

extern int nondet(void);

int main(void) {
	int n = 100;

	int j = 0;
	while (n > 0) {
		--n;
	}
	// CHECK-NOT: [non-termination]: an infinite execution found

	assert(n <= 0);
	// CHECK-NOT: assertion failed!
	// CHECK: Found errors: 0
}
