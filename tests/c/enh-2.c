// UNSUPPORTED: bself
// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: timeout 60 %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

#include <assert.h>


int main(void) {
	int x = 0, i = 0;
	int N = nondet();
	if (N <= x)
		return 0;
	while (x < N) {
		if (x < i)
			--i;
		++x;
		i += 2;
	}

	assert(x == i - 1);
}
