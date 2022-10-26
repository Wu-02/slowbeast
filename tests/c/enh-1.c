// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: timeout 60 %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | FileCheck %s

#include <assert.h>

#define N 1000000

int main(void) {
	int x = 0, i = 0;
	while (x < N) {
		if (x < i)
			--i;
		++x;
		i += 2;
	}

	assert(x == i - 1);
}
