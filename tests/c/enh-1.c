// UNSUPPORTED: bself
// REQUIRES: unbounded
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

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
