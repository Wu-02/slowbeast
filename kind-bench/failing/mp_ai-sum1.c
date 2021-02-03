#include <assert.h>

int main() {
	int x = nondet_int();
	if (x < 0 || x > 3) {
		return 0;
	}

	int n = 0;
	for (int i = 1; i < x; ++i) {
		n += i;
	}
	assert(n == x*(x-1)/2);
}
