#include <assert.h>

void __slowbeast_print(int);
int main(void) {
	int a = nondet_int();
	int b = 4;
	__slowbeast_print(a+b);
	assert(a + b == 7);
	return 0;
}
