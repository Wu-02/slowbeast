#include <assert.h>

void __slowbeast_print(int);
int main(void) {
	int a = 3;
	int b = 4;
	__slowbeast_print(a+b);
	assert(a + b == 7);
	return 0;
}
