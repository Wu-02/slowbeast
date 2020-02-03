#include <assert.h>

int main() {
	int array[10];
	int n = 7;
	array[n] = 1;
	assert(array[n] == 1);
}
