#include <assert.h>

// UNSUPPORTED: bse
// UNSUPPORTED: bself
// RUN: rm -rf %t-out
// RUN: timeout 30 %sb -out-dir=%t-out %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

int main() {
	int array[10];
	int n = 7;
	array[n+1] = 1;
	assert(array[n] == 1);
	// CHECK: [memory error] - uninitialized read
	// CHECK: Found errors: 1
}
