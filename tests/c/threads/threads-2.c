// REQUIRES: se
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -threads -exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

#include <pthread.h>
#include <assert.h>

int x, y;

void *foo(void *data) {
	(void)data;
	x = 1;
	y = 1;
	assert(x + y == 2);

	pthread_exit(0);
}

int main(void) {
	pthread_t tid;
	pthread_create(&tid, 0, foo, 0);

	y = 0;
	x = 1;

	pthread_join(tid, 0);

	// CHECK: [assertion error]: assertion failed!

	return 0;
}
