// REQUIRES: termination
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -check termination -se-exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

/*  WhileFalse.c from SV-COMP benchmarks */

/*
 * Date: 2012-03-19
 * Author: leike@informatik.uni-freiburg.de
 *
 * The loop is equivalent to false,
 * f(x) = 0 is a ranking function.
 */
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	while (false) {
	}
	return 0;
	// CHECK-NOT: [non-termination]: an infinite execution found
	// CHECK: Found errors: 0
}
