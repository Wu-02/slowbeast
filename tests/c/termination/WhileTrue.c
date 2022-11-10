// REQUIRES: termination
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -check termination -se-exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

/*  WhileTrue.c from SV-COMP benchmarks */

/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Very simple example for non-termination
 */
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	while (true) {
		// do nothing
	}
	// CHECK: [non-termination]: an infinite execution found
	// CHECK: Found errors: 1
	return 0;
}
