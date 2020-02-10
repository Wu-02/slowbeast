extern void __slowbeast_print();

// RUN: clang %s -emit-llvm -g -c -o %t.bc
// RUN: rm -rf %t-out
// RUN: sb -out-dir=%t-out -step=%step %t.bc &>%t.log
// RUN: cat %t.log | FileCheck %s


int main(void) {
	int x = nondet_int();
	int y = nondet_int();
	if (x > 0) {
		__slowbeast_print(x, y);
		if (y > 0) {
			__slowbeast_print(x, y);
		} else {
			__slowbeast_print(x, y);
		}
	} else {
		__slowbeast_print(x, y);
	}

	// CHECK: Executed paths: 3
	// CHCEK: Number of forks on branches: 2
	// CHECK: Found errors: 0
}
