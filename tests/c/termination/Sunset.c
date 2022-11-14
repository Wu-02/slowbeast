// REQUIRES: termination
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -check termination -se-exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = __VERIFIER_nondet_int();

    while (i > 10) {
        if (i == 25) {
            i = 30;
        }
        if (i <= 30) {
            i = i-1;
        } else {
            i = 20;
        }
    }
	// CHECK: [non-termination]: an infinite execution found
	// CHECK: Found errors: 1

    return 0;
}
