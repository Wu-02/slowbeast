// REQUIRES: termination
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -check termination -se-exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

/*  Ex07.c from SV-COMP benchmarks */

typedef enum { false, true } bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = 0;//__VERIFIER_nondet_int();

    while (true) {
        if (i > 0) {
            i = i-1;
        }
        if (i < 0) {
            i = i+1;
        }
    }
    // CHECK: [non-termination]: an infinite execution found
    // CHECK: Found errors: 1

    return 0;
}
