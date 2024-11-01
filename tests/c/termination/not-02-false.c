// REQUIRES: termination
// RUN: rm -rf %t-out
// RUN: %sb -out-dir=%t-out -check termination -se-exit-on-error %opts %s &>%t.log
// RUN: cat %t.log | %FILECHECK %s

// SPDX-FileCopyrightText: 2021 Y. Cyrus Liu <yliu195@stevens.edu>
//
// SPDX-License-Identifier: Apache-2.0

/*
 * Date: 2021-06-21
 * Author: yliu195@stevens.edu
 */

extern int __VERIFIER_nondet_int(void);

int main(){
    int a, x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    a = 1;
    while (x<0){
        y = ~a;
        x = y;

	// CHECK: [non-termination]: an infinite execution found
    }
}
