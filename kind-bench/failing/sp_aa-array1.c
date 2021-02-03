#include <assert.h>

// from paper Verification of Java Programs using  Symbolic Execution and Invariant Generation
int main(void) {
        int a[10];
        int i = 0;
        for (; i < 10; ++i) {
            a[i] = 0;
        }
        assert (a[0] == 0);
}
