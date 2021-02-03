#include <assert.h>

#define N 5
#define M 2
int main(void) {
//       int x = nondet();
//       __VERIFIER_assume(x == 1);
        int x = 0;
        int i;
        for (i = 0; i < N; ++i) {
                if (i == 1)
                        break;
                if (i == 3)
                        break;
                ++x;
        }
        assert (x == i);
}
