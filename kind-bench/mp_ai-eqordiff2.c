#include <assert.h>

#define N 5
#define M 2
int main(void) {
//       int x = nondet();
//       __VERIFIER_assume(x == 1);
        int x = 1;
        int i;
        for (i = 0; i < N; ++i) {
                // assertion made from the first state
               // assert(x == 1 || i > 0);
                // assertion from bifurcation point
                // assert((i <= M && x - i == 1) || (i > M && x == i));
                //assert((i <= 2 && x == i + 1) || (i > 2 && x == i));
                // THIS we want!
                assert((x == i + 1) || (i > 2 && x == i));
                if (i == M) {
                        --x;
                }
                ++x;
        }
        //assert(i > 9);
        //assert (x == N);
}
