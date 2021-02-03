#include <assert.h>

int main(void) {
        unsigned x = 1;
        unsigned i;
        const unsigned N = nondet();
        if (N < 2)
           return 0;
        for (i = 0; i < N; ++i) {
                if (i == 1)
                        --x;
                ++x;
        }
        assert (x == i);
}
