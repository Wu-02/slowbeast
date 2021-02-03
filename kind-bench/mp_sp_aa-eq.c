#include <assert.h>

int main(void) {
        unsigned  x = 0;
        unsigned  i = 0;
        unsigned int n = nondet();
        if (n < 2)
            return 0;
        for (; i < n; ++i) {
                if (i == 0)
                        ++x;
                if (i == 1)
                        --x;
                ++x;
        }

        if (nondet()) {
                ++i;
                ++x;
        }

        assert (x == i);
        assert (x == n);
}
