#include <assert.h>

int main(void) {
        unsigned x = 1;
        unsigned i = 0;
        const unsigned N = 10;
        while (i < N) {
                if (i == 5)
                        --x;

                assert (x == i || x == i + 1);
                ++i;
                ++x;
        }
}
