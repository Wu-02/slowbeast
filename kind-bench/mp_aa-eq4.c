#include <assert.h>

int main(void) {
        int c = nondet();
        unsigned x = 0;
        unsigned n = 0;
        while (nondet()) {
                if (nondet()) {
                        ++x;
                        ++n;
                }
        }
        assert(x == n);
}
