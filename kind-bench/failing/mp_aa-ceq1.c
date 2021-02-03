#include <assert.h>

int main(void) {
        int c = nondet();
        int x = 0;
        int i = 0;
        for (; i < 2; ++i) {
                if (!c) {
                        ++x;
                } else {
                        x += 2;
                }
        }
        assert (c ? x == 2*i : x == i);
}
