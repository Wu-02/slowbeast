#include <assert.h>

int main(void) {
        unsigned x = 1;
        unsigned i = 0;
        //for (i = 0; i < 10; ++i) { // 'ts ok
        for (i = 0; i < 1000; ++i) { // don't work
                if (i == 1)
                        --x;
                ++x;
        }

        for (; i < 12; ++i) {
            ++x;
        }

        assert(x == i);
}
