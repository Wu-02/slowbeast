#include <assert.h>

int main(void) {
        int x = 1;
        int i = 0;
        for (; i < 10; ++i) {
                if (i == 1)
                    --x;
                ++x;
        }
        assert (x == i);
}
