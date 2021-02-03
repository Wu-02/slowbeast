#include <assert.h>

int main(void) {
        int x = 0;
        int i = 0;
        for (; i < 10; ++i) {
                ++x;
        }
        int *p = &x;
        assert (*p == i);
}
