#include <assert.h>

int main(void) {
    int x = 1;
    while (x) {
        if (x > 1) {
            --x;
            assert(x == 1);
        } else
            ++x;
    }
}
