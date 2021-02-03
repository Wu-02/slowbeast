#include <assert.h>

int main() {
    int w = 1, x = 0;
    int y = 0, i = 0;
    int n = nondet();
    _Bool z = 0;

    while (i < n) {
        if (w % 2)
            ++x;
        if (!z)
            ++y;
        ++w;
        z = !z;
        ++i;
    }
    assert(x == y);
}
