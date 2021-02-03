#include <assert.h>

int main(void) {
    int x = 0;
    int i = 0;

    while (i < 10) {
        ++i;
    }
    ++i;
    ++i;
    while(x < 10)
        ++x;

    assert(x == i);
}
