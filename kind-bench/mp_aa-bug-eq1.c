#include <assert.h>

#define N 5
#define M 2
int main(void) {
        int x = 3;
        int i;
        for (i = 0; i < N; ++i) {
                if (i == 1)
                        break;
                ++x;
        }
        assert (x == i);
}
