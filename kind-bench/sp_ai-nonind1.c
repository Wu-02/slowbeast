#include <assert.h>

int main(void) {
    int i=0;
    while(i<5) {
        i++;
        //assert(i != 3);
        assert(i >= 0 || i < -1);
    }
    return 0;
}
