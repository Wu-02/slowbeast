// taken from https://web.eecs.umich.edu/~weimerw/p/weimer-icse2014-preprint.pdf
// (they taken it from Gulwani et al.)
//
#include <assert.h>

int  main(){
	int x = nondet();
	int y=5;
	if (x>y)
		x=y;
	while(x<=10){
		if(x>=5)
			y=y+1;
		x=x+1;
	}
    assert(y == 11);
	//assert(y==x+1);
}
