#!/bin/bash

TESTS="loadstore1"
FAILED="no"

for T in $(echo $TESTS); do
	python "$T.py" > "$T.tmp"
	diff "$T.tmp" "$T.output" || FAILED="yes"; echo "$T failed!" 1>&2
	rm "$T.tmp"
done

[ $FAILED = "no" ]
