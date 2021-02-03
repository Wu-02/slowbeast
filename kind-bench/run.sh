TO=20

SB="$(dirname 0)/../sb"

for F in *.c; do
    echo "$F" | grep -q -- '-bug-'
    hasbug=$?

    echo "timeout $TO $SB -kind $F &>$F.log"
    timeout $TO $SB -kind $F &>$F.log
    ret=$?
    if grep -q 'Found errors: 0' $F.log; then
        if [ $hasbug -eq 0 ]; then
            echo "FAILED (false negative)"
        else
            echo "PASSED (true negative)"
        fi
    elif grep -q 'Error found.' $F.log; then
        if [ $hasbug -eq 0 ]; then
            echo "PASSED (true positive)"
        else
            echo "FAILED (false positive)"
        fi
    else
        if [ $ret -eq 124 ]; then
            echo "FAILED: timeout"
        else
            echo "FAILED: retval $ret"
        fi
    fi
done
