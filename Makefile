all: pylint check

# LINTERS AND STATIC CHECKERS
pylint:
	pylint slowbeast/

fixme:
	pylint --enable=fixme slowbeast/

# FORMATTING
black:
	black slowbeast/

autopep:
	autopep8 --in-place --aggressive --aggressive --recursive slowbeast


# TESTING
check:
	lit --path=$(shell pwd) -D OPTS="-se-step=block" tests/
	lit --path=$(shell pwd) -D OPTS="-se -bse" tests/
	lit --path=$(shell pwd) -D OPTS="-se -bself" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kindse" tests/

check-bself:
	lit --path=$(shell pwd) -vv -D OPTS="-bself" tests/

check-kindse:
	lit --path=$(shell pwd) -vv -D OPTS="-kindse" tests/

check-all:
	lit --path=$(shell pwd) -D OPTS="-se-step=instr" tests/
	lit --path=$(shell pwd) -D OPTS="-se-step=block" tests/
	lit --path=$(shell pwd) -D OPTS="-se-incremental-solving" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kind" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kind -kind-naive" tests/
	lit --path=$(shell pwd) -D OPTS="-se -bse" tests/
	lit --path=$(shell pwd) -D OPTS="-se -bself" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kindse" tests/

check-v:
	lit --path=$(shell pwd) -vv -D tests/
	lit --path=$(shell pwd) -vv -D OPTS="-bself" tests/
	lit --path=$(shell pwd) -vv -D OPTS="-kindse" tests/

.PHONY: all pylint black autopep check check-bself check-all check-v
