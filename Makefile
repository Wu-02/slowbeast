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
	lit --path=$(shell pwd) -D OPTS="-se-incremental-solving" tests/
	lit --path=$(shell pwd) -D OPTS="-se -bself" tests/

#check-kind:
#	lit --path=$(shell pwd) -vv -D OPTS="-kind" tests/

check-bself:
	lit --path=$(shell pwd) -vv -D OPTS="-bself" tests/

check-all:
	lit --path=$(shell pwd) -D OPTS="-se-step=instr" tests/
	lit --path=$(shell pwd) -D OPTS="-se-step=block" tests/
	lit --path=$(shell pwd) -D OPTS="-se-incremental-solving" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kind" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kind -kind-naive" tests/

check-v:
	lit --path=$(shell pwd) -vv -D OPTS="-se-step=block" tests/
	lit --path=$(shell pwd) -vv -D OPTS="-se-incremental-solving" tests/
	lit --path=$(shell pwd) -vv -D OPTS="-se -bself" tests/

.PHONY: all pylint black autopep check check-bself check-all check-v
