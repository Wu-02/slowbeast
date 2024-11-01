all: mypy pylint check

# LINTERS AND STATIC CHECKERS
pylint:
	pylint slowbeast/

fixme:
	pylint --enable=fixme slowbeast/

# FORMATTING
black:
	black sb slowbeast/

autopep:
	autopep8 --in-place --aggressive --aggressive --recursive slowbeast

mypy:
	mypy . --exclude llvmlite --exclude benchexec --exclude slowbeast/parsers

pyre-infer:
	pyre infer -i

# TESTING
check:
	lit -j4 --path=$(shell pwd) -D OPTS="-se-step=block" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -bse" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -bself" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -threads" --filter='threads/.*\.c' tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-check termination" --filter='termination/.*\.c' tests/

check-bse:
	lit -j4 --path=$(shell pwd) -v -D OPTS="-bse" tests/

check-bself:
	lit -j4 --path=$(shell pwd) -D OPTS="-se -bself" tests/

check-bselff:
	lit -j4 --path=$(shell pwd) -D OPTS="-bselff" tests/

check-threads:
	lit -j4 --path=$(shell pwd) -D OPTS="-se -threads" --filter='threads/.*\.c' tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -threads -threads-dpor" --filter='threads/.*\.c' tests/

check-ais:
	lit -j4 --path=$(shell pwd) -D OPTS="-check termination -ais" --filter='termination/.*\.c' tests/

check-clam:
	lit -j4 --path=$(shell pwd) -v -D OPTS="-bse -external-invariants=clam" tests/
	lit -j4 --path=$(shell pwd) -a -D OPTS="-bself -external-invariants=clam" tests/


check-cfkind:
	lit -j4 --path=$(shell pwd) -a -D OPTS="-cfkind" tests/

check-all:
	lit -j4 --path=$(shell pwd) -D OPTS="-se-step=instr" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se-step=block" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se-incremental-solving" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -kind" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -kind -kind-naive" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -bse" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -bself" tests/
	lit -j4 --path=$(shell pwd) -D OPTS="-se -cfkind" tests/

check-v:
	lit -j4 --path=$(shell pwd) -a tests/
	lit -j4 --path=$(shell pwd) -a -D OPTS="-bself" tests/
	lit -j4 --path=$(shell pwd) -a -D OPTS="-cfkind" tests/

pyinstaller:
	pyinstaller -p ./llvmlite --collect-binaries z3 sb


.PHONY: all pylint black autopep check check-bself check-all check-v
