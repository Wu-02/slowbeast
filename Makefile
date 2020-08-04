all: autopep

pylint:
	pylint slowbeast/
autopep:
	autopep8 --in-place --aggressive --aggressive --recursive slowbeast

check:
	lit --path=$(shell pwd) -D OPTS="-step=instr" tests/
	lit --path=$(shell pwd) -D OPTS="-step=block" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kind" tests/
	lit --path=$(shell pwd) -D OPTS="-se -kind -kind-naive" tests/

check-v:
	lit --path=$(shell pwd) -vv -D OPTS="-step=instr" tests/
	lit --path=$(shell pwd) -vv -D OPTS="-step=block" tests/
	lit --path=$(shell pwd) -vv -D OPTS="-se -kind" tests/
	lit --path=$(shell pwd) -vv -D OPTS="-se -kind -kind-naive" tests/

.PHONY: all autopep pylint check check-v
