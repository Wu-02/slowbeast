all: autopep

pylint:
	pylint slowbeast/
autopep:
	autopep8 --in-place --aggressive --aggressive --recursive slowbeast

check:
	lit --path=$(shell pwd) -D STEP=instr tests/
	lit --path=$(shell pwd) -D STEP=block tests/

check-v:
	lit --path=$(shell pwd) -D STEP=instr -vv tests/
	lit --path=$(shell pwd) -D STEP=block -vv tests/

.PHONY: all autopep pylint check check-v
