all: autopep

pylint:
	pylint slowbeast/
autopep:
	autopep8 --in-place --aggressive --aggressive --recursive slowbeast

check:
	lit --path=$(shell pwd) tests/

check-v:
	lit --path=$(shell pwd) -vv tests/

.PHONY: all autopep pylint check check-v
