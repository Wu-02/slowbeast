all: autopep

pylint:
	pylint slowbeast/
autopep:
	autopep8 --in-place --aggressive --aggressive --recursive slowbeast

.PHONY: all autopep pylint
