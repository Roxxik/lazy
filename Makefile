.PHONY: all run name

all:
	ghc -O2 lazy.hs

run:
	@./lazy

name:
	@echo lazy
