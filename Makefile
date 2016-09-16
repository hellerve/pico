override CARGS+=-j2 --force-reinstalls
#Installs
all: install

install:
	cabal install $(CARGS)

debug:
	cabal configure --enable-executable-profiling
	cabal build -auto-all -caf-all -fforce-recomp && cabal test && cabal install $(CARGS)

#Runs all tests
test:
	for i in zepto-tests/test-*; do echo""; echo "Running test $$i"; echo "---"; zepto $$i; echo "---"; done

clean:
	rm -r dist
