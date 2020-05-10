all:
	happy -gca ParGramatyka.y
	alex -g LexGramatyka.x
	ghc --make runInterpreter.hs -o interpreter
	

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocGramatyka.* LexGramatyka.* ParGramatyka.* LayoutGramatyka.* SkelGramatyka.* PrintGramatyka.* TestGramatyka.* AbsGramatyka.* TestGramatyka ErrM.* SharedString.* ComposOp.* gramatyka.dtd XMLGramatyka.* Makefile* 
	

