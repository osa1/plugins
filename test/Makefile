Main: Main.hs
	ghc-stage2 -fplugin=Plugins --make $^ -fforce-recomp -ddump-simpl -ddump-ds -ddump-to-file -ddump-stg -dcore-lint

clean:
	rm -f *.dump-*
	rm -f *.o
	rm -f *.hi
	rm -f Main
