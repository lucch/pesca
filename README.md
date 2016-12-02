This repository is a mirror of [Haskell's "pesca: Proof Editor for Sequent
Calculus"](https://hackage.haskell.org/package/pesca).

The code was fixed to work with recent versions of GHC.

---

# PESCA = Proof Editor for Sequent Calculus

(Companion to the book Structural Proof Theory by Sara Negri and Jan von Plato,
to appear at Cambridge University Press)

(c) Aarne Ranta 24/3/2000.

To run under Unix, type

    ./pesca

To the PESCA prompt |-, type

    ?

to see the available commands, or

    m

to see the manual (the latter assumes latex and xdvi are on your path).

The pesca shell script assumes the Haskell interpreter hugs is on your path.
You can also compile the Haskell source code by hbc or ghc; the Main module is
in the file Editor.hs.

[http://www.cs.chalmers.se/~aarne/pesca/](http://www.cs.chalmers.se/~aarne/pesca/)
