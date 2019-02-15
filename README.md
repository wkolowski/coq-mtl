# HSLib

This project is an offshoot of my [book on Coq](https://zeimer.github.io/) (in Polish). My motivation was to find the best presentation of the concept of monad before I write about it.

It then turned into a Coq library that tries to implement parts of Haskell standard library. The focus is on practical functional programming and not on category theory, although (nearly) all the classes come equipped with laws and instances have to obey them.

Recently I chose to write a monadic parser combinator library as a project for one (or rather, two) of my university courses. Since the parsers are monadic, they fit here perfectly. This development is based on the paper "Monadic Parser Combinators" by Graham Hutton and Erik Meijer.

At last, this project ended up being my BSc thesis. This development is based on the paper "Just do It: Simple Monadic Equational Reasoning" by Jeremy Gibbons and Ralf Hinze.

## Directory structure

* Base.v — utilities for the whole library
* Control/ — the most important classes (Functor, Applicative, Monad etc.) live here.
* Control/Monad/ - monad instances.
* Control/Monad/Trans/ - monad transformer instances.
* Control/Monad/Class/ - monadic classes.
* Misc/ — various things, not too interesting.
* Parser/ — monadic parser combinators.
* Theory/ — various theoretical results, relating applicative functors to monoidal functors, monads with bind to monads with join, kleisli triples to monads with bind and so on. A formalization of the 'Just Do It' paper also lives here.
* Thesis/ - directory containing my thesis.
* Trash/ - this should be self-explanatory.

## Done

Applicatives come equipped with all the necessary laws and notations. Most functions that in Haskell are doubled (like liftA2 and liftM2) here come only in the Applicative version.

Alternatives also come with notations and corresponding functions, but their laws are somewhat less polished. They are there already, but I need to think about them harder.

Monads come in three flavours:
* Control.Monad — monads whose definition is based on `>>=` (bind). This is closest to the definition from the Haskell standard library and it's also the main definition used throughtout this library.
* Theory.Equivs.MonadJoin — monads whose definition is based on `join`. This resembles the definition used in category theory.
* Theory.Equivs.KleisliTriple — a weird minimalistic definition coming directly from category theory. quite similar to the one using `>>=`, except it doesn't need all the functor stuff.

All three flavours of Monads from this library are actually what in category theory is called monoidal monads (it's the same story as in Haskell). I have proved them all equivalent. Control.Monad comes equipped with all the functions one can find in Haskell standard library (well, besides `fail`) and appropriate notations, including the do-notation (although a bit retarded one).

Monad transformers are like in Haskell standard library and are based on the `>>=`-definition of Monad. They come with all laws.

For more information see the sources in Control/ — most things are a bit documented. To understand the proof style used throughtout the library, see the comments in Base.v

Control/Monad/ contains instances for the typeclasses from Control/ for the following things: Cont, Free, Identity, Lazy (an attempt to monadize laziness in Coq, but failed I think), list, option, prod, Reader, RoseTree, State, Sum, Writer. There's also a module All to ease importing everything at once. Note that, however, some instances for Foldable may be missing.

Control/Monad/Trans/ contains instances for monad transformers and include: Codensity, ContT, ListT (a fully working and verified one, based on the proposal "ListT Done right", but implemented using Church encoding; it even has a nice notation), OptionT, ReaderT, RoseTreeT, StateT, SumT, WriterT.

In the directory Parser/ there are two versions of working monadic parsers combinators with all the necessary instances: one using StateT list and the other using StateT (ListT Identity).

## Build

The most basic way to get things running is something along the lines of (probably, I haven't tried it myself):

```
git clone https://github.com/Zeimer/HSLib
cd HSLib
./rebuild.sh
```

Potential problems you may encounter:
* permission denied — use sudo.
* coq_makefile not found — probably your root user doesn't know where coq_makefile is. Try chown and chmod to allow your non-root user to run it.
* ./rebuild.sh fails — a problem most likely related to CoqPath. Try COQPATH=path to HSLib on your computer.
* incompatible version of Coq — the most recent commit known to work with Coq 8.9

A more foolproof solution is therefore:

```
sudo git clone https://github.com/Zeimer/HSLib
sudo chown -R your_username:your_username HSLib
sudo chmod -R u+rwx HSLib
COQPATH=$(pwd)
cd HSLib
sudo ./rebuild.sh
```

You can then compile the project at any time using `make` and recompile (for example in case you add a new file) using `./rebuild.sh`.

## TODO

### General

* Decide what should I write about in my thesis:
  * Precise semantics of Functor, Applicative, Monad.
  * Equivalences between definitions.
  * Which laws are there, which ones are needed and which ones are redundant.
  * Not only which types implement which classes, but also which classes they can't implement.
  * Develop pen and paper proofs so they can be put into the thesis.
  * REMEMBER: describe precisely how the tactics hs and monad work. A case study in proof engineering!
* Investigate concepts:
  * Commutative applicative functors.
  * Commutative monads.
  * Free Monads (prove it is not a transformer).
  * Codensity (prove there's no callCC).
* Classes:
  * Pin down the precise categorical semantics.
  * See how classes for monad transformers/monads are implemented in transformers/mtl/Just Do It paper.
  * Define Traversable and all its instances.
  * Define all instances for Foldable.
  * Learn how to prove general laws for Foldable.
* Laws:
  * Find minimal sets of laws for each class.
* Notation:
  * Implement idiom bracket notation.
  * Improve do notation (irrefutable patterns).
* Thievery:
  * Take a look at other Haskell proposals relating to the standard library design.
  * Browse Idris standard library and steal good stuff from there.
  * Interesting Idris classes: Cast, Uninhabited, Sized, Read

### Particular

* Investigate universe consistency issues for Vec.
* Parsers:
  * Develop parsers for lists.
  * Check if using `aplus_det` would make parsers more efficient.
* Check if the law `fmap_pure_ap` is necessary for Applicative.
* Something practical: maybe use the monadic stuff for Enumerable/Finite classes.
* Check what is the precise relation between bind and ap (and if it's possible to define monads in two nonequivalent ways due to this).
* Check if the Lazy monad makes sense.
* Partition MonadPlus and its function into more sane classes.
* Implement the Set monad.

### Technical

* Revise the compilation steps from this README file.
* Update this README.

### Potential
* Try a different design in which laws come bundled in separate classes of Sort Prop (dubious).
* Implement a reflective tactic for reasoning with functors, applicatives, monads and so on.

