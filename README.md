# HSLib

This project is an offshoot of my [book on Coq](https://zeimer.github.io/) (in Polish). My motivation was to find the best presentation of the concept of monad before I write about it.

It then turned into a Coq library that tries to implement parts of Haskell standard library. The focus is on practical functional programming and not on category theory, although (nearly) all the classes come equipped with laws and instances have to obey them.

Recently I chose to write a monadic parser combinator library as a project for one (or rather, two) of my university courses. Since the parsers are monadic, they fit here perfectly. This development is based on the paper "Monadic Parser Combinators" by Graham Hutton and Erik Meijer.

At last, this project has great chances ending up as my BSc thesis. I'm now working to make all the monads proof-friendly. This development is based on the paper "Just do It: Simple Monadic Equational Reasoning" by Jeremy Gibbons and Ralf Hinze.

## Done

* Base.v — utilities for the whole library
* Control/ — the core of the library. All the most important classes (Functor, Applicative, Monad etc.) live here.
* Instances/ — types and instances for all things from Control/ besides monad transformers.
* InstancesT/ — types and instances for monad transformers.
* Misc/ — various things, not too interesting.
* MonadClass/ — a directory in which classes for monad transformers are born. Nothing fancy yet.
* MonadJoin/ — an alternative definition of monads using the join operator.
* Parser/ — two versions of monadic parser combinators.
* Theory/ — various theoretical results, relating applicative functors to monoidal functors, monads with bind to monads with join, kleisli triples to monads with bind and so on.

Functors are a no-brainer.

Applicatives come equipped with all the necessary laws and notations. Most functions that in Haskell are doubled (like liftA2 and liftM2) here come only in the Applicative version.

Alternatives also come with notations and corresponding functions, but their laws are somewhat less polished. They are there already, but I need to think about them harder.

Monads come in three flavours:
* Control.Monad — monads whose definition is based on `>>=` (bind). This is closest to the definition from the Haskell standard library and it's also the main definition used throughtout this library.
* MonadJoin.Monad — monads whose definition is based on `join`. This resembles the definition used in category theory.
* Theory.KleisliTriple — a weird minimalistic definition coming directly from category theory.

All three flavours of Monads from this library are actually what in category theory is called monoidal monads (it's the same story as in Haskell). I have proved them all equivalent. Control.Monad and MonadJoin.Monad come equipped with all the functions one can find in Haskell standard library (well, besides `fail`) and appropriate notations, including the do-notation (although a bit retarded one).

MonadPlus is there, but the laws are not well-thought-out (besides those that come from Monad and Alternative).

Monad transformers are like in Haskell standard library and are based on the `>>=`-definition of Monad, but not yet fully worked out. The laws are there, but the classes like MonadState are lacking.

For more information see the sources in Control/ — most things are a bit documented. To understand the proof style used throughtout the library, see the comments in Base.v

Instances/ contains instances for the typeclasses from Control/ for the following things: Cont, Free, Identity, Lazy (an attempt to monadiz laziness in Coq, but failed I think), list, option, prod, Reader, RoseTree, State, Sum, Writer. There's also a module All to ease importing verything at once. Note that, however, some instances for Foldable may be missing.

InstancesT/ are instances for monad transformers and include: Codensity, ContT (along with a refactored version; ignore it), ListT (a fully working and verified one, based on the proposal "ListT Done right", but implemented using Church encoding; it even has a nice notation), OptionT, ReaderT, RoseTreeT, StateT, SumT, WriterT.

In the directory Parser/ there are two versions of working monadic parsers combinators with all the necessary instances: one using StateT list and the other using StateT (ListT Identity). The first one seems faster for now. EDIT 16.02.18: the efficiency problems were related to universe polymorphism and are now solved.

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
* incompatible version of Coq — the most recent commit known to work with Coq 8.8.1

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
* Investigate concepts:
  * Commutative applicative functors.
  * Commutative monads.
  * Free Monads.
* Classes:
  * Pin down the precise categorical semantics.
  * See how classes for monad transformers/monad are implemented in transformer/mtl/Just Do It paper.
  * Define Traversable and all its instances.
  * Define all instances for Foldable.
  * Learn how to prove general laws for Foldable.
  * Define a class that has just bind so it can be used for overloading the do notation.
* Laws:
  * Find minimal sets of laws for each class.
  * Prove all the derived laws for monads (and other clases too) by hand to give an example of reasoning with monads.
  * Derive more laws.
  * Refactor all the laws not to be point-free (point-free sucks for theorem proving).
  * Try a different design in which laws come bundled in separate classes of Sort Prop.
  * State MonadPlus laws. Take a look at the MonadPlus reform proposal.
* Notation:
  * Make sure that associativity and operator precedence are correct.
  * Implement idiom bracket notation.
  * Improve do notation.
* Tactics:
  * Implement a reflective tactic for reasoning with functors, applicatives, monads and so on.
  * Make this reflection modular using the Datatypes à la carte approach (dubious).
* Thievery:
  * Take a look at other Haskell proposals relating to the standard library design.
  * Browse Idris standard library and steal good stuff from there.

### Particular

* Investigate universe consistency issues with Applicative, Monad etc. instances for Vec.
* Codensity:
  * Decide the existence of callCC (I don't think it exists).
  * Decide if it is a commutative applicative functor or a commutative monad.
  * Prove Codensity F isomorphic to F (?) or something like that.
* Check if there are more functions for MonadPlus that can be generalized to Alternative.
* Parsers:
  * Develop parsers for lists.
  * Check if using `aplus_det` would make parsers more efficient.
* Investigate callCC for the Cont monad.
* Check if the law `fmap_pure_ap` is necessary for Applicative.
* Something practical: maybe use the monadic stuff for Enumerable/Finite classes.
* Datatypes à la carte:
  * Remove and put it somewhere else.
  * Investigate using Church encoding.

### Technical

* Revise the compilation steps from this README file.
