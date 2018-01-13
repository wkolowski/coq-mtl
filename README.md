# HSLib

This project is an offshoot of my [book on Coq](https://zeimer.github.io/) (in Polish). My motivation was to find the best presentation of the concept of monad before I write about it.

It then turned into a Coq library that tries to implement parts of Haskell standard library, namely Functor, Applicative, Alternative, Monad, MonadPlus, MonadTrans and maybe more. The focus is on practical functional programming and not on category theory, although all the classes come equipped with laws and instances have to obey them.

Recently I chose to write a monadic parser combinator library as a project for one (or rather, two) of my university courses. Since the parsers are monadic, they fit here perfectly. This development is based on the paper "Monadic Parser Combinators" by Graham Hutton and Erik Meijer.

At last, this project has great chances ending up as my BSc thesis. I'm now working to make all the monads proof-friendly. This development is based on the paper "Just do It: Simple Monadic Equational Reasoning" by Jeremy Gibbons and Ralf Hinze.

## Done

The current status of the project is experimental.

Functors are a no-brainer.

Applicatives come equipped with all the necessary laws and notations. Most functions that in Haskell are doubled (like liftA2 and liftM2) here come only in the Applicative version. There's also a tactic that facilitates basic reasoning with the Applicative laws. I'm also working on an equivalent characterization of Applicatives as Monoidal Functors, but this is work in progress.

Alternatives also come with notations and corresponding functions, but their laws are somewhat less polished. They are there already, but I need to think about them harder.

Monads come in three flavours:
* MonadBind — monads whose definition is based on `>>=` (bind). This is closest to the definition from the Haskell standard library.
* MonadJoin — monads whose definition is based on `join`. This resembles the definition used in category theory.
* MonadComp — monads whose definition is based on `>=>` (monadic composition). This definition is rare, but gives by far the best understanding of the (basic) monad laws.

All three flavours of Monads from this library are actually what in category theory is called monoidal monads (it's the same story as in Haskell; this is because Applicative is a superclass of Monad).

The laws for MonadBind and MonadJoin are complete now (I hope) and I have proved these two definitions equivalent. There's also a tactic that simplifies reasoning with MonadBind.

MonadComp is not yet polished — it lacks some of the necessary laws (i. e. those that relate `>=>` to `fmap` and `ap`.

All three definitions come equipped with all the functions one can find in Haskell standard library (well, besides `fail`) and appropriate notations, including the do-notation (although a bit retarded one).

MonadPlus is there, but doesn't have any laws (besides those that come from Monad and Alternative). The functions are not there and neither are the notations.

Monad transformers are like in Haskell standard library and are based on the `>>=`-definition of Monad, but not yet fully worked out. The laws are there, but the classes like MonadState are lacking.

Instances (Identity, Option, Sum, List, Reader, Writer, State, Cont) are defined for Functor, Applicative, Alternative and Monad whenever possible.

Instances for transformers (OpionT, SumT, ReaderT, WriterT, StateT, ContT) are also defined, but there's no instance for ListT, since it doesn't obey the laws (I think).

In the directory Parser/ there are working monadic parsers combinators with Functor/Applicative/Monad instances, but they are clumsy and need to be refactored.

Everything is compatible with Coq 8.6, but I haven't checked for 8.7.

## TODO

* Find all the necessary laws for MonadComp.
* Prove MonadComp equivalent to MonadBind and MonadJoin.
* Think on Alternative laws.
* State MonadPlus laws. Define functions for MonadPlus. Take a look at the MonadPlus reform proposal.
* Take a look at the "ListT done right proposal".
* Take a look at other Haskell proposals relating to the standard library design.
* Work more on Foldable.
* Define Traversable.
* Do something with Lazy and FreeMonad.
* Refactor all the laws not to be point-free (point-free sucks for theorem proving.
* Sort things out with tactics.
* Try a different design in which laws come bundled in separate classes of Sort Prop.
