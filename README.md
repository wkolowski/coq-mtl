# HSLib

This project is an offshoot of my [book on Coq](https://zeimer.github.io/) (in Polish). My motivation was to find the best presentation of the concept of monad before I write about it.

It ended up being a Coq library that tries to implement parts of Haskell standard library, namely Functor, Applicative, Alternative, Monad, MonadPlus, MonadTrans and maybe more. The focus is on practical functional programming and not on category theory, although all the classes come equipped with laws and instances have to obey them.

## Done

The current status of the project is highly experimental. I'm trying to find the best way to implemented the aforementioned things in Coq.

Functors and Applicatives are more or less a no-brainer. Monads are more complicated and come in three flavours:
* MonadJoin — monads whose definition is based on `join`. This resembles the definition used in category theory.
* MonadBind — monads whose definition is based on `>>=` (bind). This resembles the definition from Haskell standard library.
* MonadComp — monads whose definition is based on `>=>` (monadic composition). This definition is rare, but gives by far the best understanding of monad laws.

Applicative is currently not a superclas of Monad. MonadPlus currently has no laws, and MonadTrans is broken.

## TODO

* Make a uniform interface for MonadJoin, MonadBind and MonadComp.
* Implement MonadBind.
* Check if all Applicative utility functions have been implemented.
* Make Applicative a superclass of Monad.
* Check which definition of monads is best for use with transformers.
* State MonadPlus laws. Play with the MonadPlus reform proposal.
