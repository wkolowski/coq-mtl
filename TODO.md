# TODO

## Newest

- Applicative Laws: https://www.reddit.com/r/haskell/comments/s97ue9/has_anyone_seen_these_applicative_laws/

## General

* Investigate concepts:
  * Commutative applicative functors.
  * Commutative monads.
  * Free Monads (prove it is not a transformer).
* Classes:
  * See how classes for monad transformers/monads are implemented in transformers/mtl.
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
* Update this README to mention the Equations package.
* Remember about mscatter and mconcatMap from MonadPlus.

## Particular

* Parsers:
  * Develop parsers for lists.
  * Check if using `aplus_det` would make parsers more efficient.
* Something practical: maybe use the monadic stuff for Enumerable/Finite classes.
* Check what is the precise relation between bind and ap (and if it's possible to define monads in two nonequivalent ways due to this).
* Check if the Lazy monad makes sense.
* Implement the Set monad.

## Potential
* Implement a reflective tactic for reasoning with applicatives, monads and so on.
