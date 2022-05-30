(** A module that can be used to important all monadic classes except the
    alternative ones for nondeterminism. *)

From CoqMTL Require Export Control.Monad.Class.MonadAlt.
From CoqMTL Require Export Control.Monad.Class.MonadExcept.
From CoqMTL Require Export Control.Monad.Class.MonadFail.
From CoqMTL Require Export Control.Monad.Class.MonadFree.
From CoqMTL Require Export Control.Monad.Class.MonadNondet.
From CoqMTL Require Export Control.Monad.Class.MonadReader.
From CoqMTL Require Export Control.Monad.Class.MonadState.
From CoqMTL Require Export Control.Monad.Class.MonadStateNondet.
From CoqMTL Require Export Control.Monad.Class.MonadWriter.

(*
From CoqMTL Require Export Control.Monad.Class.MonadAlt2.
From CoqMTL Require Export Control.Monad.Class.MonadAltSet.
From CoqMTL Require Export Control.Monad.Class.MonadAltBag.
*)