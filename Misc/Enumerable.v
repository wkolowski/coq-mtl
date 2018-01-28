Add Rec LoadPath "/home/Zeimer/Code/Coq".

Require Import HSLib.Base.
Require Import Control.Monad.
Require Import HSLib.Instances.All.

(* Just for teh lulz. *)
Class Enumerable (A : Type) : Type :=
{
    enum : nat -> list A;
}.

Arguments enum _ {Enumerable} _.

Instance Enumerable_Empty_set : Enumerable Empty_set :=
{
    enum n := []
}.

Instance Enumerable_unit : Enumerable unit :=
{
    enum n := [tt]
}.

Instance Enumerable_bool : Enumerable bool :=
{
    enum := fun _ => [false; true]
}.

Instance Enumerable_prod
  (A B : Type) (instA : Enumerable A) (instB : Enumerable B)
  : Enumerable (A * B)%type :=
{
    enum n := liftA2 pair (enum A n) (enum B n)
}.

Instance Enumerable_list
  (A : Type) (inst : Enumerable A) : Enumerable (list A) :=
{
    enum := fix f (n : nat) : list (list A) :=
    match n with
        | 0 => [[]]
        | S n' => liftA2 cons (enum A n) (f n')
    end
}.

Compute enum Empty_set 123.
Compute enum unit 11.
Compute enum bool 5.
Compute enum (bool * bool) 3.
Compute enum (list Empty_set) 0.
Compute enum (list unit) 20.
Compute enum (list bool) 5.
(*Compute length (enum (list bool * list bool) 5).*)