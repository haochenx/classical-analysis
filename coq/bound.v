Require Import ssreflect.

Require Import classical.
Require Import ensemble.
Require Import realnum_common.

  
Definition Rupper (S : Ensemble Real) : Ensemble Real :=
  refi1 (fun r => forall s, s <= r).

Definition Rlower (S : Ensemble Real) : Ensemble Real :=
  refi1 (fun r => forall s, r <= s).
