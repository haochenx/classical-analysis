Require Import ssreflect ssrbool.
Require Import Classical_Prop.
Require Import classical.

Definition Ensemble (A : Set) := A -> bool.

Definition Inhabit {A} (S : Ensemble A) := exists a, S a.

Definition refi1 {A : Set} (P : A -> Prop) : Ensemble A :=
  fun a => refi0 (P a).

Lemma refi1_prop1 : forall {A : Set} (P : A -> Prop), forall a, P a -> (refi1 P) a.
Proof.
  move => A P a.
  intro Pa.
  apply -> refi0_true in Pa.
  rewrite/ refi1.
  exact Pa.
Qed.

Lemma refi1_prop2 : forall {A : Set} (P : A -> Prop), forall a, (refi1 P) a -> P a.
Proof.
  move => A P a.
  intro reH.
  apply refi0_true in reH.
  exact reH.
Qed.
