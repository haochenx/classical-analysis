Require Import ssreflect ssrbool.
Require Import Classical_Prop.

(*
Axiom constructive_definite_description :
  forall {A : Type} {P : A->Prop},
    (exists! x, P x) -> { x : A | P x }.
 *)

Definition Unique {A} (P : A -> Prop) := forall a b, P a /\ P b -> a = b.

Lemma exists_Unique : forall {A} {P : A -> Prop}, (exists! x, P x) -> Unique P.
Proof.
  move => A P [x [exs unq]].
  move => a b [Pa Pb].
  transitivity x.
  symmetry.
  apply unq.
    by [].
    apply unq.
      by [].
Qed.  
  
Axiom UniqueOut : forall {A} (P : A -> Prop), (exists! x, P x) -> A.
Axiom HUniqueOut : forall {A} {P : A -> Prop} (prf : exists! x, P x), P (UniqueOut P prf).

Lemma UniqueOut_eq :
  forall {A} {P : A -> Prop} (prf : exists! x, P x),
  forall y, P y <-> UniqueOut P prf = y.
Proof.
  move => A P prf y.
  split.
  {
    move => Py.
    apply (exists_Unique prf).
    split; [ | by[]].
    exact: HUniqueOut.
  } {
    move =><-.
    exact: HUniqueOut.
  }
Qed.
  
Theorem unique_choice :
 forall (A B:Type) (R:A -> B -> Prop),
   (forall x:A, exists! y : B, R x y) ->
   (exists f:A->B, forall x:A, R x (f x)).
Proof.
  move => A B R HH.
  exists (fun a => UniqueOut (fun b => R a b) (HH a)).
  move => a.
  apply: HUniqueOut.
Qed.



Inductive Prop_to_bool : Prop -> bool -> Prop :=
| Prop_to_bool_true : forall (P : Prop), P -> Prop_to_bool P true
| Prop_to_bool_false : forall (P : Prop), ~P -> Prop_to_bool P false
.

Lemma true_Prop_to_bool : forall P, Prop_to_bool P true -> P.
Proof.
  move => P HH.
  inversion HH.
    by [].
Qed.

Lemma false_Prop_to_bool : forall P, Prop_to_bool P false -> ~P.
Proof.
  move => P HH.
  inversion HH.
    by [].
Qed.
  
Lemma Prop_to_bool_Unique_bool : forall P, exists! b, Prop_to_bool P b.
Proof.
  move => P.
  case: (classic P).
  {
    move => pH.
    exists true.
    split.
    exact (Prop_to_bool_true _ pH).
    case.
    by [].
    move/ false_Prop_to_bool.
    by [].
  } {
    move => npH.
    exists false.
    split.
    exact (Prop_to_bool_false _ npH).
    case.
    move/ true_Prop_to_bool.
    by [].
    by [].
  }
Qed.


Definition refi0 (P : Prop) : bool :=
  UniqueOut _ (Prop_to_bool_Unique_bool P).

Lemma refi0_true :
  forall P,
    P <-> refi0 P = true.
Proof.
  intro P.
  split.
  {
    unfold refi0.
    move => pH.
    apply UniqueOut_eq.
    exact: (Prop_to_bool_true _ pH).
  } {
    unfold refi0.
    move => eqH.
    apply UniqueOut_eq in eqH.
    move: eqH.
    exact: true_Prop_to_bool.
  }
Qed.

Lemma refi0_false :
  forall P,
    ~P <-> refi0 P = false.
Proof.
  intro P.
  split.
  {
    unfold refi0.
    move => pH.
    apply UniqueOut_eq.
    exact: (Prop_to_bool_false _ pH).
  } {
    unfold refi0.
    move => eqH.
    apply UniqueOut_eq in eqH.
    move: eqH.
    exact: false_Prop_to_bool.
  }
Qed.

Definition refi2 {A B : Set} (P : A -> B -> Prop) : A -> B -> bool :=
  fun a b => refi0 (P a b).


Lemma casep : forall (P : Prop), forall (A : Type), (P -> A) -> (~P -> A) -> A.
  move => P A.
  case: (boolP (refi0 P)).
  {
    move => refiH.
    apply refi0_true in refiH.
    exact (fun f _ => f refiH).
  } {
    move/ negbTE.
    move => refiH.
    apply refi0_false in refiH.
    exact (fun _ f => f refiH).
  }
Qed.
