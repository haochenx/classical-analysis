Require Import ssreflect.
Require Import Classical_Prop.

(*
Axiom constructive_definite_description :
  forall {A : Type} {P : A->Prop},
    (exists! x, P x) -> { x : A | P x }.
 *)

Axiom UniqueOut : forall {A} (P : A -> Prop), (exists! x, P x) -> A.
Axiom HUniqueOut : forall {A} {P : A -> Prop} (prf : exists! x, P x), P (UniqueOut P prf).

  
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
