Module Classical_Analysis.

Require Import ssreflect.

Add LoadPath "../logic".
Require Import classical.
Require Import partial.

Section RealNum.

Variable Real : Set.
Variable Zero : Real.
Variable One : Real.
Variable Radd : Real -> Real -> Real.
Variable Ropp : Real -> Real.
Variable Rmult : Real -> Real -> Real.
Variable Rle : Real -> Real -> Prop.

Notation "r1 + r2" := (Radd r1 r2) (at level 50, left associativity).
Notation "r1 * r2" := (Rmult r1 r2) (at level 40, left associativity).
Notation "- r" := (Ropp r).
Notation "r1 - r2" := (r1 + (-r2)) (at level 50, left associativity).
(* HX: i have no idea about what the "r2 at next level" does... *)
Notation "r1 <= r2" := (Rle r1 r2) (at level 70, r2 at next level).
Notation "r1 >= r2" := (Rle r2 r1) (at level 70, r2 at next level).

Axiom Radd_comm : forall r1 r2, r1 + r2 = r2 + r1.
Axiom Radd_assoc : forall r1 r2 r3, (r1 + r2) + r3 = r1 + (r2 + r3).
Axiom Zero_spec : forall r, r + Zero = r.
Axiom Opp_prop : forall r, r - r = Zero.

Axiom Rmult_comm : forall r1 r2, r1 * r2 = r2 * r1.
Axiom Rmult_assoc : forall r1 r2 r3, (r1 * r2) * r3 = r1 * (r2 * r3).
Axiom One_spec : forall r, r * One = r.
Axiom Rinv_ex : forall (r : Real), r <> Zero -> exists! r', r * r' = One.

Axiom Rdist : forall (r0 r1 r2 : Real), r0 * (r1 + r2) = r0 * r1 + r0 * r2.

Axiom Rle_refl : forall (r : Real), r <= r.
Axiom Rle_asymm : forall (r1 r2 : Real), r1 <= r2 -> r2 <= r1 -> r1 = r2.
Axiom Rle_trans : forall (r1 r2 r3 : Real), r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Axiom Rle_total : forall (r1 r2 : Real), r1 <= r2 \/ r2 <= r1.

Axiom Rle_add : forall (r0 r1 r2 : Real), r1 <= r2 -> r1 + r0 <= r2 + r0.
Axiom Rle_mult : forall (r0 r1 r2 : Real), r0 >= Zero -> r1 <= r2 -> r1 * r0 <= r2 * r0.

Hypothesis casep : forall (P : Prop), forall (A : Type), (P -> A) -> (~P -> A) -> A.

Definition Rinv (r : Real) : Real -> bool.
Proof.
  apply (casep (r <> Zero)) => H.
  exact (sing (UniqueOut _ (Rinv_prop r H))).
  exact nil.
Defined.

End RealNum.
End Classical_Analysis.
