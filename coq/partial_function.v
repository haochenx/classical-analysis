Require Import classical.

Definition sing {A : Set} (a : A) := fun x => if refi0 (x = a) then true else false.
Definition nil {A : Set} := fun (_ : A) => false.

