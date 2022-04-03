Fixpoint grb (n m : nat) : bool :=
  match n with
  | O => false
  | S n' =>
      match m with
      | O => true
      | S m' => grb n' m'
      end
  end.
  
Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
  
Example test_blt_nat1: grb 2 0 = true.
Proof. simpl. reflexivity. Qed.


Example test_blt_nat2: (grb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (grb 2 1) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat4: (grb 2 3) = false.
Proof. simpl. reflexivity. Qed.

Theorem t': forall (n: nat), grb (S n) n = true.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. apply IHn.
Qed.


Theorem test: forall (m: nat), exists (n: nat), grb n m = true.
Proof.
  intros m.
  induction m.
  - exists 1. simpl. reflexivity.
  - exists (m + 2). simpl. induction m.
    + simpl. reflexivity.
    + simpl. rewrite IHm0. 
      * reflexivity. 
      * exists (S m). apply t'.
Qed.

