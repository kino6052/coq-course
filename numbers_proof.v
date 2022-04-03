Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
  
Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition grb (n m : nat) : bool :=
  leb m n.
  
Example test_blt_nat1: grb 2 0 = true.
Proof. simpl. reflexivity. Qed.


Example test_blt_nat2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Theorem t': forall (n: nat), grb n n = true.
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
      * exists (m). apply t'.
Qed.