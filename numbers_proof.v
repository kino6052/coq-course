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


Theorem inf_nat: forall (m: nat), exists (n: nat), grb n m = true.
Proof.
  intros m.
  induction m.
  - exists 1. simpl. reflexivity.
  - exists (S (S m)). simpl. apply t' with (n:=S m). 
Qed.

Lemma wrong: forall x: nat, 2 * x = 1 -> False.
Proof.
  intros x. induction x.
  - intros. inversion H.
  - intros. apply IHx. destruct x. inversion H. inversion H. 
Qed.

Theorem inf_nat_filter': forall (m: nat), exists (n: nat), grb n m = true /\ ~ exists (k: nat), 2 * k = n.
Proof.
  intros m.
  induction m.
  - exists 1. unfold not. split.
    + simpl. reflexivity.
    + intros. destruct H. apply wrong with (x:=x). apply H.
  - exists (S (S m)). unfold not. split.
    + apply t' with (n:=S m).
    (* Stuck *)
    + intros. destruct H. destruct IHm. unfold not in H0. destruct H0. apply H1.