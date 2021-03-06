Add LoadPath "$COQ_PROOFS" as Path.
Load unit_1_007_simplification.

Theorem plus_id_example: forall n m: nat,
  n = m ->
  n + n = m + m.
Proof. intros n m. intros H. rewrite <- H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. 
  intros n m o. intros H1. intros H2.
  rewrite -> H1. rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus: forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. 
Qed.


Theorem mult_S_1: forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H1.
  simpl.
  rewrite <- H1.
  reflexivity.
Qed.





