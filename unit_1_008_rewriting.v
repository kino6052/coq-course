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








