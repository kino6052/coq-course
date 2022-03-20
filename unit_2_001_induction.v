Add LoadPath "$COQ_PROOFS" as Path.
Load Basics. 

Theorem plus_n_O: forall n: nat, n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  {
    induction m. {
      reflexivity.    
    } {
      simpl. rewrite <- IHm. reflexivity.    
    }
  }
  {
    simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
  }
Qed.

Theorem plus_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.