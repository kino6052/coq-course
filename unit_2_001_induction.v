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

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. 
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma minus_Sn_n : forall n, S n - n = 1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl in IHn. simpl. rewrite -> IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.

Lemma double_plus' : forall n, double n = n + n.
Proof.
  (* Auxiliary proof *)
  assert (H1: forall m k, S(m + k) = m + (S k)).
  { intros. induction m.
  - simpl. reflexivity.
  - simpl. rewrite -> IHm. reflexivity.  
  }
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. simpl in H1. rewrite <- H1. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - rewrite -> IHn. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n). {
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
  }
  rewrite -> H. reflexivity. Qed.

Inductive bin : Type :=
  | BZ : bin (* binary zero *)
  | T2 : bin -> bin (* twice a binary number *)
  | T2P1 : bin -> bin. (* twice a binary number plus 1 *)

Fixpoint incr (m:bin) : bin :=
  match m with
  | BZ => T2P1 BZ
  | T2 m' => T2P1 m'
  | T2P1 m' => T2 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | BZ => O
  | T2 m' => 2 * bin_to_nat m'
  | T2P1 m' => 1 + 2 * bin_to_nat m'
  end.

Compute bin_to_nat (T2 (T2 (T2P1 BZ))).

Theorem bin_commute: forall b: bin, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  assert(forall n: nat, n + 0 = n). {
    intros.
    induction n.
    - reflexivity.
    - simpl. rewrite -> IHn. reflexivity.
  }

  assert(forall b: bin, bin_to_nat b + 0 = bin_to_nat b). {
    intros.
    induction b.
    - reflexivity.
    - rewrite -> H. reflexivity.
    - rewrite -> H. reflexivity. 
  }

  assert(forall n m: nat, S(n) + S(m) = S(S(n+m))). {
    intros.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite <- IHn. simpl. reflexivity.
  }
  
  intros.
  induction b.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> H. rewrite -> H. rewrite -> IHb. rewrite <- H1. reflexivity.  
Qed.



 
