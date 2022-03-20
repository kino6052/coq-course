Add LoadPath "$COQ_PROOFS" as Path.
Load unit_1_008_rewriting.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange:
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
  {
    destruct d.
    - reflexivity.
    - reflexivity.
  }
  {
    destruct d.
    - reflexivity.
    - reflexivity.
  }
  - destruct c.
  {
    destruct d.
    - reflexivity.
    - reflexivity.
  }
  {
    destruct d.
    - reflexivity.
    - reflexivity.
  }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Lemma minus_n_O : forall n : nat, n = n - 0.
Proof.
  intros [|n].
  {
    reflexivity.
  }
  {
    reflexivity.
  }
Qed.

Lemma n_plus_0_same_n : forall n : nat, 0 + n = n + 0.
Proof.
  intros.
  Admitted.

Lemma plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros [|n].
  {
    reflexivity.
  }
  {
    simpl. rewrite <- n_plus_0_same_n. reflexivity.
  }
Qed.

Fixpoint beq_bool (n m: bool) : bool :=
  match n with
  | true => match m with
    | true => true
    | false => false
    end
  | false => match m with
    | true => false
    | false => true
    end
  end.

Theorem andb_true_elim2: forall b c: bool,
  andb b c = true -> b = true.
Proof.
  intros.
  destruct b.
  - reflexivity.
  - rewrite <- H. reflexivity.
Qed.


Theorem andb_true_elim2': forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros.
  destruct c.
  - rewrite <- H. simpl. reflexivity.
  - rewrite <- H. rewrite <- andb_commutative. reflexivity.
Qed.  


Theorem andb_true_elim2'': forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros.
  destruct b.
  - rewrite <- H. simpl. reflexivity.
  - rewrite <- H. inversion H.
Qed.

Definition nandb (b1: bool) (b2: bool) : bool :=
  negb (andb b1 b2).

Theorem nandb__negb_andb : forall b1 b2 : bool,
    nandb b1 b2 = negb (andb b1 b2).
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition impb (b1: bool) (b2: bool) : bool :=
  orb (negb b1) b2.

Theorem impb_spec : forall b1 b2 : bool,
  impb b1 b2 = orb (negb b1) b2.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem impb_spec' : forall b1 b2 : bool,
  impb b1 b2 = orb (negb b1) b2.
Proof.
  intros. destruct b1.
  - destruct b2. reflexivity. reflexivity.
  - destruct b2. reflexivity. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros. simpl. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros. rewrite -> H. rewrite -> H. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros.
  destruct b.
  - simpl in H. rewrite -> H. reflexivity.
  - simpl in H. rewrite -> H. reflexivity.
Qed.





