Add LoadPath "$COQ_PROOFS" as Path.
Load unit_5_tactics.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Example and_example : (3 + 4 = 7) /\ (2 * 2 = 4).
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  assert (forall (n m: nat), n + m = m + n).
  {
    intros.
    induction n.
    - simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
    - simpl. rewrite IHn. rewrite plus_n_Sm.  reflexivity.
  }
  split.
  - induction n. 
    * reflexivity.
    * inversion H0.
  - induction m.
    * reflexivity.
    * rewrite H in H0. inversion H0.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply plus_is_O. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "¬ x" := (not x) (at level 60, right associativity): type_scope .
Check not.
(* ===> Prop -> Prop *)
End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall (P:Prop),
  not P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  destruct H. apply H0.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

Theorem not_False :
  ~False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q PQ NQ HP.
  apply NQ.
  apply PQ.
  apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P A.
  unfold not in A.
  destruct A. apply H0. apply H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof. reflexivity. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP|[HQ HR]]. split.
    + left. apply HP.
    + left. apply HP.
    + split. 
      * right. apply HQ.
      * right. apply HR.  
  - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  destruct n as [|n'].
  - left. reflexivity.
  - right. simpl in H.
    destruct m as [|m'].
    + reflexivity.
    + inversion H.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros.
  split.
  - intros. apply mult_eq_0. apply H.
  - intros [HN | HM]. 
    + inversion HN. reflexivity. 
    + inversion HM. rewrite n_times_m_comm. reflexivity.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [HP|[HQ|HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP|HQ]|HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros X P A J.
  destruct J.
  apply H. apply A.
Qed.



  