Add LoadPath "$COQ_PROOFS" as Path.
Load unit_3_001_structured_data.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  rewrite eq2.
  reflexivity.
Qed.

Theorem silly1' : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1. Qed.

Definition oddb (X: nat) := negb (evenb X).

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros.
  apply H. apply H0.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

(*Theorem rev_app_distr: forall (l1 l2 : natlist),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity. 
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.
*)

(*
To sum up, one can say apply H when H is a 
hypothesis in the context or a previously 
proven lemma of the form 
∀x1 ..., H1 → H2 → ... → Hn and the current 
goal is shape Hn (for some instantatiation of 
each of the xi). After running apply H in such
 a state, you will have a subgoal for each of 
H1 through Hn-1. In the special case where H 
isn't an implication, your proof will be 
completed.
*)

Theorem rev_exercise1 : forall (l l' : natlist),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  symmetry.
  apply rev_injective.
  rewrite rev_involutive.
  apply H.
Qed.

Theorem rev_exercise1' : forall (l l' : natlist),
     l = rev l' ->
     l' = rev l.
Proof.
  assert (forall l: natlist, rev (rev l) = l).
  {
    intros.
    induction l.
    - reflexivity.
    - simpl. rewrite <- rev_involutive. simpl. reflexivity.
  }
  intros.
  induction l'.
  - rewrite H0. simpl. reflexivity.
  - rewrite H0. rewrite H. reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. 
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Definition minustwo (n: nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with (m:=(minustwo o)).
  rewrite H0. apply H.
  reflexivity.
Qed.

(* Inductive definitions have two major properties:
  - The constructor S is injective. That is, if S n = S m, it must be the case that n = m.
  - The constructors O and S are disjoint. That is, O is not equal to S n for any n.
*)








