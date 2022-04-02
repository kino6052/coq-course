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

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity.
Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity. Qed.

Example inversion_ex3 : forall (x y z : nat) (l j : natlist),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  inversion H.
  inversion H0.
  inversion H2.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - inversion H.
  Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Example inversion_ex6 : forall
                          (x y z : nat) (l j : natlist),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros.
  inversion H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem f_equal2 : forall (A1 A2 B:Type) (f:A1 -> A2 -> B)
                          (x1 y1:A1) (x2 y2:A2),
    x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

(*
In other words, apply L in H gives us a form of "forward reasoning": from L1 → L2 and a hypothesis matching L1, it produces a hypothesis matching L2. By contrast, apply L is "backward reasoning": it says that if we know L1→L2 and we are trying to prove L2, it suffices to prove L1.
*)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem plus_equal' : forall 
                          (n m: nat) (n m: nat),
    n = m -> m + m = n + n.
Proof.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
Qed.

Theorem plus_equal'' : forall 
                          (n m: nat),
    S n = m -> m + m = S n + S n.
Proof.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
Qed.

Module test.
Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive. 
  rewrite <- H.
  rewrite  rev_involutive.
  reflexivity.
Qed.
End test.


(*
NOTE: Binding variables too soon can get you stuck!

Theorem plus_n_n_injective_stuck : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros.
  induction n as [| n' IHn'].
  - inversion H. destruct m. reflexivity. inversion H1.
  - destruct m.
    + intros. inversion H.
    + intros. 
      simpl in H. 
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' in H1.
Qed.
*)


(* Big thanks to http://www.edwardzcn98yx.com/post/ec8fb64d.html) *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  (* Hint: use [plus_n_Sm] *)
  intros n.
  induction n as [| n' IHn'].
  - intros. destruct m as [| m'].
    + reflexivity.
    + simpl in H. inversion H.
  - induction  m as [| m'].
    + intros. inversion H.
    + intros. simpl in H.
      Check plus_n_Sm.
      Search (S ( _ + _ ) ).
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      (* Use injection property *)
      injection H as IHinj.
      (* Now we can apply IHn' in IHinj with specific m ( that is m') *)
      apply IHn' in IHinj.
      Search ( ?a = ?b -> S ?a = S ?b).
      (* As a backward reasoning, we could rewrite the goal with IHinj and  *)
      rewrite IHinj.
      reflexivity.
      (* As a forward reasoning, I search the existing therom and make S n' = S m' *)
      (* apply eq_S in IHinj. *)
      (* apply IHinj. *)
Qed.

Search (_ + _ = _ + _).

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros. destruct m. reflexivity. inversion H.
  - intros. destruct m. inversion H. apply IHn in H. rewrite H. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n.
  induction n.
  - intros. induction m. 
    + reflexivity.
    + inversion H.
  - intros. induction m.
    + inversion H.
    + Search (f_equal). (* n = S n' *) apply f_equal.
      apply IHn. inversion H. reflexivity. Qed.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    
    + Search (f_equal). (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity. 
Qed.


