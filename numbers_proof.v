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

(* This black magic proof should be referred back to a lot. 
   important to note that intros moves LHS from the goal to the context.
   somehow I didn't understand that completely, all this time.
*)
(*
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].  
  (* question: how can we just destruct m, if we haven't introduced it? 
   * answer from lolisa on #coq: destruct introduces m, and all variables that come before it. *)
  Case "n=0".
  destruct m.
    SCase "m=0". intro H. reflexivity.
    SCase "m>0". 
      (* cleverly not introducing the hypothesis until later. *)
      simpl. intro contra. inversion contra.
  Case "n>0".
  destruct m as [|m'].
    SCase "m=0". intros contra. inversion contra.
    SCase "m>0".
      intro H.
      apply eq_remove_S.
      (* here is some magic trick:
        applying a hypothesis with an assumption moves the assumption to the goal. 
        but it can only be done when your goal matches whats on the RHS of that assumption.
        this really makes sense though: 
          if you know A -> B, and you need to prove B, 
          then if you can prove A, you're good.  
            (also if you can disprove A, i guess, but that doesn't apply here).
      *)
      apply IHn'.
      (* in the rest, nothing really interesting happens. *)
     simpl in H. inversion H. rewrite <- plus_n_Sm in H1. rewrite <- plus_n_Sm in H1. inversion H1. reflexivity.
Qed.
*)

Definition prop' (m n k: nat) := forall (m: nat), exists (n: nat), grb n m = true /\ ~ exists (k: nat), 2 * k = n.
Check prop'.

Definition hasFactor (f n: nat) := true.

Theorem inf_nat_filter': forall (m n k: nat), hasFactor 2 m = true -> prop' m n k /\ hasFactor 2 m = false -> prop' m n k.  
Proof.
  intros m.
  induction m.
  - 
  induction m.
  - exists 1. unfold not. split.
    + simpl. reflexivity.
    + intros. destruct H. apply wrong with (x:=x). apply H.
  - exists (S (S m)). unfold not. split.
    + apply t' with (n:=S m).
    (* Stuck *)
    + intros. destruct H. destruct IHm. unfold not in H0. destruct H0. apply H1.