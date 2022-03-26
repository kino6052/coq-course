Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
Compute (snd (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing': forall (n m : nat),
  (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing : forall (p: natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap: forall (p: natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd: forall (p: natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Qed.

Inductive natlist: Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute repeat 2 5.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Compute length [1;2;3].

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Compute app [1;2;3] [4;5;6].

Notation "x ++ y"  := (app x y) (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default: nat) (l: natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Compute hd 0 [1;2;3].

Definition tl (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Compute tl [1;2;3].

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint app' (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app' t l2)
  end.

Fixpoint nonzeros (l1:natlist) : natlist :=
  match l1 with
  | nil => nil
  | O :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.  

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | n :: t =>
    match evenb n with
    | true => oddmembers t
    | false => n :: oddmembers t
    end
  end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

(* GRADE_THEOREM 0.5: NatList.test_oddmembers *)
Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).
 
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1::t1 =>
    match l2 with
    | nil => l1
    | h2::t2 => h1::(h2::(alternate t1 t2))
    end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
      | O => true
      | S m' => false
      end
  | S n' =>
      match m with
      | O => false
      | S m' => beq_nat n' m'
      end
  end.

Compute beq_nat 5 5.

Fixpoint count (v: nat) (s: bag) : nat :=
  match s with
  | nil => O
  | h::t =>
    match (beq_nat v h) with
    | true => S (count v t)
    | false => count v t
    end 
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.
  

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed. 

Definition add (v:nat) (s:bag) : bag := app [v] s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint geb (n m : nat) : bool :=
  match m with
  | O => true
  | S m' =>
      match n with
      | O => false
      | S n' => geb n' m'
      end
  end.

Compute geb 1 1.
Compute geb 0 1.
Compute geb 1 0.

Definition member (v:nat) (s:bag) : bool := geb (count v s) 1.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h::t =>
    match beq_nat h v with
      | true => t
      | false => h::(remove_one v t)
    end 
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h::t =>
    match beq_nat h v with
      | true => remove_all v t
      | false => h::(remove_all v t)
    end 
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h1::t1 =>
    match member h1 s2 with
    | true => subset t1 (remove_one h1 s2)
    | false => false
    end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem nil_app : forall l:natlist, l ++ [] = l.
Proof. 
intros.
induction l.
- reflexivity.
(* Why was I able to rewrite? *)
- simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    simpl. reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. 
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. simpl. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  assert (H: forall l1 l2 : natlist, length (l1 ++ l2) = length l1 + length l2).
  {
    intros.
    induction l1.
    - reflexivity.
    - simpl. rewrite -> IHl1. reflexivity.  
  }

  assert (H1': forall n m : nat, S (m + n) = m + S n).
  {
    intros.
    induction m.
    - simpl. reflexivity.
    - simpl. rewrite -> IHm. reflexivity.
  }

  assert (H1: forall n m : nat, n + m = m + n).
  {
    intros.
    induction n.
    - simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity. 
    - simpl. rewrite -> IHn. rewrite <- H1'. reflexivity.  
  }

  intros l. induction l as [| n l' IHl'].
  - (* l =  *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite -> H. rewrite -> IHl'. simpl. rewrite -> H1. reflexivity.
Qed.


Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

(* GRADE_THEOREM 0.5: NatList.app_nil_r *)
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  assert (H: forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3).
  { 
    intros.
    induction l1.
    - simpl. reflexivity.
    - simpl. rewrite -> IHl1. reflexivity. 
  }

  intros.
  induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> H.  reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  assert (H': forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3).
  { 
    intros.
    induction l1.
    - simpl. reflexivity.
    - simpl. rewrite -> IHl1. reflexivity. 
  }
  
  assert (H'': forall l : natlist, l ++ [ ] = l).
  {
    intros.
    induction l.
    - reflexivity.
    - simpl. rewrite -> IHl. reflexivity.
  }

  assert (H: forall l1 l2 : natlist, rev(l1 ++ l2) = rev(l2) ++ rev(l1)).
  {
    intros.
    induction l1.
    - simpl. rewrite -> H''. reflexivity.
    - simpl. rewrite -> IHl1. rewrite -> H'. reflexivity. 
  }

  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> H. rewrite -> IHl. simpl. reflexivity. 
Qed.








