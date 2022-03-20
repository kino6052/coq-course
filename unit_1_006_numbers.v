Module NatPlayground.

Inductive nat: Type :=
  | O: nat
  | S: nat -> nat.

Definition pred (n: nat): nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n: nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb(n: nat): bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus(n: nat) (m: nat): nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m: nat): nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match (n, m) with
  | (O , _) => O
  | (S _ , O) => n
  | (S n', S m') => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.


(* Exercise *)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
   (at level 50, left associativity)
   : nat_scope.
Notation "x - y" := (minus x y)
   (at level 50, left associativity)
   : nat_scope.
Notation "x * y" := (mult x y)
   (at level 40, left associativity)
   : nat_scope.

Check ((0 + 1) + 1).

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  negb (leb m n).
  

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

