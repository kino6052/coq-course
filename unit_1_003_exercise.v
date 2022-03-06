Add LoadPath "$COQ_PROOFS" as Path.
Load unit_1_001_days_of_week.

(* Exercise 1 *)
Definition nandb (b1:bool) (b2:bool) : bool := 
  negb(andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

