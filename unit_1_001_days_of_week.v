Add LoadPath "$COQ_PROOFS" as Path.
Load unit_1_002_bool.

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Definition is_weekday (d:day) : bool :=
  match d with
  | monday => true
  | tuesday => true
  | wednesday => true
  | thursday => true
  | friday => true
  | saturday => false
  | sunday => false
  end.


