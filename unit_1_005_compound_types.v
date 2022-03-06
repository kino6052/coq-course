Add LoadPath "$COQ_PROOFS" as Path.
Load unit_1_001_days_of_week.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c: color): bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Compute monochrome white.
Compute monochrome (primary red).

Definition isred' (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary p =>
    match p with
    | red => true
    | _ => false
    end
  end.

Compute isred' (primary red).
Compute isred' (primary green).
