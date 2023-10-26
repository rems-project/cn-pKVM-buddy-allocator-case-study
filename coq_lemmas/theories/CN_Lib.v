Require List.
Require Import ZArith Bool.
Require Import Lia.
Require NArith.

Definition Loc := Z.

Definition array_shift (base : Loc) (step : Z) (index : Z) :=
  (base + step * index)%Z.
