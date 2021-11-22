Inductive COdd: nat -> nat -> Prop :=
  | CO1 : COdd 1 3
  | CO2 m n (H : COdd m n) : COdd (S (S m)) (S (S n)).