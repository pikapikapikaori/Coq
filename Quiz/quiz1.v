Inductive na: Type :=
  |O
  |S (n:na).

Fixpoint plus (n m:na):na :=
  match n with
  |O => m
  |S n' => S (plus n' m)
end.

Fixpoint square (n:na):na :=
  match n with
  |O => O
  |S n' => plus (square n') (plus n' n)
end.

Compute square(S(S(O))).