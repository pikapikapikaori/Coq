Inductive Z2:Type :=
  |zero
  |one.

Definition negx (a:Z2) :Z2 :=
  match a with
  |zero => one
  |one => zero
  end.

Definition plus (a:Z2) (b:Z2) :Z2 :=
  match a with
  |zero => b
  |one => negx b
  end.

Notation "x + y" := (plus x y).

Example testAdd1: zero + zero = zero.
Proof. reflexivity. Qed.
Example testAdd2: zero + one = one.
Proof. reflexivity. Qed.
Example testAdd3: one + zero = one.
Proof. reflexivity. Qed.
Example testAdd4: one + one = zero.
Proof. reflexivity. Qed.