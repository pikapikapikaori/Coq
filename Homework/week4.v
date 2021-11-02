Fixpoint plus (n m: nat): nat :=
  match n with
  |O => m
  |S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y).



Fixpoint minus (n m: nat): nat :=
  match n, m with
  |O, _ => O
  |S _, O => n
  |S n', S m' => minus n' m'
  end.

Definition pred (n: nat): nat :=
  match n with
  |O => O
  |S n' => n'
  end.

Fixpoint gtb (n m: nat): bool :=
  match m with
  |O => true
  |S m' =>
    match n with
    |O => false
    |S n' => gtb n' m'
    end
  end.

Definition gtb2 (n m: nat): bool :=
  match (minus n m) with
  |O => false
  |S p' => true
  end.

Compute (gtb 4 2).
Compute (gtb 2 3).
Compute (gtb2 4 2).
Compute (gtb2 2 3).

Theorem gtb_test : forall n : nat,  
  gtb (n+1) 0 = true.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Fixpoint fibs (n: nat): nat :=
  match n with
  |O => O
  |S n' =>
    match n' with
    |O => 1
    |S n'' => plus (fibs n') (fibs n'')
    end
  end.

Compute (fibs 0).
Compute (fibs 1).
Compute (fibs 2).
Compute (fibs 3).
Compute (fibs 4).
Compute (fibs 5).