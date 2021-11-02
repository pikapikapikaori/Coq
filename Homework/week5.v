Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  
Qed.

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (*n = 0*)
    reflexivity.
  - (*n = S n'*)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (*n = 0*)
    reflexivity.
  - (*n = S n'*)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (*n = 0*)
    simpl. rewrite -> plus_O_r. reflexivity.
  - (*n = S n'*)
    simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (*n = 0*) 
  rewrite -> plus_O_n. simpl. reflexivity.
  - (*n = S n'*)
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Notation "( x , y )" := (pair x y).

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Definition ht (default : nat) (l : natlist) : natprod := 
  match l with
  |nil => (0, 0)
  |h :: t => (hd 0 l, hd 0 (rev l))
end.


Example test_ht1 : ht 0 [] = (0,0).
Proof. reflexivity. Qed.
Example test_ht2 : ht 0 [3] = (3,3).
Proof. reflexivity. Qed.
Example test_ht3 : ht 0 [1;2;3;4] = (1,4).
Proof. reflexivity. Qed.


