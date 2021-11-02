Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => 
      match m with
      | O => true
      | S m' => false
      end
  | S n' => 
      match m with
      | O => false
      | S m' => eqb n' m'
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

Definition ltb (n m : nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Module NatList.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | [] => 0
  | x :: xs => 
      match eqb v x with
      | true => S (count v xs)
      | false => count v xs
      end
  end.

Definition member (v:nat) (s:bag) : bool := ltb 0 (count v s).

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | x :: xs => 
      match eqb x v with
      | true => xs
      | false => x :: remove_one v xs
      end
  end.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | [] => true
  | x :: xs => andb (member x s2) (subset xs (remove_one x s2))
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. 
    rewrite -> IHl1'. 
    reflexivity.
 Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite -> app_assoc. 
  rewrite -> app_assoc. 
  reflexivity.
Qed.


Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. 
    reflexivity.
  - (* S n' *)
    simpl. 
    rewrite IHn'. 
    reflexivity. 
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros. induction s as [|x xs].
  -(*[]*) 
    simpl. reflexivity.
  -(*x :: xs*)
    simpl. destruct x as [|y].
    +(*0*)
      simpl. 
      rewrite leb_n_Sn. 
      reflexivity.
    +(*S y*)
      simpl. 
      rewrite IHxs. 
      reflexivity.
Qed.

