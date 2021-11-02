Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Fixpoint odd (n:nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => odd n'
  end.

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

Fixpoint geb (n m : nat) : bool :=
  match n with
  | O => false
  | S n' =>
      match m with
      | O => true
      | S m' => geb n' m'
      end
  end.

Definition gtb (n m : nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Definition ltb (n m : nat) : bool :=
  andb (geb n m) (negb (eqb n m)).

Notation "x =? y" := (eqb x y) 
                     (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) 
                      (at level 70) : nat_scope.
Notation "x >? y" := (gtb x y) 
                     (at level 70) : nat_scope.
Notation "x >=? y" := (geb x y) 
                      (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) 
                     (at level 70) : nat_scope.

Module NatList.

Inductive prod (X Y : Type) : Type :=
  | pair (n1 : X) (n2 : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Inductive list (N : Type): Type :=
  | nil
  | cons (n : N) (l : list N).

Arguments nil {N}.
Arguments cons {N}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint oddmembers (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: ns => match odd n with
               | true  => n :: oddmembers ns
               | false => oddmembers ns
               end
  end.

Fixpoint evenmembers (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: ns => match even n with
               | true  => n :: evenmembers ns
               | false => evenmembers ns
               end
  end.

Fixpoint max (l : list nat) : nat :=
  match l with
  | nil => O
  | n :: ns => match leb n (max ns) with
              | true => max ns
              | false => n
              end
  end.

Definition maxPair (l : list nat) : prod nat nat :=
  pair (max (oddmembers l)) (max (evenmembers l)).

Example test_maxPair1: maxPair [1;2;5;4;8;10;3] = (5, 10).
Proof. reflexivity. Qed.
Example test_maxPair2: maxPair [2;4] = (0, 4).
Proof. reflexivity. Qed.


Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Inductive natoptprod : Type :=
  | pairopt (x y : natoption).


Definition opttonat (n : natoption) : nat :=
  match n with 
  | None => O
  | Some a => a
  end.

Fixpoint maxopt (l : list nat) : natoption :=
  match l with
  | nil => None
  | n :: ns => match ns with
              | nil => Some n
              | h::t => match leb n (opttonat (maxopt ns)) with
                        | true => maxopt ns
                        | false => Some n
                        end
              end
  end.

Definition maxPair' (l : list nat) : prod natoption natoption :=
  pair (maxopt (oddmembers l)) (maxopt (evenmembers l)).

Example test_maxPair'1: maxPair' [1;2;5;4;8;10;3] = (Some 5, Some 10).
Proof. reflexivity. Qed.
Example test_maxPair'2: maxPair' [2;4] = (None, Some 4).
Proof. reflexivity. Qed.


Theorem app_nil_r : forall (X:Type), forall l:(list X),
  l ++ [] = l.
Proof.
  intros X l. induction l as [|l ls].
  - (*Case "[]"*)
    simpl. 
    reflexivity.
  - (*Case "x :: xs"*)
    simpl. 
    rewrite IHls. 
    reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| l' IHl' ].
  - (*Case "[]"*)
    simpl.
    reflexivity.
  - (*Case "x :: xs"*)
    simpl.
    rewrite IHIHl'.
    reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [|x xs].
  - (*Case "[]"*)
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - (*Case "x :: xs"*)
    simpl.
    rewrite IHxs.
    simpl.
    rewrite app_assoc.
    reflexivity.
Qed.


Lemma concat_append : forall X : Type, forall e : X, forall l : list X,
   cons e l = [e] ++ l.
Proof.
  intros X e l.
  simpl.
  reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  induction l as [|l ls].
  - (*Case "[]"*)
    reflexivity. 
  - (*Case "x :: xs"*)
    rewrite <- IHls.
    rewrite concat_append.
    rewrite rev_app_distr.
    rewrite IHls.
    rewrite rev_app_distr.
    rewrite IHls.
    simpl.
    reflexivity.
Qed.

