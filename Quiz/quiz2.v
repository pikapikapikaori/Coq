Module NatList.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | [] => 0
  | x :: xs => match beq_nat v x with
               | true => S (count v xs)
               | false => count v xs
               end
  end.

Example  test_count1:  count 1  [1 ;2 ;3 ;1 ;4 ;1 ]  = 3. 
  Proof. reflexivity. Qed. 
Example  test_count2:  count 6  [1 ;2 ;3 ;1 ;4 ;1 ]  = 0. 
  Proof. reflexivity. Qed.