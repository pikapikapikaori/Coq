(* Definition *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
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

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem nat_equals_self : forall n : nat, n =? n = true.
Proof.
  intros n. induction n as [| n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.

Module NatList.

(* Definition *)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

(* Definition *)
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n.
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(* Definition *)
Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl. reflexivity.
Qed.

(* Exercise *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  rewrite <- snd_fst_is_swap.
  simpl. reflexivity.
Qed.

(* Definition *)
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* Exercise *)
Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | n :: t => n :: nonzeros t
  end.

Example test_nonzeros : nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl nonzeros. reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | n :: t => if odd n 
                  then n :: oddmembers t 
                else 
                  oddmembers t
  end.

Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => 0
  | n :: t => if odd n 
                  then 1 + countoddmembers t 
                else 
                  countoddmembers t
  end.

Example test_countoddmembers1 : countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2 : countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3 : countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

(* Exercise *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, l => l
    | l, nil => l
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end. 

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

(* Definition *)
Definition bag := natlist.

(* Exercise *)
Fixpoint count (v:nat) (s:bag) : nat := 
  match s with
  | nil => 0
  | x :: t => count v t + (if eqb x v then 1 else 0)
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := 
  app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := 
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool := 
  leb 1 (count v s).

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Exercise *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with 
  | nil => nil
  | x :: t => if eqb x v 
                  then t 
                else 
                  x :: remove_one v t
  end. 

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | x :: t => if eqb x v 
                  then remove_all v t 
                else 
                  x :: remove_all v t
  end. 

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool := 
  match s1, s2 with
  | nil, _ => true
  | _, nil => false
  | x :: t, s2 => if member x s2 
                        then subset t (remove_all x s2) 
                      else 
                        false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Exercise *)
Theorem bag_count_add :
  forall v n bag, count v bag = n -> count v (add v bag) = S n.
Proof.
  intros v n bag.
  simpl. intros H.
  rewrite H.
  assert (forall m, eqb m m = true) as HH. 
  { induction m.
    - reflexivity.
    - simpl. rewrite IHm. reflexivity.
  }
  rewrite HH. apply add_comm.
Qed.

(* Definition *)
Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite-> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite-> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

(* Exercise *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [|x xs].
  - reflexivity.
  - simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [|x xs].
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

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [| a l' IH].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IH.
    reflexivity.
Qed.

(* Exercise *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite <- app_assoc.
  rewrite -> (app_assoc (l1 ++ l2) l3 l4).
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| a l' IH].
  - reflexivity.
  - simpl. rewrite -> IH. destruct a.
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, l2 => false
  | l1, nil => false
  | a :: l1', b :: l2' =>
    if a =? b then eqblist l1' l2'
    else false
  end.

Example test_eqblist1 : (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l : natlist,
  true = eqblist l l.
Proof.
  induction l as [| a l' IH].
  - reflexivity.
  - simpl. rewrite -> nat_equals_self. rewrite <- IH.
    reflexivity.
Qed.

(* Exercise *)
Theorem count_member_nonzero : forall s : bag,
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  simpl. reflexivity. 
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

(* Exercise *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n s'].
  - simpl. reflexivity.
  - destruct n.
    + simpl. rewrite leb_n_Sn. reflexivity.
    + simpl. rewrite IHs'. reflexivity. Qed.

(* Exercise *)
Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(* Definition *)
Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* Exercise *)
Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | a :: _ => Some a
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

(* Exercise *)
Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End NatList.

(* Definition *)
Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) : bool :=
  match x1, x2 with
  | Id n1, Id n2 => eqb n1 n2
  end.

(* Exercise *)
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intro x.
  destruct x.
    simpl.
    rewrite -> nat_equals_self.
    reflexivity.
Qed.

(* Definition *)
Module PartialMap.

Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* Exercise *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite <- eqb_id_refl.
  reflexivity.
Qed.

(* Exercise *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intro H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

End PartialMap.

(* Exercise *)

(* It has 2^n elements. *)

