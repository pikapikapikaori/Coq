(* Definition *)
Definition minustwo (n: nat): nat :=
  match n with
  | S (S n') => n'
  | _ => O
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

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

Definition ltb (n m : nat) : bool :=
    andb (n <=? m) (negb (n =? m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Definition gtb (n m : nat) : bool := negb (leb n m).
Definition geb (n m : nat) : bool := negb (ltb n m).

Notation "x >? y" := (gtb x y) (at level 70) : nat_scope.
Notation "x >=? y" := (geb x y) (at level 70) : nat_scope.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

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

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Theorem app_assoc : forall l1 l2 l3 : list nat,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_nil_r : forall l : list nat,
  l ++ [] = l.
Proof.
  induction l as [| a l' IH].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : list nat,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| a l' IH].
  - rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IH. rewrite -> app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : list nat,
  rev (rev l) = l.
Proof.
  induction l as [| a l' IH].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IH.
    reflexivity.
Qed.

(* Exercise *)
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 4 = true ->
     oddb 3 = true.
Proof.
  intros eq1 eq2.
  apply eq1 in eq2.
  apply eq2.
Qed.

(* Exercise *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

(* Exercise *)
(** apply requires that the thing to be applied must be exactly
 the same as the theorem, while rewrite can be used more
 freely. For all situations, rewrite can be very useful, while
 apply is a more conveninet way to use rewrite. *)

(* Exercise *)
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

(* Exercise *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m:=m).
  apply eq2.
  apply eq1.
Qed.

(* Exercise *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  rewrite eq2 in eq1.
  injection eq1 as eq3 eq4.
  rewrite <- eq4 in eq3.
  apply eq3.
Qed.

(* Exercise *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j eq1.
  discriminate eq1.
Qed.

(* Exercise *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m.
    destruct m as [| m'].
    + simpl. reflexivity.
    + discriminate.
  - intros m eq1.
    destruct m as [| m'].
    + discriminate.
    + apply f_equal.
       apply IHn'.
       apply eq1.
Qed.

(* Exercise *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m.
    destruct m as [| m'].
    + simpl. reflexivity.
    + discriminate.
  - intros m eq1.
    simpl in eq1.
    destruct m as [| m'].
    + discriminate.
    + simpl in eq1.
       injection eq1 as eq1.
       rewrite <- plus_n_Sm in eq1.
       rewrite <- plus_n_Sm in eq1.
       injection eq1 as eq1.
       apply IHn' in eq1.
       apply f_equal.
       apply eq1.
Qed.

(* Exercise *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l eq1.
  generalize dependent n.
  induction l as [| h t IHl'].
  - reflexivity.
  - intros n eq1.
    destruct n as [| n'].
    + discriminate.
    + simpl.
       injection eq1 as eq1.
       apply IHl' in eq1.
       apply eq1.
Qed.

(* Definition *)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Exercise *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. 
  induction l as [| h t IHl'].
  - intros l1 l2 eq1.
    injection eq1 as H1 H2.
    rewrite <- H1.
    rewrite <- H2. 
    reflexivity.
  - destruct h as [x y]. 
    simpl. 
    destruct (split t) as [lx ly].
    intros l1 l2 eq1. 
    injection eq1 as H3 H4. 
    rewrite <- H3. 
    rewrite <- H4. 
    simpl.
    apply f_equal. 
    apply IHl'. 
    reflexivity.
Qed.

(* Exercise *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn:ft.
    + rewrite ft.
       apply ft.
    + destruct (f false) eqn:ftf.
       * apply ft.
       * apply ftf.
  - destruct (f false) eqn:ff.
    + destruct (f true) eqn:fft.
       * apply fft.
       * apply ff.
    + rewrite ff.
       apply ff.
Qed.

(* Exercise *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  induction n as [| n' IHn'].
  - destruct m.
    + destruct p. 
         * reflexivity. 
         * discriminate. 
    + discriminate. 
  - destruct m.
    + discriminate.
    + destruct p.
       * discriminate.
       * simpl. 
         apply IHn'.
Qed.

(* Exercise *)
Definition split_combine_statement: Prop :=
  forall (X Y: Type) (l: list (X * Y)) (l1: list X) (l2: list Y) ,
  combine l1 l2 = l ->
  length l1 = length l2 ->
  split l = (l1, l2).

Theorem split_combine: forall (A B : Type) (l : list (A * B)) l1 l2,
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  induction l.
  - intros [] []. 
    + reflexivity. 
    + discriminate. 
    + discriminate. 
    + discriminate.
  - intros [] [].
    + discriminate.
    + discriminate.
    + discriminate.
    + intros.
       injection H as H.
       injection H0 as H0.
       simpl.
       destruct x.
       rewrite (IHl l0 l1 H H1).
       injection H0 as Ha Hb.
       rewrite Ha, Hb.
       reflexivity.
Qed.

Theorem filter_exercise:
  forall (X : Type) (test : X -> bool)
         (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l.

  induction l as [| a t IH].
  - discriminate.
  - intros lf H.
    destruct (test a) eqn:E.
    + simpl in H.
      rewrite -> E in H.
      injection H as H'1 H'2.
      rewrite <- H'1.
      apply E.
    + simpl in H.
      rewrite -> E in H.
      apply (IH lf).
      apply H.
Qed.




