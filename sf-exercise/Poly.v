(* Definition *)
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

(* Definition *)
Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.

(* Exercise *)
(**no
  yes
  yes
  yes
  yes
  no
  no*)

(* Definition *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
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

(* Exercise *)
Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  intro X.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intro A.
  intros l m n.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| a t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

(* Exercise *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| a t IH].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IH, app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr, IH. reflexivity.
Qed.

(* Definition *)
Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Exercise *)
(* forall X Y : Type,
       list X -> list Y -> list (X * Y) *)
(* [(1, false); (2, false)]
     : list (nat * bool) *)

(* Exercise *)
Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | nil => ([], [])
  | (a, b) :: t => let (x', y') := split t in (a :: x', b :: y')
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* Definition *)
Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

(* Exercise *)
Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | a :: _ => Some a
  end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(* Definition *)
Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

(* Exercise *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (gtb n 7)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* Exercise *)
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Definition *)
Fixpoint map {X Y: Type} (f:X -> Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

(* Exercise *)
Lemma map_app_r : forall
  (X Y : Type) (f : X -> Y) (l : list X) (a : X),
  map f (l ++ [a]) = map f l ++ [f a].
Proof.
  intros X Y f l a.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. rewrite -> map_app_r, IH. reflexivity.
Qed.

(* Exercise *)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X): (list Y) :=
  match l with
  | nil => nil
  | a :: t => f a ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(* Definition *)
Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* Exercise *)
(** For, example, while inserting a nat into a nat list, and 
  we always want to know the sum. *)

(* Exercise *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1: fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct: forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

(* Exercise *)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x l => f x :: l) l [].

Example test_fold_map1: fold_map negb [true;true;true] = [false;false;false].
Proof. reflexivity. Qed.

Theorem fold_map_correct: forall
  (X Y: Type) (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

(* Exercise *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  let (x, y) := p in f x y.

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem uncurry_curry: forall
  (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry: forall
  (X Y Z : Type) (f : (X * Y) -> Z)
  (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  reflexivity.
Qed.

(* Definition *)
Module Church.

Definition cnat := forall X: Type, (X -> X) -> X -> X.

Definition zero: cnat :=
  fun (X: Type) (f: X -> X) (x: X) => x.

Definition one: cnat :=
  fun (X: Type) (f: X -> X) (x: X) => f x.

Definition two: cnat :=
  fun (X: Type) (f: X -> X) (x: X) => f (f x).

Definition three: cnat :=
  fun (X: Type) (f: X -> X) (x: X) => f (f (f x)).

(* Exercise *)
Definition succ (n: cnat): cnat :=
  fun (X: Type) (f: X -> X) (x: X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(* Exercise *)
Definition plus (n m : cnat): cnat :=
  fun (X: Type) (f: X -> X) (x: X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* Exercise *)
Definition mult (n m : cnat): cnat :=
  fun (X: Type) (f: X -> X) (x: X) => m X (n X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* Exercise *)
Definition exp (n m: cnat): cnat :=
  fun (X: Type) => m (X -> X) (n X).
  (* fun (X: Type) (f: X -> X) (x: X) => m cnat (mult n) one. *)

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.


