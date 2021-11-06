(* Exercise *)
Definition nandb (b1 : bool) (b2 : bool) : bool :=
  match (b1, b2) with
  | (true,  true)  => false
  | _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (b1,b2,b3) with
  | (true,true,true) => true
  | _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Exercise *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

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

(* Exercise *)
Definition ltb (n m : nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. reflexivity. Qed.

(* Definition *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

(* Exercise *)
Theorem plus_id_exercise: forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros. rewrite -> H. rewrite <- H0. reflexivity. Qed.

(* Definition *)
Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

(* Exercise *)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof. 
  intros p.
  rewrite <- mult_n_Sm. 
  rewrite <- mult_n_O. 
  reflexivity. Qed.

(* Definition *)
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(* Exercise *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct c.
  - simpl. 
    intros H. 
    reflexivity.
  - rewrite -> andb_commutative. 
    simpl. 
    intros H. 
    rewrite H. 
    reflexivity. 
Qed.

(* Definition *)
Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Exercise *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros a b c. rewrite b. rewrite b. reflexivity. Qed.

(* Exercise *)
Theorem negation_fn_applied_twice : 
   forall (f : bool -> bool),
   (forall (x : bool), f x = negb x) ->
   forall (b:bool), f b = negb b.
Proof.
   intros a b c. rewrite b. reflexivity. Qed.

(* Exercise *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b.  
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity. Qed.

(* Exercise *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin
  := match m with
   | Z => B1 Z
   | B0 n' => B1 n'
   | B1 n' => B0 (incr n')
  end.

Fixpoint bin_to_nat (m:bin) : nat
  := match m with
    | Z => 0
    | B0 n' => mult 2 (bin_to_nat n')
    | B1 n' => plus 1 (mult 2 (bin_to_nat n'))
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity.  Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity.  Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity.  Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity.  Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity.  Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity.  Qed.




