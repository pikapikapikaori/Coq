(* Definition *)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

(* Exercise *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
 
Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  intros n m. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed. 


Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n.
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.


Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.  
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(* Exercise *)
Lemma double_negb : forall b,
  negb (negb b) = b.
Proof.
  destruct b. reflexivity. reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - rewrite IHn.
    rewrite (double_negb (even n)). reflexivity.
Qed.

(* Exercise *)
(** destruct is case analysis, 
    coq automatically checks every case listed, 
    while by using induction coq while automatically 
    check every case when only two case are listed.*)

(* Definition *)
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(* Exercise *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite add_assoc.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. rewrite add_assoc.
  reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma mul_n_O : forall n : nat, n * 0 = 0.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma mul_plus_dist :
  forall m n p : nat, n * (m + p) = n * m + n * p.
Proof.
  intros m n p.
  induction n.
  + simpl. reflexivity. 
  + simpl. rewrite IHn.
    repeat (rewrite add_assoc).
    assert (m + p + n * m = m + n * m + p).
    {  rewrite <- add_assoc.
       replace (p + n * m) with (n * m + p).
       * rewrite add_assoc. reflexivity.
       * rewrite add_comm. reflexivity.
    }
    rewrite H. reflexivity.
Qed.

Lemma mul_n_1 : forall n, n * 1 = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed. 

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m.
  - rewrite mul_0_r.
    simpl.  reflexivity.
  - simpl.
    replace (S m) with (m + 1).
    +  rewrite mul_plus_dist.
       rewrite mul_n_1. rewrite add_comm. rewrite IHm. 
       reflexivity.
    +  rewrite add_comm. simpl. reflexivity.
Qed.

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
Check leb.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
   induction n as [|m].
   reflexivity.
   simpl. rewrite <- IHm. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b. 
  - reflexivity. 
  - reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [|q].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHq. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. 
  destruct b. destruct c.
  - reflexivity. 
  - reflexivity. 
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite mult_plus_distr_r.
    reflexivity.
Qed.

(* Exercise *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros. induction n as [|m].
  - simpl. reflexivity.
  - simpl. rewrite -> IHm. reflexivity.
Qed.

(* Exercise *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> add_assoc. rewrite -> add_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite -> add_comm. reflexivity.
Qed.

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

Fixpoint convert_to_unary (n : bin) : nat :=
  match n with
  | Z => 0
  | B0 n' => (convert_to_unary n') + (convert_to_unary n')
  | B1 n' => S ((convert_to_unary n') + (convert_to_unary n'))
  end.

Theorem binary_commute : forall b,
  convert_to_unary (incr b) = S (convert_to_unary b).
Proof.
  intros.
  induction b as [|c|c].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHc. simpl.
    assert (H : forall n m, S (n + S m) = S (S (n + m))).
    { intros.
      induction n as [|p].
      + simpl. reflexivity.
      + simpl. rewrite -> IHp. reflexivity.
    }
    rewrite -> H. reflexivity.
Qed.

