Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - simpl. reflexivity.
  - intros n H.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.

Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive empty_relation : nat -> nat -> Prop := .

Theorem empre_is_a_partial_function :
  (partial_function empty_relation).
Proof.
  unfold partial_function.
  intros.
  inversion H.
Qed.

Theorem   le_Sn_n  :  forall  n , 
   ~ ( S n <=  n ) . 
Proof . 
  unfold not.
  induction n.
  - intros.
    inversion H.
  - intros.
    apply IHn.
    apply le_S_n.
    apply H.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Lmn Lno.
  generalize dependent Lmn.
  generalize dependent m.
  induction Lno.
  - intros. apply Lmn.
  - intros. apply le_S. apply IHLno. apply Lmn.
Qed.

Theorem n_le_Sn : forall n, n <= S n.
Proof. intros. apply le_S. apply le_n. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
    apply le_n.
    apply le_trans with (n := S n). apply n_le_Sn.
    apply H1.
Qed.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b.
  generalize dependent a.
  induction b.
  - intros.
    inversion H.
    reflexivity.
  - intros.
    destruct a.
    + inversion H0.
    + apply  Sn_le_Sm__n_le_m in H.
       apply Sn_le_Sm__n_le_m in H0.
       apply IHb in H.
       * rewrite H.
         reflexivity.
       * apply H0.
Qed.