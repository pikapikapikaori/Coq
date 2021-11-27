Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive CE : nat -> nat -> Prop :=
  | CE_0: CE 0 2
  | CE_SSnm (n m : nat) (H : CE n m ): CE (S (S n)) (S (S m)).

Example test_CE : CE 4 6.
Proof.
  apply CE_SSnm.
  apply CE_SSnm.
  apply CE_0.
Qed.

Theorem CE_SS : forall n m, CE (S (S n)) (S (S m)) -> CE n m.
Proof. 
  intros n m H.
  inversion H.
  apply H2.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2.
  induction H1.
  - simpl.
    apply H2.
  - apply ev_SS.
    apply IHev.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H2.
  - apply H1.
  - apply le_S.
    apply IHle.
    apply H1.
Qed.
