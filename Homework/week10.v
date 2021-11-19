Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

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

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_app_iff: forall A l l' (a: A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A.
  induction l as [| a t IH].
  - intros l' a. split.
    + intros H. right. apply H.
    + intros [H1 | H2].
      * destruct H1.
      * apply H2.
  - intros l' x. split.
    + intros [H1 | H2]. 
      * left. left. apply H1.
      * apply IH in H2.
        destruct H2 as [H3 | H4].
        -- left. right. apply H3.
        -- right. apply H4.
    + intros [[H1 | H2] | H3].
      * left. apply H1.
      * right. apply IH. left. apply H2.
      * right. apply IH. right. apply H3.
Qed.

Fixpoint All {T: Type} (P: T -> Prop) (l: list T): Prop :=
  match l with
  | [] => True
  | a :: t => P a /\ All P t
  end.

Lemma All_In:
  forall T (P: T -> Prop) (l: list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T.
  induction l as [| a t IH].
  - split.
    + intros H. apply I.
    + intros H0 x H.
      destruct H.
  - split.
    + intros H. split.
      * apply H. left. reflexivity.
      * apply IH. intros x H2.
        apply H. right. apply H2.
    + intros [H1 H2] x H3.
      destruct H3 as [H4 | H5].
      * rewrite <- H4. apply H1.
      * apply IH. apply H2. apply H5.
Qed.