Theorem or_commut : forall P Q : Prop,  P \/ Q  -> Q \/ P.
Proof.  
  intros P Q H.
  destruct H as [H1 | H2].
  + right. apply H1.
  + left. apply H2.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros P [H1 H2].
  apply H2.
  apply H1.
Qed.

 Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  + destruct H as [H1 | H2].
     - left. apply H1.
     - destruct H2 as [H21 H22].
       right. apply H21.
  + destruct H as [H1 | H2].
     - left. apply H1.
     - destruct H2 as [H21  H22].
       right. apply H22.
Qed.

Theorem or_distributes_over_and' : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H1 as [H11 | H12].
  + destruct H2 as [H21 | H22].
     - left. apply H11.
     - left. apply H11.
  + destruct H2 as [H21 | H22].
     - left. apply H21.
     - right. split.
       * apply H12.
       * apply H22.
Qed.



