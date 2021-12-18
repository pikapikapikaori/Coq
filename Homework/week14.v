Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.


Module AExp.

Inductive aexp : Type :=
| ANum: nat -> aexp
| APlus: aexp -> aexp -> aexp
| AMinus: aexp -> aexp -> aexp
| AMult: aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a: aexp) : nat :=
  match a with
  | ANum n => n
  | APlus l r => (aeval l) + (aeval r)
  | AMinus l r => (aeval l) - (aeval r)
  | AMult l r => (aeval l) * (aeval r)
  end.

Fixpoint beval (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq l r => beq_nat (aeval l) (aeval r)
  | BLe l r => leb (aeval l) (aeval r)
  | BNot b' => negb (beval b')
  | BAnd l r => andb (beval l) (beval r)
  end.

Fixpoint optimize_0plus (a: aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) r => (optimize_0plus r)
  | APlus l r => APlus (optimize_0plus l) (optimize_0plus r)
  | AMinus l r => AMinus (optimize_0plus l) (optimize_0plus r)
  | AMult l r => AMult (optimize_0plus l) (optimize_0plus r)
  end.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BEq l r => BEq (optimize_0plus l) (optimize_0plus r)
  | BLe l r => BLe (optimize_0plus l) (optimize_0plus r)
  | BNot b' => BNot (optimize_0plus_b b')
  | BAnd l r => BAnd (optimize_0plus_b l) (optimize_0plus_b r)
  | _ => b
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
  - simpl.
    rewrite IHa1. rewrite IHa2.
    reflexivity.
  - simpl.
    rewrite IHa1. rewrite IHa2.
    reflexivity.
Qed.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b;
    try (simpl; reflexivity);
    try (simpl; repeat rewrite optimize_0plus_sound; reflexivity).
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.