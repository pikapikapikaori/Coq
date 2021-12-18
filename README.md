# Coq
     
## Introduction    
Coq class projects. 
     
## Homework     
Coq homework
### Homework 3
定义名为Z2的类型，其含zero和one，定义其上模2加法，用+表示，并证明下式。
```coq
Example testAdd1: zero + zero = zero.
Example testAdd2: zero + one = one.
Example testAdd3: one + zero = one.
Example testAdd4: one + one = zero.
```
### Homework 4
1. 定义函数gtb，使得gtb n m 返回布尔值 true当且仅当 n > m。至少用两种方法定义这个函数。     
2. 证明下面的性质。 
```coq    
Theorem gtb_test : forall n : nat,  gtb (n+1) 0 = true.
```
3. 定义斐波那契数列。
### Homework 5
1. 证明下面的性质。 
```coq    
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
(* FILL IN HERE *) Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
(* FILL IN HERE *) Admitted.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
(* FILL IN HERE *) Admitted.
```
2. 给定自然数d与自然数列表L，定义函数`(hd (d L)`，使其返回列表第一个和最后一个自然数，例如：
```coq
Example test_ht1 : ht 0 [] = (0,0).
Proof. reflexivity. Qed.
Example test_ht2 : ht 0 [3] = (3,3).
Proof. reflexivity. Qed.
Example test_ht3 : ht 0 [1;2;3;4] = (1,4).
Proof. reflexivity. Qed.
```
### Homework 6
1. 补充完整下面的定义，判断一个集合是否为另一个集合的子集。
```coq
Fixpoint subset (s1 : bag) (s2 : bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_subset1:  subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:  subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
```
2. 证明如下性质
```coq
Theorem app_assoc4 : ∀ l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.
```
3. Before doing the next exercise, make sure you've filled in the definition of remove_one in the chapter Lists.
```coq
Theorem remove_does_not_increase_count: ∀ (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
```
### Homework 7
1. 定义函数maxPair，找出输入的自然数的最大偶数和奇数，组成二元组输出，没有用0代替。
```coq
Example test_maxPair1: maxPair [1;2;5;4;8;10;3] = (5, 10).
Proof. reflexivity. Qed.
Example test_maxPair2: maxPair [2;4] = (0, 4).
Proof. reflexivity. Qed.
```
2. 把上面的函数maxPair改造成maxPair'，返回类型为option nat * option nat。当要找的数字不存在时用None而不是0替代。
```coq
Example test_maxPair‘1: maxPair’ [1;2;5;4;8;10;3] = (Some 5, Some 10).
Proof. reflexivity. Qed.
Example test_maxPair‘2: maxPair’ [2;4] = (None, Some 4).
Proof. reflexivity. Qed.
```
3. 
```coq
Theorem rev_app_distr: ∀ X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.
```
4. 
```coq
Theorem rev_involutive : ∀ X : Type, ∀ l : list X,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.
```
### Homework 8

sf-exercise chapter 1-5.

### Homework 9

1. 
```coq
Theorem or_commut : forall P Q : Prop,  P \/ Q  -> Q \/ P.
Proof.  (* FILL IN HERE *) Admitted.
```

2. 
```coq
Theorem not_both_true_and_false : ∀ P : Prop,
  ¬ (P ∧ ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
```

3. 
```coq
Theorem or_distributes_over_and : ∀ P Q R : Prop,
  P ∨ (Q ∧ R) -> (P ∨ Q) ∧ (P ∨ R).
Proof.
  (* FILL IN HERE *) Admitted.
```

4. 
```coq
Theorem or_distributes_over_and' : ∀ P Q R : Prop,
  (P ∨ Q) ∧ (P ∨ R) -> P ∨ (Q ∧ R).
Proof.
  (* FILL IN HERE *) Admitted.
```

### Homework 10

1. 
```coq
Theorem In_app_iff : ∀ A l l' (a:A),
  In a (l++l') ↔ In a l ∨ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  (* FILL IN HERE *) Admitted.
```

2. 
Recall that functions returning propositions can be seen as   properties  of their arguments. For instance, if    P  has type  nat    →   Prop, then    P    n  states that property    P  holds of    n.
Drawing inspiration from    In, write a recursive function    All  stating that some property    P  holds of all elements of a list    l. To make sure your definition is correct, prove the    All_In  lemma below. (Of course, your definition should   notjust restate the left-hand side of    All_In.)  

```coq
Fixpoint   All  { T  :   Type} ( P  :   T   →   Prop) ( l  :   list   T) :   Prop 
   (* REPLACE THIS LINE WITH ":= _your_definition_ ." *).   Admitted. 
Theorem   All_In  : 
   ∀   T  ( P  :   T   →   Prop) ( l  :   list   T), 
     ( ∀   x,   In   x   l   →   P   x )   ↔ 
     All   P   l. 
Proof. 
   (* FILL IN HERE *)   Admitted.
```

### Homework 11

1. Inductively define a relation CE such that (CE m n) holds iff m and n are two consecutive even numbers with m smaller than n.
```coq
Example test_CE : CE 4 6.
Proof. (* Fill in here *) Admitted.
```

2. 
```coq
Theorem CE_SS : forall n m, CE (S (S n)) (S (S m)) -> CE n m.
Proof. (* Fill in here *) Admitted.
```

3. 
```coq
Theorem ev_sum : ∀ n m, ev n → ev m → ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
```

4. 
```coq
Lemma le_trans : ∀ m n o, m ≤ n → n ≤ o → m ≤ o.
Proof.
  (* FILL IN HERE *) Admitted.
```

### Homework 12

1. Prove the following theorem. Hint: You may find the theorem eqb_string_false_iff in the textbook useful.
```coq
Theorem t_update_neq : ∀ (A : Type) (m : total_map A) x1 x2 v,
  x1 ≠ x2 →
  (x1 !-> v ; m) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
```

2. Prove the following lemma. Hint: You may use functional_extensionality from the Coq library.
```coq
Lemma t_update_shadow : ∀ (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
```

3. Construct a proof object for the following proposition. 
```coq
Definition conj_disj : forall P Q R, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R)
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *) . Admitted.
```

### Homework 13

1. Complete this proof without using the induction tactic. 
```coq
Theorem   plus_one_r'  :   ∀   n: nat, 
   n   +  1   =   S   n. 
Proof. 
   (* FILL IN HERE *)   Admitted.
```

2. Show that the   empty_relation defined in (an exercise in)  IndProp is a partial function. 
```coq
(* FILL IN HERE *)
```

3.  
```coq
Theorem   le_Sn_n  :  ∀   n , 
   ¬   ( S   n   ≤   n ) . 
Proof . 
   (* FILL IN HERE *)   Admitted .
```

4. 
```coq
Theorem   le_antisymmetric  : 
   antisymmetric   le . 
Proof . 
   (* FILL IN HERE *)   Admitted .
```

### Homework 14
1. Since the   optimize_0plus  transformation doesn't change the value of   aexps, we should be able to apply it to all the   aexps that appear in a   bexp  without changing the   bexp's value. Write a function that performs this transformation on   bexps and prove it is sound. Use the tacticals we've learned to make the proof as elegant as possible.  
```coq
Fixpoint   optimize_0plus_b  ( b  :   bexp) :   bexp 
   (* REPLACE THIS LINE WITH ":= _your_definition_ ." *).   Admitted. 
Theorem   optimize_0plus_b_sound  :   ∀   b, 
   beval  ( optimize_0plus_b   b)  =   beval   b. 
Proof. 
   (* FILL IN HERE *)   Admitted.
```

## Quiz.     
Class quizes.

### Quiz 1
编写二次方函数。
### Quiz 2
```coq
Definition bag := natlist.
Fixpoint  count ( v :  nat) ( s :  bag) :  nat 
   (* REPLACE THIS LINE WITH ":= _your_definition_ ." *).  Admitted.
All these proofs can be done just by   reflexivity.
Example  test_count1:  count 1  [1 ;2 ;3 ;1 ;4 ;1 ]  = 3. 
  (* FILL IN HERE *)  Admitted. 
Example  test_count2:  count 6  [1 ;2 ;3 ;1 ;4 ;1 ]  = 0. 
  (* FILL IN HERE *)  Admitted.
```
### Quiz 3
Define type ListOfNatlists whose elements are natlists.

### Quiz 4

## sf-exercise       

My solution for https://softwarefoundations.cis.upenn.edu
