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
