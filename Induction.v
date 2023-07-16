From LF Require Export Basics.

Theorem add_0_r_firsttry: forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.


Theorem add_0_r_secondary: forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem add_0_r: forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n: forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercise: 2 stars, standard, especially useful (basic_induction) *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros m n. induction m as [|m' IHm'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHm'. reflexivity.
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n,m.
  - reflexivity.
  - simpl. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite -> IHn. simpl. reflexivity.
  - simpl. rewrite -> IHn. simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n.
  - rewrite -> add_comm. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.
(* End Exercise: 2 stars, standard, especially useful (basic_induction) *)

(* Exercise: 2 stars, standard (double_plus) *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.
(* End Exercise: 2 stars, standard (double_plus) *)

(* Exercise: 2 stars, standard (eqb_refl) *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.
(* End Exercise: 2 stars, standard (eqb_refl) *)

(* Exercise: 2 stars, standard, optional (even_S) *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - rewrite -> IHn. rewrite -> negb_involutive. simpl. reflexivity.
Qed.
(* End Exercise: 2 stars, standard, optional (even_S) *)

(* Exercise: 1 star, standard, optional (destruct_induction) *)
(* 
  destruct 和 induction 都是证明策略，用于对归纳定义的类型进行推理和证明。它们的主要区别在于它们应用的场景和效果。

  destruct 策略是用于对某个类型的所有构造子进行分类讨论的。它将目标分解为每个构造子的情况，并为每种情况生成一个子目标。这种策略通常用于证明非归纳类型或证明归纳类型的某些性质，但不涉及归纳原理本身。
  induction 策略更常用于证明归纳类型的性质，它可以应用归纳原理来证明目标。它会生成两个子目标：一个基本情况，其中归纳变量的值为基本构造子；另一个归纳情况，其中归纳变量的值为构造子的递归形式。
*)
(* End Exercise: 1 star, standard, optional (destruct_induction) *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

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

(* Exercise: 2 stars, advanced, especially useful (add_comm_informal) *)

(* 
Proof: 归纳推理n
1. n=0时，需要证明0+m=m+0。此时对m分情况讨论。
  1.1. m=0时，需要证明0+0=0+0，根据加法定义显然成立。
  1.2. m=Sm'时，需要证明0+Sm'=Sm'+0，根据加法定义就是证明Sm'=S(m'+0)，根据add_0_r定理就可以证明S(m'+0)=Sm'。
2. n=Sn'时，假设n'+m=m+n'，需要证明Sn'+m=m+Sn'。此时对m分情况讨论。
  2.1. m=0时，需要证明Sn'+0=0+Sn'。根据加法定义和add_0_r定理显然成立。
  2.2. m=Sm'时，需要证明Sn'+Sm'=Sm'+Sn'，根据加法定义和plus_n_Sm进行简化显然成立。
*)
  
(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(* End Exercise: 2 stars, advanced, especially useful (add_comm_informal) *)

(* Exercise: 2 stars, standard, optional (eqb_refl_informal) *)
(* 不做了 *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.

(* End Exercise: 2 stars, standard, optional (eqb_refl_informal) *)

(* Exercise: 3 stars, standard, especially useful (mul_comm) *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc. rewrite add_comm. rewrite add_assoc. rewrite add_comm.
  assert (H: p+n=n+p).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction m.
  - simpl. rewrite <- mult_n_O. reflexivity.
  - simpl. rewrite add_comm. rewrite <- mult_n_Sm. rewrite IHm. reflexivity.
Qed.
(* End Exercise: 3 stars, standard, especially useful (mul_comm) *)

(* Exercise: 2 stars, standard, optional (plus_leb_compat_l) *)
Check leb.
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p.
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp. reflexivity.
Qed.
(* End Exercise: 2 stars, standard, optional (plus_leb_compat_l) *)

(* Exercise: 3 stars, standard, optional (more_exercises) *)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n. 
  simpl. reflexivity.
Qed.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. induction b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl. rewrite add_0_r. reflexivity.
Qed.
  
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b,c.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* Lemma add_reduce_left: forall m n p : nat,
  m + n =? m + p = true -> n =? p = true.
Proof.
  intros m n p.
  induction m.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. rewrite IHm.
    + reflexivity.
    + rewrite H. reflexivity.
Qed.
   *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p.
  - rewrite mul_0_r. rewrite mul_0_r. rewrite mul_0_r. reflexivity.
  - rewrite <- mult_n_Sm. rewrite <- mult_n_Sm. rewrite <- mult_n_Sm.
    rewrite (add_comm (n*p) n).
    rewrite (add_assoc (n + n * p) (m * p) m).
    rewrite (add_comm (n + n * p + m * p) m).
    rewrite (add_assoc m (n + n * p) (m * p)).
    rewrite (add_assoc m n (n * p)).
    rewrite (add_comm m n).
    rewrite (add_comm ((n + m) * p) (n + m)).
    rewrite IHp.
    rewrite add_assoc.
    reflexivity.
Qed.
    
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn. reflexivity.
Qed.

(* End Exercise: 3 stars, standard, optional (more_exercises) *)

(* Exercise: 2 stars, standard, optional (add_shuffle3') *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite (add_comm n m).
  rewrite add_assoc.
  reflexivity.
Qed.
(* End Exercise: 2 stars, standard, optional (add_shuffle3') *)

Fixpoint incr (m:bin) : bin :=
  match m with
    | Z => B1 Z
    | B0 n => B1 n
    | B1 n => B0 (incr n)
  end.
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
    | Z => 0
    | B0 n => 2 * (bin_to_nat n)
    | B1 n => 1 + 2 * (bin_to_nat n)
  end.

(* Exercise: 3 stars, standard, especially useful (binary_commute) *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b.
  - simpl. reflexivity.
  - simpl. rewrite add_0_r. reflexivity.
  - simpl.
    rewrite add_0_r.
    rewrite add_0_r.
    rewrite IHb.
    simpl.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.
(* End Exercise: 3 stars, standard, especially useful (binary_commute) *)





































