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