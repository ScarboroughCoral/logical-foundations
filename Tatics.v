From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercise: 2 stars, standard, optional (silly_ex) *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.
(* End Exercise: 2 stars, standard, optional (silly_ex) *)

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H. Qed.

(* Exercise: 2 stars, standard (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros.
  Search rev.
  rewrite H. symmetry. apply rev_involutive.
Qed.
(* End Exercise: 2 stars, standard (apply_exercise1) *)

(* Exercise: 1 star, standard, optional (apply_rewrite) *)
(* 
rewrite used in forewards, apply while in backwards.
 *)
(* End Exercise: 1 star, standard, optional (apply_rewrite) *)

