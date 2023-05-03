Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday  =>  friday
  | friday  =>  monday
  | saturday  => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday))  = tuesday.
Proof.  simpl.  reflexivity.  Qed.

From Coq  Require Export  String.

Inductive bool: Type :=
  | true
  | false.

Definition negb (b:bool) :  bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool  :=
  match b1  with
  | true  =>  b2
  | false => false
  end.

Definition orb  (b1:bool) (b2:bool) : bool  :=
  match b1 with
  | true =>  true
  | false => b2
  end.

Example test_orb1:  (orb  true  false)  = true.
Proof.  simpl.  reflexivity.  Qed.

Example test_orb2:  (orb  false false)  = false.
Proof.  simpl.  reflexivity.  Qed.

Example test_orb3:  (orb  true  true) = true.
Proof.  simpl.  reflexivity.  Qed.

Example test_orb4:  (orb  false true) = true.
Proof.  simpl.  reflexivity.  Qed.

Notation  "x  &&  y"  :=  (andb x y).
Notation  "x  ||  y"  :=  (orb  x y).

Example test_orb5: false  ||  false ||  true  = true.
Proof.  simpl.  reflexivity.  Qed.


Definition  negb' (b:bool)  : bool  :=
  if  b then false
  else  true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(* Exercise: 1 star, standard (nandb) *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1  with
  | true  => negb b2
  | false => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof.  simpl.  reflexivity.  Qed.
Example test_nandb2: (nandb false false) = true.
Proof.  simpl.  reflexivity.  Qed.
Example test_nandb3: (nandb false true) = true.
Proof.  simpl.  reflexivity.  Qed.
Example test_nandb4: (nandb true true) = false.
Proof.  simpl.  reflexivity.  Qed.
(* End Exercise: 1 star, standard (nandb) *)

(* Exercise: 1 star, standard (andb3) *)
Definition andb3 (b1 b2 b3 : bool) : bool :=
  andb (andb b1 b2) b3.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* End Exercise: 1 star, standard (andb3) *)
Check true.
Check negb.
Check true  : bool.

Inductive rgb : Type  :=
  | red
  | green
  | blue.

Inductive color :  Type :=
  | black
  | white
  | primary (p  : rgb).

Definition  monochrome  (c  : color)  : bool  :=
  match c with
  | black =>  true
  | white =>  true
  | primary p => false
  end.

Definition  isred (c  : color)  : bool  :=
  match c with
  | black =>  false
  | white =>  false
  | primary red =>  true
  | primary _ =>  false
  end.


Module  Playground.
  Definition  myblue: rgb :=  blue.
End Playground.

Definition  myblue  : bool  :=  true.

Check Playground.myblue : rgb.
Check myblue  : bool.


Module  TuplePlayground.
Inductive bit : Type  :=
  | B0
  | B1.

Inductive nybble  : Type  :=
  | bits  (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.
Compute all_zero(bits B1 B0 B1 B0).
Compute all_zero(bits B0 B0 B0 B0).
End TuplePlayground.

Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).
Inductive nat' : Type :=
  | stop
  | tick (foo : nat').
Definition pred (n : nat) :=
  match n with
  | O => O
  | S n' => n'
  end.
End NatPlayground.

Check S (S O).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute minustwo 11.

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.


Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => plus n' (S m)
  end.

Compute (plus 3 2).

Fixpoint mult (m n : nat) : nat :=
  match m with
  | O => O
  | S m' => plus n (mult m' n)
  end.

Example test_mult1 : (mult 4 7) = 28.
Proof. simpl. reflexivity. Qed.

Definition minus (m n : nat) : nat :=
  match m, n with
  | O, _ => O
  | _, O => m
  | S m', S n' => minus m' n'
  end.
Example test_minus1: (minus 11 9) = 2.
Proof. simpl. reflexivity. Qed.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.
Example test_exp1: (exp 2 10) = 1024.
Proof. simpl. reflexivity. Qed.

End NatPlayground2.

(* Exercise: 1 star, standard (factorial) *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
(* End Exercise: 1 star, standard (factorial) *)

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S m', S n' => eqb m' n'
  end.

Fixpoint leb (m n : nat) : bool :=
  match m, n with
  | O, _ => true
  | S m', O => false
  | S m', S n' => leb m' n'
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


(* Exercise: 1 star, standard (ltb) *)
Definition ltb (n m : nat) : bool :=
  andb (negb (eqb n m)) (leb n m).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
(* End Exercise: 1 star, standard (ltb) *)


Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_0_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem plus_id_example' : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
  Qed.

(* Exercise: 1 star, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
  Qed.
(* End Exercise: 1 star, standard (plus_id_exercise) *)

Check mult_0_l.
Check mult_n_Sm.
Check mult_n_O.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
  Qed.

(* Exercise: 1 star, standard (mult_n_1) *)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
  Qed.
(* End Exercise: 1 star, standard (mult_n_1) *)


Theorem plus_1_neq_0_fristtry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.


Theorem plus_1_neq_0_fristtry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn : E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn : E.
  - reflexivity.
  - reflexivity.
  Qed.


Theorem andb_commutive : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn : Eb.
  - destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutive' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn : Eb.
  {
    destruct c eqn : Ec.
    { reflexivity. }
    { reflexivity. }
  }
  {
    destruct c eqn : Ec.
    { reflexivity. }
    { reflexivity. }
  }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.


(* Exercise: 2 stars, standard (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn : Eb.
  - destruct c eqn : Ec.
    -- simpl. intros H. reflexivity.
    -- simpl. intros H. rewrite -> H. reflexivity.
  - destruct c eqn : Ec.
    -- simpl. intros H. reflexivity.
    -- simpl. intros H. rewrite -> H. reflexivity.
Qed.
(* End Exercise: 2 stars, standard (andb_true_elim2) *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 1 star, standard (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.
(* End Exercise: 1 star, standard (zero_nbeq_plus_1) *)


(* Exercise: 2 stars, standard, optional (decreasing) *)
(* Fixpoint plus_all_terminated (m n : nat) : nat :=
  match m, n with
  | O, O => O
  | O, n' => n'
  | m', O => m'
  | S m', S n' => m'
  end. *)
(* End Exercise: 2 stars, standard, optional (decreasing) *)

(* Exercise: 1 star, standard (identity_fn_applied_twice) *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.
(* End Exercise: 1 star, standard (identity_fn_applied_twice) *)

(* Exercise: 1 star, standard (negation_fn_applied_twice) *)
Theorem negb_negb_b_eq_b : forall b, negb (negb b) = b.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_negb_b_eq_b.
  reflexivity.
Qed.
  
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.
(* End Exercise: 1 star, standard (negation_fn_applied_twice) *)

(* Exercise: 3 stars, standard, optional (andb_eq_orb) *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.
(* End Exercise: 3 stars, standard, optional (andb_eq_orb) *)

Module LateDays.
Inductive letter : Type :=
  | A | B | C | D | F.
Inductive modifier : Type :=
  | Plus | Natural | Minus.
Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Set :=
  | Eq : comparison (* "equal" *)
  | Lt : comparison (* "less than" *)
  | Gt : comparison. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
    | A, A => Eq
    | A, _ => Gt
    | B, A => Lt
    | B, B => Eq
    | B, _ => Gt
    | C, (A | B) => Lt
    | C, C => Eq
    | C, _ => Gt
    | D, (A | B | C) => Lt
    | D, D => Eq
    | D, _ => Gt
    | F, (A | B | C | D) => Lt
    | F, F => Eq
  end.

Compute letter_comparison B A.
Check letter_comparison.

(* Exercise: 1 star, standard (letter_comparison) *)
Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* End Exercise: 1 star, standard (letter_comparison) *)

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

(* Exercise: 2 stars, standard (grade_comparison) *)
Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | (Grade l1 m1), (Grade l2 m2) => match (letter_comparison l1 l2), (modifier_comparison m1 m2) with
    | Eq, Eq => Eq
    | Eq, Lt => Lt
    | Eq, Gt => Gt
    | Gt, _ => Gt
    | Lt, _ => Lt
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. reflexivity. Qed.
  
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. reflexivity. Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. reflexivity. Qed.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. reflexivity. Qed.
(* End Exercise: 2 stars, standard (grade_comparison) *)

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Note that you can't go lower than F *)
  end.

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. (* We get stuck here. *)
Abort.

Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

(* Exercise: 2 stars, standard (lower_letter_lowers) *)
Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.
(* End Exercise: 2 stars, standard (lower_letter_lowers) *)

Check comparison.
Check Eq.
Check grade.
Check bool.
Check Grade A Plus.

(* (* Exercise: 2 stars, standard (lower_grade) *)
Definition lower_grade (g : grade) : grade
  match g with
  | Grade l m => Grade (lower_letter l) m
  end.
(* End Exercise: 2 stars, standard (lower_grade) *)
 *)

End LateDays.




















