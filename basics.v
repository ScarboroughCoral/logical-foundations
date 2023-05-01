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
















