From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* Exercise: 2 stars, standard, optional (mumble_grumble) *)
Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).
(* Check d (b a 5).*)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.

(*
d (b a 5) = No
d mumble (b a 5) = Yes
d bool (b a 5) = Yes
e bool true = Yes
e mumble (b c 0) = Yes
e bool (b c 0) = No
c = No
*)

End MumbleGrumble.
(* End Exercise: 2 stars, standard, optional (mumble_grumble) *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat' : forall X : Type, X -> nat -> list X.

Check repeat'.

Fixpoint repeat'' X x count : list X :=
match count with
| 0 => nil _
| S count' => cons _ x (repeat'' _ x count')
end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

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
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(* Exercise: 2 stars, standard (poly_exercises) *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.
(* End Exercise: 2 stars, standard (poly_exercises) *)

(* Exercise: 2 stars, standard (more_poly_exercises) *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.
(* End Exercise: 2 stars, standard (more_poly_exercises) *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Exercise: 1 star, standard, optional (combine_checks) *)
(* 
Try answering the following questions on paper and checking your answers in Coq:
*)
(* 
Q: What is the type of combine (i.e., what does Check @combine print?)
A: forall (X Y : Type), list X -> list Y -> list (X * Y)
*)
Check @combine : forall (X Y : Type), list X -> list Y -> list (X * Y).
(* 
Q: What does Compute (combine [1;2] [false;false;true;true]). print? 
A: [(1,false);(2;false)] : list (nat * bool)
*)
Compute (combine [1;2] [false;false;true;true]).
(* End Exercise: 1 star, standard, optional (combine_checks) *)

(* Exercise: 2 stars, standard, especially useful (split) *)
Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
match l with
| nil => (nil, nil)
| (x,y)::l' => (x::(fst(split l')), y::(snd(split l')))
end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.
(* End Exercise: 2 stars, standard, especially useful (split) *)

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard, optional (hd_error_poly) *)
Definition hd_error {X : Type} (l : list X) : option X :=
match l with
| nil => None
| a::l' => Some a
end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
(* End Exercise: 1 star, standard, optional (hd_error_poly) *)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Fixpoint gtb (a b : nat) :=
match a, b with
| 0, 0 => false
| a', 0 => true
| 0, b' => false
| S a', S b' => gtb a' b'
end.
Notation "x >? y" := (gtb x y) (at level 70) : nat_scope.
(* Exercise: 2 stars, standard (filter_even_gt7) *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (even n) && (n >? 7)) l.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
(* End Exercise: 2 stars, standard (filter_even_gt7) *)

(* Exercise: 3 stars, standard (partition) *)
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X := (filter test l, filter (fun x => negb (test x)) l).
Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
(* End Exercise: 3 stars, standard (partition) *)

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
(* Exercise: 3 stars, standard (map_rev) *)
Lemma map_distribute : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ (map f l2).
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. simpl. rewrite map_distribute. simpl. reflexivity.
Qed.
(* End Exercise: 3 stars, standard (map_rev) *)

(* Exercise: 2 stars, standard, especially useful (flat_map) *)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y :=
match l with
|nil => nil
|x::l' => f x ++ (flat_map f l')
end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
(* End Exercise: 2 stars, standard, especially useful (flat_map) *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* Exercise: 2 stars, standard, optional (implicit_args) *)

Fixpoint filter_explicit_type (X:Type) (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter_explicit_type X test t)
    else filter_explicit_type X test t
  end.
Check filter_explicit_type: forall X: Type, (X -> bool) -> list X -> list X.
Example test_filter_explicit_type1: filter_explicit_type nat even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.


Example test_filter_explicit_type2:
    filter_explicit_type (list nat) length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Fixpoint map_explicit_type (X Y : Type) (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map_explicit_type X Y f t)
  end.
Check map_explicit_type: forall X Y: Type, (X -> Y) -> list X -> list Y.
Example test_map_explicit_type1: map_explicit_type nat nat (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map_explicit_type2:
  map_explicit_type nat bool odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map_explicit_type3:
    map_explicit_type nat (list bool) (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
(* End Exercise: 2 stars, standard, optional (implicit_args) *)

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard, optional (fold_types_different) *)
Definition app' {X : Type} (xs ys : list X) : list X := fold cons xs ys.

Example app'_example :
  app' [1;2;3] [4;5;6] = app [1;2;3] [4;5;6].
Proof. reflexivity. Qed.
(* End Exercise: 1 star, standard, optional (fold_types_different) *)

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.
(* Exercise: 2 stars, standard (fold_length) *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.

(* End Exercise: 2 stars, standard (fold_length) *)

(* Exercise: 3 stars, standard (fold_map) *)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
 fold (fun x lr => cons (f x) lr) l [].
Theorem fold_map_correct : forall X Y (l : list X) (f: X -> Y),
  fold_map f l = map f l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.
(* Do not modify the following line: *)
Definition manual_grade_for_fold_map : option (nat*string) := None.
(* End Exercise: 3 stars, standard (fold_map) *)

(* Exercise: 2 stars, advanced (currying) *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  reflexivity. Qed.
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p. reflexivity.
Qed.
(* End Exercise: 2 stars, advanced (currying) *)

(* Exercise: 2 stars, advanced (nth_error_informal) *)
Theorem nth_error_formal: forall X l n, length l = n -> @nth_error X l n = None.
Proof. Admitted.
(* 
1. n = 0 = length l 时，nth_error l 0 = None显然成立
2. 假设 n = k = length l 时，nth_error l k = None 成立
需证明 n = k + 1 = length l 时，nth_error l (k + 1) = None 成立:
只需证明 nth_error x::l' (k + 1) = nth_error l' k = None 成立，根据假设显然成立。
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(* End Exercise: 2 stars, advanced (nth_error_informal) *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Check cnat.
Check one.
Check option.

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.
Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Example zero_church_peano : zero nat S O = 0.
Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1.
Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2.
Proof. reflexivity. Qed.

(* Exercise: 2 stars, advanced (church_scc) *)
Definition scc (n : cnat) : cnat :=
  fun (X : Type) (succ : X -> X) (x : X) => n X succ (succ x).
Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.
Example scc_2 : scc one = two.
Proof. reflexivity. Qed.
Example scc_3 : scc two = three.
Proof. reflexivity. Qed.
(* End Exercise: 2 stars, advanced (church_scc) *)

(* Exercise: 3 stars, advanced (church_plus) *)
Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (succ : X -> X) (x : X) => n X succ (m X succ x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.
(* End Exercise: 3 stars, advanced (church_plus) *)

(* Exercise: 3 stars, advanced (church_mult) *)
Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (succ : X -> X) (x : X) => n X (m X succ) x.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.
(* End Exercise: 3 stars, advanced (church_mult) *)

(* Exercise: 3 stars, advanced (church_exp) *)
Definition exp (n m : cnat) : cnat :=
  fun (X : Type) => m (X -> X) (n X).
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.
(* End Exercise: 3 stars, advanced (church_exp) *)
End Church.
End Exercises.







