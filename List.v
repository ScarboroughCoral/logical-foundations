From LF Require Export Induction.

Module NatList.

Inductive natprod: Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(* 
Instead, we need to expose the structure of p so that simpl can perform the pattern match in fst and snd. We can do this with destruct.
Notice that, unlike its behavior with nats, where it generates two subgoals, destruct generates just one subgoal here. That's because natprods can only be constructed in one way.
 *)
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.


(* Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p. simpl. reflexivity.
Qed.
(* End Exercise: 1 star, standard (snd_fst_is_swap) *)

(* Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p. simpl. reflexivity.
Qed.
(* End Exercise: 1 star, standard, optional (fst_swap_is_snd) *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Check mylist.

Compute mylist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Compute mylist1.
Compute mylist2.
Compute mylist3.

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* Exercise: 2 stars, standard, especially useful (list_funs) *)
Fixpoint nonzeros (l:natlist) : natlist :=
match l with
  | nil => nil
  | 0::t => nonzeros t
  | x::l' => x :: nonzeros l'
end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.
Fixpoint oddmembers (l:natlist) : natlist :=
match l with
  | nil => nil
  | x::l' => match odd x with
              | true => x::oddmembers l'
              | false => oddmembers l'
             end
end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat := length (oddmembers l).
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. 
  reflexivity.
Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
  reflexivity.
Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. 
  reflexivity.
Qed.
(* End Exercise: 2 stars, standard, especially useful (list_funs) *)

(* Exercise: 3 stars, advanced (alternate) *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1,l2 with
  | nil,l2 => l2
  | l1, nil => l1
  | x::l1',y::l2' => x::y::(alternate l1' l2')
end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
(* End Exercise: 3 stars, advanced (alternate) *)

Definition bag := natlist.

Check natlist.

(* Exercise: 3 stars, standard, especially useful (bag_functions) *)
Fixpoint count (v : nat) (s : bag) : nat :=
match s with
  | nil => 0
  | x::s' => if x =? v then (1 + (count v s')) else (count v s')
end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.
Definition add (v : nat) (s : bag) : bag := v::s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.
Fixpoint member (v : nat) (s : bag) : bool :=
match s with
  | nil => false
  | x::s' => if x =? v then true else member v s'
end.
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.
(* End Exercise: 3 stars, standard, especially useful (bag_functions) *)




















