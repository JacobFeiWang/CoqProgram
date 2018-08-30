Module NatNameSpace.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Inductive bin_nat : Type :=
  | b : bin_nat
  | b0 : bin_nat -> bin_nat
  | b1 : bin_nat -> bin_nat.

End NatNameSpace.

Check (S (S (S O))).
(* ===> 3 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
Check S.
Check pred.
Check minustwo.

Inductive bool : Type :=
| true : bool
| false : bool.

Fixpoint evenb (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2 : oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatNameSpace2.

Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
Compute (plus 3 2).
    
Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
Example test_mult1 : (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n' , S m' => minus n' m'
    end.
Example test_minus1: (minus 2 1) = 1.
Proof. simpl. reflexivity. Qed.
End NatNameSpace2.

Fixpoint exp (base power: nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.
Example test_exp1: (exp 9 0) = 1.
Proof. simpl. reflexivity. Qed.
Example test_exp2: (exp 9 3) = 729.
Proof. simpl. reflexivity. Qed.

Fixpoint fibo (n: nat) : nat :=
    match n with
    | O => 1
    | S O => 1
    | S n' => (fibo (minus n' 1)) + (fibo n')
    end.
Example test_fibo1: (fibo 0) = 1.
Proof. simpl. reflexivity. Qed.
Example test_fibo2: (fibo 1) = 1.
Proof. simpl. reflexivity. Qed.
Example test_fibo3: (fibo 2) = 2.
Proof. simpl. reflexivity. Qed.

Fixpoint fact (n: nat) : nat :=
    match n with
    | O => 1
    | S n' => mult (S n') (fact n')
    end.
Example test_fact1: (fact 0) = 1.
Proof. simpl. reflexivity. Qed.
Example test_fact2: (fact 1) = 1.
Proof. simpl. reflexivity. Qed.
Example test_fact3: (fact 5) = 120.
Proof. simpl. reflexivity. Qed.

Fixpoint nat_iseq (n m: nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
              | O => false
              | S m' => nat_iseq n' m'
              end
    end.
Example test_nat_iseq1: (nat_iseq 1 1) = true.
Proof. simpl. reflexivity. Qed.
Example test_nat_iseq2: (nat_iseq 4 0) = false.
Proof. simpl. reflexivity. Qed.
Example test_nat_iseq3: (nat_iseq 4 5) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint nat_leq (n m: nat) : bool :=
    match n with
    | O => true
    | S n' => match m with
              | O => false
              | S m' => nat_leq n' m'
              end
    end.

Fixpoint nat_lt (n m: nat) : bool :=
    match n with
    | O => match m with
           | O => false
           | S m' => true
           end
    | S n' => match m with
              | O => false
              | S m' => nat_lt n' m'
              end
    end.
Example test_nat_lt1: (nat_lt 0 1) = true.
Proof. simpl. reflexivity. Qed.
Example test_nat_lt2: (nat_lt 2 3) = true.
Proof. simpl. reflexivity. Qed.
Example test_nat_lt3: (nat_lt 1 1) = false.
Proof. simpl. reflexivity. Qed.
Example test_nat_lt4: (nat_lt 1 0) = false.
Proof. simpl. reflexivity. Qed.

Definition nat_lt2 (n m: nat) : bool := negb (nat_leq m n).
Example test_nat_lt21: (nat_lt 0 1) = true.
Proof. simpl. reflexivity. Qed.
Example test_nat_lt22: (nat_lt 2 3) = true.
Proof. simpl. reflexivity. Qed.
Example test_nat_lt23: (nat_lt 1 1) = false.
Proof. simpl. reflexivity. Qed.
Example test_nat_lt24: (nat_lt 1 0) = false.
Proof. simpl. reflexivity. Qed.