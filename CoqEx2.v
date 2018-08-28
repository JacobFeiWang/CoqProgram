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