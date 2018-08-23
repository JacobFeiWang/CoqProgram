Module NatNameSpace.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatNameSpace.

Check (S (S (S O))).
(* ===> 3 : nat *)