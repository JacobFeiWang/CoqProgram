Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o ->
    n + m = m + o.
Proof. intros n m o. intros H1 H2. rewrite -> H1. rewrite -> H2. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof. intros n m. rewrite -> plus_0_n. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) =  m * m.
Proof. intros n m. intros H. rewrite -> H. rewrite <- plus_1_l. reflexivity. Qed.

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

Theorem plus_1_neq_0_firstry: forall n : nat,
    nat_iseq (n + 1) 0 = false.
Proof. intros n. simpl. Abort.

Theorem plus_1_neq_0_secondtry: forall n : nat,
    nat_iseq (n + 1) 0 = false.
Proof.
    intros n. destruct n as [| n'].
    - reflexivity.
    - reflexivity. Qed.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Theorem negb_involutive: forall b : bool,
    negb (negb b) = b.
Proof.
    intros b. destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Definition andb (a b: bool) : bool :=
    match a with
    | true => b
    | false => false
    end.

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
    intros b c. destruct b.
    - destruct c.
        + reflexivity.
        + reflexivity.
    - destruct c.
        + reflexivity.
        + reflexivity.
Qed.

Theorem andb3_commutative:
    forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
    intros b c d. destruct b.
    { destruct c.
        { destruct d.
            { reflexivity. }
            { reflexivity. } }
        { destruct d.
            { reflexivity. }
            { reflexivity. } }
    }
    { destruct c.
        { destruct d.
            { reflexivity. }
            { reflexivity. } }
        { destruct d.
            { reflexivity. }
            { reflexivity. } }
    }
Qed.

Theorem andb_commutative2:
    forall b c, andb b c = andb c b.
Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_true_elim2: forall b c: bool,
    andb b c = true -> c = true.
Proof.
    intros b c H.
    destruct c.
        - reflexivity.
        - rewrite <- H.
          destruct b.
          * reflexivity.
          * reflexivity.
Qed.

Theorem zero_nbeq_plus_1: forall n : nat,
    nat_iseq 0 (n + 1) = false.
Proof.
    intros [].
    - reflexivity.
    - reflexivity.
Qed.

(* Rejected but correct recursive function because of
 * Coq's imperfect decreasing judgement *)
(* Fixpoint my_recursive (n m: nat) : nat :=
    match n with
    | O => match m with
           | O => O
           | S m' => 1 + (my_recursive n m')
           end
    | S n' => match m with
              | O => 1 + (my_recursive n' m)
              | S m' => 1 + (my_recursive n m')
              end
    end.
*)

Theorem identity_fn_applied_twice:
    forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
    intros.
    rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem negation_fn_applied_twice:
    forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
    intros.
    rewrite -> H.
    rewrite -> H.
    destruct b.
        - reflexivity.
        - reflexivity.
Qed.

Definition orb (a b : bool) : bool :=
    match a with
    | true => true
    | false => b
    end.

Lemma andb_true_x:
    forall x : bool, andb true x = x.
Proof. reflexivity. Qed.

Lemma andb_false_x:
    forall x : bool, andb false x = false.
Proof. reflexivity. Qed.

Lemma orb_true_x:
    forall x : bool, orb true x = true.
Proof. reflexivity. Qed.

Lemma orb_false_x:
    forall x : bool, orb false x = x.
Proof. reflexivity. Qed.

Theorem andb_eq_orb:
    forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
    intros.
    destruct b.
        rewrite -> andb_true_x in H.
        rewrite -> orb_true_x in H.
        symmetry.
        apply H.
        rewrite -> andb_false_x in H.
        rewrite -> orb_false_x in H.
        apply H.
Qed.

Theorem andb_eq_orb2:
    forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
    destruct b,c;
    intros H;
    inversion H;
    reflexivity.
Qed.
