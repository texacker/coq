Require Import List.
Require Import ZArith.
Open Scope Z_scope.

(************************************** Implementation of the insertion insertion_sort algorithm **************************************)

Fixpoint insert (z:Z) (l : list Z) { struct l } : list Z :=
  match l with
    | nil        => z::nil
    | head::tail => if Z_le_gt_dec z head
                    then
                      z::head::tail
                    else
                      head::(insert z tail)
end.

Fixpoint insertion_sort (l : list Z) { struct l } : (list Z) :=
  match l with
    | nil        => nil
    | head::tail => insert head (insertion_sort tail)
end.

(*********************************************************** Helper methods ***********************************************************)

Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z::nil)
  | sorted2 : forall (z1 z2 : Z) (l : list Z), z1 <= z2 -> sorted (z2::l) -> sorted (z1::z2::l).

Hint Resolve sorted0 sorted1 sorted2 : insertion_sort.

Fixpoint count (z:Z) (l : list Z) {struct l} : nat :=
  match l with
  | nil        => O
  | head::tail => if Z.eq_dec z head
                  then
                    S (count z tail)
                  else
                    count z tail
end.

Definition is_equal (l l' : list Z) :=
  forall z : Z,
    count z l = count z l'.

Lemma is_equal_refl :
  forall l : list Z,
    is_equal l l.
Proof.
  unfold is_equal.
  trivial.
Qed.

Lemma is_equal_syme :
  forall l l' : list Z,
    is_equal l l' -> is_equal l' l.
Proof.
  unfold is_equal.
  auto.
Qed.

Lemma is_equal_trans :
  forall l l' l'' : list Z,
    is_equal l l' -> is_equal l' l'' -> is_equal l l''.
Proof.
  intros.
  unfold is_equal in *.
  intro; eapply trans_eq; eauto.
Qed.

Lemma is_equal_cons :
  forall (z : Z) (l l' : list Z),
    is_equal l l' -> is_equal (z::l) (z::l').
Proof.
  intros z l l' H z'.
  simpl.
  case (Z.eq_dec z' z).
  auto.
  auto.
Qed.

Lemma is_equal_perm :
  forall (x y : Z) (l l' : list Z),
    is_equal l l' -> is_equal (x::y::l) (y::x::l').
Proof.
  intros x y l l' H z; simpl.
  case (Z.eq_dec z x); case (Z.eq_dec z y); simpl; case (H z); auto.
Qed.

Hint Resolve is_equal_cons is_equal_refl is_equal_perm : insertion_sort.

(******************************************************** Proofs of correctness *******************************************************)

Lemma sorted_insert :
  forall (l : list Z) (x : Z),
    sorted l -> sorted (insert x l).
Proof.
  intros l x H; elim H.

  simpl; auto with insertion_sort.

  intro z; simpl.
  case (Z_le_gt_dec x z); simpl; auto with insertion_sort zarith.

  simpl.
  intros z1 z2; case (Z_le_gt_dec x z2); simpl; intros;
  case (Z_le_gt_dec x z1); simpl; auto with insertion_sort zarith.
Qed.

Lemma insert_preserves :
  forall (l : list Z) (x : Z),
    is_equal (x::l) (insert x l).
Proof.
  induction l as [ | a l0 H]; simpl.
  auto with insertion_sort.
  intros x; case (Z_le_gt_dec x a); simpl.
  auto with insertion_sort.
  intro; apply is_equal_trans with (a :: x :: l0); auto with insertion_sort.
Qed.

Lemma insertion_sort_sorted :
  forall (l : list Z),
    sorted (insertion_sort l).
Proof.
  induction l.
  auto with insertion_sort.
  simpl.
  apply sorted_insert.
  assumption.
Qed.

Lemma insertion_sort_preserves:
  forall (l : list Z),
    is_equal l (insertion_sort l).
Proof.
  induction l.
  auto with insertion_sort.
  simpl.
  eauto using is_equal_trans, insert_preserves with insertion_sort.
Qed.
