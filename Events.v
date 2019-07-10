From hahn Require Import Hahn.
From Coq Require Import Arith.
Require Import List.
Require Import Bool.

Section Events.

Notation "a ²" := (a × a) (at level 1, format "a ²").

Definition val_t := nat.
Definition loc_t := nat.

Record MixedEvent := {
  scevent : bool;
  index : nat;
  location : loc_t;
  rvals : list val_t;
  wvals : list val_t;
}.

Fixpoint natl_eqb l1 l2 :=
  match l1,l2 with
  | nil,nil => true
  | (h1::t1),(h2::t2) => Nat.eqb h1 h2 && natl_eqb t1 t2
  | _,_ => false
  end.

Fixpoint get_val start (list:list val_t) loc :=
  match list with
  | nil => None
  | h::t => if Nat.eqb start loc then Some h else get_val (S start) t loc
  end.

Lemma natl_eqb_eq l1 l2 :
  natl_eqb l1 l2 = true <-> l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; intro l2.
  - split; intro H.
    + destruct l2.
      * reflexivity.
      * inversion H.
    + subst. reflexivity.
  - split; intro H.
    + destruct l2.
      * inversion H.
      * inversion H.
        rewrite Bool.andb_true_iff in H1.
        destruct H1.
        rewrite Nat.eqb_eq in H0.
        rewrite IHl1 in H1.
        subst.
        reflexivity.
    + subst.
      simpl.
      rewrite Bool.andb_true_iff.
      split.
      * rewrite Nat.eqb_eq.
        reflexivity.
      * rewrite IHl1.
        reflexivity.
Qed.

Definition mev_eqb mev1 mev2 :=
  Bool.eqb (scevent mev1) (scevent mev2) &&
  Nat.eqb (index mev1) (index mev2) &&
  Nat.eqb (location mev1) (location mev2) &&
  natl_eqb (rvals mev1) (rvals mev2) &&
  natl_eqb (wvals mev1) (wvals mev2).

Lemma mev_eqb_eq mev1 mev2 :
  mev_eqb mev1 mev2 = true <-> mev1 = mev2.
Proof.
  split; intro H.
  - unfold mev_eqb in H.
    repeat rewrite Bool.andb_true_iff in H.
    destruct H as [[[[H1 H2] H3] H4] H5].
    destruct mev1.
    destruct mev2.
    simpl in *.
    f_equal;
    try rewrite <- eqb_true_iff;
    try rewrite <- Nat.eqb_eq;
    try rewrite <- natl_eqb_eq;
    assumption.
  - subst.
    unfold mev_eqb.
    repeat rewrite Bool.andb_true_iff.
    repeat split;
    try rewrite eqb_true_iff;
    try rewrite Nat.eqb_eq;
    try rewrite natl_eqb_eq;
    reflexivity.
Qed.

Lemma mev_eq_dec (x y : MixedEvent) : {x = y} + {x <> y}.
Proof.
  destruct (mev_eqb x y) eqn:eq.
  - rewrite mev_eqb_eq in eq.
    left.
    assumption.
  - right.
    intro.
    rewrite <- mev_eqb_eq in H.
    rewrite H in eq.
    inversion eq.
Qed.

Definition vals_dom loc (list:list val_t) n :=
  loc <= n /\ n < (loc + length list).

Definition rvals_dom e := vals_dom (location e) (rvals e).
Definition wvals_dom e := vals_dom (location e) (wvals e).

Definition ev_dom e :=
  rvals_dom e ∪₁ wvals_dom e.

Definition in_dom n e := ev_dom e n.

Definition range a b c :=
  a <= c /\ c < a + b.

Definition overlap e e' :=
  exists n, ev_dom e n /\ ev_dom e' n.

Definition nooverlap e e' :=
  ev_dom e ∩₁ ev_dom e' ⊆₁ ∅.

Definition size_n n e :=
  exists a, ev_dom e ≡₁ range a n.

Definition aligned_n n e :=
  exists a, ev_dom e ≡₁ range a n /\ a mod n = 0.

Definition aligned e :=
  aligned_n 1 e \/ aligned_n 2 e \/ aligned_n 4 e.

Definition starts_at n ev :=
  location ev = n.

Definition wf_event e :=
  (exists n, ev_dom e n) /\
  forall n n',
  rvals_dom e n ->
  wvals_dom e n' ->
  rvals_dom e ≡₁ wvals_dom e.

End Events.