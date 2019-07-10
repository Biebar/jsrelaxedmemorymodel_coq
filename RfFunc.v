From hahn Require Import Hahn.
Require Import Exec.
Require Import Events.

Section RfFunc.

Lemma init_dec exec E : {init exec E} + {~(init exec E)}.
Proof.
  destruct (IW exec) as [iw|] eqn:eqinit.
  - destruct (mev_eq_dec iw E).
    + subst. left. unfold init. rewrite eqinit. reflexivity.
    + right. intro. apply n. unfold init in H.
      rewrite eqinit in H. auto.
  - right. intro H. unfold init in H. rewrite eqinit in H.
    contradiction.
Qed.

Definition rf_func exec :=
  functional (rf exec)⁻¹.

Notation "a ²" := (a × a) (at level 1, format "a ²").

Definition aligned_and_no_overlap exec :=
  (EV exec)\₁(init exec) ⊆₁ aligned /\ overlap ∩ (EV exec \₁ init exec)² ⊆ same_loc.

Definition strong_tearfree e :=
  functional ((rf e) ∩ (((tearfree e)² ∩ same_loc) ∪ (init e × tearfree e)))⁻¹.

Definition unisized exec := aligned_and_no_overlap exec /\ strong_tearfree exec.

Lemma uni__tf exec :
  consistent exec ->
  unisized exec ->
  forall E, EV exec E -> tearfree exec E.
Proof.
  intros cst [[aligned nover] _] E EVE.
  destruct (init_dec exec E).
  - right. assumption.
  - left. split.
    + apply aligned.
      split; assumption.
    + assumption.
Qed.

Lemma uni__sameloc exec :
  well_formed exec ->
  unisized exec ->
  ⦗EV exec \₁ init exec⦘ ⨾ rf exec ⊆ same_loc.
Proof.
  intros wf alnoov X Y H.
  destruct (alnoov) as [[_ noov] _].
  unfolder in H.
  destruct H as [[EVX ninitX] rfXY].
  apply noov.
  split.
  - apply rf__overlap with exec; assumption.
  - destruct rfXY as [b [_ rfbXY]].
    destruct (wf_rfb_wr exec wf b) as [H _].
    apply H in rfbXY.
    unfolder in rfbXY.
    destruct rfbXY as [_ [_ WY]].
    destruct (WY).
    split; split; try assumption.
    intro initY.
    apply wf_iww in initY; try assumption.
    destruct initY.
    contradiction.
Qed.

Theorem rf_is_func exec :
  well_formed exec -> consistent exec ->
  unisized exec -> rf_func exec.
Proof.
  intros wf cst uni R.
  assert (forall W, rf exec W R ->
      ((tearfree exec)² ∩ same_loc ∪ init exec × tearfree exec) W R)
    as lemma.
  {
    intros W rfWR.
    assert (tearfree exec R). {
      apply uni__tf; try assumption.
      apply rf__ev in rfWR; try assumption.
      destruct rfWR.
      assumption.
    }
    assert (EV exec W). {
      apply rf__ev in rfWR; try assumption.
      destruct rfWR.
      assumption.
    }
    destruct (init_dec exec W) as [IW | nIW].
    + right. split; assumption.
    + left. split.
      * split; try assumption.
        apply uni__tf; assumption.
      * apply uni__sameloc with exec; try assumption.
        exists W.
        repeat (split; auto).
  }
  intros W1 W2.
  unfold transp.
  intros rf1 rf2.
  destruct (uni) as [[align noov] tf].
  apply tf with R;
  split;
  try assumption;
  apply lemma;
  assumption.
Qed.

End RfFunc.