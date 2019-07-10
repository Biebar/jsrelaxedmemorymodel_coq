From hahn Require Import Hahn.
Require Import Exec.
Require Import Events.

Section Scdrf.

Lemma drf_tot__hb_sc e X Y :
  well_formed e ->
  consistent e ->
  data_race_free e ->
  tot e X Y ->
  overlap X Y ->
  writes e X \/ writes e Y ->
  hb e X Y \/ (same_loc X Y /\ sc e X /\ sc e Y).
Proof.
  intros wf cst drf totXY overlapXY wXY.
  unfold data_race_free in drf.
  destruct drf with X Y as [hbXY | [hbYX | [[nWX nWY] | [novrlpXY | [slXY [scX scY]]]]]];
  auto.
  - exfalso.
    destruct wf_tot with e as [[irrefl trans] tot]; try assumption.
    apply irrefl with X.
    apply trans with Y; try assumption.
    apply cst_hb_tot; try assumption.
    apply cst_ufxd.
    assumption.
  - exfalso.
    destruct wXY; contradiction.
  - exfalso.
    destruct overlapXY.
      apply novrlpXY with x.
      destruct H.
      split; assumption.
Qed.

Theorem sc_drf e :
  well_formed e ->
  consistent e ->
  data_race_free e ->
  seqcst e.
Proof.

  intros wf cst drf.
  unfold seqcst.
  unfolder.
  intros n.
  split.
  { intros Y [X [rfbYX totXY]].
    assert (hb e X Y \/ (same_loc X Y /\ sc e X /\ sc e Y)) as [hbXY | [slXY [scX scY]]]. {
      apply drf_tot__hb_sc; auto.
      exists n. split; destruct (rfb__dom e X Y n wf rfbYX); try assumption.
      right. eapply rfb__w; eassumption.
    }
    - apply (cst_rf_hb e (cst_ufxd e cst) X).
      exists Y.
      split; try assumption.
      econstructor. eauto.
    - destruct (wf_tot e wf) as [[irrefl trans] _].
      apply irrefl with X.
      apply trans with Y; try assumption. 
      apply cst_hb_tot; try apply cst_ufxd; try assumption.
      constructor. left. right.
      apply sw_intro; auto.
      eexists; eauto.
      apply same_loc_sym. auto.
  }
  intros Z' [Z [[eqZZ' [wZ domZn]] [X [totZX [Y [rfbYX totYZ]]]]]].
  subst.
  assert (in_dom n Y /\ in_dom n X) as [domYn domXn]. {
    apply rfb__dom with e; assumption.
  }
  assert (hb e Y Z \/ (same_loc Y Z /\ sc e Y /\ sc e Z)) as drfYZ. {
    apply drf_tot__hb_sc; auto.
    exists n; auto.
  }
  assert (hb e Z X \/ (same_loc Z X /\ sc e Z /\ sc e X)) as drfZX. {
    apply drf_tot__hb_sc; auto.
    exists n; auto.
  }
  assert (hb e Y X \/ (same_loc Y X /\ sc e Y /\ sc e X)) as drfYX. {
    apply drf_tot__hb_sc; auto.
    - destruct (wf_tot e wf) as [[_ trans] _].
      apply trans with Z; assumption.
    - exists n; auto.
    - left.
      apply rfb__w with X n; assumption.
  }
  destruct drfYZ as [hbYZ | [slYZ [ScY scZ]]];
  destruct drfZX as [hbZX | [slZX [ScZ' ScX]]];
  [ apply (cst_rf_hb_hb e (cst_ufxd e cst) n Z) |
    destruct drfYX as [hbYX | [slYX [ScY _]]];
      [apply (cst_ddagger e cst Z) | apply (cst_sw_tot e (cst_ufxd e cst) Z)] |
    destruct drfYX as [hbYX | [slYX [_ ScX]]];
      [apply (cst_dagger e cst Z) | apply (cst_sw_tot e (cst_ufxd e cst) Z)] |
    apply (cst_sw_tot e (cst_ufxd e cst) Z)
  ];
  unfolder;
  split; auto;
  repeat (eexists; split; eauto).
  - split; try assumption.
    apply rfb__rf with n.
    assumption.
  - apply sw_intro; auto.
    apply rfb__rf with n.
    assumption.
  - split; try assumption.
    apply rfb__rf with n.
    assumption.
  - split.
    + apply (cst_hb_tot e (cst_ufxd e cst)).
      eassumption.
    + eapply same_loc_trans;
      try eassumption.
      apply same_loc_sym.
      assumption.
  - apply sw_intro; auto.
    apply rfb__rf with n.
    assumption.
  - apply sw_intro; auto.
    apply rfb__rf with n.
    assumption.
    eapply same_loc_trans;
    eassumption.
Qed.


End Scdrf.