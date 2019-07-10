From hahn Require Import Hahn.
Require Import Exec.
Require Import Events.

Section Deadness.

Record dead e := {
  dead_hb_tot : (hb e) ⊆ (tot e);
  dead_WRsc : ⦗writes e⦘ ⨾ (tot e) ⨾ ⦗reads e ∩₁ (sc e)⦘ ⊆ (hb e);
  dead_WscW : ⦗writes e ∩₁ (sc e)⦘ ⨾ (tot e) ⨾ ⦗writes e⦘ ⊆ (hb e);
}.

Definition tot_permutation e e' :=
  EV e = EV e' /\
  IW e = IW e' /\
  sb e = sb e' /\
  rfb e = rfb e'.

Record dead_wrt e e' := {
  deadwrt_WRsc :
    forall X Y, writes e X -> reads e Y -> sc e Y -> tot e X Y ->
      tot e' X Y;
  deadwrt_WscW :
    forall X Y, writes e X -> writes e Y -> sc e X -> tot e X Y ->
      tot e' X Y;
}.

Record dead_general exec := {
  deadg_hb_tot : (hb exec) ⊆ (tot exec);
  deadg_WRsc :
    forall X Y, writes exec X -> reads exec Y -> sc exec Y -> tot exec X Y ->
    forall exec', well_formed exec' -> consistent_sc_unfixed exec' -> tot_permutation exec exec' -> tot exec' X Y;
  deadg_WscW :
    forall X Y, writes exec X -> writes exec Y -> sc exec X -> tot exec X Y ->
    forall exec', well_formed exec' -> consistent_sc_unfixed exec' -> tot_permutation exec exec' -> tot exec' X Y;
}.

Lemma dead_wrt_general :
  forall e, dead_general e <-> (hb e ⊆ tot e) /\
  forall e', well_formed e' -> consistent_sc_unfixed e' -> tot_permutation e e' ->
             dead_wrt e e'.
Proof.
  intro e.
  split.
  - intros [hbtot WRsc WscW].
    split. assumption.
    intros e' wf' cst' totperm.
    constructor; auto.
  - intros [hbtot H].
    constructor.
    + assumption.
    + intros.
      apply deadwrt_WRsc with e; auto.
    + intros.
      apply deadwrt_WscW with e; auto.
Qed.

Record dead_fixed e := {
  deadf_hb_tot : (hb e) ⊆ (tot e);
  deadf_WscRsc :
    forall X Y, writes e X -> reads e Y -> sc e X -> sc e Y -> tot e X Y ->
    forall e', well_formed e' -> consistent e' -> tot_permutation e e' -> tot e' X Y;
  deadf_WscWsc :
    forall X Y, writes e X -> writes e Y -> sc e X -> sc e Y -> tot e X Y ->
    forall e', well_formed e' -> consistent e' -> tot_permutation e e' -> tot e' X Y;
}.

Lemma dead_general__fixed e :
  dead_general e -> dead_fixed e.
Proof.
  intros [H1 H2 H3].
  constructor;
  intros;
  [apply H1 | apply H2 | apply H3];
  auto;
  apply cst_ufxd;
  assumption.
Qed.

Lemma totperm_sym e e' : tot_permutation e e' -> tot_permutation e' e.
Proof.
  intros [H1 [H2 [H3 H4]]].
  repeat (split; auto).
Qed.

Lemma totperm_rfb e e' : tot_permutation e e' -> rfb e = rfb e'.
Proof.
  intros [_[_[_ H]]].
  assumption.
Qed.

Lemma totperm_w :
  forall e e', tot_permutation e e' -> writes e = writes e'.
Proof.
  intros e e'[eqE _].
  unfold writes.
  rewrite eqE.
  reflexivity.
Qed.

Lemma totperm_rf :
  forall e e', tot_permutation e e' -> rf e = rf e'.
Proof.
  intros e e' dead.
  unfold rf.
  rewrite totperm_rfb with _ e';
  auto.
Qed.

Lemma totperm_init :
  forall e e', tot_permutation e e' -> init e = init e'.
Proof.
  intros e e' [eqE [eqIW [eqsb eqrfb]]].
  unfold init.
  rewrite eqIW.
  reflexivity.
Qed.

Lemma totperm_sw :
  forall e e', tot_permutation e e' -> sw e = sw e'.
Proof.
  intros e e' totperm.
  unfold sw.
  rewrite (totperm_rf e e' totperm).
  rewrite totperm_init with e e'; try assumption.
  destruct totperm as [eqE [eqIW [eqsb eqrfb]]].
  replace (sc e) with (sc e').
  reflexivity.
  unfold sc.
  rewrite eqE.
  reflexivity.
Qed.


Lemma totperm_hb :
  forall e e', tot_permutation e e' -> hb e = hb e'.
Proof.
  intros e e' totperm.
  unfold hb.
  rewrite totperm_init with e e'; auto.
  rewrite totperm_sw with e e'; auto.
  destruct totperm as [eqE [eqIW [eqsb eqrfb]]].
  rewrite eqE.
  rewrite eqsb.
  reflexivity.
Qed.

Lemma totperm_tearfree :
  forall e e', tot_permutation e e' -> tearfree e = tearfree e'.
Proof.
  intros e e' totperm.
  unfold tearfree.
  rewrite totperm_init with e e'; try assumption.
  destruct totperm as [eqev _].
  rewrite eqev.
  reflexivity.
Qed.

Lemma totperm_sc e e' :
  tot_permutation e e' -> sc e = sc e'.
Proof.
  intros [eqev _].
  unfold sc.
  rewrite eqev.
  reflexivity.
Qed.


Lemma dead__deadg e :
  dead e -> dead_general e.
Proof.
  intros [hbtot WRsc WscW].
  constructor; try assumption;
  intros;
  apply cst_hb_tot; try assumption;
  erewrite <- totperm_hb; try eassumption;
  [ apply WRsc | apply WscW ];
  unfolder;
  repeat (split; try assumption).
Qed.

Lemma rfb_w_dom :
  forall e X Y n, well_formed e -> rfb e n Y X -> ev_dom Y n.
Proof.
  intros e X Y n H rfbnYX.
  apply wf_rfb_dom in rfbnYX; try assumption.
  destruct rfbnYX.
  assumption.
Qed.

Lemma drf_totWovrlp e e' X Y n :
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  data_race_free e -> (hb e) ⊆ (tot e) ->
  in_dom n X -> in_dom n Y ->
  writes e X \/ writes e Y ->
  tot e X Y ->
  hb e' X Y \/ (same_loc X Y /\ sc e X /\ sc e Y).
Proof.
  intros wfe wfe' totperm drfe hbtot domnX domnY WXoY totXY.
  destruct (drfe X Y) as [hbXY|[hbZY|[[nWX nWZ]|[novrlpXY|[slXY[scX scY]]]]]].
  - left. rewrite <- totperm_hb with e e'; assumption.
  - exfalso.
    destruct (wf_tot e wfe) as [[irrefl trans] _].
    apply irrefl with Y.
    apply trans with X; try assumption.
    apply hbtot. assumption.
  - exfalso. destruct WXoY; auto.
  - exfalso.
    apply novrlpXY with n.
    split; assumption.
  - right.
    split; auto.
Qed.

Theorem deadness_seqcst_fixed e e' :
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  data_race_free e ->
  dead_fixed e ->
  hb e ⊆ tot e ->
  hb e' ⊆ tot e' ->
  seqcst e' -> seqcst e.
Proof.
  intros wf wf' totperm drf dead hbtot hbtot' sce' n.
  split.
  {
    intros X [Y [rfbXY totYX]].
    apply (proj1 (sce' n) X).
    exists Y.
    split. { erewrite <- totperm_rfb; eassumption. }
    destruct drf_totWovrlp with e e' Y X n as [hbYX | [slYX [scY scX]]];
    auto.
    - apply rfb_r_dom with e X; assumption.
    - apply rfb_w_dom with e Y; assumption.
    - right. eapply rfb__w; eassumption.
    - exfalso.
      destruct (wf_tot e wf) as [[irrefl trans] _].
      apply (irrefl X).
      apply trans with Y; try assumption.
      apply hbtot.
      constructor. left. right.
      apply sw_intro; auto.
      + eapply rfb__rf. eassumption.
      + apply same_loc_sym. assumption.
  }
  intros Z H.
  unfolder in H.
  destruct H as [[WZ Zwn] [X [totZX [Y [rfbnYX totYZ]]]]].
  assert (tot e' Y Z). {
    destruct drf_totWovrlp with e e' Y Z n as [hbYZ | [slYZ [scY scZ]]];
    auto.
    - apply wf_rfb_dom in rfbnYX; try assumption.
      destruct rfbnYX.
      assumption.
    - apply deadf_WscWsc with e; auto.
      apply wf_rfb_wr in rfbnYX; try assumption.
      unfolder in rfbnYX.
      destruct rfbnYX.
      assumption.
      apply seqcst__cst; auto.
  }
  assert(tot e' Z X). {
    destruct drf_totWovrlp with e e' Z X n as [hbZX | [slZX [scZ scX]]];
    auto.
    - apply wf_rfb_dom in rfbnYX; try assumption.
      destruct rfbnYX.
      assumption.
    - apply deadf_WscRsc with e; auto.
      apply wf_rfb_wr in rfbnYX; try assumption.
      unfolder in rfbnYX.
      destruct rfbnYX as [_[_ RX]].
      assumption.
      apply seqcst__cst; auto.
  }
  unfold seqcst, irreflexive in sce'.
  apply sce' with n Z.
  unfolder.
  split.
  - split; try assumption.
    rewrite <- totperm_w with e e';
    assumption.
  - repeat (eexists; split; eauto).
    destruct totperm as [eqE [eqIW [eqsb eqrfb]]].
    rewrite <- eqrfb.
    assumption.
Qed.


Theorem deadness_seqcst e e' :
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  data_race_free e ->
  dead_wrt e e' ->
  hb e ⊆ tot e ->
  hb e' ⊆ tot e' ->
  seqcst e' -> seqcst e.
Proof.
  intros wf wf' totperm drf dead hbtot hbtot' sce' n.
  split.
  {
    intros X [Y [rfbXY totYX]].
    apply (proj1 (sce' n) X).
    exists Y.
    split. { erewrite <- totperm_rfb; eassumption. }
    destruct drf_totWovrlp with e e' Y X n as [hbYX | [slYX [scY scX]]];
    auto.
    - apply rfb_r_dom with e X; assumption.
    - apply rfb_w_dom with e Y; assumption.
    - right. eapply rfb__w; eassumption.
    - exfalso.
      destruct (wf_tot e wf) as [[irrefl trans] _].
      apply (irrefl X).
      apply trans with Y; try assumption.
      apply hbtot.
      constructor. left. right.
      apply sw_intro; auto.
      + eapply rfb__rf. eassumption.
      + apply same_loc_sym. assumption.
  }
  intros Z H.
  unfolder in H.
  destruct H as [[WZ Zwn] [X [totZX [Y [rfbnYX totYZ]]]]].
  assert (tot e' Y Z). {
    destruct drf_totWovrlp with e e' Y Z n as [hbYZ | [slYZ [scY scZ]]];
    auto.
    - apply wf_rfb_dom in rfbnYX; try assumption.
      destruct rfbnYX.
      assumption.
    - apply deadwrt_WscW with e; auto.
      apply wf_rfb_wr in rfbnYX; try assumption.
      unfolder in rfbnYX.
      destruct rfbnYX.
      assumption.
  }
  assert(tot e' Z X). {
    destruct drf_totWovrlp with e e' Z X n as [hbZX | [slZX [scZ scX]]];
    auto.
    - apply wf_rfb_dom in rfbnYX; try assumption.
      destruct rfbnYX.
      assumption.
    - apply deadwrt_WRsc with e; auto.
      apply wf_rfb_wr in rfbnYX; try assumption.
      unfolder in rfbnYX.
      destruct rfbnYX as [_[_ RX]].
      assumption.
  }
  unfold seqcst, irreflexive in sce'.
  apply sce' with n Z.
  unfolder.
  split.
  - split; try assumption.
    rewrite <- totperm_w with e e';
    assumption.
  - repeat (eexists; split; eauto).
    destruct totperm as [eqE [eqIW [eqsb eqrfb]]].
    rewrite <- eqrfb.
    assumption.
Qed.

Theorem deadness_cst e e' :
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  dead_wrt e e' ->
  (hb e) ⊆ (tot e) ->
  consistent_sc_unfixed e' ->
  consistent_sc_unfixed e.
Proof.
  intros wf wf' totperm dead hbtot cst'.
  constructor.
  - assumption.
  - rewrite totperm_rf with _ e', totperm_tearfree with _ e';
    try apply cst_rf_tf;
    assumption.
  - rewrite totperm_hb with _ e', totperm_rf with _ e';
    try apply cst_rf_hb;
    assumption.
  - rewrite totperm_w with _ e',
            totperm_hb with _ e',
            totperm_rfb with _ e';
    try apply cst_rf_hb_hb;
    assumption.
  - intros Z H.
    apply (cst_sw_tot e' cst' Z).
    rewrite <- totperm_w with e _,
            <- totperm_sc with e _,
            <- totperm_sw with e _;
    try assumption.
    unfolder in H.
    destruct H as [[wZ scZ] [X [[totZX slZX] [Y [swYX totYZ]]]]].
    repeat (eexists; split; eauto).
    + split; try assumption.
      apply deadwrt_WRsc with e;
      apply sw_r_sc in swYX;
      destruct swYX;
      auto.
    + apply sw_init_sc in swYX; try assumption.
      destruct swYX as [wY [iwY | scY]].
      * apply cst_hb_tot; try assumption.
        constructor.
        right. split.
        -- rewrite <- totperm_init with e _; assumption.
        -- destruct totperm. rewrite <- H. destruct wZ. assumption.
      * apply deadwrt_WscW with e;
        auto.
Qed.

Theorem deadness_cst_fixed e e' :
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  dead_fixed e ->
  consistent e' ->
  consistent e.
Proof.
  intros wf wf' totperm dead cst'.
  constructor.
  constructor.
  - apply deadf_hb_tot.
    assumption.
  - rewrite totperm_rf with _ e', totperm_tearfree with _ e';
    try apply cst_rf_tf;
    try apply cst_ufxd;
    assumption.
  - rewrite totperm_hb with _ e', totperm_rf with _ e';
    try apply cst_rf_hb;
    try apply cst_ufxd;
    assumption.
  - rewrite totperm_w with _ e',
            totperm_hb with _ e',
            totperm_rfb with _ e';
    try apply cst_rf_hb_hb;
    try apply cst_ufxd;
    assumption.
  - intros Z H.
    apply (cst_sw_tot e' (cst_ufxd e' cst') Z).
    rewrite <- totperm_w with e _,
            <- totperm_sc with e _,
            <- totperm_sw with e _;
    try assumption.
    unfolder in H.
    destruct H as [[wZ scZ] [X [[totZX slZX] [Y [swYX totYZ]]]]].
    repeat (eexists; split; eauto).
    + split; try assumption.
      apply deadf_WscRsc with e;
      apply sw_r_sc in swYX;
      destruct swYX;
      auto.
    + apply sw_init_sc in swYX; try assumption.
      destruct swYX as [wY [iwY | scY]].
      * apply cst_hb_tot; try apply cst_ufxd; try assumption.
        constructor.
        right. split.
        -- rewrite <- totperm_init with e _; assumption.
        -- destruct totperm. rewrite <- H. destruct wZ. assumption.
      * apply deadf_WscWsc with e;
        auto.
  - intros Z H.
    apply (cst_dagger e' cst' Z).
    rewrite <- totperm_w with e _,
            <- totperm_sc with e _,
            <- totperm_hb with e _,
            <- totperm_rf with e _;
    try assumption.
    unfolder in H.
    destruct H as [[wZ scZ] [X [hbZX [Y' [[rfYX hbYX] [Y [[eqYY' scY] [totYZ slYZ]]]]]]]].
    subst.
    exists Z.
    repeat (eexists; repeat (split; eauto)).
    apply deadf_WscWsc with e; auto.
    destruct rfYX as [n [_ rfbYX]].
    eapply rfb__w; eassumption.
  - intros Z H.
    apply (cst_ddagger e' cst' Z).
    rewrite <- totperm_w with e _,
            <- totperm_sc with e _,
            <- totperm_hb with e _,
            <- totperm_rf with e _;
    try assumption.
    unfolder in H.
    destruct H as [[wZ scZ] [X' [[totZX slZX] [X [[eqXX' scX] [Y [[rfYX hbYX] hbYZ]]]]]]].
    subst.
    repeat (eexists; repeat (split; eauto)).
    apply deadf_WscRsc with e; auto.
    destruct rfYX as [n [_rfbYX]].
    eapply rfb__r; eassumption.
Qed.

Theorem deadness_valid :
  forall e e',
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  dead_wrt e e' ->
  (hb e) ⊆ (tot e) ->
  ~(consistent_sc_unfixed e) ->
  ~(consistent_sc_unfixed e').
Proof.
  intros e e' wf wf' totperm dead hbtot ncst cst'.
  apply deadness_cst with e e' in cst'; auto.
Qed.

Theorem deadness_sc :
  forall e e',
  well_formed e -> well_formed e' ->
  tot_permutation e e' ->
  dead_wrt e e' ->
  data_race_free e ->
  hb e ⊆ tot e ->
  hb e' ⊆ tot e' ->
  ~(seqcst e) -> ~(seqcst e').
Proof.
  intros. intro cst'.
  apply deadness_seqcst with e e' in cst';
  auto.
Qed.

End Deadness.
