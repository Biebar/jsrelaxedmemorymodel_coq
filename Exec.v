From hahn Require Import Hahn.

Require Import Events.

Section Exec.

Notation "a ²" := (a × a) (at level 1, format "a ²").

Record MExec := {
  EV : MixedEvent -> Prop;
  IW : option MixedEvent;
  sb : MixedEvent -> MixedEvent -> Prop;
  rfb : nat -> MixedEvent -> MixedEvent -> Prop;
  tot : MixedEvent -> MixedEvent -> Prop;
}.

Definition is_rmw e := rvals_dom e ≡₁ wvals_dom e.
Definition is_read e := wvals_dom e ⊆₁ ∅ \/ is_rmw e.
Definition is_write e := rvals_dom e ⊆₁ ∅ \/ is_rmw e.
Definition is_sc e := scevent e = true.

Definition writes exec :=
  EV exec ∩₁ is_write.

Definition reads exec :=
  EV exec ∩₁ is_read.

Definition sc exec :=
  EV exec ∩₁ is_sc.

Definition same_loc e e' :=
  ev_dom e ≡₁ ev_dom e'.

Definition same_val_wr n e e' :=
  get_val (location e) (wvals e) n = get_val (location e') (rvals e') n.

Definition init exec e := match IW exec with
  | None => False
  | Some e' => e = e'
end.

Definition sthd exec :=
  (sb exec)＊ ∪ (sb exec)＊⁻¹.

Definition rf exec :=
  ⋃ n , rfb exec n.

Definition sw e := 
  rf e ∩ ( ((sc e)² ∩ same_loc) ∪ ((init e × sc e)∩(fun y x => forall z, rf e z y -> x = z))).

Definition hb e :=
  (sb e ∪ sw e ∪ init e × EV e)⁺.

Definition tearfree e :=
  aligned ∩₁ (EV e) ∪₁ init e.

Lemma sw_intro e X Y:
  rf e X Y -> sc e X -> sc e Y -> same_loc X Y -> sw e X Y.
Proof.
  intros rfXY scX scY slXY.
  split; try assumption.
  left.
  repeat (split; try assumption).
Qed.

Lemma sw_hb e :
  sw e ⊆ hb e.
Proof.
  do 2 eapply inclusion_trans.
  apply inclusion_union_r2. 
  apply inclusion_union_r1.
  apply ct_step.
  apply inclusion_refl.
Qed.

Lemma same_loc_sym :
  forall X Y, same_loc X Y -> same_loc Y X.
Proof.
  intros X Y [H1 H2].
  split; assumption.
Qed.

Lemma same_loc_trans X Y Z :
  same_loc X Y -> same_loc Y Z -> same_loc X Z.
Proof.
  intros slXY slYZ.
  unfold same_loc in *.
  rewrite slXY.
  assumption.
Qed.

Lemma same_loc_in_dom X Y n :
  same_loc X Y -> in_dom n X -> in_dom n Y.
Proof.
  intros sl id.
  apply (proj1 sl).
  apply id.
Qed.


Record well_formed exec := {
  wf_ev : forall e, EV exec e -> wf_event e;
  wf_index : forall e e', EV exec e -> EV exec e' -> index e = index e' -> e = e';
  wf_iww : init exec ⊆₁ writes exec \₁ reads exec;
  wf_iwn : forall ev ev', init exec ev -> ev_dom ev' ⊆₁ ev_dom ev;
  wf_iwsc : init exec ∩₁ sc exec ⊆₁ ∅;
  wf_rfb_func : forall n, functional (rfb exec n)⁻¹;
  wf_rfb_val : forall n, rfb exec n ⊆ same_val_wr n;
  wf_rfb_dom : forall n, rfb exec n ⊆ in_dom n × in_dom n;
  wf_rfb_wr : forall n, rfb exec n ≡ ⦗writes exec⦘ ⨾ (rfb exec n) ⨾ ⦗reads exec⦘;
  wf_loc_size : (EV exec\₁init exec) ⊆₁ size_n 1 ∪₁ size_n 2 ∪₁ size_n 4;
  wf_sb : strict_partial_order (sb exec);
  wf_rmw_sc : writes exec ∩₁ reads exec ⊆₁ sc exec;
  wf_sc_align : sc exec ⊆₁ aligned;
  wf_tot : strict_total_order (EV exec) (tot exec);
  wf_rfeq : forall X, rf exec X X -> False;
}.

Record consistent_sc_unfixed exec := {
  cst_hb_tot : (hb exec) ⊆ (tot exec);
  cst_rf_tf : functional ((rf exec) ∩ ((tearfree exec)×(tearfree exec)) ∩ same_loc)⁻¹;
  cst_rf_hb : irreflexive ((hb exec) ⨾ (rf exec));
  cst_rf_hb_hb : forall n, irreflexive (⦗writes exec⦘ ⨾ (hb exec) ⨾
                           (rfb exec n)⁻¹ ⨾ (hb exec) ⨾ ⦗in_dom n⦘);
  cst_sw_tot : irreflexive (⦗writes exec ∩₁ (sc exec)⦘ ⨾
               (tot exec ∩ same_loc) ⨾ (sw exec)⁻¹ ⨾ (tot exec));
}.

Record consistent exec := {
  cst_ufxd : consistent_sc_unfixed exec;
  cst_dagger : irreflexive (⦗writes exec ∩₁ (sc exec)⦘ ⨾
               (hb exec) ⨾ (rf exec ∩ (hb exec))⁻¹ ⨾
               ⦗sc exec⦘ ⨾ (tot exec ∩ same_loc));
  cst_ddagger : irreflexive (⦗writes exec ∩₁ (sc exec)⦘ ⨾
                (tot exec ∩ same_loc) ⨾ ⦗sc exec⦘ ⨾ 
                (rf exec ∩ (hb exec))⁻¹ ⨾ (hb exec));
}.

Definition data_race_free e :=
  forall X Y,
    hb e X Y \/ hb e Y X \/
    (~(writes e X) /\ ~(writes e Y)) \/
    nooverlap X Y \/
   (same_loc X Y /\ sc e X /\ sc e Y).

Definition seqcst e :=
  forall n, irreflexive (rfb e n ⨾ tot e) /\
  irreflexive (⦗writes e ∩₁ in_dom n⦘ ⨾ (tot e) ⨾ (rfb e n)⁻¹ ⨾ (tot e)).


Lemma rf__overlap exec :
  well_formed exec ->
  rf exec ⊆ overlap.
Proof.
  intros wf X Y [b [_ rfbXY]].
  eexists.
  eapply wf_rfb_dom; eauto.
Qed.

Lemma rf__ev exec :
  well_formed exec ->
  rf exec ⊆ (EV exec)².
Proof.
  intros wf X Y [b [_ H]].
  destruct (wf_rfb_wr exec wf b) as [H1 _].
  apply H1 in H.
  unfolder in H.
  destruct H as [[EVX _] [_ [EVY _]]].
  split; assumption.
Qed.


Lemma rfb__w exec X Y n :
  well_formed exec ->
  rfb exec n X Y -> writes exec X.
Proof.
  intros wf rf.
  apply wf_rfb_wr in rf; try assumption.
  unfolder in rf.
  destruct rf.
  assumption.
Qed.

Lemma rfb__r exec X Y n :
  well_formed exec ->
  rfb exec n X Y -> reads exec Y.
Proof.
  intros wf rf.
  apply wf_rfb_wr in rf; try assumption.
  unfolder in rf.
  destruct rf as [_[_ H]].
  assumption.
Qed.

Lemma rf__wr exec X Y:
  well_formed exec ->
  rf exec X Y ->
  writes exec X /\ reads exec Y.
Proof.
  intros wf rfXY.
  destruct rfXY as [n [_ rfbXY]].
  apply (proj1 (wf_rfb_wr exec wf n)) in rfbXY.
  unfolder in rfbXY.
  destruct rfbXY as [H1 [_ H2]].
  split; assumption.
Qed.

Lemma rfb__rf exec X Y n :
  rfb exec n X Y -> rf exec X Y.
Proof.
  intro rfbXY.
  exists n.
  split; trivial.
Qed.


Lemma sw_r_sc e X Y :
  well_formed e -> sw e X Y -> reads e Y /\ sc e Y.
Proof.
  intros wf swXY.
  unfold sw in swXY.
  unfolder in swXY.
  destruct swXY as [rfXY H].
  split.
  - apply rf__wr in rfXY;
    destruct rfXY; assumption.
  - destruct H as [[[_ scY] _] | [[_ scY] _]];
    assumption.
Qed.

Lemma sw_init_sc e X Y :
  well_formed e -> sw e X Y -> writes e X /\ (init e X \/ sc e X).
Proof.
  intros wf swXY.
  unfold sw in swXY.
  unfolder in swXY.
  destruct swXY as [rfXY H].
  split.
  - apply rf__wr in rfXY;
    destruct rfXY;
    assumption.
  - destruct H as [[[scX _] _] | [[iwX _] _]];
    auto.
Qed.

Lemma rfb__dom e :
  forall X Y n,
  well_formed e ->
  rfb e n Y X ->
  ev_dom Y n /\ ev_dom X n.
Proof.
  intros X Y n wf rfb.
  apply wf_rfb_dom in rfb;
  assumption.
Qed.

Lemma rfb_w_dom :
  forall e X Y n, well_formed e -> rfb e n Y X -> ev_dom Y n.
Proof.
  intros e X Y n H rfbnYX.
  apply wf_rfb_dom in rfbnYX; try assumption.
  destruct rfbnYX.
  assumption.
Qed.
Lemma rfb_r_dom :
  forall e X Y n, well_formed e -> rfb e n Y X -> ev_dom X n.
Proof.
  intros e X Y n H rfbnYX.
  apply wf_rfb_dom in rfbnYX; try assumption.
  destruct rfbnYX.
  assumption.
Qed.

Lemma rf__neq e X Y:
  well_formed e -> rf e X Y -> X <> Y.
Proof.
  intros wf [n [_ rfnXY]] eq.
  subst.
  eapply wf_rfeq;
  try eapply rfb__rf;
  eassumption.
Qed.

Lemma seqcst__rfbtot e :
  well_formed e -> seqcst e -> forall n, rfb e n ⊆ tot e.
Proof.
  intros wf sqc n X Y rfbnXY.
  destruct (wf_tot e wf) as [[irrefl trans] total].
  assert (EV e X /\ EV e Y) as [evX evY].
    apply rf__ev; try  eapply rfb__rf; eassumption.
  destruct (total X evX Y evY).
  - eapply rf__neq; try eapply rfb__rf; eassumption.
  - assumption.
  - exfalso.
    apply (proj1 (sqc n) X).
    exists Y.
    auto.
Qed.

Lemma same_loc__overlap e :
  forall X Y,
  well_formed e ->
  EV e X \/ EV e Y ->
  same_loc X Y -> 
  overlap X Y.
Proof.
  intros X Y wf [ev|ev] slXY;
  apply wf_ev in ev; try assumption;
  destruct ev as [[n domn] _];
  exists n;
  split; try assumption;
  [apply (proj1 slXY) | apply (proj2 slXY)];
  assumption.
Qed.

Theorem seqcst__cst exec : 
  well_formed exec -> seqcst exec -> (hb exec) ⊆ (tot exec) ->
  consistent exec.
Proof.
  intros wf sqc hbtot.
  pose proof (seqcst__rfbtot exec wf sqc) as rfbtot.
  constructor.
  constructor.
  - assumption.
  - intros R W1 W2.
    unfolder.
    intros [[rf1 [tf1 tfR]] sl1] [[rf2 [tf2 _]] sl2].
    destruct (mev_eq_dec W1 W2) as [eq | neq]. assumption. exfalso.
    destruct (wf_tot exec) as [[irrefl trans] total]; try assumption.
    assert (tot exec W1 W2 \/ tot exec W2 W1) as [tot12 | tot21]. {
      apply total;
      apply rf__ev in rf1; apply rf__ev in rf2;
      destruct rf1, rf2; assumption.
    }
    + destruct rf1 as [n [_ rfb1]].
      apply (proj2 (sqc n) W2).
      unfolder.
      split. split.
      * destruct rf2 as [H1[H2 rfb2]]. eapply rfb__w;
        eassumption.
      * apply same_loc_in_dom with W1.
        -- apply same_loc_trans with R; try assumption.
            apply same_loc_sym. assumption.
        -- eapply rfb_w_dom; eassumption.
      * repeat (eexists; split; eauto).
        destruct rf2 as [n' [_ rfb2]].
        apply (rfbtot n').
        auto.
    + destruct rf2 as [n [_ rfb2]].
      apply (proj2 (sqc n) W1).
      unfolder.
      split. split.
      * destruct rf1 as [H1[H2 rfb1]]. eapply rfb__w;
        eassumption.
      * apply same_loc_in_dom with W2.
        -- apply same_loc_trans with R; try assumption.
            apply same_loc_sym. assumption.
        -- eapply rfb_w_dom; eassumption.
      * repeat (eexists; split; eauto).
        destruct rf1 as [n' [_ rfb1]].
        apply (rfbtot n').
        auto.
  - intros Y [X [hbYX rfXY]].
    unfold transp in rfXY.
    destruct (wf_tot exec wf) as [[irrefl trans] total].
    apply irrefl with X.
    apply trans with Y.
    + destruct rfXY as [n [_ rfnXY]].
      apply (rfbtot n).
      assumption.
    + auto.
  - intros n Z' [Z [[eqZ WZ] [X [hbZX [Y [rfbYX [Z'' [hbYZ [eqZ' domnZ]]]]]]]]].
    subst.
    apply (proj2 (sqc n) Z).
    unfolder.
    split; auto.
    repeat (eexists; split; eauto).
  - intros Z' [Z [[eqZZ' [wZ _]] [X [[totZX slZX] [Y [[[n [_ rfnYX]] _] totYZ]]]]]].
    subst.
    apply (proj2 (sqc n) Z).
    unfolder.
    split.
    + split; try assumption.
      apply same_loc_in_dom with X.
      * apply same_loc_sym. assumption.
      * apply rfb_r_dom with exec Y; assumption.
    + repeat (eexists; split; eauto).
  - intros Z' [Z [[eqZZ' [wZ _]] [X [hbZX [Y' [[[n [_ rfbnYX]] _] [Y [[eqYY' _] [totYZ slYZ]]]]]]]]].
    subst.
    apply (proj2 (sqc n) Z).
    unfolder.
    split.
    + split; auto.
      eapply same_loc_in_dom; try eassumption.
      eapply rfb_w_dom; eassumption.
    + repeat (eexists; split; eauto).
  - intros Z' [Z [[eqZZ' [wZ _]] [X [[totZX slZX] [X' [[eqXX' _] [Y [[[n [_ rfnYX]] _] hbYZ]]]]]]]].
    subst.
    apply (proj2 (sqc n) Z).
    unfolder.
    split.
    + split; auto.
      eapply same_loc_in_dom.
      * apply same_loc_sym. eassumption.
      * eapply rfb_r_dom; eassumption.
    + repeat (eexists; split; eauto).
Qed. 

End Exec.