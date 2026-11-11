(** Indexed degeneracy layers: face equations, fillers as whole-cell maps,
    and layers as lifts of their latching boundaries. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet LeSProp NatLemmas Notation RewLemmas
  Equiv Funext FinitePrefix.
From Bonak.νSet Require Import Layer νDgnSet.
From Bonak.Presheaf Require Import GeneratingFaces.
From Bonak.Presheaf.Dgn Require Import Generators.
From Bonak.Reedy Require Import GeneratorBoundary.
From Bonak.Reedy.Dgn Require Import Reedy Matching.
From Bonak.Equiv Require Import Boundary Matching.
From Bonak.Equiv.Dgn Require Import Latching.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** Face equations of indexed degeneracy frames and whole cells. *)

Module DgnFaceOn (A: LayerSig) (S: νDgnSetSig A).
Import A.
Module Export DgnSet := S.
Module Export Faces := IndexedMatching A DgnSet.νSet.

Definition faceDown {p k} (dc2: DepsCohs2 p k) (fuel: nat) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs)))) :=
  faceAtDepth dc2.(_depsCohs) fuel ε d.

Lemma faceDownStep {p k} (dc2: DepsCohs2 p.+1 k) fuel (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs)))):
  faceDown dc2 fuel.+1 ε d =
  let y := faceDown (proj1DepsCohs2 dc2) fuel ε d.1 in
  ((y.1; y.2.1); y.2.2).
Proof. now exact (faceAtDepthNext dc2.(_depsCohs) fuel ε d). Defined.

Lemma faceDownAboveId {p k} (deps: DepsReflCohsSup p k)
  i (Hi: i <= p) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  faceDown (Cohs2OfReflCohsSup deps) i ε (mkReflFrameAbove deps i Hi d c) =
  (d; c).
Proof.
  revert p k deps Hi d c; induction i; intros p k deps Hi d c.
  - unfold faceDown, mkReflFrameAbove, mkReflFramesAbove,
      mkReflFramesAboveOf0AndS, mkReflFrameAboveOf0AndS.
    cbn [projT2].
    unfold mkReflFrameAbove0, mkReflLayerAbove0.
    cbn [faceAtDepth chainDown νFace cohsChainExt cohsChainNext
      getFrame getPainting projT1 projT2].
    rewrite nth_lam.
    symmetry.
    now exact (eq_existT_curried
      (mkIdRestrReflFrameBelow deps.(_depsReflCohsInf) 0 leR_O ε d) eq_refl).
  - destruct p; [now destruct (leR_O_contra Hi) |].
    rewrite faceDownStep.
    change
      ((let y := faceDown (Cohs2OfReflCohsSup deps.(1)%depsreflcohssup) i ε
          (mkReflFrameAbove deps.(1)%depsreflcohssup i Hi d.1 (d.2; c)) in
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup deps) &T
            mkPainting (RestrExtOfReflCohsSup deps) d'})) = (d; c)).
    now rewrite IHi.
Qed.

Definition aboveTotal {p k} (deps: DepsReflCohsSup p k)
  (extra: DepsReflCohsSupExtension p k deps) i (Hi: i <= p)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  {d': mkFrame (mkDepsRestr (depsCohs := CohsOfReflCohsSup deps)) &T
    mkPainting (mkExtraDeps (CohsExtOfReflCohsSup deps)) d'} :=
  (mkReflFrameAbove deps i Hi d c; mkReflPaintingAbove deps extra i Hi d c).

Lemma aboveTotalStep {p k} (deps: DepsReflCohsSup p.+1 k)
  (extra: DepsReflCohsSupExtension p.+1 k deps) i (Hi: i <= p)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  aboveTotal deps extra i.+1 (⇑ Hi) d c =
  let y := aboveTotal deps.(1)%depsreflcohssup (AddReflCohSupDep deps extra)
    i Hi d.1 (d.2; c) in
  ((y.1; y.2.1); y.2.2).
Proof.
  now reflexivity.
Qed.

Lemma faceDownAboveSup {p k} (deps: DepsReflCohs2 p k)
  q i (Hq: q <= i) (Hi: i <= p) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)))
  (c: mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d):
  faceDown (Cohs2OfReflCohsSup (mkDepsReflCohsSup deps)) q ε
    (mkReflFrameAbove (mkDepsReflCohsSup deps) i.+1 (⇑ Hi) d c) =
  let y := faceDown (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d in
  aboveTotal deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup) i Hi y.1 y.2.
Proof.
  revert p k deps i Hq Hi d c; induction q; intros p k deps i Hq Hi d c.
  - unfold faceDown, aboveTotal.
    cbn [faceAtDepth chainDown νFace cohsChainExt cohsChainNext
      getFrame getPainting projT1 projT2].
    unfold mkReflFrameAbove, mkReflFramesAbove, mkReflFramesAboveOf0AndS,
      mkReflFrameAboveOf0AndS.
    cbn [projT2].
    unfold mkReflFramesAboveS.
    cbn [mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove
      ReflFramesAboveSDef mkReflLayerAbove projT1 projT2].
    rewrite nth_lam.
    symmetry.
    now exact (eq_existT_curried
      ((mkCohReflRestrFramesAboveSup deps).2 i 0 Hi leR_O ε d.1 (d.2; c))
      eq_refl).
  - destruct i; [now destruct (leR_O_contra Hq) |].
    destruct p; [now destruct (leR_O_contra Hi) |].
    rewrite 2 faceDownStep.
    cbv zeta.
    rewrite (aboveTotalStep deps.(_depsReflCohsSup)
      deps.(_extraDepsReflCohsSup) i (⇓ Hi)).
    now exact (f_equal
      (fun y:
        {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) &T
          mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) &T
            mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d'}))
      (IHq _ _ deps.(1)%depsreflcohs2 i Hq Hi d.1 (d.2; c))).
Qed.

Definition belowPair {p k} (deps: DepsReflCohsSup p k)
  (extra: DepsReflCohsSupExtension p k deps) i (Hi: i <= k)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  {d': mkFrame (mkDepsRestr (depsCohs := CohsOfReflCohsSup deps)).(1) &T
    mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup deps))) d'} :=
  (mkReflFrameBelow deps.(_depsReflCohsInf) i Hi d;
   mkReflPaintingBelow deps extra i Hi d c).

Lemma belowPairStep {p k} (deps: DepsReflCohsSup p.+1 k)
  (extra: DepsReflCohsSupExtension p.+1 k deps) i (Hi: i <= k)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  belowPair deps extra i Hi d c =
  let y := belowPair deps.(1)%depsreflcohssup (AddReflCohSupDep deps extra)
    i.+1 (⇑ Hi) d.1 (d.2; c) in
  ((y.1; y.2.1); y.2.2).
Proof.
  now reflexivity.
Qed.

Lemma faceDownBelowInf {p k} (deps: DepsReflCohs2 p k)
  q (Hq: q <= p) i (Hi: i <= k) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps))):
  faceDown (Cohs2OfReflCohsSup (mkDepsReflCohsSup deps)).(1) q ε
    (mkReflFrameBelow (mkDepsReflCohsSup deps).(_depsReflCohsInf) i Hi d) =
  let y := faceDown (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d in
  belowPair deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup) i Hi y.1 y.2.
Proof.
  revert p k deps Hq i Hi d; induction q; intros p k deps Hq i Hi d.
  - unfold faceDown, belowPair.
    cbn [faceAtDepth chainDown νFace cohsChainExt cohsChainNext
      getFrame getPainting projT1 projT2].
    unfold mkReflFrameBelow, mkReflFramesBelow.
    cbn [mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow
      ReflFramesBelowDef mkReflLayerBelow projT1 projT2].
    rewrite nth_lmap.
    symmetry.
    now exact (eq_existT_curried
      ((mkCohReflRestrFramesBelowInf deps).2 i 0 Hi leR_O ε d.1)
      eq_refl).
  - destruct p; [now destruct (leR_O_contra Hq) |].
    rewrite 2 faceDownStep. cbv zeta.
    rewrite (belowPairStep deps.(_depsReflCohsSup)
      deps.(_extraDepsReflCohsSup) i Hi).
    now exact (f_equal
      (fun y:
        {d': mkFrame (mkDepsRestr (depsCohs :=
          CohsOfReflCohsSup deps.(_depsReflCohsSup).(1)%depsreflcohssup)).(1) &T
          mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup
            deps.(_depsReflCohsSup).(1)%depsreflcohssup))) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (mkDepsRestr (depsCohs :=
            CohsOfReflCohsSup deps.(_depsReflCohsSup))).(1) &T
            mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup
              deps.(_depsReflCohsSup)))) d'}))
      (IHq _ _ deps.(1)%depsreflcohs2 Hq i.+1 (⇑ Hi) d.1)).
Qed.

Lemma faceDownAboveInf {p k} (deps: DepsReflCohs2 p k)
  q i (Hi: i <= q) (Hq: q <= p) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)))
  (c: mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d):
  faceDown (Cohs2OfReflCohsSup (mkDepsReflCohsSup deps)) q.+1 ε
    (mkReflFrameAbove (mkDepsReflCohsSup deps) i (Hi ↕ (↑ Hq)) d c) =
  let y := faceDown (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d in
  aboveTotal deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)
    i (Hi ↕ Hq) y.1 y.2.
Proof.
  revert p k deps q Hi Hq d c; induction i; intros p k deps q Hi Hq d c.
  - rewrite faceDownStep.
    now exact (f_equal
      (fun y:
        {d': mkFrame (mkDepsRestr (depsCohs :=
          CohsOfReflCohsSup deps.(_depsReflCohsSup))).(1) &T
          mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup
            deps.(_depsReflCohsSup)))) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) &T
            mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d'}))
      (faceDownBelowInf deps q Hq 0 leR_O ε d)).
  - destruct q; [now destruct (leR_O_contra Hi) |].
    destruct p; [now destruct (leR_O_contra Hq) |].
    rewrite faceDownStep.
    rewrite (faceDownStep (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d).
    cbv zeta.
    rewrite (aboveTotalStep deps.(_depsReflCohsSup)
      deps.(_extraDepsReflCohsSup) i (Hi ↕ Hq)).
    now exact (f_equal
      (fun y:
        {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) &T
          mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) &T
            mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d'}))
      (IHi _ _ deps.(1)%depsreflcohs2 q Hi Hq d.1 (d.2; c))).
Qed.

End DgnFaceOn.


(** Indexed degeneracy fillers as whole-cell maps with a prescribed frame. *)

Module DgnStepOn (A: LayerSig) (S: νDgnSetSig A).
Import A.
Module Export Faces := DgnFaceOn A S.

Definition stepData {n} (Y: DgnPrefix n.+1):
  DgnData (νDataAt Y.1.1) Y.1.2 :=
  (νDgnSetAt n).(dgnStepData) Y.1.1 Y.2.1 Y.1.2 Y.2.2.

Definition stepDeps {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet):
  DepsReflCohsSup n 0 :=
  dgnDepsReflCohsSupFromData (νDataAt Y.1.1) Y.1.2 E (stepData Y).

Definition StepType {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet): Type :=
  (νDgnSetAt n.+1).(dgnStepType) Y.1 Y.2 E.

Definition stepOutput {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet): HSet :=
  {d: νFrame Y.1 & E d}.

Definition stepFrame {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  i (Hi: i <= n) (x: prefixCell Y.1): νFrame Y.1 :=
  mkReflFrameAbove (stepDeps Y E) i Hi x.1 x.2.

Definition TopMaps {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet): Type :=
  forall i, i <= n -> prefixCell Y.1 -> stepOutput Y E.

Definition layerAbove {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (L: StepType Y E): TopMaps Y E :=
  fun i Hi x => (stepFrame Y E i Hi x; L.1 i Hi x.1 x.2).

Definition previousAbove {n} (Y: DgnPrefix n.+2)
  i (Hi: i <= n) (x: prefixCell Y.1.1): prefixCell Y.1 :=
  layerAbove (dgnBond Y) Y.1.2 Y.2.2 i Hi x.

Definition TopCommutation (n: nat):
  forall (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet), TopMaps Y E -> Type :=
  match n as n return
    forall (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet), TopMaps Y E -> Type with
  | 0 => fun _ _ _ => unit
  | S n => fun Y E f =>
      forall q r (Hq: q <= r) (Hr: r <= n) (x: prefixCell Y.1.1),
      f r.+1 (⇑ Hr) (previousAbove Y q (Hq ↕ Hr) x) =
      f q (Hq ↕ ↑ Hr) (previousAbove Y r Hr x)
  end.

Definition TopFrames {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E): Type :=
  forall i (Hi: i <= n) (x: prefixCell Y.1),
    (f i Hi x).1 = stepFrame Y E i Hi x.

Lemma layerAboveDD {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (L: StepType Y E): TopCommutation n Y E (layerAbove Y E L).
Proof.
  destruct n as [|n].
  - now exact tt.
  - intros q r Hq Hr x.
    apply (eq_existT_curried
      (((stepData Y).(dgnDataCore).(cohReflAboveAboveFrames) E).2
        q r Hq Hr x.1 x.2)).
    now exact (L.2.2 q r Hq Hr x.1 x.2).
Defined.

Definition mapsLayer {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E) (hf: TopFrames Y E f): dgnHasReflFromData
    (νDataAt Y.1.1) Y.1.2 E (stepData Y) :=
  fun i Hi d c => rew [E] (hf i Hi (d; c)) in
    (f i Hi (d; c)).2.

Lemma reframeTotal {B: HSet} {E: B -> HSet}
  (x: {b: B & E b}) (b: B) (p: x.1 = b):
  ((b; rew [E] p in x.2): {b: B & E b}) = x.
Proof. destruct x as [a e]; cbn in p. now destruct p. Defined.

Lemma mapsLayerWhole {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E) (hf: TopFrames Y E f) i Hi (x: prefixCell Y.1):
  ((stepFrame Y E i Hi x; mapsLayer Y E f hf i Hi x.1 x.2): stepOutput Y E)
    = f i Hi x.
Proof. now apply reframeTotal. Defined.

Lemma totalSndEq {B: HSet} {P: B -> Type} {x y: B} {u: P x} {v: P y}
  (e: x = y) (h: ((x; u): {b: B &T P b}) = (y; v)):
  rew [P] e in u = v.
Proof.
  pose proof (projT2_eq h) as H.
  now rewrite (B.(UIP) (h := projT1_eq h) (g := e)) in H.
Defined.

Definition stepDeps2 {n} (Y: DgnPrefix n.+2) (E: νFrame Y.1 -> HSet):
  DepsReflCohs2 n 0 :=
  dgnDepsReflCohs2FromData (νDataAt Y.1.1.1) Y.1.1.2 Y.1.2 E
    (stepData (dgnBond Y)) Y.2.2.1 Y.2.2.2.

Lemma mapsLayerCohTop {n} (Y: DgnPrefix n.+2) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E) (hf: TopFrames Y E f) (hc: TopCommutation n.+1 Y E f):
  cohReflAboveAboveL (stepDeps2 Y E) (mapsLayer Y E f hf).
Proof.
  intros q r Hq Hr d c.
  apply (totalSndEq (B := νFrame Y.1) (P := fun b => E b)).
  change (((stepFrame Y E r.+1 (⇑ Hr) (previousAbove Y q (Hq ↕ Hr) (d; c));
      mapsLayer Y E f hf r.+1 (⇑ Hr)
        (previousAbove Y q (Hq ↕ Hr) (d; c)).1
        (previousAbove Y q (Hq ↕ Hr) (d; c)).2): stepOutput Y E)
    = (stepFrame Y E q (Hq ↕ ↑ Hr) (previousAbove Y r Hr (d; c));
      mapsLayer Y E f hf q (Hq ↕ ↑ Hr)
        (previousAbove Y r Hr (d; c)).1
        (previousAbove Y r Hr (d; c)).2)).
  rewrite 2 mapsLayerWhole.
  now exact (hc q r Hq Hr (d; c)).
Defined.

Definition mapsLayerCoh {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E) (hf: TopFrames Y E f) (hc: TopCommutation n Y E f):
  dgnCohLFromData (νDataAt Y.1.1) Y.1.2 E (stepData Y) (mapsLayer Y E f hf).
Proof.
  destruct n as [|n].
  - now exact tt.
  - now exact (mkCohReflAboveAbovePaintings (stepDeps2 Y E)
      (TopReflCoh2Dep (deps := stepDeps2 Y E)
        (mapsLayer Y E f hf) (mapsLayerCohTop Y E f hf hc))).
Defined.

Definition mapsToLayer {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E) (hf: TopFrames Y E f) (hc: TopCommutation n Y E f): StepType Y E :=
  (mapsLayer Y E f hf; mapsLayerCoh Y E f hf hc).

Lemma mapsToLayerAbove {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (f: TopMaps Y E) (hf: TopFrames Y E f) (hc: TopCommutation n Y E f)
  i Hi (x: prefixCell Y.1):
  layerAbove Y E (mapsToLayer Y E f hf hc) i Hi x = f i Hi x.
Proof. now apply mapsLayerWhole. Defined.

Definition prefixGenerator {n} (X: DgnPrefix n.+2) (i: FaceDepth n):
  prefixCell X.1.1 -> prefixCell X.1 :=
  previousAbove X (depth i) (depthBound i).

Lemma coherenceIrrel {p k} (deps: DepsReflCohsSup p k)
  (extra: DepsReflCohsSupExtension p k deps)
  (frames: mkCohReflAboveAboveFrameTypes deps)
  (a b: mkCohReflAboveAbovePaintingTypes deps extra frames): a = b.
Proof.
  revert k deps extra frames a b; induction p; intros k deps extra frames a b.
  - now exact (hunit_ext _ _).
  - destruct a as [a a'], b as [b b'].
    pose proof (IHp _ _ _ _ a b) as e. destruct e.
    apply (f_equal (fun c => (a; c))).
    repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro].
    now apply (mkPainting (mkExtraDeps (CohsExtOfReflCohsSup deps)) _).(UIP).
Defined.

Lemma stepLayerEq {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  (L K: StepType Y E)
  (h: forall i Hi d c, L.1 i Hi d c = K.1 i Hi d c): L = K.
Proof.
  assert (e: L.1 = K.1).
  { apply functional_extensionality_dep; intro i.
    apply spropFunext; intro Hi.
    apply functional_extensionality_dep; intro d.
    apply functional_extensionality_dep; intro c. now apply h. }
  apply (eq_existT_curried e).
  now apply coherenceIrrel.
Defined.

Lemma stepFrameFaceId {n} (Y: DgnPrefix n.+1) (E: νFrame Y.1 -> HSet)
  i (Hi: i <= n) a (x: prefixCell Y.1):
  faceAtDepth (prefixDepsCohs Y.1) i a (stepFrame Y E i Hi x) = x.
Proof. now exact (faceDownAboveId (stepDeps Y E) i Hi a x.1 x.2). Defined.

Lemma stepFrameFaceSup {n} (Y: DgnPrefix n.+2) (E: νFrame Y.1 -> HSet)
  q i (Hq: q <= i) (Hi: i <= n) a (x: prefixCell Y.1):
  faceAtDepth (prefixDepsCohs Y.1) q a (stepFrame Y E i.+1 (⇑ Hi) x) =
  previousAbove Y i Hi (faceAtDepth (prefixDepsCohs Y.1.1) q a x.1).
Proof. now exact (faceDownAboveSup (stepDeps2 Y E) q i Hq Hi a x.1 x.2). Defined.

Lemma stepFrameFaceInf {n} (Y: DgnPrefix n.+2) (E: νFrame Y.1 -> HSet)
  q i (Hi: i <= q) (Hq: q <= n) a (x: prefixCell Y.1):
  faceAtDepth (prefixDepsCohs Y.1) q.+1 a (stepFrame Y E i (Hi ↕ ↑ Hq) x) =
  previousAbove Y i (Hi ↕ Hq) (faceAtDepth (prefixDepsCohs Y.1.1) q a x.1).
Proof. now exact (faceDownAboveInf (stepDeps2 Y E) q i Hi Hq a x.1 x.2). Defined.

End DgnStepOn.


(** Indexed degeneracy layers as lifts of their latching boundaries. *)

Module DgnLayerOn (A: LayerSig) (S: νDgnSetSig A).
Import A.
Module Export Step := DgnStepOn A S.

Definition LowerModel (n: nat): forall (Y: DgnPrefix n.+1)
  (D: Diagram arity n.+1), Equiv (prefixCell Y.1) (cells D None) -> Type :=
  match n as n return forall (Y: DgnPrefix n.+1)
    (D: Diagram arity n.+1), Equiv (prefixCell Y.1) (cells D None) -> Type with
  | 0 => fun _ _ _ => unit
  | S n => fun Y D upper =>
      {lower: Equiv (prefixCell Y.1.1) (cells D (Some None)) &T
        ((forall (i: FaceDepth n) a (x: prefixCell Y.1),
          lower (faceAtDepth (prefixDepsCohs Y.1.1) (depth i) a x.1) =
            act D (i := Some None) (j := None)
              (shapeFace (depthFaceWord arity n i a)) (upper x)) *
         (forall (i: FaceDepth n) (x: prefixCell Y.1.1),
          upper (previousAbove Y (depth i) (depthBound i) x) =
            act D (i := None) (j := Some None)
              (shapeMask (depthFaceWord hunit n i tt)) (lower x)))%type}
  end.

Section Comparison.
Context {n} (Y: DgnPrefix n.+1) (D: Diagram arity n.+1).
Context (upper: Equiv (prefixCell Y.1) (cells D None)).
Context (model: LowerModel n Y D upper).
Context (boundary: Equiv (νFrame Y.1) (MatchingObject arity D)).
Context (frameLaw: forall d (i: FaceDepth n) a,
  (boundary d).1 None (shapeFace (depthFaceWord arity n i a)) =
    upper (faceAtDepth (prefixDepsCohs Y.1) (depth i) a d)).

Lemma stepFrameBoundary (E: νFrame Y.1 -> HSet) (i: FaceDepth n)
  (x: prefixCell Y.1):
  boundary (stepFrame Y E (depth i) (depthBound i) x) =
    latchingBoundary arity D (i := None)
      (shapeMask (depthFaceWord hunit n i tt)) (upper x).
Proof.
  apply (eqvInj (matchingEquivFace arity D)).
  apply finiteMatchingFacesExt; intros q a.
  change ((boundary (stepFrame Y E (depth i) (depthBound i) x)).1 None
      (shapeFace (depthFaceWord arity n q a)) =
    act D (i := None) (j := None)
      (shapeComp (shapeFace (depthFaceWord arity n q a))
        (shapeMask (depthFaceWord hunit n i tt))) (upper x)).
  rewrite frameLaw.
  destruct i as [i Hi], q as [q Hq]; cbn [depth depthBound].
  destruct (natOrder q i) as [h|e|h].
  - destruct i as [|i]; [now destruct (leR_O_contra h)|].
    destruct n as [|k]; [now destruct (leR_O_contra Hi)|].
    change (upper (faceAtDepth (prefixDepsCohs Y.1) q a
        (stepFrame Y E i.+1 (⇑ (⇓ Hi)) x)) =
      act D (i := None) (j := None)
        (shapeComp (shapeFace (depthFaceWord arity k.+1
          (weakenDepth {| depth := q; depthBound := (⇓ h) ↕ (⇓ Hi) |}) a))
          (shapeMask (depthFaceWord hunit k.+1
            (nextDepth {| depth := i; depthBound := ⇓ Hi |}) tt))) (upper x)).
    rewrite stepFrameFaceSup, depthFaceMaskSup.
    2: now exact (⇓ h).
    2: now exact (⇓ h).
    change (upper (previousAbove Y i (⇓ Hi)
        (faceAtDepth (prefixDepsCohs Y.1.1) q a x.1)) =
      act D (i := None) (j := None)
        (shapeComp (shapeMask (depthFaceWord hunit k
          {| depth := i; depthBound := ⇓ Hi |} tt))
          (shapeFace (depthFaceWord arity k
            {| depth := q; depthBound := (⇓ h) ↕ (⇓ Hi) |} a))) (upper x)).
    rewrite (snd model.2 {| depth := i; depthBound := ⇓ Hi |}).
    rewrite (fst model.2 {| depth := q; depthBound := (⇓ h) ↕ (⇓ Hi) |}).
    now exact (actComp D (i := None) (j := Some None) (k := None) _ _ _).
  - destruct e. rewrite stepFrameFaceId, depthFaceMaskId. now symmetry; exact (actId D None (upper x)).
  - destruct q as [|q]; [now destruct (leR_O_contra h)|].
    destruct n as [|k]; [now destruct (leR_O_contra Hq)|].
    change (upper (faceAtDepth (prefixDepsCohs Y.1) q.+1 a
        (stepFrame Y E i ((⇓ h) ↕ ↑ (⇓ Hq)) x)) =
      act D (i := None) (j := None)
        (shapeComp (shapeFace (depthFaceWord arity k.+1
          (nextDepth {| depth := q; depthBound := ⇓ Hq |}) a))
          (shapeMask (depthFaceWord hunit k.+1
            (weakenDepth {| depth := i; depthBound := (⇓ h) ↕ (⇓ Hq) |}) tt))) (upper x)).
    rewrite stepFrameFaceInf, depthFaceMaskInf.
    2: now exact (⇓ h).
    rewrite (snd model.2 {| depth := i; depthBound := (⇓ h) ↕ (⇓ Hq) |}).
    rewrite (fst model.2 {| depth := q; depthBound := ⇓ Hq |}).
    now exact (actComp D (i := None) (j := Some None) (k := None) _ _ _).
Defined.

Lemma indexedGeneratorsDD (E: νFrame Y.1 -> HSet) (L: StepType Y E):
  GeneratorRelations n.+1 D (stepOutput Y E)
    (fun i x => layerAbove Y E L (depth i) (depthBound i) (invEq upper x)).
Proof.
  destruct n as [|k].
  - now exact tt.
  - intros i j hij x.
    rewrite <- (secEq model.1 x).
    rewrite <- (snd model.2 i), <- (snd model.2 j), 2 retEq.
    now exact (layerAboveDD Y E L (depth i) (depth j) hij (depthBound j) (invEq model.1 x)).
Defined.

Definition indexedToGenerators (E: νFrame Y.1 -> HSet) (L: StepType Y E):
  GeneratorLifts D (stepOutput Y E) (fun x => boundary x.1).
Proof.
  refine (@Build_GeneratorLifts arity n.+1 D (stepOutput Y E)
    (fun x => boundary x.1)
    (fun i x => layerAbove Y E L (depth i) (depthBound i) (invEq upper x))
    (indexedGeneratorsDD E L) _).
  intros i x.
  change (boundary (stepFrame Y E (depth i) (depthBound i) (invEq upper x)) =
    latchingBoundary arity D (i := None) (shapeMask (depthFaceWord hunit n i tt)) x).
  rewrite (stepFrameBoundary E i (invEq upper x)). now rewrite secEq.
Defined.

Lemma generatorsIndexedDD (E: νFrame Y.1 -> HSet)
  (G: GeneratorLifts D (stepOutput Y E) (fun x => boundary x.1)):
  TopCommutation n Y E
    (fun i Hi x => G.(generator) {| depth := i; depthBound := Hi |} (upper x)).
Proof.
  destruct n as [|k].
  - now exact tt.
  - intros q r Hq Hr x.
    rewrite (snd model.2 {| depth := q; depthBound := Hq ↕ Hr |}),
      (snd model.2 {| depth := r; depthBound := Hr |}).
    now exact (G.(generatorDD) {| depth := q; depthBound := Hq ↕ Hr |}
      {| depth := r; depthBound := Hr |} Hq (model.1 x)).
Defined.

Lemma generatorsIndexedFrames (E: νFrame Y.1 -> HSet)
  (G: GeneratorLifts D (stepOutput Y E) (fun x => boundary x.1)):
  TopFrames Y E
    (fun i Hi x => G.(generator) {| depth := i; depthBound := Hi |} (upper x)).
Proof.
  intros i Hi x. apply (eqvInj boundary).
  change (boundary (G.(generator) {| depth := i; depthBound := Hi |} (upper x)).1
    = boundary (stepFrame Y E i Hi x)).
  rewrite G.(generatorBoundary). symmetry.
  now exact (stepFrameBoundary E {| depth := i; depthBound := Hi |} x).
Defined.

Definition generatorsToLayer (E: νFrame Y.1 -> HSet)
  (G: GeneratorLifts D (stepOutput Y E) (fun x => boundary x.1)): StepType Y E :=
  mapsToLayer Y E
    (fun i Hi x => G.(generator) {| depth := i; depthBound := Hi |} (upper x))
    (generatorsIndexedFrames E G) (generatorsIndexedDD E G).

Lemma indexedGeneratorsRet (E: νFrame Y.1 -> HSet) (L: StepType Y E):
  generatorsToLayer E (indexedToGenerators E L) = L.
Proof.
  apply stepLayerEq; intros i Hi d c.
  apply (totalSndEq (B := νFrame Y.1) (P := fun d => E d) eq_refl).
  change (layerAbove Y E (generatorsToLayer E (indexedToGenerators E L)) i Hi (d; c)
    = layerAbove Y E L i Hi (d; c)).
  unfold generatorsToLayer. rewrite mapsToLayerAbove.
  change (layerAbove Y E L i Hi (invEq upper (upper (d; c))) = layerAbove Y E L i Hi (d; c)).
  now rewrite retEq.
Defined.

Lemma indexedGeneratorsSec (E: νFrame Y.1 -> HSet)
  (G: GeneratorLifts D (stepOutput Y E) (fun x => boundary x.1)):
  indexedToGenerators E (generatorsToLayer E G) = G.
Proof.
  apply generatorLiftsEq.
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro x.
  change (layerAbove Y E (generatorsToLayer E G) (depth i) (depthBound i) (invEq upper x)
    = G.(generator) i x).
  unfold generatorsToLayer. rewrite mapsToLayerAbove.
  now rewrite secEq.
Defined.

Definition indexedLayerGeneratorsEquiv (E: νFrame Y.1 -> HSet):
  Equiv (StepType Y E) (GeneratorLifts D (stepOutput Y E) (fun x => boundary x.1)) :=
  qinvEquiv (indexedToGenerators E) (generatorsToLayer E)
    (indexedGeneratorsRet E) (indexedGeneratorsSec E).

Definition indexedLayerLiftsEquiv (E: νFrame Y.1 -> HSet):
  Equiv (StepType Y E)
    (LatchingLifts arity D (stepOutput Y E) (fun x => boundary x.1)) :=
  compEquiv (indexedLayerGeneratorsEquiv E)
    (generatorLiftsEquiv D (stepOutput Y E) (fun x => boundary x.1)).

Lemma indexedLayerLiftsFace (E: νFrame Y.1 -> HSet) (L: StepType Y E)
  (i: FaceDepth n) (x: prefixCell Y.1):
  (indexedLayerLiftsEquiv E L).(lift) None
    (shapeMask (depthFaceWord hunit n i tt)) (upper x)
    = layerAbove Y E L (depth i) (depthBound i) x.
Proof.
  unfold indexedLayerLiftsEquiv; cbn [eqvFun compEquiv].
  rewrite generatorLiftsFace.
  change (layerAbove Y E L (depth i) (depthBound i) (invEq upper (upper x)) =
    layerAbove Y E L (depth i) (depthBound i) x).
  now rewrite retEq.
Defined.

End Comparison.
End DgnLayerOn.
