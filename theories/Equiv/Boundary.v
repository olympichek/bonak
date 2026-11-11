(** Indexed frames as compatible families of their codimension-one faces.
    Reconstruction successively attaches the face layers, using the overlap
    equations to identify the base frame of each new painting. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet Notation LeSProp NatLemmas Equiv.
From Bonak.νSet Require Import Layer νSet.
From Bonak.Equiv Require Import Face.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Painting (A: LayerSig) (V: νSetSig A).
Module Export Faces := FaceOn A V.

Definition Cell {p k} {deps: DepsRestr p k} (ext: DepsRestrExtension p k deps): HSet :=
  {d: mkFrame deps & mkPainting ext d}.

Fixpoint unpackPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): Cell extTop -> Cell ext :=
  match c with
  | ExtChainNil => fun x => x
  | ExtChainCons c => fun x =>
      let y := unpackPainting c x in (y.1.1; (y.1.2; y.2))
  end.

Lemma unpackGetPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (x: Cell ext):
  unpackPainting c (getPainting c x.1 x.2) = x.
Proof.
  revert x; induction c; intro x; cbn; [now reflexivity|].
  now exact (f_equal (fun y: Cell ext =>
    ((y.1.1; (y.1.2; y.2)): Cell (AddRestrDep deps ext)))
    (IHc ((x.1; x.2.1); x.2.2))).
Qed.

Lemma getUnpackPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (x: Cell extTop):
  getPainting c (unpackPainting c x).1 (unpackPainting c x).2 = x.
Proof.
  induction c; cbn; [now reflexivity|]. now exact IHc.
Qed.

Definition paintingChainEquiv {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): Equiv (Cell ext) (Cell extTop) :=
  qinvEquiv (fun x => getPainting c x.1 x.2) (unpackPainting c)
    (unpackGetPainting c) (getUnpackPainting c).

Lemma extChainComposeNil {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): extChainCompose ExtChainNil c = c.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

End Painting.

Module FrameBoundary (A: LayerSig) (V: νSetSig A).
Import A.
Module Export Paintings := Painting A V.

Definition earlierFace {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) (ω: arity)
  (W: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)).(1)):
  Cell (mkDepsCohs dc2Top).(_extraDeps) :=
  let Wc := getFrame (cohsChainNext1 (cohs2ChainCohs c)) W in
  getPainting (cohsChainExt (DepsCohsChainCons (cohs2ChainCohs c)))
    (mkRestrFrame (depsCohs := proj1DepsCohs (mkDepsCohs dc2)) 0 leR_O ω Wc.1)
    (nth Wc.2 ω).

Lemma restrictionBoundary {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) (ε ω: arity)
  (W: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)).(1)):
  νFace (dcTop := dc2Top.(_depsCohs)) DepsCohsChainNil ε (earlierFace c ω W).1
  = νFace (cohs2ChainDepsCohs c) ω
      (mkRestrFrame (depsCohs := mkDepsCohs dc2Top) 0 leR_O ε W).
Proof.
  unfold earlierFace, νFace.
  cbn [cohsChainExt cohsChainNext getFrame].
  rewrite (getPaintingRestr2 (dc2Top := dc2Top) ExtChainNil c ε).
  rewrite <- (cohs2ChainDepsNext c).
  rewrite (getFrameRestr (cohs2ChainCohs c) ε).
  rewrite (mkRestrFrameLenIrr (cohs2ChainLenEq c)
    (Hq := cohsChainLe (cohs2ChainCohs c))
    (Hq' := cohsChainLe (cohs2ChainDepsCohs c)) ε).
  rewrite restrShiftPair, extChainComposeNil. now reflexivity.
Qed.

Lemma cohs2ChainLift {P K} (dc2Top: DepsCohs2 P K)
  {p k} {dc: DepsCohs p k} (c0: DepsCohsChain dc2Top.(_depsCohs) dc):
  {dc2: DepsCohs2 p k &T {c: DepsCohs2Chain dc2Top dc2 &T
    ((dc; c0): {dc0: DepsCohs p k &T DepsCohsChain dc2Top.(_depsCohs) dc0})
      = (dc2.(_depsCohs); cohs2ChainDepsCohs c)}}.
Proof.
  induction c0 as [|p k dc c0 IH].
  - now exact (dc2Top; (DepsCohs2ChainNil; eq_refl)).
  - destruct IH as [dc2 [c e]].
    refine (proj1DepsCohs2 dc2; (DepsCohs2ChainCons c; _)).
    now exact (f_equal (fun z: {dc0: DepsCohs p.+1 k &T
      DepsCohsChain dc2Top.(_depsCohs) dc0} =>
      ((proj1DepsCohs z.1; DepsCohsChainCons z.2):
        {dc0: DepsCohs p k.+1 &T DepsCohsChain dc2Top.(_depsCohs) dc0})) e).
Qed.

Section Attach.
Context {P K} (dc2Top: DepsCohs2 P K).
Context (W: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)).(1)).
Context (t: arity -> Cell (mkDepsCohs dc2Top).(_extraDeps)).
Context (overlap: forall p k (dc2: DepsCohs2 p k)
  (c: DepsCohs2Chain dc2Top dc2) ε ω,
  νFace (dcTop := dc2Top.(_depsCohs)) DepsCohsChainNil ε (earlierFace c ω W).1
  = νFace (cohs2ChainDepsCohs c) ω (t ε).1).

Lemma attachFaceBoundary ε:
  mkRestrFrame (depsCohs := mkDepsCohs dc2Top) 0 leR_O ε W = (t ε).1.
Proof.
  apply νFaceEq. intros p k dc c0 ω.
  destruct (cohs2ChainLift dc2Top c0) as [dc2 [c e]].
  refine (f_equal (fun z: {dc0: DepsCohs p k &T
    DepsCohsChain dc2Top.(_depsCohs) dc0} => νFace z.2 ω
      (mkRestrFrame (depsCohs := mkDepsCohs dc2Top) 0 leR_O ε W)) e • _).
  refine (_ • eq_sym (f_equal (fun z: {dc0: DepsCohs p k &T
    DepsCohsChain dc2Top.(_depsCohs) dc0} => νFace z.2 ω (t ε).1) e)).
  now exact (eq_sym (restrictionBoundary c ε ω W) • overlap p k dc2 c ε ω).
Qed.

Definition attachFaces: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)) :=
  (W; lam (fun ε => rew [mkPainting (mkDepsCohs dc2Top).(_extraDeps)]
    (eq_sym (attachFaceBoundary ε)) in (t ε).2)).

Lemma attachedTopFace ε:
  νFace (dcTop := mkDepsCohs dc2Top) DepsCohsChainNil ε attachFaces = t ε.
Proof.
  unfold attachFaces, νFace; cbn [cohsChainNext getFrame cohsChainExt getPainting].
  rewrite nth_lam.
  generalize (attachFaceBoundary ε).
  destruct (t ε) as [d cp]; cbn. intro e. destruct e. now reflexivity.
Qed.

End Attach.

End FrameBoundary.

Module FaceDepthTheory (A: LayerSig) (V: νSetSig A).
Import A.
Module Export Boundaries := FrameBoundary A V.

Definition ChainPack {P K} (dcTop: DepsCohs P K): Type :=
  {p: nat &T {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}}}.

Definition chainStep {P K} {dcTop: DepsCohs P K} (s: ChainPack dcTop): ChainPack dcTop :=
  (match s.1 as p return
    {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}} -> ChainPack dcTop with
  | 0 => fun t => (0; t)
  | S p => fun t => (p; (t.1.+1; (proj1DepsCohs t.2.1; DepsCohsChainCons t.2.2)))
  end) s.2.

Fixpoint chainDown {P K} (dcTop: DepsCohs P K) j: ChainPack dcTop :=
  match j with
  | 0 => (P; (K; (dcTop; DepsCohsChainNil)))
  | S j => chainStep (chainDown dcTop j)
  end.

Definition chainPrefix {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (s: ChainPack dc): ChainPack dcTop :=
  (s.1; (s.2.1; (s.2.2.1; cohsChainCompose c s.2.2.2))).

Lemma chainPrefixStep {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (s: ChainPack dc):
  chainPrefix c (chainStep s) = chainStep (chainPrefix c s).
Proof. destruct s as [[|q] t]; now reflexivity. Qed.

Lemma chainDownHead {P K} (dcTop: DepsCohs P.+1 K) j:
  chainDown dcTop j.+1 = chainPrefix (DepsCohsChainCons DepsCohsChainNil)
    (chainDown (proj1DepsCohs dcTop) j).
Proof.
  induction j; [now reflexivity|].
  now exact (f_equal chainStep IHj • eq_sym (chainPrefixStep
    (DepsCohsChainCons DepsCohsChainNil) (chainDown (proj1DepsCohs dcTop) j))).
Qed.

Lemma chainDownReify {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc):
  chainDown dcTop (cohsChainLen c) = (p; (k; (dc; c))).
Proof. induction c; cbn [cohsChainLen chainDown]; [now reflexivity|now rewrite IHc]. Qed.

Lemma chainStage {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc): p + cohsChainLen c = P.
Proof. induction c; cbn; [now symmetry; apply plus_n_O|now rewrite <- plus_n_Sm]. Qed.

Definition chainDepth {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc): FaceDepth P :=
  {| depth := cohsChainLen c;
     depthBound := leR_eq_r (chainStage c) (leR_add_l p) |}.

Definition faceAtDepth {P K} (dcTop: DepsCohs P K) j ε
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop))): Cell dcTop.(_extraDeps) :=
  νFace (chainDown dcTop j).2.2.2 ε d.

Lemma faceAtChain {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc) ε d:
  faceAtDepth dcTop (cohsChainLen c) ε d = νFace c ε d.
Proof. unfold faceAtDepth. now rewrite chainDownReify. Qed.

Lemma faceAtDepthNext {P K} (dcTop: DepsCohs P.+1 K) j ε d:
  faceAtDepth dcTop j.+1 ε d =
  getPainting (ExtChainCons ExtChainNil)
    (faceAtDepth (proj1DepsCohs dcTop) j ε d.1).1
    (faceAtDepth (proj1DepsCohs dcTop) j ε d.1).2.
Proof.
  unfold faceAtDepth. rewrite chainDownHead. cbn [chainPrefix].
  now exact (νFaceCompose (DepsCohsChainCons DepsCohsChainNil)
    (chainDown (proj1DepsCohs dcTop) j).2.2.2 ε d).
Qed.

Fixpoint previousCohsChain {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain (proj1DepsCohs (mkDepsCohs dc2Top)) (proj1DepsCohs (mkDepsCohs dc2)) :=
  match c with
  | DepsCohs2ChainNil => DepsCohsChainNil
  | DepsCohs2ChainCons c => DepsCohsChainCons (previousCohsChain c)
  end.

Lemma previousCohsHead {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  cohsChainCompose (DepsCohsChainCons DepsCohsChainNil) (previousCohsChain c)
    = DepsCohsChainCons (cohs2ChainCohs c).
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma previousCohsLength {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  cohsChainLen (previousCohsChain c) = cohsChainLen (cohs2ChainDepsCohs c).
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma previousCohsFrame {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) W:
  getFrame (cohsChainNext1 (cohs2ChainCohs c)) W
    = getFrame (cohsChainNext (previousCohsChain c)) W.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma earlierFaceAsDepth {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) ω W:
  earlierFace c ω W = getPainting (ExtChainCons ExtChainNil)
    (faceAtDepth (proj1DepsCohs (mkDepsCohs dc2Top))
      (cohsChainLen (cohs2ChainDepsCohs c)) ω W).1
    (faceAtDepth (proj1DepsCohs (mkDepsCohs dc2Top))
      (cohsChainLen (cohs2ChainDepsCohs c)) ω W).2.
Proof.
  rewrite <- previousCohsLength, faceAtChain.
  unfold earlierFace, νFace.
  rewrite <- previousCohsHead, cohsChainExtCompose, getPaintingCompose.
  now rewrite previousCohsFrame.
Qed.

End FaceDepthTheory.

Module BoundaryFaces (A: LayerSig) (V: νSetSig A).
Import A.
Module Export Depths := FaceDepthTheory A V.

Definition FaceTuple {P K} (dcTop: DepsCohs P K): HSet :=
  hforall i: FaceDepth P, hforall ε: arity, Cell dcTop.(_extraDeps).

Definition frameFaces {P K} (dcTop: DepsCohs P K)
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop))): FaceTuple dcTop :=
  fun i ε => faceAtDepth dcTop (depth i) ε d.

Definition FaceCompatible {P K} (dc2Top: DepsCohs2 P K)
  (f: FaceTuple (mkDepsCohs dc2Top)): Type :=
  forall p k (dc2Q: DepsCohs2 p k) (c1: DepsCohs2Chain dc2Top dc2Q)
    p' k' (dc2R: DepsCohs2 p' k') (c2: DepsCohs2Chain dc2Q dc2R) ε ω,
    νFace (cohs2ChainDepsCohs c1) ε
      (f (chainDepth (DepsCohsChainCons (cohs2ChainCohs (cohs2ChainCompose c1 c2)))) ω).1
    = νFace (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)) ω
      (f (chainDepth (cohs2ChainCohs c1)) ε).1.

Lemma frameFacesCompatible {P K} (dc2Top: DepsCohs2 P K)
  (d: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top))):
  FaceCompatible dc2Top (frameFaces (mkDepsCohs dc2Top) d).
Proof.
  intros p k dc2Q c1 p' k' dc2R c2 ε ω.
  unfold frameFaces, chainDepth; cbn [depth].
  rewrite 2 faceAtChain. now apply νFaceCoh.
Qed.

Definition shiftFaces {P K} (dcTop: DepsCohs P.+1 K) (f: FaceTuple dcTop):
  FaceTuple (proj1DepsCohs dcTop) :=
  fun i ε => unpackPainting (ExtChainCons ExtChainNil) (f (nextDepth i) ε).

Lemma prefixChainLength {P K} {dcTop: DepsCohs P.+1 K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain (proj1DepsCohs dcTop) dc):
  cohsChainLen (cohsChainCompose (DepsCohsChainCons DepsCohsChainNil) c)
  = (cohsChainLen c).+1.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma cohs2ComposeAssoc {P K} {dcTop: DepsCohs2 P K}
  {p k} {dcQ: DepsCohs2 p k} {p' k'} {dcR: DepsCohs2 p' k'}
  {p'' k''} {dcS: DepsCohs2 p'' k''}
  (a: DepsCohs2Chain dcTop dcQ) (b: DepsCohs2Chain dcQ dcR) (c: DepsCohs2Chain dcR dcS):
  cohs2ChainCompose (cohs2ChainCompose a b) c = cohs2ChainCompose a (cohs2ChainCompose b c).
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma shiftedUpperSlot {P K} {dcTop: DepsCohs2 P.+1 K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain (proj1DepsCohs2 dcTop) dc):
  chainDepth (cohs2ChainCohs (cohs2ChainCompose (DepsCohs2ChainCons DepsCohs2ChainNil) c))
    = nextDepth (chainDepth (cohs2ChainCohs c)).
Proof.
  apply depthEq; cbn. rewrite cohs2ChainCohsCompose.
  now exact (prefixChainLength (dcTop := mkDepsCohs dcTop) (cohs2ChainCohs c)).
Qed.

Lemma shiftedEarlierSlot {P K} {dcTop: DepsCohs2 P.+1 K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain (proj1DepsCohs2 dcTop) dc):
  chainDepth (DepsCohsChainCons (cohs2ChainCohs
    (cohs2ChainCompose (DepsCohs2ChainCons DepsCohs2ChainNil) c)))
    = nextDepth (chainDepth (DepsCohsChainCons (cohs2ChainCohs c))).
Proof.
  apply depthEq; cbn. rewrite cohs2ChainCohsCompose.
  now exact (f_equal S (prefixChainLength (dcTop := mkDepsCohs dcTop) (cohs2ChainCohs c))).
Qed.

Lemma unpackFaceStep {P K} (dcTop: DepsCohs2 P.+1 K)
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain (proj1DepsCohs dcTop.(_depsCohs)) dc)
  ε (t: Cell (mkDepsCohs dcTop).(_extraDeps)):
  getPainting (ExtChainCons ExtChainNil)
    (νFace c ε (unpackPainting (ExtChainCons ExtChainNil) t).1).1
    (νFace c ε (unpackPainting (ExtChainCons ExtChainNil) t).1).2
  = νFace (cohsChainCompose (DepsCohsChainCons DepsCohsChainNil) c) ε t.1.
Proof. now exact (eq_sym (νFaceCompose (DepsCohsChainCons DepsCohsChainNil) c ε t.1)). Qed.

Lemma shiftFacesCompatible {P K} (dcTop: DepsCohs2 P.+1 K)
  (f: FaceTuple (mkDepsCohs dcTop)) (H: FaceCompatible dcTop f):
  FaceCompatible (proj1DepsCohs2 dcTop) (shiftFaces (mkDepsCohs dcTop) f).
Proof.
  intros p k dcQ c1 p' k' dcR c2 ε ω.
  apply (eqvInj (paintingChainEquiv
    (extTop := dcTop.(_depsCohs).(_extraDeps)) (ExtChainCons ExtChainNil))).
  cbn [eqvFun paintingChainEquiv qinvEquiv]. unfold shiftFaces.
  rewrite 2 unpackFaceStep.
  pose proof (H p k dcQ
    (cohs2ChainCompose (DepsCohs2ChainCons DepsCohs2ChainNil) c1)
    p' k' dcR c2 ε ω) as h.
  rewrite cohs2ComposeAssoc, shiftedEarlierSlot, shiftedUpperSlot in h.
  rewrite 3 cohs2ChainDepsCohsCompose in h.
  rewrite cohs2ChainDepsCohsCompose. now exact h.
Qed.

End BoundaryFaces.

Module ReconstructFrame (A: LayerSig) (V: νSetSig A).
Import A.
Module Export Faces := BoundaryFaces A V.

Definition Realization {P K} (dc: DepsCohs P K) (f: FaceTuple dc): Type :=
  {d: mkFrame (mkDepsRestr (depsCohs := dc)) &T forall i ε, frameFaces dc d i ε = f i ε}.

Definition zeroFrame {K} (dc: DepsCohs 0 K) (f: FaceTuple dc):
  mkFrame (mkDepsRestr (depsCohs := dc)) :=
  (tt; lam (fun ε => rew [mkPainting dc.(_extraDeps)]
    (eq_sym (hunit_ext tt (f (firstDepth 0) ε).1)) in (f (firstDepth 0) ε).2)).

Lemma zeroFrameFace {K} (dc: DepsCohs 0 K) (f: FaceTuple dc) i ε:
  frameFaces dc (zeroFrame dc f) i ε = f i ε.
Proof.
  destruct i as [[|j] h]; [|destruct (leR_O_contra h)].
  change (frameFaces dc (zeroFrame dc f) (firstDepth 0) ε = f (firstDepth 0) ε).
  unfold frameFaces, faceAtDepth, zeroFrame, νFace.
  cbn [depth chainDown cohsChainNext getFrame cohsChainExt getPainting].
  rewrite nth_lam.
  generalize (hunit_ext tt (f (firstDepth 0) ε).1).
  destruct (f (firstDepth 0) ε) as [[] cp]; cbn. intro e.
  replace e with (@eq_refl unit tt) by apply hunit.(UIP). now reflexivity.
Qed.

Definition zeroRealization {K} (dc: DepsCohs 0 K) (f: FaceTuple dc): Realization dc f :=
  (zeroFrame dc f; zeroFrameFace dc f).

Lemma cohs2ComposeNil {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc):
  cohs2ChainCompose DepsCohs2ChainNil c = c.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma earlierSlot {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc):
  nextDepth (chainDepth (previousCohsChain c))
  = chainDepth (DepsCohsChainCons (cohs2ChainCohs c)).
Proof.
  apply depthEq; cbn. rewrite previousCohsLength, cohs2ChainLenEq. now reflexivity.
Qed.

Section Finish.
Context {P K} (dc: DepsCohs2 P K) (f: FaceTuple (mkDepsCohs dc)).
Context (H: FaceCompatible dc f).
Context (r: Realization (proj1DepsCohs (mkDepsCohs dc)) (shiftFaces (mkDepsCohs dc) f)).

Lemma earlierFaceRealized {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain dc dc2) ω:
  earlierFace c ω r.1 = f (chainDepth (DepsCohsChainCons (cohs2ChainCohs c))) ω.
Proof.
  rewrite earlierFaceAsDepth, <- previousCohsLength.
  refine (f_equal (fun x: Cell (proj1DepsCohs (mkDepsCohs dc)).(_extraDeps) =>
    getPainting (ExtChainCons ExtChainNil) x.1 x.2)
    (r.2 (chainDepth (previousCohsChain c)) ω) • _).
  now exact (getUnpackPainting (ExtChainCons ExtChainNil)
    (f (nextDepth (chainDepth (previousCohsChain c))) ω)
    • f_equal (fun i => f i ω) (earlierSlot c)).
Qed.

Lemma finishingOverlap p k (dc2: DepsCohs2 p k) (c: DepsCohs2Chain dc dc2) ε ω:
  νFace (dcTop := dc.(_depsCohs)) DepsCohsChainNil ε (earlierFace c ω r.1).1
  = νFace (cohs2ChainDepsCohs c) ω (f (firstDepth P.+1) ε).1.
Proof.
  rewrite earlierFaceRealized.
  pose proof (H P K dc DepsCohs2ChainNil p k dc2 c ε ω) as h.
  rewrite cohs2ComposeNil in h. now exact h.
Qed.

Definition finishedFrame: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc)) :=
  attachFaces dc r.1 (f (firstDepth P.+1)) finishingOverlap.

Lemma finishedFrameFace i ε: frameFaces (mkDepsCohs dc) finishedFrame i ε = f i ε.
Proof.
  destruct i as [[|j] h].
  - now exact (attachedTopFace dc r.1 (f (firstDepth P.+1)) finishingOverlap ε).
  - unfold frameFaces; cbn [depth]. rewrite faceAtDepthNext.
    refine (f_equal (fun x: Cell (proj1DepsCohs (mkDepsCohs dc)).(_extraDeps) =>
      getPainting (ExtChainCons ExtChainNil) x.1 x.2)
      (r.2 {| depth := j; depthBound := ⇓ h |} ε) • _).
    now apply getUnpackPainting.
Qed.

Definition finishRealization: Realization (mkDepsCohs dc) f :=
  (finishedFrame; finishedFrameFace).

End Finish.

Fixpoint reconstructFrame (P: nat): forall K (dc: DepsCohs2 P K)
  (f: FaceTuple (mkDepsCohs dc)), FaceCompatible dc f -> Realization (mkDepsCohs dc) f :=
  match P with
  | 0 => fun K dc f H => finishRealization dc f H
      (zeroRealization (proj1DepsCohs (mkDepsCohs dc)) (shiftFaces (mkDepsCohs dc) f))
  | S P => fun K dc f H => finishRealization dc f H
      (reconstructFrame P K.+1 (proj1DepsCohs2 dc) (shiftFaces (mkDepsCohs dc) f)
        (shiftFacesCompatible dc f H))
  end.

Definition IndexedFaceBoundary {P K} (dc: DepsCohs2 P K): Type :=
  {f: FaceTuple (mkDepsCohs dc) &T FaceCompatible dc f}.

Lemma faceCompatibleProp {P K} (dc: DepsCohs2 P K)
  (f: FaceTuple (mkDepsCohs dc)) (H H': FaceCompatible dc f): H = H'.
Proof.
  repeat (apply functional_extensionality_dep; intro).
  now apply (Cell dc.(_depsCohs).(_extraDeps)).(UIP).
Qed.

Definition frameBoundary {P K} (dc: DepsCohs2 P K)
  (d: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc))): IndexedFaceBoundary dc :=
  (frameFaces (mkDepsCohs dc) d; frameFacesCompatible dc d).

Definition boundaryFrame {P K} (dc: DepsCohs2 P K) (b: IndexedFaceBoundary dc):
  mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc)) :=
  (reconstructFrame P K dc b.1 b.2).1.

Lemma boundaryFrameRet {P K} (dc: DepsCohs2 P K) d:
  boundaryFrame dc (frameBoundary dc d) = d.
Proof.
  apply νFaceEq; intros p k dc' c ε.
  rewrite <- 2 faceAtChain.
  now exact ((reconstructFrame P K dc (frameFaces (mkDepsCohs dc) d)
    (frameFacesCompatible dc d)).2 (chainDepth c) ε).
Qed.

Lemma boundaryFrameSec {P K} (dc: DepsCohs2 P K) b:
  frameBoundary dc (boundaryFrame dc b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro ε.
    now exact ((reconstructFrame P K dc b.1 b.2).2 i ε).
  - now apply faceCompatibleProp.
Qed.

Definition indexedFaceBoundaryEquiv {P K} (dc: DepsCohs2 P K):
  Equiv (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc))) (IndexedFaceBoundary dc) :=
  qinvEquiv (frameBoundary dc) (boundaryFrame dc) (boundaryFrameRet dc) (boundaryFrameSec dc).

Definition prefixDepsCohs2 {n} (X: (νSetAt n.+2).(prefix)): DepsCohs2 n 0 := {|
  _depsCohs := prefixDepsCohs X.1;
  _extraDepsCohs := TopCohDep X.2;
  _cohPaintings := (νDataAt X.1.1).(cohPaintings) X.1.2 X.2;
|}.

End ReconstructFrame.

Module ChainPairs (A: LayerSig) (V: νSetSig A).
Module Export Frames := ReconstructFrame A V.
Definition IndexedChainPack {P K} (dc: DepsCohs2 P K): Type :=
  {p: nat &T {k: nat &T {d: DepsCohs2 p k &T DepsCohs2Chain dc d}}}.
Definition indexedChainLength {P K} {dc: DepsCohs2 P K} (c: IndexedChainPack dc): nat :=
  cohsChainLen (cohs2ChainDepsCohs c.2.2.2).
Definition prependIndexedChain {P K} (dc: DepsCohs2 P.+1 K)
  (c: IndexedChainPack (proj1DepsCohs2 dc)): IndexedChainPack dc :=
  (c.1; (c.2.1; (c.2.2.1; cohs2ChainCompose (DepsCohs2ChainCons DepsCohs2ChainNil) c.2.2.2))).
Lemma prependIndexedChainLength {P K} (dc: DepsCohs2 P.+1 K) c:
  indexedChainLength (prependIndexedChain dc c) = (indexedChainLength c).+1.
Proof.
  unfold indexedChainLength, prependIndexedChain; cbn.
  rewrite cohs2ChainDepsCohsCompose. now apply prefixChainLength.
Qed.
Fixpoint indexedChainAtDepth P: forall K (dc: DepsCohs2 P K) (i: FaceDepth P),
  {c: IndexedChainPack dc &T indexedChainLength c = depth i}.
Proof.
  destruct P as [|P]; intros K dc [[|i] hi].
  - now exact ((0; (K; (dc; DepsCohs2ChainNil))); eq_refl).
  - destruct (leR_O_contra hi).
  - now exact ((P.+1; (K; (dc; DepsCohs2ChainNil))); eq_refl).
  - pose (c := indexedChainAtDepth P K.+1 (proj1DepsCohs2 dc)
      {| depth := i; depthBound := ⇓ hi |}).
    now exact (prependIndexedChain dc c.1; prependIndexedChainLength dc c.1 • f_equal S c.2).
Defined.
Definition IndexedChainPair {P K} (dc: DepsCohs2 P K): Type :=
  {c: IndexedChainPack dc &T IndexedChainPack c.2.2.1}.
Definition joinIndexedChains {P K} {dc: DepsCohs2 P K} (c: IndexedChainPair dc): IndexedChainPack dc :=
  (c.2.1; (c.2.2.1; (c.2.2.2.1; cohs2ChainCompose c.1.2.2.2 c.2.2.2.2))).
Definition prependIndexedPair {P K} (dc: DepsCohs2 P.+1 K)
  (c: IndexedChainPair (proj1DepsCohs2 dc)): IndexedChainPair dc :=
  (prependIndexedChain dc c.1; c.2).
Lemma prependIndexedPairJoin {P K} (dc: DepsCohs2 P.+1 K) c:
  joinIndexedChains (prependIndexedPair dc c) = prependIndexedChain dc (joinIndexedChains c).
Proof.
  unfold joinIndexedChains, prependIndexedPair, prependIndexedChain; cbn.
  now rewrite cohs2ComposeAssoc.
Qed.
Fixpoint indexedPairAtDepth P: forall K (dc: DepsCohs2 P K)
  (i j: FaceDepth P), depth i <= depth j ->
  {c: IndexedChainPair dc &T ((indexedChainLength c.1 = depth i) *
    (indexedChainLength (joinIndexedChains c) = depth j))%type}.
Proof.
  destruct P as [|P]; intros K dc [[|i] hi] [[|j] hj] hij;
    try (destruct (leR_O_contra hi)); try (destruct (leR_O_contra hj));
    try (destruct (leR_O_contra hij)).
  - now exact (((0; (K; (dc; DepsCohs2ChainNil))); (0; (K; (dc; DepsCohs2ChainNil)))); (eq_refl, eq_refl)).
  - now exact (((P.+1; (K; (dc; DepsCohs2ChainNil))); (P.+1; (K; (dc; DepsCohs2ChainNil)))); (eq_refl, eq_refl)).
  - pose (c := indexedChainAtDepth P.+1 K dc {| depth := j.+1; depthBound := hj |}).
    refine (((P.+1; (K; (dc; DepsCohs2ChainNil))); c.1); (eq_refl, _)).
    unfold joinIndexedChains, indexedChainLength; cbn. rewrite cohs2ComposeNil. now exact c.2.
  - pose (c := indexedPairAtDepth P K.+1 (proj1DepsCohs2 dc)
      {| depth := i; depthBound := ⇓ hi |} {| depth := j; depthBound := ⇓ hj |} (⇓ hij)).
    refine (prependIndexedPair dc c.1; (_, _)).
    + now exact (prependIndexedChainLength dc c.1.1 • f_equal S (fst c.2)).
    + rewrite prependIndexedPairJoin, prependIndexedChainLength.
      now exact (f_equal S (snd c.2)).
Defined.
Lemma indexedChainComposeLe {P K} {dc: DepsCohs2 P K}
  {p k} {d: DepsCohs2 p k} {p' k'} {d': DepsCohs2 p' k'}
  (c: DepsCohs2Chain dc d) (c': DepsCohs2Chain d d'):
  cohsChainLen (cohs2ChainDepsCohs c) <= cohsChainLen (cohs2ChainDepsCohs (cohs2ChainCompose c c')).
Proof. induction c'; cbn; [now exact leR_refl|now exact (↑ IHc')]. Qed.
End ChainPairs.
