(** Face functors derived from the recursive frame and painting decomposition. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet LeSProp Notation.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category Require Import FunctorAlgebra.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module FaceOn (A: LayerSig) (S: νStrictGpdSig A).
Import A.
Module Export Core := S.

Inductive DepsChain {P K} (depsTop: DepsRestr P K):
  forall {p k}, DepsRestr p k -> Type :=
| DepsChainNil: DepsChain depsTop depsTop
| DepsChainCons {p k} {deps: DepsRestr p.+1 k}:
    DepsChain depsTop deps -> DepsChain depsTop deps.(1).

Arguments DepsChainNil {P K depsTop}.
Arguments DepsChainCons {P K depsTop p k deps} _.

Inductive ExtChain {P K} {depsTop: DepsRestr P K}
  (extTop: DepsRestrExtension P K depsTop):
  forall {p k} {deps: DepsRestr p k}, DepsRestrExtension p k deps -> Type :=
| ExtChainNil: ExtChain extTop extTop
| ExtChainCons {p k} {deps: DepsRestr p.+1 k}
    {ext: DepsRestrExtension p.+1 k deps}:
    ExtChain extTop ext -> ExtChain extTop (AddRestrDep deps ext).

Arguments ExtChainNil {P K depsTop extTop}.
Arguments ExtChainCons {P K depsTop extTop p k deps ext} _.

Inductive DepsCohsChain {P K} (dcTop: DepsCohs P K):
  forall {p k}, DepsCohs p k -> Type :=
| DepsCohsChainNil: DepsCohsChain dcTop dcTop
| DepsCohsChainCons {p k} {dc: DepsCohs p.+1 k}:
    DepsCohsChain dcTop dc -> DepsCohsChain dcTop (proj1DepsCohs dc).

Arguments DepsCohsChainNil {P K dcTop}.
Arguments DepsCohsChainCons {P K dcTop p k dc} _.

Inductive DepsCohs2Chain {P K} (dc2Top: DepsCohs2 P K):
  forall {p k}, DepsCohs2 p k -> Type :=
| DepsCohs2ChainNil: DepsCohs2Chain dc2Top dc2Top
| DepsCohs2ChainCons {p k} {dc2: DepsCohs2 p.+1 k}:
    DepsCohs2Chain dc2Top dc2 -> DepsCohs2Chain dc2Top (proj1DepsCohs2 dc2).

Arguments DepsCohs2ChainNil {P K dc2Top}.
Arguments DepsCohs2ChainCons {P K dc2Top p k dc2} _.

Fixpoint chainCompose {P K} {depsTop: DepsRestr P K}
  {p k} {depsMid: DepsRestr p k} {p' k'} {deps: DepsRestr p' k'}
  (c1: DepsChain depsTop depsMid) (c2: DepsChain depsMid deps):
  DepsChain depsTop deps :=
  match c2 with
  | DepsChainNil => c1
  | DepsChainCons c2' => DepsChainCons (chainCompose c1 c2')
  end.

Fixpoint extChainCompose {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {depsMid: DepsRestr p k} {extMid: DepsRestrExtension p k depsMid}
  {p' k'} {deps: DepsRestr p' k'} {ext: DepsRestrExtension p' k' deps}
  (c1: ExtChain extTop extMid) (c2: ExtChain extMid ext):
  ExtChain extTop ext :=
  match c2 with
  | ExtChainNil => c1
  | ExtChainCons c2' => ExtChainCons (extChainCompose c1 c2')
  end.

Fixpoint extChainDeps {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): DepsChain depsTop deps :=
  match c with
  | ExtChainNil => DepsChainNil
  | ExtChainCons c' => DepsChainCons (extChainDeps c')
  end.

Fixpoint cohsChainExt {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  ExtChain dcTop.(_extraDeps) dc.(_extraDeps) :=
  match c with
  | DepsCohsChainNil => ExtChainNil
  | DepsCohsChainCons c' => ExtChainCons (cohsChainExt c')
  end.

Fixpoint cohsChainNext {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  DepsChain (mkDepsRestr (depsCohs := dcTop)) (mkDepsRestr (depsCohs := dc)) :=
  match c with
  | DepsCohsChainNil => DepsChainNil
  | DepsCohsChainCons c' => DepsChainCons (cohsChainNext c')
  end.

Fixpoint cohsChainDeps {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): DepsChain dcTop.(_deps) dc.(_deps) :=
  match c with
  | DepsCohsChainNil => DepsChainNil
  | DepsCohsChainCons c' => DepsChainCons (cohsChainDeps c')
  end.

Fixpoint cohsChainNext1 {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  DepsChain (mkDepsRestr (depsCohs := dcTop)).(1)
            (mkDepsRestr (depsCohs := dc)).(1) :=
  match c with
  | DepsCohsChainNil => DepsChainNil
  | DepsCohsChainCons c' => DepsChainCons (cohsChainNext1 c')
  end.

Fixpoint cohsChainCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (c1: DepsCohsChain dcTop dcMid) (c2: DepsCohsChain dcMid dc):
  DepsCohsChain dcTop dc :=
  match c2 with
  | DepsCohsChainNil => c1
  | DepsCohsChainCons c2' => DepsCohsChainCons (cohsChainCompose c1 c2')
  end.

Fixpoint cohsChainLen {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): nat :=
  match c with
  | DepsCohsChainNil => 0
  | DepsCohsChainCons c' => (cohsChainLen c').+1
  end.

Lemma cohsChainStage {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): p + cohsChainLen c = P.
Proof.
  induction c as [|p k dc c IH]; cbn [cohsChainLen].
  - now symmetry; apply plus_n_O.
  - rewrite <- plus_n_Sm. now exact IH.
Defined.

Fixpoint cohsChainLe {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): cohsChainLen c <= k :=
  match c with
  | DepsCohsChainNil => leR_O
  | DepsCohsChainCons c' => ⇑ (cohsChainLe c')
  end.

Fixpoint cohs2ChainCohs {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain (mkDepsCohs dc2Top) (mkDepsCohs dc2) :=
  match c with
  | DepsCohs2ChainNil => DepsCohsChainNil
  | DepsCohs2ChainCons c' => DepsCohsChainCons (cohs2ChainCohs c')
  end.

Fixpoint cohs2ChainDepsCohs {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain dc2Top.(_depsCohs) dc2.(_depsCohs) :=
  match c with
  | DepsCohs2ChainNil => DepsCohsChainNil
  | DepsCohs2ChainCons c' => DepsCohsChainCons (cohs2ChainDepsCohs c')
  end.

Fixpoint cohs2ChainCompose {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Mid: DepsCohs2 p k} {p' k'} {dc2: DepsCohs2 p' k'}
  (c1: DepsCohs2Chain dc2Top dc2Mid) (c2: DepsCohs2Chain dc2Mid dc2):
  DepsCohs2Chain dc2Top dc2 :=
  match c2 with
  | DepsCohs2ChainNil => c1
  | DepsCohs2ChainCons c2' => DepsCohs2ChainCons (cohs2ChainCompose c1 c2')
  end.

Lemma cohsChainExtCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (a: DepsCohsChain dcTop dcMid) (b: DepsCohsChain dcMid dc):
  cohsChainExt (cohsChainCompose a b) =
  extChainCompose (cohsChainExt a) (cohsChainExt b).
Proof.
  induction b; cbn; [now reflexivity | now rewrite IHb].
Defined.

Lemma cohsChainNextCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (a: DepsCohsChain dcTop dcMid) (b: DepsCohsChain dcMid dc):
  cohsChainNext (cohsChainCompose a b) =
  chainCompose (cohsChainNext a) (cohsChainNext b).
Proof.
  induction b; cbn; [now reflexivity | now rewrite IHb].
Defined.

Lemma extChainDepsExt {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  extChainDeps (cohsChainExt c) = cohsChainDeps c.
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Lemma cohs2ChainDepsNext {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  cohsChainDeps (cohs2ChainCohs c) = cohsChainNext (cohs2ChainDepsCohs c).
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Lemma cohs2ChainCohsCompose {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Mid: DepsCohs2 p k} {p' k'} {dc2: DepsCohs2 p' k'}
  (c1: DepsCohs2Chain dc2Top dc2Mid) (c2: DepsCohs2Chain dc2Mid dc2):
  cohs2ChainCohs (cohs2ChainCompose c1 c2) =
  cohsChainCompose (cohs2ChainCohs c1) (cohs2ChainCohs c2).
Proof.
  induction c2; cbn; [now reflexivity | now rewrite IHc2].
Defined.

Lemma cohs2ChainDepsCohsCompose {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Mid: DepsCohs2 p k} {p' k'} {dc2: DepsCohs2 p' k'}
  (c1: DepsCohs2Chain dc2Top dc2Mid) (c2: DepsCohs2Chain dc2Mid dc2):
  cohs2ChainDepsCohs (cohs2ChainCompose c1 c2) =
  cohsChainCompose (cohs2ChainDepsCohs c1) (cohs2ChainDepsCohs c2).
Proof.
  induction c2; cbn; [now reflexivity | now rewrite IHc2].
Defined.

Lemma cohs2ChainLenEq {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  cohsChainLen (cohs2ChainCohs c) = cohsChainLen (cohs2ChainDepsCohs c).
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Fixpoint getFrame {P K} {depsTop: DepsRestr P K} {p k} {deps: DepsRestr p k}
  (c: DepsChain depsTop deps): Functor (mkFrame depsTop) (mkFrame deps) :=
  match c with
  | DepsChainNil => idFunctor _
  | DepsChainCons c' => getFrame c' ⨟ᶠ proj _
  end.

Fixpoint getPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): Functor (total (mkPainting ext)) (total (mkPainting extTop)) :=
  match c with
  | ExtChainNil => idFunctor _
  | @ExtChainCons _ _ _ _ _ _ deps ext c' =>
      totalAssoc (mkLayer deps.(_restrFrames)) (mkPainting ext) ⨟ᶠ getPainting c'
  end.

Lemma getFrameCompose {P K} {depsTop: DepsRestr P K}
  {p k} {depsMid: DepsRestr p k} {p' k'} {deps: DepsRestr p' k'}
  (c1: DepsChain depsTop depsMid) (c2: DepsChain depsMid deps):
  getFrame c1 ⨟ᶠ getFrame c2 = getFrame (chainCompose c1 c2).
Proof.
  induction c2.
  - now apply functorIdR.
  - cbn [getFrame chainCompose]. now rewrite <- functorAssocEq, IHc2.
Defined.

Lemma getPaintingCompose {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {depsMid: DepsRestr p k} {extMid: DepsRestrExtension p k depsMid}
  {p' k'} {deps: DepsRestr p' k'} {ext: DepsRestrExtension p' k' deps}
  (a: ExtChain extTop extMid) (b: ExtChain extMid ext):
  getPainting (extChainCompose a b) = getPainting b ⨟ᶠ getPainting a.
Proof.
  induction b.
  - symmetry. now apply functorIdL.
  - cbn [getPainting extChainCompose]. now rewrite IHb, functorAssocEq.
Defined.

Lemma getFrameGetPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext):
  getPainting c ⨟ᶠ proj (mkPainting extTop) ⨟ᶠ getFrame (extChainDeps c) =
  proj (mkPainting ext).
Proof.
  induction c.
  - rewrite functorIdL. now apply functorIdR.
  - transitivity ((totalAssoc (mkLayer deps.(_restrFrames)) (mkPainting ext0) ⨟ᶠ
      (getPainting c ⨟ᶠ proj (mkPainting extTop) ⨟ᶠ getFrame (extChainDeps c))) ⨟ᶠ
      proj (mkLayer deps.(_restrFrames))).
    + apply (functorEqPath (mkFrame deps.(1)).(hsetGroupoidUIP)).
      unshelve econstructor; now intros.
    + rewrite IHc. apply (functorEqPath (mkFrame deps.(1)).(hsetGroupoidUIP)).
      unshelve econstructor; now intros.
Defined.

Definition νHead {p k} (dc: DepsCohs p k) (ε: arity):
  Functor (mkFrame (mkDepsRestr (depsCohs := dc))) (total (mkPainting dc.(_extraDeps))) :=
  layerProj (mkPainting dc.(_extraDeps)) (fun ω => mkRestrFrame (depsCohs := dc) 0 leR_O ω) ε.

Lemma mkRestrFrameProj {p k} (dc: DepsCohs p.+1 k) q (Hq: q <= k) ε:
  mkRestrFrame (depsCohs := dc) q Hq ε ⨟ᶠ proj (mkLayer dc.(_deps).(_restrFrames)) =
  proj (mkLayer (mkDepsRestr (depsCohs := dc)).(1).(_restrFrames)) ⨟ᶠ
    mkRestrFrame (depsCohs := proj1DepsCohs dc) q.+1 (⇑ Hq) ε.
Proof.
  now apply (functorEqPath (mkFrame dc.(_deps).(1)).(hsetGroupoidUIP)), totalProj.
Defined.

Lemma getFrameRestr {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) ε:
  mkRestrFrame (depsCohs := dcTop) 0 leR_O ε ⨟ᶠ getFrame (cohsChainDeps c) =
  getFrame (cohsChainNext1 c) ⨟ᶠ
    mkRestrFrame (depsCohs := dc) (cohsChainLen c) (cohsChainLe c) ε.
Proof.
  induction c.
  - rewrite functorIdL. now apply functorIdR.
  - cbn [cohsChainDeps cohsChainNext1 cohsChainLen cohsChainLe getFrame].
    rewrite <- functorAssocEq, IHc, functorAssocEq, mkRestrFrameProj.
    now rewrite functorAssocEq.
Defined.

Lemma getFrameNext1 {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  getFrame (cohsChainNext c) ⨟ᶠ proj (mkLayer (mkDepsRestr (depsCohs := dc)).(_restrFrames)) =
  proj (mkLayer (mkDepsRestr (depsCohs := dcTop)).(_restrFrames)) ⨟ᶠ
    getFrame (cohsChainNext1 c).
Proof.
  induction c.
  - rewrite functorIdL. now rewrite functorIdR.
  - cbn [cohsChainNext cohsChainNext1 getFrame].
    rewrite <- functorAssocEq, IHc, functorAssocEq.
    apply (functorEqPath (mkFrame (mkDepsRestr (depsCohs := proj1DepsCohs dc)).(1)).(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
Defined.

Lemma mkRestrFrameLenIrr {p k} {dc: DepsCohs p k} {q q'} (e: q = q')
  {Hq: q <= k} {Hq': q' <= k} ε:
  mkRestrFrame (depsCohs := dc) q Hq ε = mkRestrFrame (depsCohs := dc) q' Hq' ε.
Proof. now destruct e. Defined.

Lemma restrShiftPair {p k} (dc2: DepsCohs2 p k) q (Hq: q <= k) ε ω:
  νHead (proj1DepsCohs (mkDepsCohs dc2)) ω ⨟ᶠ
    totalMap (mkRestrPainting dc2.(_extraDepsCohs) q Hq ε) =
  mkRestrFrame (depsCohs := mkDepsCohs dc2) q Hq ε ⨟ᶠ νHead dc2.(_depsCohs) ω.
Proof.
  apply (functorEqPath (total (mkPainting dc2.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
  now apply feqSym, layerFace.
Defined.

Lemma getPaintingRestr2 {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) ε:
  getPainting (ExtChainCons (cohsChainExt (cohs2ChainCohs c))) ⨟ᶠ
    proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ νHead dc2Top.(_depsCohs) ε =
  totalMap (mkRestrPainting dc2.(_extraDepsCohs)
    (cohsChainLen (cohs2ChainDepsCohs c)) (cohsChainLe (cohs2ChainDepsCohs c)) ε) ⨟ᶠ
    getPainting (cohsChainExt (cohs2ChainDepsCohs c)).
Proof.
  induction c.
  - cbn [cohs2ChainCohs cohsChainExt cohs2ChainDepsCohs cohsChainLen cohsChainLe].
    rewrite functorIdR. unfold νHead. symmetry.
    transitivity (totalMap (sigmaFst _ (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)))) ⨟ᶠ
      layerProj (mkPainting dc2Top.(_depsCohs).(_extraDeps))
        (fun ω => mkRestrFrame (depsCohs := dc2Top.(_depsCohs)) 0 leR_O ω) ε).
    + now apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)), layerHeadTotal.
    + apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
      unshelve econstructor; now intros.
  - transitivity (totalAssoc _ _ ⨟ᶠ
      (getPainting (ExtChainCons (cohsChainExt (cohs2ChainCohs c))) ⨟ᶠ
       proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ νHead dc2Top.(_depsCohs) ε)).
    + apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
      unshelve econstructor; now intros.
    + rewrite IHc.
      apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
      unshelve econstructor; now intros.
Defined.

Definition νFace {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (ε: arity):
  Functor (mkFrame (mkDepsRestr (depsCohs := dcTop))) (total (mkPainting dcTop.(_extraDeps))) :=
  getFrame (cohsChainNext c) ⨟ᶠ
    νHead dc ε ⨟ᶠ
    getPainting (cohsChainExt c).

Lemma νFaceCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (a: DepsCohsChain dcTop dcMid) (b: DepsCohsChain dcMid dc) (ε: arity):
  νFace (cohsChainCompose a b) ε =
  getFrame (cohsChainNext a) ⨟ᶠ νFace b ε ⨟ᶠ getPainting (cohsChainExt a).
Proof.
  unfold νFace. rewrite cohsChainExtCompose, cohsChainNextCompose.
  rewrite <- getFrameCompose, getPaintingCompose.
  apply (functorEqPath (total (mkPainting dcTop.(_extraDeps))).(hsetGroupoidUIP)).
  unshelve econstructor; now intros.
Defined.

Lemma νHeadProj {p k} (dc: DepsCohs p k) ε:
  νHead dc ε ⨟ᶠ proj (mkPainting dc.(_extraDeps)) =
  proj (mkLayer (mkDepsRestr (depsCohs := dc)).(_restrFrames)) ⨟ᶠ
    mkRestrFrame (depsCohs := dc) 0 leR_O ε.
Proof.
  unfold νHead, layerProj, reindexTotal.
  rewrite functorAssocEq.
  rewrite (functorEqPath (mkFrame dc.(_deps)).(hsetGroupoidUIP)
    (totalProj (forgetPull (mkPainting dc.(_extraDeps))
      (mkRestrFrame (depsCohs := dc) 0 leR_O ε)))).
  rewrite <- functorAssocEq.
  now rewrite (functorEqPath (mkFrame (mkDepsRestr (depsCohs := dc)).(1)).(hsetGroupoidUIP) (nthProj _ ε)).
Defined.

Lemma νFaceProjection {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (a: DepsCohsChain dcTop dcMid) (b: DepsCohsChain dcMid dc) ε:
  νFace (cohsChainCompose a b) ε ⨟ᶠ proj (mkPainting dcTop.(_extraDeps)) ⨟ᶠ
    getFrame (cohsChainDeps a) =
  getFrame (cohsChainNext a) ⨟ᶠ νFace b ε ⨟ᶠ proj (mkPainting dcMid.(_extraDeps)).
Proof.
  rewrite νFaceCompose.
  transitivity ((getFrame (cohsChainNext a) ⨟ᶠ νFace b ε) ⨟ᶠ
    (getPainting (cohsChainExt a) ⨟ᶠ proj (mkPainting dcTop.(_extraDeps)) ⨟ᶠ
      getFrame (cohsChainDeps a))).
  - apply (functorEqPath (mkFrame dcMid.(_deps)).(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
  - rewrite <- extChainDepsExt, getFrameGetPainting. now reflexivity.
Defined.

Lemma νFaceCohHead {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) ε ω:
  νFace (DepsCohsChainCons (cohs2ChainCohs c)) ω ⨟ᶠ
    proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ νHead dc2Top.(_depsCohs) ε =
  νHead (mkDepsCohs dc2Top) ε ⨟ᶠ proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
    νFace (cohs2ChainDepsCohs c) ω.
Proof.
  unfold νFace at 1.
  transitivity ((getFrame (cohsChainNext (cohs2ChainCohs c)) ⨟ᶠ
      proj (mkLayer (mkDepsRestr (depsCohs := mkDepsCohs dc2)).(_restrFrames)) ⨟ᶠ
      νHead (proj1DepsCohs (mkDepsCohs dc2)) ω) ⨟ᶠ
    (getPainting (ExtChainCons (cohsChainExt (cohs2ChainCohs c))) ⨟ᶠ
      proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ νHead dc2Top.(_depsCohs) ε)).
  { apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  rewrite getPaintingRestr2.
  transitivity ((getFrame (cohsChainNext (cohs2ChainCohs c)) ⨟ᶠ
      proj (mkLayer (mkDepsRestr (depsCohs := mkDepsCohs dc2)).(_restrFrames))) ⨟ᶠ
    (νHead (proj1DepsCohs (mkDepsCohs dc2)) ω ⨟ᶠ
      totalMap (mkRestrPainting dc2.(_extraDepsCohs)
        (cohsChainLen (cohs2ChainDepsCohs c)) (cohsChainLe (cohs2ChainDepsCohs c)) ε)) ⨟ᶠ
    getPainting (cohsChainExt (cohs2ChainDepsCohs c))).
  { apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  rewrite restrShiftPair, getFrameNext1.
  rewrite <- (mkRestrFrameLenIrr (cohs2ChainLenEq c)
    (Hq := cohsChainLe (cohs2ChainCohs c)) (Hq' := cohsChainLe (cohs2ChainDepsCohs c)) ε).
  transitivity ((proj (mkLayer
      (paintings := (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)).(_paintings))
      (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)).(_restrFrames)) ⨟ᶠ
    (getFrame (cohsChainNext1 (cohs2ChainCohs c)) ⨟ᶠ
      mkRestrFrame (depsCohs := mkDepsCohs dc2) (cohsChainLen (cohs2ChainCohs c))
        (cohsChainLe (cohs2ChainCohs c)) ε)) ⨟ᶠ
    νHead dc2.(_depsCohs) ω ⨟ᶠ getPainting (cohsChainExt (cohs2ChainDepsCohs c))).
  { apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  rewrite <- getFrameRestr, cohs2ChainDepsNext.
  unfold νFace. rewrite νHeadProj.
  apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
  unshelve econstructor; now intros.
Defined.

Lemma νFaceCoh {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Q: DepsCohs2 p k} (c1: DepsCohs2Chain dc2Top dc2Q)
  {p' k'} {dc2P: DepsCohs2 p' k'} (c2: DepsCohs2Chain dc2Q dc2P) ε ω:
  νFace (DepsCohsChainCons (cohs2ChainCohs (cohs2ChainCompose c1 c2))) ω ⨟ᶠ
    proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
    νFace (cohs2ChainDepsCohs c1) ε =
  νFace (cohs2ChainCohs c1) ε ⨟ᶠ
    proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
    νFace (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)) ω.
Proof.
  rewrite cohs2ChainCohsCompose, cohs2ChainDepsCohsCompose.
  change (νFace (cohsChainCompose (cohs2ChainCohs c1)
    (DepsCohsChainCons (cohs2ChainCohs c2))) ω ⨟ᶠ
    proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
    νFace (cohs2ChainDepsCohs c1) ε =
    νFace (cohs2ChainCohs c1) ε ⨟ᶠ proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
    νFace (cohsChainCompose (cohs2ChainDepsCohs c1) (cohs2ChainDepsCohs c2)) ω).
  unfold νFace at 2.
  transitivity ((νFace (cohsChainCompose (cohs2ChainCohs c1)
      (DepsCohsChainCons (cohs2ChainCohs c2))) ω ⨟ᶠ
      proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
      getFrame (cohsChainNext (cohs2ChainDepsCohs c1))) ⨟ᶠ
    νHead dc2Q.(_depsCohs) ε ⨟ᶠ getPainting (cohsChainExt (cohs2ChainDepsCohs c1))).
  { apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  rewrite <- cohs2ChainDepsNext.
  rewrite (νFaceProjection (cohs2ChainCohs c1) (DepsCohsChainCons (cohs2ChainCohs c2)) ω).
  transitivity (getFrame (cohsChainNext (cohs2ChainCohs c1)) ⨟ᶠ
    (νFace (DepsCohsChainCons (cohs2ChainCohs c2)) ω ⨟ᶠ
      proj (mkPainting (mkExtraDeps dc2Q.(_extraDepsCohs))) ⨟ᶠ νHead dc2Q.(_depsCohs) ε) ⨟ᶠ
    getPainting (cohsChainExt (cohs2ChainDepsCohs c1))).
  { apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  rewrite νFaceCohHead.
  rewrite νFaceCompose.
  transitivity ((νFace (cohs2ChainCohs c1) ε ⨟ᶠ
      proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
      getFrame (cohsChainDeps (cohs2ChainCohs c1))) ⨟ᶠ
    νFace (cohs2ChainDepsCohs c2) ω ⨟ᶠ getPainting (cohsChainExt (cohs2ChainDepsCohs c1))).
  - rewrite (νFaceProjection (cohs2ChainCohs c1) DepsCohsChainNil ε).
    apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
  - rewrite cohs2ChainDepsNext.
    apply (functorEqPath (total (mkPainting dc2Top.(_depsCohs).(_extraDeps))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
Defined.

End FaceOn.

Module Face (A: LayerSig).
Module Source := νStrictGpd.νStrictGpd A.
Include FaceOn A Source.
End Face.

Module Type FaceSig (A: LayerSig) (S: νStrictGpdSig A).
Include FaceOn A S.
End FaceSig.

Module FaceSimplicial := FaceOn SimplicialLayer νStrictGpdSimplicial.
Module FaceCubical := FaceOn CubicalLayer νStrictGpdCubical.

(** A frame functor is determined by all of its face functors. *)
Module FaceExtensionalityOn (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S).
Import A.
Module Export Faces := F.

Fixpoint getPaintingInv {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): Functor (total (mkPainting extTop)) (total (mkPainting ext)) :=
  match c with
  | ExtChainNil => idFunctor _
  | @ExtChainCons _ _ _ _ _ _ deps ext c' =>
      getPaintingInv c' ⨟ᶠ totalUnassoc (mkLayer deps.(_restrFrames)) (mkPainting ext)
  end.

Lemma getPaintingInvR {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext):
  getPainting c ⨟ᶠ getPaintingInv c = idFunctor (total (mkPainting ext)).
Proof.
  induction c.
  - now apply functorIdL.
  - cbn [getPainting getPaintingInv].
    rewrite <- functorAssocEq, (functorAssocEq _ (getPainting c)), IHc, functorIdR.
    apply (functorEqPath (total (mkPainting (AddRestrDep deps ext0))).(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
Defined.

Lemma getPaintingEq {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) {X: HSetGroupoid}
  (F L: Functor X (total (mkPainting ext)))
  (e: F ⨟ᶠ getPainting c ≐ L ⨟ᶠ getPainting c): F ≐ L.
Proof.
  apply pathFunctorEq.
  pose proof (f_equal (fun R => R ⨟ᶠ getPaintingInv c)
    (functorEqPath (total (mkPainting extTop)).(hsetGroupoidUIP) e)) as h.
  cbn beta in h.
  rewrite 2 functorAssocEq, getPaintingInvR, 2 functorIdR in h. now exact h.
Defined.

Lemma frameEqStep {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) {X: HSetGroupoid}
  (F L: Functor X (mkFrame (mkDepsRestr (depsCohs := dcTop))))
  (Hfaces: forall ε, F ⨟ᶠ νFace c ε ≐ L ⨟ᶠ νFace c ε)
  (Hb: (F ⨟ᶠ getFrame (cohsChainNext c)) ⨟ᶠ proj _ ≐
       (L ⨟ᶠ getFrame (cohsChainNext c)) ⨟ᶠ proj _):
  F ⨟ᶠ getFrame (cohsChainNext c) ≐ L ⨟ᶠ getFrame (cohsChainNext c).
Proof.
  apply (layerExt (mkPainting dc.(_extraDeps))
    (fun ε => mkRestrFrame (depsCohs := dc) 0 leR_O ε) _ _ Hb).
  intro ε. apply (getPaintingEq (cohsChainExt c)).
  unshelve econstructor.
  - intro x. now exact ((Hfaces ε).(objEq) x).
  - intros x y f. now exact ((Hfaces ε).(homEq) x y f).
Defined.

Lemma frameEqDescend {P K} {dcTop: DepsCohs P K} {X: HSetGroupoid}
  (F L: Functor X (mkFrame (mkDepsRestr (depsCohs := dcTop))))
  (Hfaces: forall p k (dc: DepsCohs p k) (c: DepsCohsChain dcTop dc) ε,
    F ⨟ᶠ νFace c ε ≐ L ⨟ᶠ νFace c ε)
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc):
  F ⨟ᶠ getFrame (cohsChainNext c) ≐ L ⨟ᶠ getFrame (cohsChainNext c) -> F ≐ L.
Proof.
  induction c as [|p k dc c IHc]; intro h.
  - unshelve econstructor; [now exact h.(objEq)|now exact h.(homEq)].
  - apply IHc. apply (frameEqStep c F L (Hfaces _ _ _ c)).
    unshelve econstructor; [now exact h.(objEq)|now exact h.(homEq)].
Defined.

Fixpoint fullCohsChainSig {P}: forall {K} (dcTop: DepsCohs P K),
  {k0: nat &T {dc0: DepsCohs 0 k0 &T DepsCohsChain dcTop dc0}} :=
  match P with
  | 0 => fun K dcTop => (K; (dcTop; DepsCohsChainNil))
  | S P' => fun K dcTop =>
      let s := fullCohsChainSig (proj1DepsCohs dcTop) in
      (s.1; (s.2.1;
        cohsChainCompose (DepsCohsChainCons DepsCohsChainNil) s.2.2))
  end.

Lemma νFaceEq {P K} {dcTop: DepsCohs P K} {X: HSetGroupoid}
  (F L: Functor X (mkFrame (mkDepsRestr (depsCohs := dcTop))))
  (Hfaces: forall p k (dc: DepsCohs p k) (c: DepsCohsChain dcTop dc) ε,
    F ⨟ᶠ νFace c ε ≐ L ⨟ᶠ νFace c ε): F ≐ L.
Proof.
  pose (s := fullCohsChainSig dcTop).
  apply (frameEqDescend F L Hfaces s.2.2).
  apply (frameEqStep s.2.2 F L (Hfaces _ _ _ s.2.2)).
  refine (Build_FunctorEq (fun x => hunit_ext _ _) _).
  intros x y f. now apply hunit_ext.
Defined.

End FaceExtensionalityOn.

Module FaceExtensionality (A: LayerSig).
Module Core := νStrictGpd.νStrictGpd A.
Module FaceOperations := FaceOn A Core.
Include FaceExtensionalityOn A Core FaceOperations.
End FaceExtensionality.
