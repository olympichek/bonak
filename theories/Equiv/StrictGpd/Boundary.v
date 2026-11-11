(** Functors into the indexed frames of strict groupoids as compatible
    families of their codimension-one face functors. A functor from a strict
    groupoid [X] into a frame is determined by its composites with the face
    functors, and every family of functors into the top cells satisfying the
    overlap law arises in this way. Reconstruction attaches the face layers
    one at a time, using the overlap law to identify the base of each new
    painting. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation LeSProp.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category Require Import FunctorAlgebra.
From Bonak.Presheaf Require Import GeneratingFaces.
From Bonak.Equiv.StrictGpd Require Import Tower Face.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

(** Functor equalities that hold pointwise by computation. *)
Local Ltac pointwise :=
  apply (functorEqPath (groupoidStrictness _));
  unshelve econstructor; now intros.

Module BoundaryOn (A: LayerSig) (S: νStrictGpdSig A) (F: FaceSig A S).
Import A.
Module Export Extensionality := FaceExtensionalityOn A S F.
Module Export Tower := TowerOn A S.

Definition Cell {p k} {deps: DepsRestr p k} (ext: DepsRestrExtension p k deps):
  StrictGroupoid := total (mkPainting ext).

(** * Chains of a given length *)

Definition ChainPack {P K} (dcTop: DepsCohs P K): Type :=
  {p: nat &T {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}}}.

Definition chainStep {P K} {dcTop: DepsCohs P K} (s: ChainPack dcTop):
  ChainPack dcTop :=
  (match s.1 as p return
    {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}} -> ChainPack dcTop
  with
  | 0 => fun t => (0; t)
  | S p => fun t =>
      (p; (t.1.+1; (proj1DepsCohs t.2.1; DepsCohsChainCons t.2.2)))
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
Proof.
  induction c; cbn [cohsChainLen chainDown]; [now reflexivity|now rewrite IHc].
Qed.

Definition chainDepth {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc): FaceDepth P :=
  {| depth := cohsChainLen c;
     depthBound := leR_eq_r (cohsChainStage c) (leR_add_l p) |}.

Lemma prefixChainLength {P K} {dcTop: DepsCohs P.+1 K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain (proj1DepsCohs dcTop) dc):
  cohsChainLen (cohsChainCompose (DepsCohsChainCons DepsCohsChainNil) c)
  = (cohsChainLen c).+1.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma cohs2ComposeNil {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc):
  cohs2ChainCompose DepsCohs2ChainNil c = c.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Lemma cohs2ComposeAssoc {P K} {dcTop: DepsCohs2 P K}
  {p k} {dcQ: DepsCohs2 p k} {p' k'} {dcR: DepsCohs2 p' k'}
  {p'' k''} {dcS: DepsCohs2 p'' k''} (a: DepsCohs2Chain dcTop dcQ)
  (b: DepsCohs2Chain dcQ dcR) (c: DepsCohs2Chain dcR dcS):
  cohs2ChainCompose (cohs2ChainCompose a b) c
  = cohs2ChainCompose a (cohs2ChainCompose b c).
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Qed.

Definition IndexedChainPack {P K} (dc: DepsCohs2 P K): Type :=
  {p: nat &T {k: nat &T {d: DepsCohs2 p k &T DepsCohs2Chain dc d}}}.

Definition indexedChainLength {P K} {dc: DepsCohs2 P K}
  (c: IndexedChainPack dc): nat := cohsChainLen (cohs2ChainDepsCohs c.2.2.2).

Definition prependIndexedChain {P K} (dc: DepsCohs2 P.+1 K)
  (c: IndexedChainPack (proj1DepsCohs2 dc)): IndexedChainPack dc :=
  (c.1; (c.2.1; (c.2.2.1;
    cohs2ChainCompose (DepsCohs2ChainCons DepsCohs2ChainNil) c.2.2.2))).

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
    now exact (prependIndexedChain dc c.1;
      prependIndexedChainLength dc c.1 • f_equal S c.2).
Defined.

Definition IndexedChainPair {P K} (dc: DepsCohs2 P K): Type :=
  {c: IndexedChainPack dc &T IndexedChainPack c.2.2.1}.

Definition joinIndexedChains {P K} {dc: DepsCohs2 P K}
  (c: IndexedChainPair dc): IndexedChainPack dc :=
  (c.2.1; (c.2.2.1; (c.2.2.2.1; cohs2ChainCompose c.1.2.2.2 c.2.2.2.2))).

Definition prependIndexedPair {P K} (dc: DepsCohs2 P.+1 K)
  (c: IndexedChainPair (proj1DepsCohs2 dc)): IndexedChainPair dc :=
  (prependIndexedChain dc c.1; c.2).

Lemma prependIndexedPairJoin {P K} (dc: DepsCohs2 P.+1 K) c:
  joinIndexedChains (prependIndexedPair dc c)
  = prependIndexedChain dc (joinIndexedChains c).
Proof.
  unfold joinIndexedChains, prependIndexedPair, prependIndexedChain; cbn.
  now rewrite cohs2ComposeAssoc.
Qed.

(** A pair of composable chains reaching the depths [i <= j]. *)
Fixpoint indexedPairAtDepth P: forall K (dc: DepsCohs2 P K)
  (i j: FaceDepth P), depth i <= depth j ->
  {c: IndexedChainPair dc &T ((indexedChainLength c.1 = depth i) *
    (indexedChainLength (joinIndexedChains c) = depth j))%type}.
Proof.
  destruct P as [|P]; intros K dc [[|i] hi] [[|j] hj] hij;
    try (destruct (leR_O_contra hi)); try (destruct (leR_O_contra hj));
    try (destruct (leR_O_contra hij)).
  - now exact (((0; (K; (dc; DepsCohs2ChainNil)));
      (0; (K; (dc; DepsCohs2ChainNil)))); (eq_refl, eq_refl)).
  - now exact (((P.+1; (K; (dc; DepsCohs2ChainNil)));
      (P.+1; (K; (dc; DepsCohs2ChainNil)))); (eq_refl, eq_refl)).
  - pose (c := indexedChainAtDepth P.+1 K dc
      {| depth := j.+1; depthBound := hj |}).
    refine (((P.+1; (K; (dc; DepsCohs2ChainNil))); c.1); (eq_refl, _)).
    unfold joinIndexedChains, indexedChainLength; cbn.
    rewrite cohs2ComposeNil. now exact c.2.
  - pose (c := indexedPairAtDepth P K.+1 (proj1DepsCohs2 dc)
      {| depth := i; depthBound := ⇓ hi |}
      {| depth := j; depthBound := ⇓ hj |} (⇓ hij)).
    refine (prependIndexedPair dc c.1; (_, _)).
    + now exact (prependIndexedChainLength dc c.1.1 • f_equal S (fst c.2)).
    + rewrite prependIndexedPairJoin, prependIndexedChainLength.
      now exact (f_equal S (snd c.2)).
Defined.

(** * Faces indexed by depth *)

Definition faceAtDepth {P K} (dcTop: DepsCohs P K) (j: nat) (ε: arity):
  Functor (mkFrame (mkDepsRestr (depsCohs := dcTop)))
    (Cell dcTop.(_extraDeps)) :=
  νFace (chainDown dcTop j).2.2.2 ε.

Lemma faceAtChain {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc) ε:
  faceAtDepth dcTop (cohsChainLen c) ε = νFace c ε.
Proof. unfold faceAtDepth. now rewrite chainDownReify. Qed.

Lemma faceAtDepthNext {P K} (dcTop: DepsCohs P.+1 K) j ε:
  faceAtDepth dcTop j.+1 ε =
  proj (mkLayer (mkDepsRestr (depsCohs := dcTop)).(_restrFrames)) ⨟ᶠ
    faceAtDepth (proj1DepsCohs dcTop) j ε ⨟ᶠ
    getPainting (ExtChainCons ExtChainNil).
Proof.
  unfold faceAtDepth. rewrite chainDownHead. cbn [chainPrefix].
  rewrite νFaceCompose. now pointwise.
Qed.

(** A frame functor is determined by its faces at all depths. *)
Lemma depthFacesEq {X: StrictGroupoid} {P K} {dcTop: DepsCohs P K}
  (F L: Functor X (mkFrame (mkDepsRestr (depsCohs := dcTop))))
  (h: forall (i: FaceDepth P) ε, F ⨟ᶠ faceAtDepth dcTop (depth i) ε
    ≐ L ⨟ᶠ faceAtDepth dcTop (depth i) ε): F ≐ L.
Proof.
  apply νFaceEq. intros p k dc c ε.
  rewrite <- (faceAtChain c ε). now exact (h (chainDepth c) ε).
Qed.

Lemma frameFacesExt {X: StrictGroupoid} {P K} {dcTop: DepsCohs P K}
  (F L: Functor X (mkFrame (mkDepsRestr (depsCohs := dcTop))))
  (h: forall (i: FaceDepth P) ε, F ⨟ᶠ faceAtDepth dcTop (depth i) ε
    = L ⨟ᶠ faceAtDepth dcTop (depth i) ε): F = L.
Proof.
  apply (functorEqPath (groupoidStrictness _)), depthFacesEq.
  intros i ε. now apply pathFunctorEq, h.
Qed.

(** * Face tuples and their overlap law *)

Definition FaceTuple (X: StrictGroupoid) {P K} (dcTop: DepsCohs P K): Type :=
  forall (i: FaceDepth P) (ε: arity), Functor X (Cell dcTop.(_extraDeps)).

Definition frameFaces {X: StrictGroupoid} {P K} (dcTop: DepsCohs P K)
  (d: Functor X (mkFrame (mkDepsRestr (depsCohs := dcTop)))):
  FaceTuple X dcTop :=
  fun i ε => d ⨟ᶠ faceAtDepth dcTop (depth i) ε.

(** The overlap law of a face family, indexed by depths. *)
Definition DepthLaw {X: StrictGroupoid} {P K} (dc: DepsCohs2 P K)
  (f: FaceTuple X (mkDepsCohs dc)): Type :=
  forall (i j: FaceDepth P), depth i <= depth j -> forall a c,
    f (nextDepth j) c ⨟ᶠ proj _ ⨟ᶠ faceAtDepth dc.(_depsCohs) (depth i) a
    = f (weakenDepth i) a ⨟ᶠ proj _ ⨟ᶠ faceAtDepth dc.(_depsCohs) (depth j) c.

Lemma frameFacesDepthLaw {X: StrictGroupoid} {P K} (dc: DepsCohs2 P K)
  (d: Functor X (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc)))):
  DepthLaw dc (frameFaces (mkDepsCohs dc) d).
Proof.
  intros i j hij a c.
  destruct (indexedPairAtDepth P K dc i j hij)
    as [[[p1 [k1 [d1 c1]]] [p2 [k2 [d2 c2]]]] [e1 e2]].
  change (cohsChainLen (cohs2ChainDepsCohs c1) = depth i) in e1.
  change (cohsChainLen (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2))
    = depth j) in e2.
  pose proof (νFaceCoh c1 c2 a c) as h.
  rewrite <- (faceAtChain (DepsCohsChainCons
    (cohs2ChainCohs (cohs2ChainCompose c1 c2))) c) in h.
  rewrite <- (faceAtChain (cohs2ChainDepsCohs c1) a) in h.
  rewrite <- (faceAtChain (cohs2ChainCohs c1) a) in h.
  rewrite <- (faceAtChain
    (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)) c) in h.
  cbn [cohsChainLen] in h. rewrite 2 cohs2ChainLenEq, e1, e2 in h.
  unfold frameFaces.
  refine (_ • f_equal (compFunctor d) h • _); now pointwise.
Qed.

(** * Restriction of the base of a frame *)

(** The face at the depth of [c] of the base of a frame, seen as a cell
    of the frame's top painting. *)
Definition earlierFace {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) (ω: arity):
  Functor (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top)).(1))
    (Cell (mkDepsCohs dc2Top).(_extraDeps)) :=
  getFrame (cohsChainNext1 (cohs2ChainCohs c)) ⨟ᶠ
    νHead (proj1DepsCohs (mkDepsCohs dc2)) ω ⨟ᶠ
    getPainting (cohsChainExt (DepsCohsChainCons (cohs2ChainCohs c))).

Lemma restrictionBoundary {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) (ε ω: arity):
  earlierFace c ω ⨟ᶠ proj (mkPainting (mkDepsCohs dc2Top).(_extraDeps)) ⨟ᶠ
    νHead dc2Top.(_depsCohs) ε =
  mkRestrFrame (depsCohs := mkDepsCohs dc2Top) 0 leR_O ε ⨟ᶠ
    νFace (cohs2ChainDepsCohs c) ω.
Proof.
  unfold earlierFace.
  transitivity (getFrame (cohsChainNext1 (cohs2ChainCohs c)) ⨟ᶠ
    νHead (proj1DepsCohs (mkDepsCohs dc2)) ω ⨟ᶠ
    (getPainting (ExtChainCons (cohsChainExt (cohs2ChainCohs c))) ⨟ᶠ
      proj (mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs))) ⨟ᶠ
      νHead dc2Top.(_depsCohs) ε)).
  { now pointwise. }
  rewrite getPaintingRestr2.
  transitivity (getFrame (cohsChainNext1 (cohs2ChainCohs c)) ⨟ᶠ
    (νHead (proj1DepsCohs (mkDepsCohs dc2)) ω ⨟ᶠ
      totalMap (mkRestrPainting dc2.(_extraDepsCohs)
        (cohsChainLen (cohs2ChainDepsCohs c))
        (cohsChainLe (cohs2ChainDepsCohs c)) ε)) ⨟ᶠ
    getPainting (cohsChainExt (cohs2ChainDepsCohs c))).
  { now pointwise. }
  rewrite restrShiftPair.
  rewrite <- (mkRestrFrameLenIrr (cohs2ChainLenEq c)
    (Hq := cohsChainLe (cohs2ChainCohs c))
    (Hq' := cohsChainLe (cohs2ChainDepsCohs c)) ε).
  transitivity ((getFrame (cohsChainNext1 (cohs2ChainCohs c)) ⨟ᶠ
      mkRestrFrame (depsCohs := mkDepsCohs dc2)
        (cohsChainLen (cohs2ChainCohs c)) (cohsChainLe (cohs2ChainCohs c)) ε) ⨟ᶠ
    νHead dc2.(_depsCohs) ω ⨟ᶠ
    getPainting (cohsChainExt (cohs2ChainDepsCohs c))).
  { now pointwise. }
  rewrite <- getFrameRestr, cohs2ChainDepsNext.
  unfold νFace. now pointwise.
Qed.

Fixpoint previousCohsChain {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain (proj1DepsCohs (mkDepsCohs dc2Top))
    (proj1DepsCohs (mkDepsCohs dc2)) :=
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
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  getFrame (cohsChainNext1 (cohs2ChainCohs c))
  = getFrame (cohsChainNext (previousCohsChain c)).
Proof.
  induction c;
    cbn [cohs2ChainCohs cohsChainNext1 cohsChainNext previousCohsChain
      getFrame];
    [now reflexivity|now rewrite IHc].
Qed.

Lemma earlierFaceAsDepth {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) ω:
  earlierFace c ω =
  faceAtDepth (proj1DepsCohs (mkDepsCohs dc2Top))
    (cohsChainLen (cohs2ChainDepsCohs c)) ω ⨟ᶠ
    getPainting (ExtChainCons ExtChainNil).
Proof.
  rewrite <- previousCohsLength, faceAtChain.
  unfold earlierFace, νFace.
  rewrite <- previousCohsHead, cohsChainExtCompose, getPaintingCompose.
  rewrite previousCohsFrame. now pointwise.
Qed.

Lemma restrictionBoundaryDepth {P K} (dc: DepsCohs2 P K) (i: FaceDepth P) ε ω:
  mkRestrFrame (depsCohs := mkDepsCohs dc) 0 leR_O ε ⨟ᶠ
    faceAtDepth dc.(_depsCohs) (depth i) ω =
  faceAtDepth (proj1DepsCohs (mkDepsCohs dc)) (depth i) ω ⨟ᶠ
    getPainting (ExtChainCons ExtChainNil) ⨟ᶠ
    proj (mkPainting (mkDepsCohs dc).(_extraDeps)) ⨟ᶠ νHead dc.(_depsCohs) ε.
Proof.
  destruct (indexedChainAtDepth P K dc i) as [[p [k [d c]]] e].
  change (cohsChainLen (cohs2ChainDepsCohs c) = depth i) in e.
  rewrite <- e, (faceAtChain (cohs2ChainDepsCohs c) ω).
  rewrite <- (earlierFaceAsDepth c ω).
  now symmetry; apply restrictionBoundary.
Qed.

(** * Reconstruction *)

Definition Realization {X: StrictGroupoid} {P K} (dc: DepsCohs P K)
  (f: FaceTuple X dc): Type :=
  {d: Functor X (mkFrame (mkDepsRestr (depsCohs := dc))) &T
    forall i ε, d ⨟ᶠ faceAtDepth dc (depth i) ε = f i ε}.

Definition zeroFrameOfFaces {X: StrictGroupoid} {K} (dc: DepsCohs 0 K)
  (f: FaceTuple X dc): Functor X (mkFrame (mkDepsRestr (depsCohs := dc))).
Proof.
  refine (layerPair (mkPainting dc.(_extraDeps))
    (fun ε => mkRestrFrame (depsCohs := dc) 0 leR_O ε)
    (terminalFunctor X) (f (firstDepth 0)) _).
  intro ε. refine (Build_FunctorEq (fun x => hunit_ext _ _) _).
  intros x y g. now apply hunit_ext.
Defined.

Lemma zeroFrameOfFacesFace {X: StrictGroupoid} {K} (dc: DepsCohs 0 K) f i ε:
  zeroFrameOfFaces (X := X) dc f ⨟ᶠ faceAtDepth dc (depth i) ε = f i ε.
Proof.
  destruct i as [[|j] h]; [|destruct (leR_O_contra h)].
  apply (functorEqPath (groupoidStrictness _)).
  refine (feqWhiskerL _ _ •ᶠ layerPairHead _ _ _ _ _ ε).
  unshelve econstructor; now intros.
Qed.

(** The faces of the base of a frame, as cells of its next painting. *)
Definition shiftFaces {X: StrictGroupoid} {P K} (dcTop: DepsCohs P.+1 K)
  (f: FaceTuple X dcTop): FaceTuple X (proj1DepsCohs dcTop) :=
  fun i ε => f (nextDepth i) ε ⨟ᶠ getPaintingInv (ExtChainCons ExtChainNil).

Lemma shiftFacesLaw {X: StrictGroupoid} {P K} (dc: DepsCohs2 P.+1 K)
  (f: FaceTuple X (mkDepsCohs dc)) (H: DepthLaw dc f):
  DepthLaw (proj1DepsCohs2 dc) (shiftFaces (mkDepsCohs dc) f).
Proof.
  intros i j hij a c.
  pose proof (H (nextDepth i) (nextDepth j) (⇑ hij) a c) as h.
  cbn [depth nextDepth weakenDepth] in h. rewrite 2 faceAtDepthNext in h.
  apply (functorEqPath (groupoidStrictness _)).
  apply (getPaintingEq (extTop := dc.(_depsCohs).(_extraDeps))
    (ExtChainCons ExtChainNil)), pathFunctorEq.
  unfold shiftFaces.
  refine (_ • h • _); now pointwise.
Qed.

Section Finish.
Context {X: StrictGroupoid} {P K} (dc: DepsCohs2 P K)
  (f: FaceTuple X (mkDepsCohs dc)) (H: DepthLaw dc f).
Context (r: Realization (proj1DepsCohs (mkDepsCohs dc))
  (shiftFaces (mkDepsCohs dc) f)).

Lemma finishingBoundary ε:
  r.1 ⨟ᶠ mkRestrFrame (depsCohs := mkDepsCohs dc) 0 leR_O ε
  ≐ f (firstDepth P.+1) ε ⨟ᶠ proj (mkPainting (mkDepsCohs dc).(_extraDeps)).
Proof.
  apply depthFacesEq. intros i ω. apply pathFunctorEq.
  transitivity (r.1 ⨟ᶠ (mkRestrFrame (depsCohs := mkDepsCohs dc) 0 leR_O ε ⨟ᶠ
    faceAtDepth dc.(_depsCohs) (depth i) ω)).
  { now apply functorAssocEq. }
  rewrite restrictionBoundaryDepth.
  transitivity ((r.1 ⨟ᶠ
      faceAtDepth (proj1DepsCohs (mkDepsCohs dc)) (depth i) ω) ⨟ᶠ
    getPainting (ExtChainCons ExtChainNil) ⨟ᶠ
    proj (mkPainting (mkDepsCohs dc).(_extraDeps)) ⨟ᶠ νHead dc.(_depsCohs) ε).
  { now pointwise. }
  rewrite (r.2 i ω). unfold shiftFaces.
  refine (_ • H (firstDepth P) i leR_O ε ω). now pointwise.
Qed.

Definition finishedFrame:
  Functor X (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc))) :=
  layerPair (mkPainting (mkDepsCohs dc).(_extraDeps))
    (fun ε => mkRestrFrame (depsCohs := mkDepsCohs dc) 0 leR_O ε)
    r.1 (f (firstDepth P.+1)) finishingBoundary.

Lemma finishedFrameFace i ε:
  finishedFrame ⨟ᶠ faceAtDepth (mkDepsCohs dc) (depth i) ε = f i ε.
Proof.
  destruct i as [[|j] h].
  - apply (functorEqPath (groupoidStrictness _)).
    refine (feqWhiskerL _ _ •ᶠ layerPairHead _ _ _ _ _ ε).
    unshelve econstructor; now intros.
  - cbn [depth]. rewrite faceAtDepthNext.
    transitivity (r.1 ⨟ᶠ faceAtDepth (proj1DepsCohs (mkDepsCohs dc)) j ε ⨟ᶠ
      getPainting (ExtChainCons ExtChainNil)).
    + apply (functorEqPath (groupoidStrictness _)).
      refine (feqSym (feqAssoc _ _ _) •ᶠ _).
      refine (feqWhiskerR (feqSym (feqAssoc _ _ _)) _ •ᶠ _).
      now exact (feqWhiskerR (feqWhiskerR (layerPairProj _ _ _ _ _) _) _).
    + rewrite (r.2 {| depth := j; depthBound := ⇓ h |} ε).
      unfold shiftFaces. now pointwise.
Qed.

Definition finishRealization: Realization (mkDepsCohs dc) f :=
  (finishedFrame; finishedFrameFace).

End Finish.

Definition zeroRealization {X: StrictGroupoid} {K} (dc: DepsCohs 0 K)
  (f: FaceTuple X dc): Realization dc f :=
  (zeroFrameOfFaces dc f; zeroFrameOfFacesFace dc f).

Fixpoint reconstructFrame {X: StrictGroupoid} (P: nat):
  forall K (dc: DepsCohs2 P K) (f: FaceTuple X (mkDepsCohs dc)),
  DepthLaw dc f -> Realization (mkDepsCohs dc) f :=
  match P with
  | 0 => fun K dc f H => finishRealization dc f H
      (zeroRealization (proj1DepsCohs (mkDepsCohs dc))
        (shiftFaces (mkDepsCohs dc) f))
  | S P => fun K dc f H => finishRealization dc f H
      (reconstructFrame P K.+1 (proj1DepsCohs2 dc)
        (shiftFaces (mkDepsCohs dc) f) (shiftFacesLaw dc f H))
  end.

Definition frameOfFaces {X: StrictGroupoid} {P K} (dc: DepsCohs2 P K)
  (f: FaceTuple X (mkDepsCohs dc)) (H: DepthLaw dc f):
  Functor X (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc))) :=
  (reconstructFrame P K dc f H).1.

Lemma frameOfFacesFace {X: StrictGroupoid} {P K} (dc: DepsCohs2 P K) f H i ε:
  frameOfFaces (X := X) dc f H ⨟ᶠ faceAtDepth (mkDepsCohs dc) (depth i) ε
  = f i ε.
Proof. now exact ((reconstructFrame P K dc f H).2 i ε). Qed.

Definition prefixDepsCohs2 {n} (X: (νStrictGpdAt n.+2).(prefix)):
  DepsCohs2 n 0 := {|
  _depsCohs := prefixDepsCohs X.1;
  _extraDepsCohs := TopCohDep X.2;
  _cohPaintings := (νDataAt X.1.1).(cohPaintings) X.1.2 X.2;
|}.

End BoundaryOn.

Module Type BoundarySig (A: LayerSig) (S: νStrictGpdSig A) (F: FaceSig A S).
Include BoundaryOn A S F.
End BoundarySig.

Module Boundary (A: LayerSig).
Module Source := νStrictGpd.νStrictGpd A.
Module FaceOperations := FaceOn A Source.
Include BoundaryOn A Source FaceOperations.
End Boundary.
