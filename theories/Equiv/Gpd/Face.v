(** Face operations on the indexed groupoid side.

    The face maps are derived from frame projection and painting extension.
    These operations recurse on endpoint-indexed chains connecting stages of the
    dependency construction.

    The construction uses relative indices: a stage [p] under an ambient
    dimension [n] is represented by the difference [k := n - p]. Descending
    changes both indices, and for open [p] the landing stage after several steps
    cannot be expressed by reducing a subtraction. A chain records that landing
    stage in its endpoint index. The endpoint index directly determines the
    result type of the recursion. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT LeSProp Notation RewLemmas νGpd.HGpd νGpd.Layer
  νGpd.Lemmas νGpd.
From Bonak.Equiv.Gpd Require Tower.

From Bonak Require Import Limit.

From Bonak.Lib Require Import NatLemmas.
From Bonak.Equiv.Gpd Require Import PathAlgebra.

Set Primitive Projections.
From Bonak Require Import νGpd.Pasting.

Set Keyed Unification.

Module Face (A: LayerGpdSig).
Import A.

Module Export Tower := Bonak.Equiv.Gpd.Tower.Tower A.

(** Chains of projections between frame stages *)

Inductive DepsChain {P K} (depsTop: DepsRestr P K):
  forall {p k}, DepsRestr p k -> Type :=
| DepsChainNil: DepsChain depsTop depsTop
| DepsChainCons {p k} {deps: DepsRestr p.+1 k}:
    DepsChain depsTop deps -> DepsChain depsTop deps.(1).

Arguments DepsChainNil {P K depsTop}.
Arguments DepsChainCons {P K depsTop p k deps} _.

(** [getFrame]: project a frame down along a chain — iterated first
    projection. *)

Fixpoint getFrame {P K} {depsTop: DepsRestr P K} {p k} {deps: DepsRestr p k}
  (c: DepsChain depsTop deps): mkFrame depsTop -> mkFrame deps :=
  match c with
  | DepsChainNil => fun d => d
  | DepsChainCons c' => fun d => (getFrame c' d).1
  end.

(** Chains of climbs through painting extensions *)

Inductive ExtChain {P K} {depsTop: DepsRestr P K}
  (extTop: DepsRestrExtension P K depsTop):
  forall {p k} {deps: DepsRestr p k}, DepsRestrExtension p k deps -> Type :=
| ExtChainNil: ExtChain extTop extTop
| ExtChainCons {p k} {deps: DepsRestr p.+1 k}
    {ext: DepsRestrExtension p.+1 k deps}:
    ExtChain extTop ext -> ExtChain extTop (AddRestrDep deps ext).

Arguments ExtChainNil {P K depsTop extTop}.
Arguments ExtChainCons {P K depsTop extTop p k deps ext} _.

(** [getPainting]: rebuild a cell at the top of the chain from a frame and
    a painting over it, moving layers from the painting to the frame. *)

Fixpoint getPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext):
  forall (d: mkFrame deps), mkPainting ext d ->
  { d': mkFrame depsTop &T mkPainting extTop d' } :=
  match c with
  | ExtChainNil => fun d cp => (d; cp)
  | ExtChainCons c' => fun d cp => getPainting c' (d; cp.1) cp.2
  end.

(** The frame chain underlying a painting chain. *)

Fixpoint extChainDeps {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): DepsChain depsTop deps :=
  match c with
  | ExtChainNil => DepsChainNil
  | ExtChainCons c' => DepsChainCons (extChainDeps c')
  end.

(** The rebuilt cell projects back onto the frame it was built from. *)

Lemma getFrameGetPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (d: mkFrame deps) (cp: mkPainting ext d):
  getFrame (extChainDeps c) (getPainting c d cp).1 = d.
Proof.
  revert d cp; induction c; intros d cp.
  - now reflexivity.
  - cbn. now rewrite IHc.
Defined.

(** Chains in the [DepsCohs] world

    A [DepsCohsChain] from the top of level n down to stage p induces,
    definitionally, the level-(n+1) frame descent ([cohsChainNext], through
    [mkDepsRestr]) and the level-n painting climb ([cohsChainExt]) — so a
    single chain supplies both witnesses the face maps need, at their two
    adjacent levels. *)

Inductive DepsCohsChain {P K} (dcTop: DepsCohs P K):
  forall {p k}, DepsCohs p k -> Type :=
| DepsCohsChainNil: DepsCohsChain dcTop dcTop
| DepsCohsChainCons {p k} {dc: DepsCohs p.+1 k}:
    DepsCohsChain dcTop dc -> DepsCohsChain dcTop (proj1DepsCohs dc).

Arguments DepsCohsChainNil {P K dcTop}.
Arguments DepsCohsChainCons {P K dcTop p k dc} _.

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

(** The length of a chain is the offset of the restriction it commutes
    with ([getFrameRestr]); it is bounded by the codomain's [k]. *)

Fixpoint cohsChainLen {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): nat :=
  match c with
  | DepsCohsChainNil => 0
  | DepsCohsChainCons c' => (cohsChainLen c').+1
  end.

Fixpoint cohsChainLe {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): cohsChainLen c <= k :=
  match c with
  | DepsCohsChainNil => leR_O
  | DepsCohsChainCons c' => ⇑ (cohsChainLe c')
  end.

(** Given a full frame one level up, project it down to stage [p.+1],
    take the ε-component of its top layer, and rebuild a full cell from
    that painting. This defines the face operation associated to a [νGpd]. *)

Definition νFace {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop))):
  { d': mkFrame dcTop.(_deps) &T mkPainting dcTop.(_extraDeps) d' } :=
  getPainting (cohsChainExt c)
    (mkRestrFrame (depsCohs := dc) 0 leR_O ε (getFrame (cohsChainNext c) d).1)
    (nth (getFrame (cohsChainNext c) d).2 ε).

(** Commutation of the projections with the restrictions

    Restricting at the top-stage diagonal and projecting down equals
    projecting down one level up and restricting at the accumulated
    offset. *)

Lemma getFrameRestr {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop)).(1)):
  getFrame (cohsChainDeps c) (mkRestrFrame (depsCohs := dcTop) 0 leR_O ε d) =
  mkRestrFrame (depsCohs := dc) (cohsChainLen c) (cohsChainLe c) ε
    (getFrame (cohsChainNext1 c) d).
Proof.
  induction c.
  - now reflexivity.
  - cbn. now rewrite IHc.
Defined.

(** Chains of coherence data, with their lower restriction-data chains. *)

Inductive DepsCohs2Chain {P K} (dc2Top: DepsCohs2 P K):
  forall {p k}, DepsCohs2 p k -> Type :=
| DepsCohs2ChainNil: DepsCohs2Chain dc2Top dc2Top
| DepsCohs2ChainCons {p k} {dc2: DepsCohs2 p.+1 k}:
    DepsCohs2Chain dc2Top dc2 -> DepsCohs2Chain dc2Top (proj1DepsCohs2 dc2).

Arguments DepsCohs2ChainNil {P K dc2Top}.
Arguments DepsCohs2ChainCons {P K dc2Top p k dc2} _.

Fixpoint cohs2ChainDepsCohs {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain dc2Top.(_depsCohs) dc2.(_depsCohs) :=
  match c with
  | DepsCohs2ChainNil => DepsCohsChainNil
  | DepsCohs2ChainCons c' => DepsCohsChainCons (cohs2ChainDepsCohs c')
  end.

(** Chains in the [DepsCohs3] world.  Their upper image supplies the
    [DepsCohs2] chain one dimension higher, while their lower image supplies
    the chain at the current dimension.  These are the two adjacent chain
    families needed to compare composites of face exchange paths. *)

Inductive DepsCohs3Chain {P K} (dc3Top: DepsCohs3 P K):
  forall {p k}, DepsCohs3 p k -> Type :=
| DepsCohs3ChainNil: DepsCohs3Chain dc3Top dc3Top
| DepsCohs3ChainCons {p k} {dc3: DepsCohs3 p.+1 k}:
    DepsCohs3Chain dc3Top dc3 ->
    DepsCohs3Chain dc3Top (proj1DepsCohs3 dc3).

Arguments DepsCohs3ChainNil {P K dc3Top}.
Arguments DepsCohs3ChainCons {P K dc3Top p k dc3} _.

Fixpoint cohs3ChainDepsCohs2 {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (c: DepsCohs3Chain dc3Top dc3):
  DepsCohs2Chain dc3Top.(_depsCohs2) dc3.(_depsCohs2) :=
  match c with
  | DepsCohs3ChainNil => DepsCohs2ChainNil
  | DepsCohs3ChainCons c' =>
      DepsCohs2ChainCons (cohs3ChainDepsCohs2 c')
  end.

Fixpoint cohs3ChainCompose {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3Mid: DepsCohs3 p k} {p' k'} {dc3: DepsCohs3 p' k'}
  (c1: DepsCohs3Chain dc3Top dc3Mid)
  (c2: DepsCohs3Chain dc3Mid dc3): DepsCohs3Chain dc3Top dc3 :=
  match c2 with
  | DepsCohs3ChainNil => c1
  | DepsCohs3ChainCons c2' =>
      DepsCohs3ChainCons (cohs3ChainCompose c1 c2')
  end.

(** Packaged chains

    A chain determines its endpoint but the endpoint's indices are an
    open subtraction, so the endpoint travels with the chain: a package
    is a chain together with the stage and offset it lands on. Packages
    are the form in which chains are consumed, since a face map is
    indexed by a dimension rather than by a chain.

    Packages are rigid: a chain from a fixed source is determined by its
    length ([dcPackEq] and its two analogues), because both constructors
    are determined by the length and the landing indices follow. Every
    identification of packages below is therefore an identification of
    natural numbers. *)

Definition DCPack {P K} (dcTop: DepsCohs P K): Type :=
  {p: nat &T {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}}}.

Definition Chain2Pack {P K} (dc2Top: DepsCohs2 P K): Type :=
  {p: nat &T {k: nat &T {dc2: DepsCohs2 p k &T DepsCohs2Chain dc2Top dc2}}}.

Definition Chain3Pack {P K} (dc3Top: DepsCohs3 P K): Type :=
  {p: nat &T {k: nat &T {dc3: DepsCohs3 p k &T DepsCohs3Chain dc3Top dc3}}}.

(** Descending one stage. At stage [0] there is nothing left to descend
    to, and the package stalls. *)

Definition dcStep {P K} {dcTop: DepsCohs P K} (s: DCPack dcTop):
  DCPack dcTop :=
  (match s.1 as p0 return
     {k: nat &T {dc: DepsCohs p0 k &T DepsCohsChain dcTop dc}} ->
     DCPack dcTop with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs s'.2.1;
       DepsCohsChainCons s'.2.2)))
   end) s.2.

Definition chain2Step {P K} {dc2Top: DepsCohs2 P K}
  (s: Chain2Pack dc2Top): Chain2Pack dc2Top :=
  (match s.1 as p0 return
     {k: nat &T {dc2: DepsCohs2 p0 k &T DepsCohs2Chain dc2Top dc2}} ->
     Chain2Pack dc2Top with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs2 s'.2.1;
       DepsCohs2ChainCons s'.2.2)))
   end) s.2.

Definition chain3Step {P K} {dc3Top: DepsCohs3 P K}
  (s: Chain3Pack dc3Top): Chain3Pack dc3Top :=
  (match s.1 as p0 return
     {k: nat &T {dc3: DepsCohs3 p0 k &T DepsCohs3Chain dc3Top dc3}} ->
     Chain3Pack dc3Top with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs3 s'.2.1;
       DepsCohs3ChainCons s'.2.2)))
   end) s.2.

(** Lengths *)

Fixpoint cohs2ChainLen {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2): nat :=
  match c with
  | DepsCohs2ChainNil => 0
  | DepsCohs2ChainCons c' => (cohs2ChainLen c').+1
  end.

Fixpoint cohs3ChainLen {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (c: DepsCohs3Chain dc3Top dc3): nat :=
  match c with
  | DepsCohs3ChainNil => 0
  | DepsCohs3ChainCons c' => (cohs3ChainLen c').+1
  end.

Definition dcPackLen {P K} {dcTop: DepsCohs P K} (s: DCPack dcTop): nat :=
  cohsChainLen s.2.2.2.

Definition chain2PackLen {P K} {dc2Top: DepsCohs2 P K}
  (s: Chain2Pack dc2Top): nat := cohs2ChainLen s.2.2.2.

Definition chain3PackLen {P K} {dc3Top: DepsCohs3 P K}
  (s: Chain3Pack dc3Top): nat := cohs3ChainLen s.2.2.2.

(** Rigidity: the length determines the package *)

Lemma dcPackEqLen {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) {p' k'} {dc': DepsCohs p' k'}
  (c': DepsCohsChain dcTop dc'):
  cohsChainLen c = cohsChainLen c' ->
  ((p; (k; (dc; c))): DCPack dcTop) = (p'; (k'; (dc'; c'))).
Proof.
  revert p' k' dc' c'.
  induction c; intros p' k' dc' c' H.
  - destruct c'; [now reflexivity | now discriminate H].
  - destruct c'; [now discriminate H |].
    cbn in H. injection H as H.
    now exact (f_equal dcStep (IHc _ _ _ c' H)).
Defined.

Lemma dcPackEq {P K} {dcTop: DepsCohs P K} (s t: DCPack dcTop):
  dcPackLen s = dcPackLen t -> s = t.
Proof.
  destruct s as (p, (k, (dc, c))), t as (p', (k', (dc', c'))).
  now exact (dcPackEqLen c c').
Defined.

Lemma chain2PackEqLen {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2)
  {p' k'} {dc2': DepsCohs2 p' k'} (c': DepsCohs2Chain dc2Top dc2'):
  cohs2ChainLen c = cohs2ChainLen c' ->
  ((p; (k; (dc2; c))): Chain2Pack dc2Top) = (p'; (k'; (dc2'; c'))).
Proof.
  revert p' k' dc2' c'.
  induction c; intros p' k' dc2' c' H.
  - destruct c'; [now reflexivity | now discriminate H].
  - destruct c'; [now discriminate H |].
    cbn in H. injection H as H.
    now exact (f_equal chain2Step (IHc _ _ _ c' H)).
Defined.

Lemma chain2PackEq {P K} {dc2Top: DepsCohs2 P K} (s t: Chain2Pack dc2Top):
  chain2PackLen s = chain2PackLen t -> s = t.
Proof.
  destruct s as (p, (k, (dc2, c))), t as (p', (k', (dc2', c'))).
  now exact (chain2PackEqLen c c').
Defined.

Lemma chain3PackEqLen {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (c: DepsCohs3Chain dc3Top dc3)
  {p' k'} {dc3': DepsCohs3 p' k'} (c': DepsCohs3Chain dc3Top dc3'):
  cohs3ChainLen c = cohs3ChainLen c' ->
  ((p; (k; (dc3; c))): Chain3Pack dc3Top) = (p'; (k'; (dc3'; c'))).
Proof.
  revert p' k' dc3' c'.
  induction c; intros p' k' dc3' c' H.
  - destruct c'; [now reflexivity | now discriminate H].
  - destruct c'; [now discriminate H |].
    cbn in H. injection H as H.
    now exact (f_equal chain3Step (IHc _ _ _ c' H)).
Defined.

Lemma chain3PackEq {P K} {dc3Top: DepsCohs3 P K} (s t: Chain3Pack dc3Top):
  chain3PackLen s = chain3PackLen t -> s = t.
Proof.
  destruct s as (p, (k, (dc3, c))), t as (p', (k', (dc3', c'))).
  now exact (chain3PackEqLen c c').
Defined.

Lemma cohs2ChainDepsCohsLen {P K} {T: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain T dc2):
  cohsChainLen (cohs2ChainDepsCohs c) = cohs2ChainLen c.
Proof. induction c; cbn; [now reflexivity | now rewrite IHc]. Defined.

Lemma cohs3ChainDepsCohs2Len {P K} {T: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (c: DepsCohs3Chain T dc3):
  cohs2ChainLen (cohs3ChainDepsCohs2 c) = cohs3ChainLen c.
Proof. induction c; cbn; [now reflexivity | now rewrite IHc]. Defined.

(** Which identification of packages is used never matters: the length
    is a decidable invariant that determines the package, so package
    equality satisfies UIP. *)

Lemma natDec (n m: nat): {n = m} + {n <> m}.
Proof. now decide equality. Defined.

Lemma dcPackDec {P K} {dcTop: DepsCohs P K} (s t: DCPack dcTop):
  {s = t} + {s <> t}.
Proof.
  destruct (natDec (dcPackLen s) (dcPackLen t)) as [H|H].
  - now left; now exact (dcPackEq s t H).
  - right; intro e. now exact (H (f_equal dcPackLen e)).
Defined.

Lemma dcPackUIP {P K} {dcTop: DepsCohs P K} {s t: DCPack dcTop}
  (e e': s = t): e = e'.
Proof. now exact (UIP_dec _ dcPackDec s t e e'). Defined.

(** Faces at the bottom of a chain

    A face map erases one dimension from a cell — a frame together with a
    painting over it. At the bottom of a chain, where the offset is large
    enough to name that dimension directly, the erasure is the pair of the
    frame restriction and the painting restriction, and it is indexed by
    the dimension rather than by a chain. *)

Definition restrCell {p k} {depsCohs: DepsCohs p k}
  (ext: DepsCohsExtension p k depsCohs) (j: nat) (Hj: j <= k) (ε: arity)
  (D: mkFrame (mkDepsRestr (depsCohs := depsCohs)).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs := depsCohs); mkExtraDeps ext)).2 D):
  { d': mkFrame depsCohs.(_deps) &T mkPainting depsCohs.(_extraDeps) d' } :=
  (mkRestrFrame j Hj ε D; mkRestrPainting ext j Hj ε D C).

(** A face at the bottom of a chain is restricted there and rebuilt
    through the chain. Its index [j] is relative to that bottom stage. *)

Definition faceAt {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain dc2Top dc2) (j: nat) (Hj: j <= k) (ε: arity)
  (D: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs := dc2.(_depsCohs));
        mkExtraDeps dc2.(_extraDepsCohs))).2 D):
  { d': mkFrame (dc2Top.(_depsCohs)).(_deps) &T
        mkPainting (dc2Top.(_depsCohs)).(_extraDeps) d' } :=
  getPainting (cohsChainExt (cohs2ChainDepsCohs c))
    (restrCell dc2.(_extraDepsCohs) j Hj ε D C).1
    (restrCell dc2.(_extraDepsCohs) j Hj ε D C).2.

(** The exchange law and its pasting, at the bottom of a chain

    A [DepsCohs3] carries, at every stage, both the exchange between two
    successive face maps — as frame coherence and painting coherence — and
    the hexagon on three of them. Erasing two dimensions from a cell in the
    two orders therefore agrees by the stored data, and the three ways of
    erasing three dimensions paste by it. *)

Lemma restrCellCoh {p k} (dc3: DepsCohs3 p k)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D):
  restrCell dc3.(_depsCohs2).(_extraDepsCohs) Q HQ ε
    (restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) R
       (HR ↕ ↑ HQ) ω D C).1
    (restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) R
       (HR ↕ ↑ HQ) ω D C).2 =
  restrCell dc3.(_depsCohs2).(_extraDepsCohs) R (HR ↕ HQ) ω
    (restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) Q.+1
       (⇑ HQ) ε D C).1
    (restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) Q.+1
       (⇑ HQ) ε D C).2.
Proof.
  unfold restrCell.
  unshelve eapply eq_existT_curried.
  - now exact ((mkDepsCohs2 dc3).(_depsCohs).(_cohs).2 Q HQ R HR ε ω D).
  Unshelve.
  - now exact ((mkDepsCohs2 dc3).(_cohPaintings).2 Q HQ R HR ε ω D C).
Defined.

Section RestrCellCoh2.
Context {p k} (dc3: DepsCohs3 p k) (ext3: DepsCohs3Extension p k dc3).

(** The stage below carries the exchange between the two face maps above
    the one [dc3] itself governs. *)
Let dc3Up := proj1DepsCohs3 (toDepsCohs3 (mkCoh2Paintings ext3)).
Let ext0 := dc3.(_depsCohs2).(_extraDepsCohs).
Let extUp := (proj1DepsCohs2 (mkDepsCohs2 dc3Up)).(_extraDepsCohs).

Lemma restrCellCoh2
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (S: nat) (HS: S <= R)
  (ε ω θ: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3Up)).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3Up)).(_depsCohs));
        mkExtraDeps extUp)).2 D):
  f_equal (fun z => restrCell ext0 Q HQ ε z.1 z.2)
    (restrCellCoh dc3Up R (HR ↕ ↑ HQ) S HS ω θ D C)
  • (restrCellCoh dc3 Q HQ S (HS ↕ HR) ε θ
       (restrCell extUp R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C).1
       (restrCell extUp R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C).2
     • f_equal (fun z => restrCell ext0 S (HS ↕ (HR ↕ HQ)) θ z.1 z.2)
         (restrCellCoh dc3Up Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D C))
  = restrCellCoh dc3 Q HQ R HR ε ω
      (restrCell extUp S (↑ (↑ (HS ↕ (HR ↕ HQ)))) θ D C).1
      (restrCell extUp S (↑ (↑ (HS ↕ (HR ↕ HQ)))) θ D C).2
    • (f_equal (fun z => restrCell ext0 R (HR ↕ HQ) ω z.1 z.2)
         (restrCellCoh dc3Up Q.+1 (⇑ HQ) S (↑ (HS ↕ HR)) ε θ D C)
       • restrCellCoh dc3 R (HR ↕ HQ) S HS ω θ
           (restrCell extUp Q.+2 (⇑ (⇑ HQ)) ε D C).1
           (restrCell extUp Q.+2 (⇑ (⇑ HQ)) ε D C).2).
Proof.
  unfold restrCellCoh, restrCell.
  unshelve eapply eq_existT_curried_hex.
  - now exact ((mkDepsCohs2 dc3).(_coh2Frames).2 Q HQ R HR S HS ε ω θ D).
  - now exact (mkCoh2Painting ext3 Q HQ R HR S HS ε ω θ D C).
Defined.

End RestrCellCoh2.

(** [deepPainting] reads a top cell's painting at the bottom of a chain.
    Each descent step prefixes the layer it passes. Restriction at dimension
    [j] reads the first [j] layers; at dimension [0] the remaining painting
    does not affect the face. *)

Fixpoint deepPaintingTail {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  mkPainting (mkExtraDeps dc2.(_extraDepsCohs))
    (getFrame (cohsChainNext (cohs2ChainDepsCohs c)) d) :=
  match c with
  | DepsCohs2ChainNil => Q
  | DepsCohs2ChainCons c' =>
      ((getFrame (cohsChainNext (cohs2ChainDepsCohs c')) d).2;
        deepPaintingTail c' d Q)
  end.

Definition deepPainting {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  (mkPaintings (mkDepsRestr (depsCohs := dc2.(_depsCohs));
    mkExtraDeps dc2.(_extraDepsCohs))).2
    (getFrame (cohsChainNext (cohs2ChainDepsCohs c)) d).1 :=
  ((getFrame (cohsChainNext (cohs2ChainDepsCohs c)) d).2;
    deepPaintingTail c d Q).

Definition faceDeep {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain dc2Top dc2) (j: nat) (Hj: j <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d) :=
  faceAt c j Hj ε (getFrame (cohsChainNext (cohs2ChainDepsCohs c)) d).1
    (deepPainting c d Q).

Lemma νFaceAsDeep {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain dc2Top dc2) (ε: arity) d Q:
  νFace (cohs2ChainDepsCohs c) ε d = faceDeep c 0 leR_O ε d Q.
Proof. destruct c; now reflexivity. Defined.

(** [deepCell] pairs the descended frame with [deepPainting], giving
    the cell on which the bottom restriction acts. *)

Definition deepCell {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain dc2Top dc2)
  (z: { d': mkFrame (mkDepsCohs dc2Top).(_deps) &T
            mkPainting (mkDepsCohs dc2Top).(_extraDeps) d' }):
  { D: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))).(1) &T
       (mkPaintings (mkDepsRestr (depsCohs := dc2.(_depsCohs));
         mkExtraDeps dc2.(_extraDepsCohs))).2 D } :=
  ((getFrame (cohsChainNext (cohs2ChainDepsCohs c)) z.1).1;
   deepPainting c z.1 z.2).

(** The extension descends along a chain in lockstep with the [DepsCohs3]
    it extends. *)

Fixpoint chain3Ext {P K} {dc3Top: DepsCohs3 P K}
  (ext3: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (c: DepsCohs3Chain dc3Top dc3): DepsCohs3Extension p k dc3 :=
  match c with
  | DepsCohs3ChainNil => ext3
  | DepsCohs3ChainCons c' => AddCoh3Dep _ (chain3Ext ext3 c')
  end.

(** The hexagon along a chain

    [faceRebuild] is the rebuilding half of [faceAt], so a face at the
    bottom rebuilt through the chain is [faceRebuild] of a [restrCell] and
    the exchange law is [faceRebuild] of [restrCellCoh]. Rebuilding is a
    function, so it carries the pasting of the three exchanges: the
    hexagon along the chain is the image of [restrCellCoh2], the two
    [f_equal] laws distributing it over the composites. *)

Definition faceRebuild {P K} {dc3Top: DepsCohs3 P K} {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3)
  (w: { d': mkFrame dc3.(_depsCohs2).(_depsCohs).(_deps) &T
            mkPainting dc3.(_depsCohs2).(_depsCohs).(_extraDeps) d' }) :=
  getPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    w.1 w.2.

Section FaceAtCoh2.
Context {P K} {dc3Top: DepsCohs3 P K} {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3) (ext3: DepsCohs3Extension p k dc3).
Let dc3Up := proj1DepsCohs3 (toDepsCohs3 (mkCoh2Paintings ext3)).
Let ext0 := dc3.(_depsCohs2).(_extraDepsCohs).
Let extUp := (proj1DepsCohs2 (mkDepsCohs2 dc3Up)).(_extraDepsCohs).
Let CellUp := { d': mkFrame dc3Up.(_depsCohs2).(_depsCohs).(_deps) &T
                mkPainting dc3Up.(_depsCohs2).(_depsCohs).(_extraDeps) d' }.

Lemma faceAtCoh2
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (S: nat) (HS: S <= R)
  (ε ω θ: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3Up)).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3Up)).(_depsCohs));
        mkExtraDeps extUp)).2 D):
  f_equal (fun z: CellUp => faceRebuild a (restrCell ext0 Q HQ ε z.1 z.2))
    (restrCellCoh dc3Up R (HR ↕ ↑ HQ) S HS ω θ D C)
  • (f_equal (faceRebuild a)
       (restrCellCoh dc3 Q HQ S (HS ↕ HR) ε θ
          (restrCell extUp R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C).1
          (restrCell extUp R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C).2)
     • f_equal (fun z: CellUp =>
         faceRebuild a (restrCell ext0 S (HS ↕ (HR ↕ HQ)) θ z.1 z.2))
         (restrCellCoh dc3Up Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D C))
  = f_equal (faceRebuild a)
      (restrCellCoh dc3 Q HQ R HR ε ω
         (restrCell extUp S (↑ (↑ (HS ↕ (HR ↕ HQ)))) θ D C).1
         (restrCell extUp S (↑ (↑ (HS ↕ (HR ↕ HQ)))) θ D C).2)
    • (f_equal (fun z: CellUp =>
         faceRebuild a (restrCell ext0 R (HR ↕ HQ) ω z.1 z.2))
         (restrCellCoh dc3Up Q.+1 (⇑ HQ) S (↑ (HS ↕ HR)) ε θ D C)
       • f_equal (faceRebuild a)
           (restrCellCoh dc3 R (HR ↕ HQ) S HS ω θ
              (restrCell extUp Q.+2 (⇑ (⇑ HQ)) ε D C).1
              (restrCell extUp Q.+2 (⇑ (⇑ HQ)) ε D C).2)).
Proof.
  rewrite <- (f_equal_compose
    (fun z: CellUp => restrCell ext0 Q HQ ε z.1 z.2)
    (faceRebuild a) (restrCellCoh dc3Up R (HR ↕ ↑ HQ) S HS ω θ D C)).
  rewrite <- (f_equal_compose
    (fun z: CellUp => restrCell ext0 S (HS ↕ (HR ↕ HQ)) θ z.1 z.2)
    (faceRebuild a) (restrCellCoh dc3Up Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D C)).
  rewrite <- (f_equal_compose
    (fun z: CellUp => restrCell ext0 R (HR ↕ HQ) ω z.1 z.2)
    (faceRebuild a) (restrCellCoh dc3Up Q.+1 (⇑ HQ) S (↑ (HS ↕ HR)) ε θ D C)).
  rewrite <- 4 eq_trans_map_distr.
  now exact (f_equal (fun h => f_equal (faceRebuild a) h)
    (restrCellCoh2 dc3 ext3 Q HQ R HR S HS ε ω θ D C)).
Defined.

End FaceAtCoh2.

(** An extension determines the coherence data one level up. Descending
    the extension together with the data lifts a chain to that level. *)

Definition mkDepsCohs3 {p k} (dc3: DepsCohs3 p k)
  (ext3: DepsCohs3Extension p k dc3): DepsCohs3 p.+1 k :=
  toDepsCohs3 (mkCoh2Paintings ext3).

Fixpoint cohs3ChainUp {P K} {dc3Top: DepsCohs3 P K}
  (ext3: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (c: DepsCohs3Chain dc3Top dc3):
  DepsCohs3Chain (mkDepsCohs3 dc3Top ext3)
    (mkDepsCohs3 dc3 (chain3Ext ext3 c)) :=
  match c with
  | DepsCohs3ChainNil => DepsCohs3ChainNil
  | DepsCohs3ChainCons c' => DepsCohs3ChainCons (cohs3ChainUp ext3 c')
  end.

(** The chain one level up that a hexagon's middle level runs along: the
    lift, extended by the step the level shift contributes. *)

Definition chainUp1 {P K} {dc3Top: DepsCohs3 P K}
  (ext3: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (c: DepsCohs3Chain dc3Top dc3):
  DepsCohs3Chain (mkDepsCohs3 dc3Top ext3)
    (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext ext3 c))) :=
  DepsCohs3ChainCons (cohs3ChainUp ext3 c).

(** The exchange law with the inner face read one level up

    A hexagon pastes exchanges at two consecutive levels, so the inner
    face of a composite is the face map of the chain lifted by
    [chainUp1]. Descending a cell that lifted map produced recovers the
    [restrCell] the bottom of the chain sees, and the exchange between the
    lifted face map and the one at the current level is again the bottom
    exchange rebuilt through the chain. *)

Lemma deepCellRebuildUp {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3)
  (Y: { D: mkFrame
             (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(1) &T
           (mkPaintings (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs));
             mkExtraDeps dc3.(_depsCohs2).(_extraDepsCohs))).2 D }):
  deepCell (cohs3ChainDepsCohs2 a)
    (getPainting (cohsChainExt (cohs2ChainDepsCohs
       (cohs3ChainDepsCohs2 (chainUp1 e0 a)))) Y.1 Y.2) = Y.
Proof.
  induction a; intros.
  - now reflexivity.
  - now exact (f_equal (fun w: { D: mkFrame (mkDepsRestr
        (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(1) &T
        (mkPaintings (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs));
          mkExtraDeps dc3.(_depsCohs2).(_extraDepsCohs))).2 D } =>
      ((w.1.1; (w.1.2; w.2)):
        { D: mkFrame (mkDepsRestr
               (depsCohs :=
                  (proj1DepsCohs3 dc3).(_depsCohs2).(_depsCohs))).(1) &T
          (mkPaintings (mkDepsRestr
             (depsCohs := (proj1DepsCohs3 dc3).(_depsCohs2).(_depsCohs));
             mkExtraDeps
               (proj1DepsCohs3 dc3).(_depsCohs2).(_extraDepsCohs))).2 D }))
      (IHa ((Y.1; Y.2.1); Y.2.2))).
Defined.

Lemma deepCellFaceAtUp {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3) (j: nat) (Hj: j <= k.+1) (ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D):
  deepCell (cohs3ChainDepsCohs2 a)
    (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) j Hj ω D C) =
  restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) j Hj ω D C.
Proof. now exact (deepCellRebuildUp e0 a _). Defined.

Lemma faceAtCohUp {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D):
  faceAt (cohs3ChainDepsCohs2 a) Q HQ ε
    (deepCell (cohs3ChainDepsCohs2 a)
      (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) R (HR ↕ ↑ HQ) ω D C)).1
    (deepCell (cohs3ChainDepsCohs2 a)
      (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) R (HR ↕ ↑ HQ) ω D C)).2 =
  faceAt (cohs3ChainDepsCohs2 a) R (HR ↕ HQ) ω
    (deepCell (cohs3ChainDepsCohs2 a)
      (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) Q.+1 (⇑ HQ) ε D C)).1
    (deepCell (cohs3ChainDepsCohs2 a)
      (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) Q.+1 (⇑ HQ) ε D C)).2.
Proof.
  rewrite 2 (deepCellFaceAtUp e0).
  now exact (f_equal (faceRebuild a) (restrCellCoh dc3 Q HQ R HR ε ω D C)).
Defined.

(** Both exchanges as conjugates

    A leg of the hexagon identifies two composites of face maps read at
    the top of a chain, and factors through the composite read at the
    bottom, where the stored exchange lives. [faceAtCohUpConj] exposes that
    factorization for a leg at the current level, [faceAtDeepConj] for the
    image of a leg one level up. *)

Lemma faceAtCohUpConj {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D):
  faceAtCohUp e0 a Q HQ R HR ε ω D C =
  f_equal (fun w => faceAt (cohs3ChainDepsCohs2 a) Q HQ ε w.1 w.2)
    (deepCellFaceAtUp e0 a R (HR ↕ ↑ HQ) ω D C)
  • (f_equal (faceRebuild a) (restrCellCoh dc3 Q HQ R HR ε ω D C)
     • eq_sym (f_equal
         (fun w => faceAt (cohs3ChainDepsCohs2 a) R (HR ↕ HQ) ω w.1 w.2)
         (deepCellFaceAtUp e0 a Q.+1 (⇑ HQ) ε D C))).
Proof.
  unfold faceAtCohUp.
  lazymatch goal with
  | |- _ = f_equal ?F ?s • (?h • eq_sym (f_equal ?G ?t)) =>
      change ((rew [fun x => F x = G _] eq_sym s in
        rew [fun y => F _ = G y] eq_sym t in h) =
        f_equal F s • (h • eq_sym (f_equal G t)))
  end.
  rewrite path_reindex_left, path_reindex_right.
  lazymatch goal with
  | |- _ = f_equal ?F ?s • (?h • eq_sym (f_equal ?G ?t)) =>
      now rewrite <- (eq_sym_map_distr F s), <- (eq_sym_map_distr G t),
        eq_sym_involutive
  end.
Defined.

Lemma faceAtDeepConj {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3) (j: nat) (Hj: j <= k) (α: arity)
  {X Y: { d': mkFrame (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs).(_deps)
          &T mkPainting
               (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs).(_extraDeps) d' }}
  (h: X = Y):
  f_equal (fun w => faceAt (cohs3ChainDepsCohs2 a) j Hj α
                      (deepCell (cohs3ChainDepsCohs2 a) w).1
                      (deepCell (cohs3ChainDepsCohs2 a) w).2)
    (f_equal (faceRebuild (chainUp1 e0 a)) h)
  = f_equal (fun w => faceAt (cohs3ChainDepsCohs2 a) j Hj α w.1 w.2)
      (deepCellRebuildUp e0 a X)
    • (f_equal (fun w => faceAt (cohs3ChainDepsCohs2 a) j Hj α w.1 w.2) h
       • eq_sym (f_equal
           (fun w => faceAt (cohs3ChainDepsCohs2 a) j Hj α w.1 w.2)
           (deepCellRebuildUp e0 a Y))).
Proof.
  rewrite f_equal_compose.
  now exact (fEqualCompHomot
    (fun w => faceAt (cohs3ChainDepsCohs2 a) j Hj α w.1 w.2)
    (fun z => deepCell (cohs3ChainDepsCohs2 a) (faceRebuild (chainUp1 e0 a) z))
    (deepCellRebuildUp e0 a) h).
Defined.

(** The three cells a leg moves between: [CellAbove] is what a face map
    one level up consumes, [CellHere] what a face map at the current level
    consumes, and [CellRestr] what [restrCell] produces and [faceRebuild]
    consumes. *)

Definition CellAbove {p k} (dc3: DepsCohs3 p k) :=
  { D: mkFrame (mkDepsRestr (depsCohs :=
         (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1) &T
    (mkPaintings (mkDepsRestr (depsCohs :=
       (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
       mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D }.

Definition CellHere {p k} (dc3: DepsCohs3 p k) :=
  { D: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(1) &T
    (mkPaintings (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs));
       mkExtraDeps dc3.(_depsCohs2).(_extraDepsCohs))).2 D }.

Definition CellRestr {p k} (dc3: DepsCohs3 p k) :=
  { d': mkFrame dc3.(_depsCohs2).(_depsCohs).(_deps) &T
        mkPainting dc3.(_depsCohs2).(_depsCohs).(_extraDeps) d' }.

(** The identification at a hexagon vertex

    A vertex of the hexagon read at the top is a face at the current level
    of the descent of a face one level up, applied to a cell a further
    face map produced. Normalizing it moves that cell along [β] and then
    replaces the descent by the [restrCell] it computes to. The two legs
    meeting at a vertex normalize it the same way, which is what lets
    [hexReindex] share the six identifications. *)

Definition vertexNorm {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3)
  (j: nat) (Hj: j <= k) (α: arity) (i: nat) (Hi: i <= k.+1) (γ: arity)
  {X Y: CellAbove dc3} (β: X = Y) :=
  f_equal (fun w =>
    faceAt (cohs3ChainDepsCohs2 a) j Hj α
      (deepCell (cohs3ChainDepsCohs2 a) w).1
      (deepCell (cohs3ChainDepsCohs2 a) w).2)
    (f_equal (fun z: CellAbove dc3 =>
       faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) i Hi γ z.1 z.2) β)
  • f_equal (fun w: CellHere dc3 =>
      faceAt (cohs3ChainDepsCohs2 a) j Hj α w.1 w.2)
      (deepCellRebuildUp e0 a
        (restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) i Hi γ
           Y.1 Y.2)).

Lemma hexLegHere {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  {X Y: CellAbove dc3} (β: X = Y):
  faceAtCohUp e0 a Q HQ R HR ε ω X.1 X.2 =
  vertexNorm e0 a Q HQ ε R (HR ↕ ↑ HQ) ω β
  • (f_equal (faceRebuild a) (restrCellCoh dc3 Q HQ R HR ε ω Y.1 Y.2)
     • eq_sym (vertexNorm e0 a R (HR ↕ HQ) ω Q.+1 (⇑ HQ) ε β)).
Proof.
  rewrite (homotopy_cell_reindex _ _
    (fun Z: CellAbove dc3 => faceAtCohUp e0 a Q HQ R HR ε ω Z.1 Z.2) β).
  rewrite (faceAtCohUpConj e0 a Q HQ R HR ε ω Y.1 Y.2).
  lazymatch goal with
  | |- path_change ?s (?u • (?h • eq_sym ?v)) ?t = ?R =>
      change (path_change s (path_change u h v) t = R)
  end.
  rewrite path_change_nest.
  unfold path_change, vertexNorm.
  lazymatch goal with
  | |- _ = (f_equal ?F (f_equal ?G ?s) • _) •
      (_ • eq_sym (f_equal ?H (f_equal ?I ?t) • _)) =>
      now rewrite (f_equal_compose G F s), (f_equal_compose I H t)
  end.
Defined.

Lemma hexLegAbove {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top)
  (e1: DepsCohs3Extension P.+1 K (mkDepsCohs3 dc3Top e0))
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (j: nat) (Hj: j <= k) (α: arity)
  (Q: nat) (HQ: Q <= k.+1) (R: nat) (HR: R <= Q) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs := (proj1DepsCohs2 (mkDepsCohs2
        (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext e0 a))))).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs := (proj1DepsCohs2 (mkDepsCohs2
        (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext e0 a))))).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2
          (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext e0 a))))).(_extraDepsCohs)
        )).2 D):
  f_equal (fun w => faceAt (cohs3ChainDepsCohs2 a) j Hj α
             (deepCell (cohs3ChainDepsCohs2 a) w).1
             (deepCell (cohs3ChainDepsCohs2 a) w).2)
    (faceAtCohUp e1 (chainUp1 e0 a) Q HQ R HR ε ω D C)
  = vertexNorm e0 a j Hj α Q HQ ε
      (deepCellFaceAtUp e1 (chainUp1 e0 a) R (HR ↕ ↑ HQ) ω D C)
    • (f_equal
         (fun z: CellRestr
                   (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext e0 a))) =>
            faceRebuild a
              (restrCell dc3.(_depsCohs2).(_extraDepsCohs) j Hj α z.1 z.2))
         (restrCellCoh (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext e0 a)))
            Q HQ R HR ε ω D C)
       • eq_sym (vertexNorm e0 a j Hj α R (HR ↕ HQ) ω
           (deepCellFaceAtUp e1 (chainUp1 e0 a) Q.+1 (⇑ HQ) ε D C))).
Proof.
  rewrite (faceAtCohUpConj e1 (chainUp1 e0 a) Q HQ R HR ε ω D C).
  rewrite 2 eq_trans_map_distr.
  rewrite <- eq_sym_f_equal.
  rewrite (faceAtDeepConj e0 a j Hj α).
  unfold vertexNorm.
  now exact (legRegroup _ _ _ _ _).
Defined.

Section Hex.
Context {P K} {dc3Top: DepsCohs3 P K} {p k} {dc3: DepsCohs3 p k}
  (e0: DepsCohs3Extension P K dc3Top)
  (e1: DepsCohs3Extension P.+1 K (mkDepsCohs3 dc3Top e0))
  (a: DepsCohs3Chain dc3Top dc3).

Let a1 := chainUp1 e0 a.
Let c := cohs3ChainDepsCohs2 a.
Let u := cohs3ChainDepsCohs2 a1.
Let v := cohs3ChainDepsCohs2 (chainUp1 e1 a1).
Let dcV := proj1DepsCohs2 (mkDepsCohs2
  (proj1DepsCohs3 (mkDepsCohs3 dc3 (chain3Ext e0 a)))).

Lemma faceAtCoh2Up
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (s: nat) (Hs: s <= R)
  (ε ω θ: arity)
  (D: mkFrame (mkDepsRestr (depsCohs := dcV.(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs := dcV.(_depsCohs));
        mkExtraDeps dcV.(_extraDepsCohs))).2 D):
  f_equal (fun w => faceAt c Q HQ ε (deepCell c w).1 (deepCell c w).2)
    (faceAtCohUp e1 a1 R (HR ↕ ↑ HQ) s Hs ω θ D C)
  • (faceAtCohUp e0 a Q HQ s (Hs ↕ HR) ε θ
       (deepCell u (faceAt v R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C)).1
       (deepCell u (faceAt v R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C)).2
     • f_equal (fun w => faceAt c s (Hs ↕ (HR ↕ HQ)) θ
                  (deepCell c w).1 (deepCell c w).2)
         (faceAtCohUp e1 a1 Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D C))
  = faceAtCohUp e0 a Q HQ R HR ε ω
      (deepCell u (faceAt v s (↑ (↑ (Hs ↕ (HR ↕ HQ)))) θ D C)).1
      (deepCell u (faceAt v s (↑ (↑ (Hs ↕ (HR ↕ HQ)))) θ D C)).2
    • (f_equal (fun w => faceAt c R (HR ↕ HQ) ω
                  (deepCell c w).1 (deepCell c w).2)
         (faceAtCohUp e1 a1 Q.+1 (⇑ HQ) s (↑ (Hs ↕ HR)) ε θ D C)
       • faceAtCohUp e0 a R (HR ↕ HQ) s Hs ω θ
           (deepCell u (faceAt v Q.+2 (⇑ (⇑ HQ)) ε D C)).1
           (deepCell u (faceAt v Q.+2 (⇑ (⇑ HQ)) ε D C)).2).
Proof.
  rewrite (hexLegAbove e0 e1 a Q HQ ε R (HR ↕ ↑ HQ) s Hs ω θ D C).
  rewrite (hexLegHere e0 a Q HQ s (Hs ↕ HR) ε θ
    (deepCellFaceAtUp e1 a1 R.+1 (⇑ (HR ↕ ↑ HQ)) ω D C)).
  rewrite (hexLegAbove e0 e1 a s (Hs ↕ (HR ↕ HQ)) θ Q.+1 (⇑ HQ) R.+1 (⇑ HR)
    ε ω D C).
  rewrite (hexLegHere e0 a Q HQ R HR ε ω
    (deepCellFaceAtUp e1 a1 s (↑ (↑ (Hs ↕ (HR ↕ HQ)))) θ D C)).
  rewrite (hexLegAbove e0 e1 a R (HR ↕ HQ) ω Q.+1 (⇑ HQ) s (↑ (Hs ↕ HR))
    ε θ D C).
  rewrite (hexLegHere e0 a R (HR ↕ HQ) s Hs ω θ
    (deepCellFaceAtUp e1 a1 Q.+2 (⇑ (⇑ HQ)) ε D C)).
  now exact (hexReindex _ _ _ _ _ _ _ _ _ _ _ _
    (faceAtCoh2 a (chain3Ext e0 a) Q HQ R HR s Hs ε ω θ D C)).
Defined.

End Hex.

Definition dcPackOf {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): DCPack dcTop := (p; (k; (dc; c))).

End Face.

Module FaceSimplicial := Face SimplicialGpdLayer.
Module FaceCubical := Face CubicalGpdLayer.
