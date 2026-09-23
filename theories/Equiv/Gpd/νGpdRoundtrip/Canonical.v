(** Total-cell restriction paths whose frame projections are the
    descent restriction paths. The zero case uses the pair law;
    positive indices reassociate the parent law recursively. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Association.
From Bonak.Lib Require Import Equiv.
From Bonak Require Import Limit.
Import Logic.EqNotations.

Set Primitive Projections.
From Bonak Require Import νGpd.Pasting.

Set Keyed Unification.
Module Canonical (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Import A.

Module Export Association := Bonak.Equiv.Gpd.νGpdRoundtrip.Association.Association A Base Translations.
#[local] Arguments Desc {X n Xpre}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments descCell {X m XpB SB}.

#[local] Arguments frtCellPair {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments DescS {X n Xpre S0}.
#[local] Arguments descCellPairRestrAt {X n XpB0 S0} HD {pB kB dcB}.
#[local] Arguments descQcells {X M XpB0 S0 HD p k dcB}.


#[local] Arguments frtTopAlignU {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments descCellPairRestrAtAsFace {X n XpB0 S0} HD {pB kB dcB}.
#[local] Arguments frtTrBaseOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshCohsOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtDepsCohsGen {X M XpB0 S0 HD p k dc2}.
#[local] Arguments frtPairLawAlignU {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments _frBound {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frFrames {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frPaintings {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frFrameEqvs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frPaintingEqvs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtDeps {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtFramesNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPaintingsNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtRestr0At {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPtStep {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frTr {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtTopNext {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtRestrictionTotalZero {X}.
#[local] Arguments descCellFace {X n XpB SB}.
#[local] Arguments _frDepsA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descQcellsPaired {X M XpB0 S0} HD q {p k dcB}.
#[local] Arguments descQcellsPairedCons {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments mkCellFramesOf {X} M {P K depsTop p k deps}.
#[local] Arguments descCells {X m XpB SB}.
#[local] Arguments descTop {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtQcellsAt {X M XpB0 S0} HD {p k dcB}.

Section FG.
Variable X: νGpds.

(** The zero correction is the generated restriction-painting law. *)
Definition descCanonicalZeroRpChoice {p k} (dc3: DepsCohs3 p k):
  FrtRpZeroType (mkExtraDeps dc3.(_depsCohs2).(_extraDepsCohs))
    (mkRestrPaintings dc3.(_depsCohs2).(_extraDepsCohs)) :=
  (rpZeroChainOf p dc3.(_depsCohs2).(_extraDepsCohs)).2.

Lemma descCellPairRestrCanonicalZero {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (ε: arity) (t: (g X).(G0) M.+1):
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let z := deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t) in
  frtCellPair HD cb ((g X).(GFace) M p Hdim ε t)
  = restrCell dc3.(_depsCohs2).(_extraDepsCohs) 0 Hq ε z.1 z.2.
Proof.
  intros cb z.
  now exact (=projT1_eq (descCellPairRestrAt HD cb p Hdim Hlen ε t);
    projT2_eq (descCellPairRestrAt HD cb p Hdim Hlen ε t)
      • eq_sym (descCanonicalZeroRpChoice dc3 Hq ε (descTop HD cb t).1 z.2)).
Defined.

Local Lemma descCanonicalZeroAsPair {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (ε: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrCanonicalZero HD a Hlen Hq Hdim ε t =
  descCellPairRestrAt HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))
    p Hdim Hlen ε t.
Proof.
  pose (law := descCellPairRestrAt HD
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) p Hdim Hlen ε t).
  change ((=projT1_eq law; projT2_eq law • eq_refl) = law).
  now exact (f_equal (fun h => (=projT1_eq law; h))
    (eq_trans_refl_r (projT2_eq law)) • totalPathReencode law).
Defined.


(** At every positive offset, the frame is the selected projected parent
    path. Its combined layer and painting is built by that same source
    change and projection. *)
Fixpoint descCanonicalPaintingPaired {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (q: nat) {struct q}:
  forall {p k} {dc3: DepsCohs3 p k}
    (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
    (Hlen: cohs3ChainLen (descChain HD).2
      = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (Hq: q <= k) (Hdim: q + p <= M) (epsilon: arity)
    (t: (g X).(G0) M.+1),
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let z := deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t) in
  rew [fun D => mkPainting dc3.(_depsCohs2).(_depsCohs).(_extraDeps) D]
    descQcellsPaired HD q cb Hlen Hq Hdim epsilon t in
    (frtCellPair HD cb ((g X).(GFace) M (q + p) Hdim epsilon t)).2
  = (restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq epsilon z.1 z.2).2.
Proof.
  destruct q as [|q]; intros p k dc3 a Hlen Hq Hdim epsilon t cb z.
  - now exact (projT2_eq (descCellPairRestrAt HD cb p Hdim Hlen epsilon t)
      • eq_sym (descCanonicalZeroRpChoice dc3 Hq epsilon
          (descTop HD cb t).1 z.2)).
  - destruct a as [|p k dc3 a].
    + now destruct (leR_O_contra Hq).
    + pose (cp := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)).
      pose (parentDim := leR_eq (plus_n_Sm q p) Hdim).
      pose (parentLen := Hlen • plus_n_Sm (cohsChainLen cp) p).
      pose (parentFrame := descQcellsPaired HD q cp parentLen (⇓ Hq)
        parentDim epsilon t).
      pose (parentPainting := descCanonicalPaintingPaired M XpB0 S0 HD q
        p.+1 k dc3 a parentLen (⇓ Hq) parentDim epsilon t).
      pose (indexDim := pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
        (Hq := parentDim) (Hq' := Hdim) epsilon t).
      pose (frameRead := fun u => (frtCellPair HD cp u).1).
      pose (paintingRead := fun u => (frtCellPair HD cp u).2).
      now exact (source_reindex_combined (f_equal frameRead indexDim) parentFrame
        (f_equal_dep_sigT frameRead paintingRead indexDim) parentPainting).
Defined.

Definition descCanonicalPairPaired {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (q: nat) (Hq: q <= k) (Hdim: q + p <= M) (epsilon: arity)
  (t: (g X).(G0) M.+1):
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let z := deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t) in
  frtCellPair HD cb ((g X).(GFace) M (q + p) Hdim epsilon t) =
  restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq epsilon z.1 z.2 :=
  (=descQcellsPaired HD q (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))
      Hlen Hq Hdim epsilon t;
    descCanonicalPaintingPaired HD q a Hlen Hq Hdim epsilon t).

(** Numeric presentation is a source change of the same selected pair. *)
Definition descCellPairRestrCanonical {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (epsilon: arity) (t: (g X).(G0) M.+1):
  let cp := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let z := deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t) in
  frtCellPair HD cp ((g X).(GFace) M dim Hdim epsilon t) =
  restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq epsilon z.1 z.2 :=
  path_reindex_source (f_equal
    (frtCellPair HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (pshFaceDimIrr (g X) Hd
      (Hq := Hdim) (Hq' := leR_eq Hd Hdim) epsilon t))
    (descCanonicalPairPaired HD a Hlen q Hq (leR_eq Hd Hdim) epsilon t).

Lemma descCellPairRestrCanonicalFrame {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (q: nat) (Hq: q <= k) (Hdim: q + p <= M) (ε: arity)
  (t: (g X).(G0) M.+1):
  projT1_eq (descCellPairRestrCanonical HD a q Hq (q + p) Hdim eq_refl Hlen ε t)
  = descQcells (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen q Hq Hdim ε t.
Proof.
  now exact (projT1_eq (totalPathDecodeEncode
    (descQcellsPaired HD q (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))
      Hlen Hq Hdim ε t)
    (descCanonicalPaintingPaired HD q a Hlen Hq Hdim ε t))).
Defined.

Section CanonicalPaintingCons.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p.+1 k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p.+1)%nat)
  (q: nat) (Hq: q <= k) (Hdim: q + p.+1 <= M)
  (epsilon: arity) (t: (g X).(G0) M.+1).

Let cp := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Let childLen := Hlen • eq_sym (plus_n_Sm (cohsChainLen cp) p).
Let computedLen := childLen • plus_n_Sm (cohsChainLen cp) p.
Let originalFrame := descQcellsPaired HD q cp Hlen Hq Hdim epsilon t.
Let adjustedFrame := descQcellsPaired HD q cp computedLen Hq Hdim epsilon t.
Let originalPainting := descCanonicalPaintingPaired HD q a Hlen Hq Hdim epsilon t.
Let adjustedPainting := descCanonicalPaintingPaired HD q a computedLen Hq Hdim epsilon t.
Let childFrame := descQcellsPaired HD q.+1 (DepsCohsChainCons cp)
  childLen (⇑ Hq) (leR_add_shift Hdim) epsilon t.
Let childPainting := descCanonicalPaintingPaired HD q.+1 (DepsCohs3ChainCons a)
  childLen (⇑ Hq) (leR_add_shift Hdim) epsilon t.
Let frameRead := fun u => (frtCellPair HD cp u).1.
Let paintingRead := fun u => (frtCellPair HD cp u).2.
Let indexDim := pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
  (Hq := Hdim) (Hq' := leR_add_shift Hdim) epsilon t.
Let indexFrame := f_equal frameRead indexDim.
Let indexPainting := f_equal_dep_sigT frameRead paintingRead indexDim.
Let parentTarget := restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq epsilon
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).1
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.
Let combined := fun D =>
  mkPainting (proj1DepsCohs3 dc3).(_depsCohs2).(_depsCohs).(_extraDeps) D.

Definition descCanonicalPaintingConsCell:
  projT1_eq originalFrame =
  f_equal (fun u => (frameRead u).1) indexDim • childFrame :=
  descQcellsPairedCons HD cp Hlen q Hq Hdim epsilon t •
  f_equal (fun c => c • childFrame)
    (f_equal_compose frameRead (fun z => z.1) indexDim).

Lemma descCanonicalPaintingConsCell_dep:
  rew [fun c => rew [combined] c in
      ((frameRead ((g X).(GFace) M (q + p.+1) Hdim epsilon t)).2;
       paintingRead ((g X).(GFace) M (q + p.+1) Hdim epsilon t)) =
      (parentTarget.1.2; parentTarget.2)]
    descCanonicalPaintingConsCell in
    pair_path_display originalFrame originalPainting =
  f_equal_dep_sigT (fun u => (frameRead u).1)
    (fun u => ((frameRead u).2; paintingRead u)) indexDim
    ⊙[fun D => GDom (combined D)] childPainting.
Proof.
  now exact (pair_path_parameter_cell_dep2
    (fun h => descQcellsPaired HD q cp h Hq Hdim epsilon t)
    (fun h => descCanonicalPaintingPaired HD q a h Hq Hdim epsilon t)
    (natUIP Hlen computedLen) ⊙
    source_projection_recover_comp_dep2 indexFrame adjustedFrame
      indexPainting adjustedPainting ⊙
    pair_path_section_whisker_dep2 frameRead paintingRead indexDim
      childFrame childPainting).
Defined.
End CanonicalPaintingCons.

Local Lemma descCanonicalPairPairedCons {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p.+1 k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs
        (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))) + p)%nat)
  (q: nat) (Hq: q.+1 <= k.+1) (Hdim: q.+1 + p <= M)
  (epsilon: arity) (t: (g X).(G0) M.+1):
  let cp := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let parentDim := leR_eq (plus_n_Sm q p) Hdim in
  let parentLen := Hlen • plus_n_Sm (cohsChainLen cp) p in
  descCanonicalPairPaired HD (DepsCohs3ChainCons a) Hlen q.+1 Hq Hdim epsilon t =
  f_equal unassoc (path_reindex_source
    (eq_sym (f_equal (frtCellPair HD cp)
      (pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
        (Hq := parentDim) (Hq' := Hdim) epsilon t)))
    (descCanonicalPairPaired HD a parentLen q (⇓ Hq) parentDim epsilon t)).
Proof.
  intros cp parentDim parentLen.
  pose (frameRead := fun u => (frtCellPair HD cp u).1).
  pose (paintingRead := fun u => (frtCellPair HD cp u).2).
  pose (indexDim := pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
    (Hq := parentDim) (Hq' := Hdim) epsilon t).
  pose (parentFrame := descQcellsPaired HD q cp parentLen (⇓ Hq)
    parentDim epsilon t).
  pose (parentPainting := descCanonicalPaintingPaired HD q a parentLen (⇓ Hq)
    parentDim epsilon t).
  pose (childFrame := path_reindex_source
    (eq_sym (f_equal frameRead indexDim)) parentFrame).
  pose (childPainting := source_reindex_display
    (fun D => mkPainting dc3.(_depsCohs2).(_depsCohs).(_extraDeps) D)
    (f_equal frameRead indexDim) parentFrame
    (f_equal_dep_sigT frameRead paintingRead indexDim) parentPainting).
  now exact (pair_path_display_total childFrame childPainting •
    f_equal (fun h => f_equal unassoc h)
      (source_reindex_section_total frameRead paintingRead indexDim
        parentFrame parentPainting)).
Defined.

Lemma descCellPairRestrCanonicalZeroRead {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (epsilon: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrCanonical HD a 0 Hq p Hdim eq_refl Hlen epsilon t =
  descCellPairRestrCanonicalZero HD a Hlen Hq Hdim epsilon t.
Proof.
  now reflexivity.
Defined.

Lemma descCellPairRestrCanonicalCons {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p.+1 k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q.+1 <= k.+1) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q.+1 + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs
        (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))) + p)%nat)
  (epsilon: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrCanonical HD (DepsCohs3ChainCons a)
    q.+1 Hq dim Hdim Hd Hlen epsilon t =
  f_equal unassoc (descCellPairRestrCanonical HD a q (⇓ Hq) dim Hdim
    (Hd • plus_n_Sm q p)
    (Hlen • plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs
      (cohs3ChainDepsCohs2 a))) p) epsilon t).
Proof.
  subst dim.
  rewrite (natUIP (eq_refl • plus_n_Sm q p) (plus_n_Sm q p)).
  unfold descCellPairRestrCanonical.
  cbn [pshFaceDimIrr f_equal path_reindex_source].
  rewrite (descCanonicalPairPairedCons HD a Hlen q Hq Hdim epsilon t).
  rewrite <- pshFaceDimIrr_sym, <- eq_sym_f_equal, eq_sym_involutive.
  now reflexivity.
Defined.

Lemma descCellPairRestrCanonicalIrr {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim dim': nat) (e: dim = dim')
  (Hdim: dim <= M) (Hdim': dim' <= M)
  (Hd: dim = (q + p)%nat) (Hd': dim' = (q + p)%nat)
  (Hlen Hlen': cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (epsilon: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrCanonical HD a q Hq dim Hdim Hd Hlen epsilon t =
  f_equal (frtCellPair HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (pshFaceDimIrr (g X) e epsilon t) •
  descCellPairRestrCanonical HD a q Hq dim' Hdim' Hd' Hlen' epsilon t.
Proof.
  destruct e.
  destruct (natUIP Hd Hd'), (natUIP Hlen Hlen').
  cbn [pshFaceDimIrr f_equal].
  now exact (eq_sym (eq_trans_refl_l _)).
Defined.

Lemma frtCellPairDeepCell {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (t: (g X).(G0) M.+1):
  frtCellPair (DescS HD) (DepsCohsChainCons (frtChainUp a)) t
  = deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t).
Proof.
  induction a as [|p k dc3 a IH].
  - now reflexivity.
  - now exact (f_equal unassoc IH).
Defined.

Lemma frtCellPairDeepCellFrame {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (t: (g X).(G0) M.+1):
  f_equal (fun z: CellHere dc3 => (z.1; z.2.1)) (frtCellPairDeepCell HD a t)
  = eq_sym (frtTopAlignU HD a t)
    • getFrameDeepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t).
Proof.
  induction a as [|p k dc3 a IH].
  -
  now reflexivity.
  -
  cbn [frtCellPairDeepCell cohs3ChainDepsCohs2 getFrameDeepCell f_equal].
  rewrite eq_trans_refl_r.
  assert (topAlignCons: frtTopAlignU HD (DepsCohs3ChainCons a) t = f_equal (fun z => z.1) (frtTopAlignU HD a t)).
  {
    unfold frtTopAlignU.
    cbn [chainNextUpEq].
    Unset Keyed Unification.
    lazymatch goal with |- @f_equal ?B ?C ?g ?u ?v (@f_equal ?A _ ?f ?x ?y ?h) = _ => refine (eq_trans (@f_equal_compose A B C x y f g h) _) end.
    lazymatch goal with |- _ = @f_equal ?B ?C ?g ?u ?v (@f_equal ?A _ ?f ?x ?y ?h) => refine (eq_trans _ (eq_sym (@f_equal_compose A B C x y f g h))) end.
    now reflexivity.
  }
  Set Keyed Unification.
  lazymatch goal with |- f_equal ?F _ = ?rhs =>
    change (f_equal F (f_equal unassoc (frtCellPairDeepCell HD a t)) = rhs)
  end.
  lazymatch goal with |- @f_equal ?B ?C ?g ?u ?v (@f_equal ?A _ ?f ?x ?y ?h) = _ =>
    refine (eq_trans (@f_equal_compose A B C x y f g h) _)
  end.
  rewrite topAlignCons.
  assert (Hdeep: f_equal (fun z => z.1)
    (getFrameDeepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)) = eq_refl).
  {
    clear IH topAlignCons.
    destruct a; now reflexivity.
  }
  pose proof (f_equal (fun h => f_equal (fun z => z.1) h) IH) as HI.
  cbn beta in HI.
  rewrite eq_trans_map_distr, Hdeep, eq_trans_refl_r in HI.
  lazymatch type of HI with
  | @eq _ (@f_equal ?B ?C ?g ?u ?v (@f_equal ?A _ ?f ?x ?y ?h)) _ =>
    rewrite (@f_equal_compose A B C x y f g h) in HI
  end.
  lazymatch goal with |- _ = eq_sym (@f_equal ?A ?B ?F ?x ?y ?h) => refine (eq_trans _ (eq_sym (@eq_sym_f_equal A B F x y h))) end.
  now exact HI.
Defined.

Definition descCellPairRestrTotal {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (ε: arity) (t: (g X).(G0) M.+1):
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let z := frtCellPair (DescS HD) (DepsCohsChainCons (frtChainUp a)) t in
  frtCellPair HD cb ((g X).(GFace) M dim Hdim ε t)
  = restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq ε z.1 z.2 :=
  descCellPairRestrCanonical HD a q Hq dim Hdim Hd Hlen ε t
  • f_equal (fun z: CellHere dc3 =>
      restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq ε z.1 z.2)
      (eq_sym (frtCellPairDeepCell HD a t)).

Lemma readCorrection {T A B: Type} (F: A -> B) (G: T -> A)
  {x y: T} {z: A} (p: z = G x) (s: z = G y) (h: x = y)
  (H: f_equal G h = eq_sym p • s):
  f_equal F s • f_equal (fun u => F (G u)) (eq_sym h) = f_equal F p.
Proof.
  rewrite <- (f_equal_compose G F (eq_sym h)), <- eq_trans_map_distr,
    <- eq_sym_map_distr, H, eq_trans_sym_distr, eq_sym_involutive.
  now rewrite eq_trans_assoc, eq_trans_sym_inv_r, eq_trans_refl_l.
Defined.

Lemma descCellPairRestrTotalZero {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (ε: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrTotal HD a 0 Hq p Hdim eq_refl Hlen ε t
  = descCellPairRestrAt HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) p Hdim Hlen ε t
    • f_equal (frtPairRestrAt dc3.(_depsCohs2).(_depsCohs) ε) (frtTopAlignU HD a t).
Proof.
  unfold descCellPairRestrTotal.
  rewrite (descCellPairRestrCanonicalZeroRead HD a Hlen Hq Hdim ε t).
  rewrite (descCanonicalZeroAsPair HD a Hlen Hq Hdim ε t).
  apply f_equal.
  refine (eq_trans (eq_sym (eq_trans_refl_l _)) _).
  now exact (readCorrection (frtPairRestrAt dc3.(_depsCohs2).(_depsCohs) ε)
    (fun z: CellHere dc3 => (z.1; z.2.1))
    (x := frtCellPair (DescS HD) (DepsCohsChainCons (frtChainUp a)) t)
    (y := deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t))
    (frtTopAlignU HD a t)
    (getFrameDeepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t))
    (frtCellPairDeepCell HD a t) (frtCellPairDeepCellFrame HD a t)).
Defined.

Lemma descCellPairRestrTotalCons {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p.+1 k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q.+1 <= k.+1) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q.+1 + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))) + p)%nat)
  (ε: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrTotal HD (DepsCohs3ChainCons a) q.+1 Hq dim Hdim Hd Hlen ε t
  = f_equal unassoc (descCellPairRestrTotal HD a q (⇓ Hq) dim Hdim
      (Hd • plus_n_Sm q p)
      (Hlen • plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p) ε t).
Proof.
  unfold descCellPairRestrTotal.
  rewrite (descCellPairRestrCanonicalCons HD a q Hq dim Hdim Hd Hlen ε t).
  assert (Hdeep: frtCellPairDeepCell HD (DepsCohs3ChainCons a) t
    = f_equal unassoc (frtCellPairDeepCell HD a t)) by now reflexivity.
  rewrite Hdeep.
  assert (Hmap: forall (x y: CellHere dc3) (h: x = y),
    f_equal (fun z: CellHere (proj1DepsCohs3 dc3) =>
      restrCell (proj1DepsCohs3 dc3).(_depsCohs2).(_extraDepsCohs) q.+1 Hq ε z.1 z.2)
      (eq_sym (f_equal unassoc h))
    = f_equal unassoc (f_equal (fun z: CellHere dc3 =>
        restrCell dc3.(_depsCohs2).(_extraDepsCohs) q (⇓ Hq) ε z.1 z.2) (eq_sym h))).
  { intros x y h. destruct h. now reflexivity. }
  rewrite (Hmap _ _ (frtCellPairDeepCell HD a t)).
  symmetry.
  lazymatch goal with
  | |- @f_equal ?A ?B ?F ?x ?z (@eq_trans _ _ ?y _ ?h ?j) = _ =>
    now exact (@eq_trans_map_distr A B x y z F h j)
  end.
Defined.

Lemma descCellPairRestrTotalIrr {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim dim': nat) (e: dim = dim')
  (Hdim: dim <= M) (Hdim': dim' <= M)
  (Hd: dim = (q + p)%nat) (Hd': dim' = (q + p)%nat)
  (Hlen Hlen': cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (ε: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrTotal HD a q Hq dim Hdim Hd Hlen ε t
  = f_equal (frtCellPair HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
      (pshFaceDimIrr (g X) e ε t)
    • descCellPairRestrTotal HD a q Hq dim' Hdim' Hd' Hlen' ε t.
Proof.
  unfold descCellPairRestrTotal.
  rewrite (descCellPairRestrCanonicalIrr HD a q Hq dim dim' e Hdim Hdim' Hd Hd' Hlen Hlen' ε t).
  rewrite <- eq_trans_assoc.
  now reflexivity.
Defined.

Definition frtPairRead {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (z: νTotal S0) :=
  ((getFrame (extChainDeps (cohsChainExt cB)) z.1;
    chainPainting (cohsChainExt cB) z.1 z.2)
   : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D}).

Definition descPairFaceComparisonZero {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (ε: arity) (z: νTotal (next S0)):
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let w := deepCell (cohs3ChainDepsCohs2 a) z in
  frtPairRead cb (gFaceC S0 (descChain HD).2 0 p Hdim ε z)
    = restrCell dc3.(_depsCohs2).(_extraDepsCohs) 0 Hq ε w.1 w.2.
Proof.
  intros cb w.
  refine (f_equal (frtPairRead cb)
    (gFaceCAsνFace S0 (descChain HD).2 p Hdim cb Hlen ε z) • _).
  refine (chainPaintingGetPainting (cohsChainExt cb)
    (mkRestrFrame (depsCohs := dc3.(_depsCohs2).(_depsCohs)) 0 leR_O ε
      (getFrame (cohsChainNext cb) z.1).1)
    (nth (getFrame (cohsChainNext cb) z.1).2 ε) • _).
  now exact (f_equal (frtPairRestrAt dc3.(_depsCohs2).(_depsCohs) ε)
    (getFrameDeepCell (cohs3ChainDepsCohs2 a) z)).
Defined.

Lemma descPairFaceComparison {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3):
  forall (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (ε: arity) (t: νTotal (next S0)),
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let z := deepCell (cohs3ChainDepsCohs2 a) t in
  frtPairRead cb (gFaceC S0 (descChain HD).2 0 dim Hdim ε t)
  = restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq ε z.1 z.2.
Proof.
  induction a as [|p k dc3 a IH]; intros q Hq dim Hdim Hd Hlen ε t cb z.
  - destruct q as [|q].
    + subst dim.
      now exact (descPairFaceComparisonZero HD DepsCohs3ChainNil Hlen Hq Hdim ε t).
    + destruct (leR_O_contra Hq).
  - destruct q as [|q].
    + subst dim.
      now exact (descPairFaceComparisonZero HD (DepsCohs3ChainCons a) Hlen Hq Hdim ε t).
    + now exact (f_equal unassoc (IH q (⇓ Hq) dim Hdim
        (Hd • plus_n_Sm q p)
        (Hlen • plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p)
        ε t)).
Defined.

Lemma descPairFaceComparisonZeroRead {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (ε: arity) (t: νTotal (next S0)):
  descPairFaceComparison HD a 0 Hq p Hdim eq_refl Hlen ε t
  = descPairFaceComparisonZero HD a Hlen Hq Hdim ε t.
Proof. destruct a; now reflexivity. Defined.

Lemma descPairFaceComparisonCons {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p.+1 k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q.+1 <= k.+1) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q.+1 + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))) + p)%nat)
  (ε: arity) (t: νTotal (next S0)):
  descPairFaceComparison HD (DepsCohs3ChainCons a) q.+1 Hq dim Hdim Hd Hlen ε t
  = f_equal unassoc (descPairFaceComparison HD a q (⇓ Hq) dim Hdim
      (Hd • plus_n_Sm q p)
      (Hlen • plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p) ε t).
Proof. now reflexivity. Defined.

Lemma descCellPairRestrCanonicalZeroAsFace {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (ε: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrCanonicalZero HD a Hlen Hq Hdim ε t
  = f_equal (frtPairRead (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
      (descCellFace HD p Hdim Hdim ε t)
    • descPairFaceComparisonZero HD a Hlen Hq Hdim ε (descCell (DescS HD) t).
Proof.
  rewrite (descCanonicalZeroAsPair HD a Hlen Hq Hdim ε t).
  rewrite (descCellPairRestrAtAsFace HD
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) p Hdim Hlen ε t).
  unfold descPairFaceComparisonZero.
  cbn [getFrameDeepCell f_equal].
  now rewrite eq_trans_refl_r.
Defined.

Lemma descCellPairRestrCanonicalAsFace {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3):
  forall (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (ε: arity) (t: (g X).(G0) M.+1),
  descCellPairRestrCanonical HD a q Hq dim Hdim Hd Hlen ε t
  = f_equal (frtPairRead (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
      (descCellFace HD dim Hdim Hdim ε t)
    • descPairFaceComparison HD a q Hq dim Hdim Hd Hlen ε (descCell (DescS HD) t).
Proof.
  induction a as [|p k dc3 a IH]; intros q Hq dim Hdim Hd Hlen ε t.
  - destruct q as [|q].
    + subst dim.
      rewrite (descCellPairRestrCanonicalZeroRead HD DepsCohs3ChainNil Hlen Hq Hdim ε t).
      rewrite (descPairFaceComparisonZeroRead HD DepsCohs3ChainNil Hlen Hq Hdim ε (descCell (DescS HD) t)).
      apply descCellPairRestrCanonicalZeroAsFace.
    + destruct (leR_O_contra Hq).
  - destruct q as [|q].
    + subst dim.
      rewrite (descCellPairRestrCanonicalZeroRead HD (DepsCohs3ChainCons a) Hlen Hq Hdim ε t).
      rewrite (descPairFaceComparisonZeroRead HD (DepsCohs3ChainCons a) Hlen Hq Hdim ε (descCell (DescS HD) t)).
      apply descCellPairRestrCanonicalZeroAsFace.
    + rewrite (descCellPairRestrCanonicalCons HD a q Hq dim Hdim Hd Hlen ε t).
      rewrite (descPairFaceComparisonCons HD a q Hq dim Hdim Hd Hlen ε (descCell (DescS HD) t)).
      rewrite (IH q (⇓ Hq) dim Hdim (Hd • plus_n_Sm q p)
        (Hlen • plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p) ε t).
      lazymatch goal with
      | |- @f_equal ?A ?B ?F ?x ?z (@eq_trans _ _ ?y _ ?h ?j) = _ =>
        refine (eq_trans (@eq_trans_map_distr A B x y z F h j) _)
      end.
      apply (f_equal (fun e => e • _)).
      lazymatch goal with
      | |- @f_equal ?B ?C ?g ?u ?v (@f_equal ?A _ ?f ?x ?y ?h) = _ =>
        now exact (@f_equal_compose A B C x y f g h)
      end.
Defined.

Lemma frtPairReadDeepCell {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3) (z: νTotal (next S0)):
  frtPairRead (DepsCohsChainCons (frtChainUp a)) z
  = deepCell (cohs3ChainDepsCohs2 a) z.
Proof.
  induction a as [|p k dc3 a IH].
  - now reflexivity.
  - now exact (f_equal unassoc IH).
Defined.

Lemma frtPairReadDeepCellAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (t: (g X).(G0) M.+1):
  frtPairReadDeepCell a (descCell (DescS HD) t) = frtCellPairDeepCell HD a t.
Proof.
  induction a as [|p k dc3 a IH].
  - now reflexivity.
  - now exact (f_equal (fun h => f_equal unassoc h) IH).
Defined.

Definition descPairFaceComparisonTotal {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (ε: arity) (z: νTotal (next S0)):
  let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a) in
  let w := frtPairRead (DepsCohsChainCons (frtChainUp a)) z in
  frtPairRead cb (gFaceC S0 (descChain HD).2 0 dim Hdim ε z)
    = restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq ε w.1 w.2 :=
  descPairFaceComparison HD a q Hq dim Hdim Hd Hlen ε z
  • f_equal (fun w: CellHere dc3 =>
      restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq ε w.1 w.2)
      (eq_sym (frtPairReadDeepCell a z)).

Lemma descCellPairRestrTotalAsFace {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (ε: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrTotal HD a q Hq dim Hdim Hd Hlen ε t
  = f_equal (frtPairRead (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
      (descCellFace HD dim Hdim Hdim ε t)
    • descPairFaceComparisonTotal HD a q Hq dim Hdim Hd Hlen ε (descCell (DescS HD) t).
Proof.
  unfold descCellPairRestrTotal, descPairFaceComparisonTotal.
  rewrite (descCellPairRestrCanonicalAsFace HD a q Hq dim Hdim Hd Hlen ε t).
  rewrite (frtPairReadDeepCellAt HD a t).
  rewrite <- eq_trans_assoc.
  now reflexivity.
Defined.

End FG.
End Canonical.

(** Canonical constructions shared by the higher correspondence proofs. *)
Module Type CanonicalSig (A: LayerGpdSig)
  (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Include Canonical A Base Translations.
End CanonicalSig.
