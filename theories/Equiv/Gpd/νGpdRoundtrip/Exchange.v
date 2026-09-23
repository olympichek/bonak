(** Canonical comparison paths and the local coherence square used by
    positive restrictions in the backward round trip. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Canonical.
From Bonak.Lib Require Import Equiv.
From Bonak.Equiv.Gpd Require Import PathAlgebra.
From Bonak Require Import Limit.
Import Logic.EqNotations.

Set Primitive Projections.
From Bonak Require Import νGpd.Pasting.

Set Keyed Unification.

Module ExchangeOn (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base)
  (CanonicalBase: Bonak.Equiv.Gpd.νGpdRoundtrip.Canonical.CanonicalSig A Base Translations).
Import A.

Module Export Canonical := CanonicalBase.

Definition localPairRead {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (z: CellRestr dc3Top): CellRestr dc3 :=
  (getFrame (extChainDeps (cohsChainExt
     (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))) z.1;
   chainPainting (cohsChainExt
     (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) z.1 z.2).

Definition localReadRebuild {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (z: CellRestr dc3):
  localPairRead a (faceRebuild a z) = z :=
  chainPaintingGetPainting (cohsChainExt
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) z.1 z.2.

Definition localRestriction {p k} (dc3: DepsCohs3 p k)
  (q: nat) (Hq: q <= k) (epsilon: arity) (z: CellHere dc3): CellRestr dc3 :=
  restrCell dc3.(_depsCohs2).(_extraDepsCohs) q Hq epsilon z.1 z.2.

(** This is the normal form for one comparison, before the final correction
    from deepCell to frtPairRead at the next stage. *)
Definition localFaceComparison {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (q: nat) (Hq: q <= k) (epsilon: arity) (z: CellHere dc3):
  localPairRead a
    (faceAt (cohs3ChainDepsCohs2 a) q Hq epsilon z.1 z.2)
  = localRestriction dc3 q Hq epsilon z :=
  localReadRebuild a (localRestriction dc3 q Hq epsilon z).

(** Local comparison coherence for all [Q] and [R], obtained from
    the read/rebuild normal forms. Positive layers use [R = 0]. *)
Lemma localFaceComparisonCoh {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q)
  (epsilon omega: arity) (w: CellBelow dc3):
  f_equal (localPairRead a)
    (faceAtCohUp e0 a Q HQ R HR epsilon omega w.1 w.2)
  • (localFaceComparison a R (HR ↕ HQ) omega
       (cellR e0 a Q HQ R HR epsilon omega w)
     • f_equal (localRestriction dc3 R (HR ↕ HQ) omega)
         (deepCellFaceAtUp e0 a Q.+1 (⇑ HQ) epsilon w.1 w.2))
  = localFaceComparison a Q HQ epsilon
      (cellL e0 a Q HQ R HR epsilon omega w)
    • (f_equal (localRestriction dc3 Q HQ epsilon)
         (deepCellFaceAtUp e0 a R (HR ↕ ↑ HQ) omega w.1 w.2)
       • restrCellCoh dc3 Q HQ R HR epsilon omega w.1 w.2).
Proof.
  rewrite (faceAtCohUpConj e0 a Q HQ R HR epsilon omega w.1 w.2).
  pose proof (readRebuildSquare
    (faceRebuild a) (localPairRead a) (localReadRebuild a)
    (f_equal (localRestriction dc3 Q HQ epsilon)
       (deepCellFaceAtUp e0 a R (HR ↕ ↑ HQ) omega w.1 w.2))
    (restrCellCoh dc3 Q HQ R HR epsilon omega w.1 w.2)
    (f_equal (localRestriction dc3 R (HR ↕ HQ) omega)
       (deepCellFaceAtUp e0 a Q.+1 (⇑ HQ) epsilon w.1 w.2))) as H.
  rewrite (@f_equal_comp2 _ _ _
    (localRestriction dc3 R (HR ↕ HQ) omega) (faceRebuild a) _ _
    (deepCellFaceAtUp e0 a Q.+1 (⇑ HQ) epsilon w.1 w.2)) in H.
  rewrite (@f_equal_comp2 _ _ _
    (localRestriction dc3 Q HQ epsilon) (faceRebuild a) _ _
    (deepCellFaceAtUp e0 a R (HR ↕ ↑ HQ) omega w.1 w.2)) in H.
  now exact H.
Defined.

Definition localZeroLength {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3):
  cohs2ChainLen (cohs3ChainDepsCohs2 a)
  = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + 0)%nat :=
  eq_sym (cohs2ChainDepsCohsLen (cohs3ChainDepsCohs2 a))
    • plus_n_O _.

(** The zero clause of [descPairFaceComparison] after removing the
    lower tail of the descent, retaining its three correction paths. *)
Definition localCanonicalZero {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (Hq: 0 <= k) (epsilon: arity) (z: {d: mkFrame (mkDepsCohs dc3Top.(_depsCohs2)).(_deps) &T
  mkPainting (mkDepsCohs dc3Top.(_depsCohs2)).(_extraDeps) d}):
  localPairRead a
    (faceAt (cohs3ChainDepsCohs2 a) 0 Hq epsilon
      (deepCell (cohs3ChainDepsCohs2 a) z).1
      (deepCell (cohs3ChainDepsCohs2 a) z).2)
  = localRestriction dc3 0 Hq epsilon (deepCell (cohs3ChainDepsCohs2 a) z) :=
  f_equal (localPairRead a)
    (faceDeepAsνFace (cohs3ChainDepsCohs2 a) 0 Hq
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) (localZeroLength a)
      epsilon z.1 z.2)
  • (chainPaintingGetPainting
       (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
       (mkRestrFrame 0 leR_O epsilon
          (getFrame (cohsChainNext (cohs2ChainDepsCohs
            (cohs3ChainDepsCohs2 a))) z.1).1)
       (nth (getFrame (cohsChainNext (cohs2ChainDepsCohs
          (cohs3ChainDepsCohs2 a))) z.1).2 epsilon)
     • f_equal (frtPairRestrAt dc3.(_depsCohs2).(_depsCohs) epsilon)
         (getFrameDeepCell (cohs3ChainDepsCohs2 a) z)).

Lemma localCanonicalZeroNormal {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (Hq: 0 <= k) (epsilon: arity) (z: {d: mkFrame (mkDepsCohs dc3Top.(_depsCohs2)).(_deps) &T
  mkPainting (mkDepsCohs dc3Top.(_depsCohs2)).(_extraDeps) d}):
  localCanonicalZero a Hq epsilon z =
  localFaceComparison a 0 Hq epsilon (deepCell (cohs3ChainDepsCohs2 a) z).
Proof.
  unfold localCanonicalZero, localFaceComparison, localReadRebuild.
  rewrite eq_trans_assoc.
  symmetry.
  now exact (faceDeepAsνFaceReadCellZero (cohs3ChainDepsCohs2 a) Hq
    (localZeroLength a) epsilon z.1 z.2).
Defined.

(** The positive comparison and its normal form reassociate along
    the same path. *)
Lemma localFaceComparisonCons {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p.+1 k} (a: DepsCohs3Chain dc3Top dc3)
  (q: nat) (Hq: q.+1 <= k.+1) (epsilon: arity) (z: {d: mkFrame (mkDepsCohs dc3Top.(_depsCohs2)).(_deps) &T
  mkPainting (mkDepsCohs dc3Top.(_depsCohs2)).(_extraDeps) d}):
  localFaceComparison (DepsCohs3ChainCons a) q.+1 Hq epsilon
    (deepCell (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)) z)
  = f_equal unassoc
      (localFaceComparison a q (⇓ Hq) epsilon
        (deepCell (cohs3ChainDepsCohs2 a) z)).
Proof.
  unfold localFaceComparison, localReadRebuild, localRestriction.
  cbn [cohs3ChainDepsCohs2 cohs2ChainDepsCohs cohsChainExt].
  rewrite chainPaintingGetPaintingCons.
  now reflexivity.
Defined.

(** A comparison through a common intermediate face. *)
Lemma readSectionPrefix {U V: Type} (read: U -> V)
  {a b c: U} {v: V} (alpha: a = b) (beta: c = b)
  (tail: read b = v) (normal: read c = v)
  (H: f_equal read beta • tail = normal):
  f_equal read alpha • tail
  = f_equal read (alpha • eq_sym beta) • normal.
Proof.
  now rewrite eq_trans_map_distr, <- eq_sym_map_distr,
    <- eq_trans_assoc, <- H, eq_trans_sym_cancel_l.
Defined.

#[local] Arguments Desc {X n Xpre}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments descPairFaceComparisonZero {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparison {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonZeroRead {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonCons {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonTotal {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments frtPairReadDeepCell {M XpB0 S0 p k dc3}.

Section CanonicalBridge.
Variable X: νGpds.

Definition descFaceAtPrefixZero {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (epsilon: arity) (z: νTotal (next S0)):
  gFaceC S0 (descChain HD).2 0 p Hdim epsilon z
  = faceAt (cohs3ChainDepsCohs2 a) 0 Hq epsilon
      (deepCell (cohs3ChainDepsCohs2 a) z).1
      (deepCell (cohs3ChainDepsCohs2 a) z).2 :=
  gFaceCAsνFace S0 (descChain HD).2 p Hdim
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen epsilon z
  • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 a) 0 Hq
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) (localZeroLength a)
      epsilon z.1 z.2).

(** A successor clause returns the parent path. The rebuilt top
    cell in its codomain is unchanged by conversion. *)
Fixpoint descFaceAtPrefix {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3) {struct a}:
  forall (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
    (Hd: dim = (q + p)%nat)
    (Hlen: cohs3ChainLen (descChain HD).2
      = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (epsilon: arity) (z: νTotal (next S0)),
  gFaceC S0 (descChain HD).2 0 dim Hdim epsilon z
  = faceAt (cohs3ChainDepsCohs2 a) q Hq epsilon
      (deepCell (cohs3ChainDepsCohs2 a) z).1
      (deepCell (cohs3ChainDepsCohs2 a) z).2.
Proof.
  destruct a as [|p k dc3 a]; intros q Hq dim Hdim Hd Hlen epsilon z.
  - destruct q as [|q].
    + subst dim.
      now exact (descFaceAtPrefixZero HD DepsCohs3ChainNil Hlen Hq Hdim epsilon z).
    + destruct (leR_O_contra Hq).
  - destruct q as [|q].
    + subst dim.
      now exact (descFaceAtPrefixZero HD (DepsCohs3ChainCons a) Hlen Hq Hdim epsilon z).
    + now exact (@descFaceAtPrefix M XpB0 S0 HD p.+1 k dc3 a q (⇓ Hq)
        dim Hdim (Hd • plus_n_Sm q p)
        (Hlen • plus_n_Sm (cohsChainLen
          (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p) epsilon z).
Defined.

Lemma descPairFaceComparisonZeroNormal {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (epsilon: arity) (z: νTotal (next S0)):
  descPairFaceComparisonZero HD a Hlen Hq Hdim epsilon z
  = f_equal (localPairRead a)
      (descFaceAtPrefixZero HD a Hlen Hq Hdim epsilon z)
    • localFaceComparison a 0 Hq epsilon (deepCell (cohs3ChainDepsCohs2 a) z).
Proof.
  unfold descPairFaceComparisonZero, descFaceAtPrefixZero.
  apply readSectionPrefix.
  now exact (localCanonicalZeroNormal a Hq epsilon z).
Defined.

(** Precise canonical comparison bridge. The induction has the same
    dimensions and length proofs as descPairFaceComparison itself. *)
Lemma descPairFaceComparisonNormal {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3):
  forall (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
    (Hd: dim = (q + p)%nat)
    (Hlen: cohs3ChainLen (descChain HD).2
      = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (epsilon: arity) (z: νTotal (next S0)),
  descPairFaceComparison HD a q Hq dim Hdim Hd Hlen epsilon z
  = f_equal (localPairRead a)
      (descFaceAtPrefix HD a q Hq dim Hdim Hd Hlen epsilon z)
    • localFaceComparison a q Hq epsilon (deepCell (cohs3ChainDepsCohs2 a) z).
Proof.
  induction a as [|p k dc3 a IH]; intros q Hq dim Hdim Hd Hlen epsilon z.
  - destruct q as [|q].
    + subst dim.
      rewrite (descPairFaceComparisonZeroRead HD DepsCohs3ChainNil
        Hlen Hq Hdim epsilon z).
      now exact (descPairFaceComparisonZeroNormal HD DepsCohs3ChainNil
        Hlen Hq Hdim epsilon z).
    + destruct (leR_O_contra Hq).
  - destruct q as [|q].
    + subst dim.
      rewrite (descPairFaceComparisonZeroRead HD (DepsCohs3ChainCons a)
        Hlen Hq Hdim epsilon z).
      now exact (descPairFaceComparisonZeroNormal HD (DepsCohs3ChainCons a)
        Hlen Hq Hdim epsilon z).
    + rewrite (descPairFaceComparisonCons HD a q Hq dim Hdim Hd Hlen epsilon z).
      rewrite (IH q (⇓ Hq) dim Hdim (Hd • plus_n_Sm q p)
        (Hlen • plus_n_Sm (cohsChainLen
          (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p) epsilon z).
      rewrite eq_trans_map_distr.
      rewrite (localFaceComparisonCons a q Hq epsilon z).
      rewrite f_equal_compose.
      now reflexivity.
Defined.

Lemma descPairFaceComparisonTotalNormal {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
  (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (epsilon: arity) (z: νTotal (next S0)):
  descPairFaceComparisonTotal HD a q Hq dim Hdim Hd Hlen epsilon z
  = f_equal (localPairRead a)
      (descFaceAtPrefix HD a q Hq dim Hdim Hd Hlen epsilon z)
    • (localFaceComparison a q Hq epsilon (deepCell (cohs3ChainDepsCohs2 a) z)
       • f_equal (localRestriction dc3 q Hq epsilon)
           (eq_sym (frtPairReadDeepCell a z))).
Proof.
  unfold descPairFaceComparisonTotal.
  rewrite (descPairFaceComparisonNormal HD a q Hq dim Hdim Hd Hlen epsilon z).
  now rewrite <- eq_trans_assoc.
Defined.

End CanonicalBridge.

#[local] Arguments Desc {X n Xpre}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments FrtDepsCohs {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments _fcXB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcRpB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcCohsB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtDcB {X M XpB0 S0 HD p k dcB cB}.

Section PairExchangeAtoms.
Variable X: νGpds.

(** The q-indexed version of frtPairRestrPaintingAt. *)
Definition frtPairRestrPaintingAtQ {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (q: nat) (Hq: q <= k) (ε: arity)
  (z: {D: mkFrame (mkDepsRestr (depsCohs := dcB)).(1) &T
          (mkPaintings ((mkDepsRestr (depsCohs := dcB));
             FC.(_fcXB))%extradepsrestr).2 D}):
  {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D} :=
  (mkRestrFrame (depsCohs := dcB) q Hq ε z.1;
   FC.(_fcRpB).2 q Hq ε z.1 z.2).

(** Same definition as frtPairSqExchange with dimension 0 replaced by q.
    Only the lower omega restriction remains dimension 0. *)
Definition frtPairSqExchangeQ {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (q: nat) (Hq: q <= k) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs := frtDcB FC)).(1)):
  frtPairRestrAt dcB ω
    ((mkDepsRestr (depsCohs := frtDcB FC)).(_restrFrames).2 q Hq ε D)
  = frtPairRestrPaintingAtQ FC q Hq ε
      ((mkDepsRestr (depsCohs := proj1DepsCohs (frtDcB FC))).(_restrFrames).2
         0 leR_O ω D.1;
       nth D.2 ω) :=
  (= eq_sym (FC.(_fcCohsB).2 q Hq 0 leR_O ε ω D.1);
     rewSwapSym _ (FC.(_fcCohsB).2 q Hq 0 leR_O ε ω D.1)
       (nth_lmap _ D.2 ω)).

End PairExchangeAtoms.

End ExchangeOn.

Module Type ExchangeSig (A: LayerGpdSig)
  (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base)
  (CanonicalBase: Bonak.Equiv.Gpd.νGpdRoundtrip.Canonical.CanonicalSig A Base Translations).
Include ExchangeOn A Base Translations CanonicalBase.
End ExchangeSig.
