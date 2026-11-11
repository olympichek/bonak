(** Maps of the terminal filler of an indexed prefix induce coherent maps
    of the extracted diagrams. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Notation LeSProp NatLemmas
  RewLemmas Funext Equiv PathSquares FinitePrefix.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Face Diagram Causality
  DiagramPrefix.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** Mapping the terminal filler preserves the faces and selected exchange
    of a stored prefix. *)

Module IndexedLayerCausalityOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (D: IndexedDiagramSig A Core Faces).
Import A.
Module Export Prefix := IndexedDiagramPrefixOn A Core Faces D.
Module Frame := Prefix.Frame.
Module C := Frame.Causality.
Module Painting := Frame.Painting.

Local Lemma composeExchangeSquare {M N: Type} (l r: M -> N)
  {u0 u1 u2 v0 v1 v2: M}
  (c0: l u0 = r v0) (c1: l u1 = r v1) (c2: l u2 = r v2)
  (p0: u0 = u1) (p1: u1 = u2) (q0: v0 = v1) (q1: v1 = v2)
  (h0: c0 • f_equal r q0 = f_equal l p0 • c1)
  (h1: c1 • f_equal r q1 = f_equal l p1 • c2):
  c0 • f_equal r (q0 • q1) = f_equal l (p0 • p1) • c2.
Proof.
  destruct p0, p1, q0, q1.
  change (c0 • eq_refl = eq_refl • c1) in h0.
  change (c1 • eq_refl = eq_refl • c2) in h1.
  change (c0 • eq_refl = eq_refl • c2).
  now exact (h0 • eq_trans_refl_l c1 • eq_sym (eq_trans_refl_r c1) • h1).
Defined.

Local Lemma reverseExchangeSquare {M N: Type} (l r: M -> N)
  {u0 u1 v0 v1: M} (c0: l u0 = r v0) (c1: l u1 = r v1)
  (p: u0 = u1) (q: v0 = v1)
  (h: c0 • f_equal r q = f_equal l p • c1):
  c1 • f_equal r (eq_sym q) = f_equal l (eq_sym p) • c0.
Proof.
  destruct p, q.
  change (c0 • eq_refl = eq_refl • c1) in h.
  change (c1 • eq_refl = eq_refl • c0).
  now exact (eq_trans_refl_r c1 • eq_sym (eq_trans_refl_l c1)
    • eq_sym h • eq_trans_refl_r c0 • eq_sym (eq_trans_refl_l c0)).
Defined.

Local Lemma exchangeInputSquare {X M N: Type} (l r: M -> N) (u v: X -> M)
  (c: forall x, l (u x) = r (v x)) {x y: X} (p: x = y):
  c x • f_equal r (f_equal v p) = f_equal l (f_equal u p) • c y.
Proof. destruct p. now exact (eq_trans_refl_r _ • eq_sym (eq_trans_refl_l _)). Defined.

Lemma prefixFaceOneRead (B: (νGpdAt 1).(prefix)) (E: νFrame B -> HGpd)
  q (Hq: q <= 0) a (x: prefixCell (B; E)):
  prefixFace (B; E) q Hq a x =
    νFace (dcTop := prefixCohs B) DepsCohsChainNil a x.1.
Proof.
  pose proof (leR0Eq Hq) as eqQ. subst q.
  unfold prefixFace.
  rewrite (C.chain2EndpointPackEq
    (completeChain2 (prefixCohs2 (B; E)))
    (prefixCohs2 (B; E); DepsCohs2ChainNil)).
  now exact (eq_sym (νFaceAsDeep (dc2Top := prefixCohs2 (B; E))
    DepsCohs2ChainNil a x.1 x.2)).
Defined.

Definition prefixFillerFaceMapOne (B: (νGpdAt 1).(prefix))
  (E F: νFrame B -> HGpd) (α: forall d, E d -> F d)
  q (Hq: q <= 0) a (x: prefixCell (B; E)):
  prefixFace (B; E) q Hq a x = prefixFace (B; F) q Hq a (x.1; α x.1 x.2) :=
  prefixFaceOneRead B E q Hq a x
    • eq_sym (prefixFaceOneRead B F q Hq a (x.1; α x.1 x.2)).

Local Lemma eraseChangeLower {P} {dc: DepsCohs3 P 0}
  (d: C.ChainedFaceData dc) (lower: C.LowerChainPackage dc) (upper: C.UpperChainPackage dc)
  (p: d.(C.lowerChain) = lower) (q: d.(C.upperChain) = upper):
  f_equal (fun z: C.LocalFaceData dc P => z.(C.lowerFace))
    (f_equal C.eraseChainedFaceData (C.changeChainedDataEq d lower upper p q)) =
  f_equal (@C.lowerChainFace P dc) p.
Proof. destruct d; cbn in p, q. now destruct p, q. Defined.

Section Layer.
Context {n} (B: (νGpdAt n.+2).(prefix)).
Local Abbreviation LowerChains :=
  ({d: DepsCohs2 0 n &T DepsCohs2Chain (prefixCohs2 B) d}).
Local Definition commonChain: LowerChains := completeChain2 (prefixCohs2 B).

Definition topExtension (E: νFrame B -> HGpd): DepsCohs2Extension n 0 (prefixCohs2 B) :=
  @TopCoh2Dep n (prefixCohs2 B) (prefixThird (B; E)).

Definition commonReadoutData (E: νFrame B -> HGpd) (s: LowerChains):
  C.LocalFaceData (prefixCohs3 (B; E)) n :=
  @C.Build_LocalFaceData n 0 (prefixCohs3 (B; E)) n
    (fun q Hq a x => faceDeep s.2 q Hq a x.1 x.2)
    (fun q Hq a x => Frame.upperReadout (Frame.canonicalContractionData s.2).1
      (Painting.chain2Ext (topExtension E) s.2) q Hq a
      (Painting.readUpper s.2 (topExtension E) x).1
      (Painting.readUpper s.2 (topExtension E) x).2)
    (fun q Hq r Hr a b x => Frame.reconstructedExchange s.2
      (Frame.canonicalContractionData s.2) (Painting.chain2Ext (topExtension E) s.2)
      q Hq r Hr a b (Painting.readUpper s.2 (topExtension E) x).1
      (Painting.readUpper s.2 (topExtension E) x).2).

Definition commonUpper (E: νFrame B -> HGpd) :=
  C.upperFace (commonReadoutData E commonChain).
Definition commonExchange (E: νFrame B -> HGpd) :=
  C.faceExchange (commonReadoutData E commonChain).

Definition commonReadoutNormalize (E: νFrame B -> HGpd):
  commonReadoutData E commonChain = normalizedPrefixLocalData (B; E) :=
  eq_sym (f_equal (commonReadoutData E) (prefixLowerChain (B; E)))
    • Frame.canonicalReadoutDataNormalize (completeChain3 (prefixCohs3 (B; E))).2
    • prefixLocalDataNormalize (B; E).

Local Lemma prefixNormalizeLower (E: νFrame B -> HGpd):
  f_equal (fun d: C.LocalFaceData (prefixCohs3 (B; E)) n => d.(C.lowerFace))
    (prefixLocalDataNormalize (B; E)) = prefixLocalLower (B; E).
Proof.
  now exact (eraseChangeLower (prefixChainedData (B; E))
    (completeChain2 (prefixCohs2 B)) (completeChain2 (prefixCohs2 (B; E)))
    (prefixLowerChain (B; E)) (prefixUpperChain (B; E))).
Defined.

Lemma commonReadoutNormalizeLower (E: νFrame B -> HGpd):
  f_equal (fun d: C.LocalFaceData (prefixCohs3 (B; E)) n => d.(C.lowerFace))
    (commonReadoutNormalize E) = eq_refl.
Proof.
  unfold commonReadoutNormalize.
  rewrite 2 eq_trans_map_distr, fEqualSym.
  rewrite (f_equal_compose (commonReadoutData E)
    (fun d => d.(C.lowerFace)) (prefixLowerChain (B; E))).
  rewrite Frame.canonicalReadoutLower, prefixNormalizeLower.
  change ((eq_sym (prefixLocalLower (B; E)) • eq_refl) • prefixLocalLower (B; E) = eq_refl).
  rewrite eq_trans_refl_r. now apply eq_trans_sym_inv_l.
Defined.

Local Lemma commonReadoutLowerCompare (E: νFrame B -> HGpd)
  q (Hq: q <= n) a x:
  C.localDataLowerCompare (commonReadoutNormalize E) q Hq a x = eq_refl.
Proof.
  unfold C.localDataLowerCompare.
  rewrite <- (f_equal_compose
    (fun d: C.LocalFaceData (prefixCohs3 (B; E)) n => d.(C.lowerFace))
    (fun l => l q Hq a x) (commonReadoutNormalize E)).
  rewrite commonReadoutNormalizeLower. now reflexivity.
Defined.

Definition commonUpperCompare (E: νFrame B -> HGpd) q (Hq: q <= n.+1) a
  (x: prefixCell (B; E)):
  commonUpper E q Hq a x = prefixFace (B; E) q Hq a x :=
  C.localDataUpperCompare (commonReadoutNormalize E) q Hq a x.

Lemma commonExchangeCompare (E: νFrame B -> HGpd)
  q (Hq: q <= n) r (Hr: r <= q) a b (x: prefixCell (B; E)):
  commonExchange E q Hq r Hr a b x
    • f_equal (prefixFace B r (Hr ↕ Hq) b) (commonUpperCompare E q.+1 (⇑ Hq) a x)
  = f_equal (prefixFace B q Hq a) (commonUpperCompare E r (Hr ↕ ↑ Hq) b x)
    • prefixExchange (B; E) q Hq r Hr a b x.
Proof.
  pose proof (C.localDataPathSquareSource _ _ (commonReadoutNormalize E)
    q Hq r Hr a b x) as h.
  rewrite 2 commonReadoutLowerCompare, 2 eq_trans_refl_r in h.
  now exact (eq_sym h).
Defined.

Context (E F: νFrame B -> HGpd) (α: forall d, E d -> F d).

Definition mapLayerCell (x: prefixCell (B; E)): prefixCell (B; F) :=
  (x.1; α x.1 x.2).

Local Definition topMap: Painting.Cohs2ExtensionMap (topExtension E) (topExtension F) :=
  @Painting.TopCohs2Map n (prefixCohs2 B)
    (prefixThird (B; E)) (prefixThird (B; F)) α.
Local Definition descendedMap := Painting.chain2Map topMap commonChain.2.
Local Definition sourceInput (x: prefixCell (B; E)) :=
  Painting.readUpper commonChain.2 (topExtension E) x.
Local Definition targetInput (x: prefixCell (B; E)) :=
  Painting.readUpper commonChain.2 (topExtension F) (mapLayerCell x).

Local Definition inputMap (x: prefixCell (B; E)):
  Painting.mapExchangeCell descendedMap (sourceInput x) = targetInput x :=
  eq_sym (Painting.readUpperMap commonChain.2 topMap x).

Local Definition targetUpper q (Hq: q <= n.+1) a
  (z: Painting.ExchangeCell (Painting.chain2Ext (topExtension F) commonChain.2)) :=
  Frame.upperReadout (Frame.canonicalContractionData commonChain.2).1
    (Painting.chain2Ext (topExtension F) commonChain.2) q Hq a z.1 z.2.

Local Definition targetExchange q (Hq: q <= n) r (Hr: r <= q) a b
  (z: Painting.ExchangeCell (Painting.chain2Ext (topExtension F) commonChain.2)) :=
  Frame.reconstructedExchange commonChain.2 (Frame.canonicalContractionData commonChain.2)
    (Painting.chain2Ext (topExtension F) commonChain.2) q Hq r Hr a b z.1 z.2.

Local Definition firstUpperMap q (Hq: q <= n.+1) a (x: prefixCell (B; E)) :=
  Frame.upperReadoutMap (Frame.canonicalContractionData commonChain.2).1
    descendedMap q Hq a (sourceInput x).1 (sourceInput x).2.

Definition commonUpperMap q (Hq: q <= n.+1) a (x: prefixCell (B; E)):
  commonUpper E q Hq a x = commonUpper F q Hq a (mapLayerCell x) :=
  firstUpperMap q Hq a x • f_equal (targetUpper q Hq a) (inputMap x).

Lemma commonExchangeMap q (Hq: q <= n) r (Hr: r <= q) a b
  (x: prefixCell (B; E)):
  commonExchange E q Hq r Hr a b x
    • f_equal (prefixFace B r (Hr ↕ Hq) b) (commonUpperMap q.+1 (⇑ Hq) a x)
  = f_equal (prefixFace B q Hq a) (commonUpperMap r (Hr ↕ ↑ Hq) b x)
    • commonExchange F q Hq r Hr a b (mapLayerCell x).
Proof.
  refine (composeExchangeSquare (prefixFace B q Hq a) (prefixFace B r (Hr ↕ Hq) b)
    (commonExchange E q Hq r Hr a b x)
    (targetExchange q Hq r Hr a b (Painting.mapExchangeCell descendedMap (sourceInput x)))
    (commonExchange F q Hq r Hr a b (mapLayerCell x))
    (firstUpperMap r (Hr ↕ ↑ Hq) b x)
    (f_equal (targetUpper r (Hr ↕ ↑ Hq) b) (inputMap x))
    (firstUpperMap q.+1 (⇑ Hq) a x)
    (f_equal (targetUpper q.+1 (⇑ Hq) a) (inputMap x)) _ _).
  - now exact (Frame.reconstructedExchangeMap commonChain.2
      (Frame.canonicalContractionData commonChain.2) descendedMap
      q Hq r Hr a b (sourceInput x).1 (sourceInput x).2).
  - now exact (exchangeInputSquare (prefixFace B q Hq a) (prefixFace B r (Hr ↕ Hq) b)
      (targetUpper r (Hr ↕ ↑ Hq) b) (targetUpper q.+1 (⇑ Hq) a)
      (targetExchange q Hq r Hr a b) (inputMap x)).
Defined.

Definition prefixFillerFaceMap q (Hq: q <= n.+1) a (x: prefixCell (B; E)):
  prefixFace (B; E) q Hq a x = prefixFace (B; F) q Hq a (mapLayerCell x) :=
  eq_sym (commonUpperCompare E q Hq a x)
    • commonUpperMap q Hq a x • commonUpperCompare F q Hq a (mapLayerCell x).

Lemma prefixFillerExchangeMap q (Hq: q <= n) r (Hr: r <= q) a b
  (x: prefixCell (B; E)):
  prefixExchange (B; E) q Hq r Hr a b x
    • f_equal (prefixFace B r (Hr ↕ Hq) b) (prefixFillerFaceMap q.+1 (⇑ Hq) a x)
  = f_equal (prefixFace B q Hq a) (prefixFillerFaceMap r (Hr ↕ ↑ Hq) b x)
    • prefixExchange (B; F) q Hq r Hr a b (mapLayerCell x).
Proof.
  pose (start := reverseExchangeSquare (prefixFace B q Hq a) (prefixFace B r (Hr ↕ Hq) b)
    (commonExchange E q Hq r Hr a b x) (prefixExchange (B; E) q Hq r Hr a b x)
    (commonUpperCompare E r (Hr ↕ ↑ Hq) b x) (commonUpperCompare E q.+1 (⇑ Hq) a x)
    (commonExchangeCompare E q Hq r Hr a b x)).
  pose (middle := composeExchangeSquare (prefixFace B q Hq a) (prefixFace B r (Hr ↕ Hq) b)
    (prefixExchange (B; E) q Hq r Hr a b x) (commonExchange E q Hq r Hr a b x)
    (commonExchange F q Hq r Hr a b (mapLayerCell x))
    (eq_sym (commonUpperCompare E r (Hr ↕ ↑ Hq) b x)) (commonUpperMap r (Hr ↕ ↑ Hq) b x)
    (eq_sym (commonUpperCompare E q.+1 (⇑ Hq) a x)) (commonUpperMap q.+1 (⇑ Hq) a x)
    start (commonExchangeMap q Hq r Hr a b x)).
  now exact (composeExchangeSquare (prefixFace B q Hq a) (prefixFace B r (Hr ↕ Hq) b)
    (prefixExchange (B; E) q Hq r Hr a b x)
    (commonExchange F q Hq r Hr a b (mapLayerCell x))
    (prefixExchange (B; F) q Hq r Hr a b (mapLayerCell x))
    (eq_sym (commonUpperCompare E r (Hr ↕ ↑ Hq) b x) • commonUpperMap r (Hr ↕ ↑ Hq) b x)
    (commonUpperCompare F r (Hr ↕ ↑ Hq) b (mapLayerCell x))
    (eq_sym (commonUpperCompare E q.+1 (⇑ Hq) a x) • commonUpperMap q.+1 (⇑ Hq) a x)
    (commonUpperCompare F q.+1 (⇑ Hq) a (mapLayerCell x))
    middle (commonExchangeCompare F q Hq r Hr a b (mapLayerCell x))).
Defined.

End Layer.
End IndexedLayerCausalityOn.
