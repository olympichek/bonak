(** Maps of the terminal filler of an indexed prefix induce coherent maps
    of the extracted diagrams. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Notation LeSProp NatLemmas
  RewLemmas Funext Equiv PathSquares FinitePrefix.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Presheaf Require Import FaceStructure BoundedMap.
From Bonak.Presheaf.Gpd Require Import Presentation Comparison Transformation
  Bounded.
From Bonak.Reedy.Gpd Require Import Reedy Matching ExtensionMap Bounded.
From Bonak.Equiv.Gpd Require Import Face Diagram Causality DiagramPrefix.

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


(** Bounded maps of indexed prefix data induce coherent maps of the
    extracted presentations, preserving the selected face comparisons. *)

Module IndexedDiagramCausalityOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (D: IndexedDiagramSig A Core Faces).
Import A.
Module LayerMap := IndexedLayerCausalityOn A Core Faces D.
Module Export Prefix := LayerMap.Prefix.
Module C := Prefix.Comparisons.

Definition packedCarrier (Y: νGpds) n: HGpd := prefixCell (νGpdPack n.+1 Y).1.
Definition indexedFace (Y: νGpds) n := prefixFace (νGpdPack n.+2 Y).1.
Definition indexedExchange (Y: νGpds) n := prefixExchange (νGpdPack n.+3 Y).1.

Definition packedFaceStructure (Y: νGpds): FaceStr arity := {|
  S0 := packedCarrier Y;
  SFace := indexedFace Y;
|}.
Definition packedFaceCoherence (Y: νGpds): CohOf (packedFaceStructure Y) :=
  indexedExchange Y.

Section BoundedReadout.
Context (Y Z: νGpds) (B: nat -> SProp) (down: forall n, B n.+1 -> B n).
Context (f: forall n, B n -> packedCarrier Y n -> packedCarrier Z n).
Context (indexedFaceMap: forall n q (Hq: q <= n) a (h: B n.+1) (x: packedCarrier Y n.+1),
  indexedFace Z n q Hq a (f n.+1 h x) =
    f n (down n h) (indexedFace Y n q Hq a x)).
Context (indexedExchangeMap: forall n q (Hq: q <= n) r (Hr: r <= q) a b
  (h: B n.+2) (x: packedCarrier Y n.+2),
  (f_equal (indexedFace Z n q Hq a) (indexedFaceMap n.+1 r (Hr ↕ ↑ Hq) b h x)
    • indexedFaceMap n q Hq a (down n.+1 h) (indexedFace Y n.+1 r (Hr ↕ ↑ Hq) b x))
    • f_equal (f n (down n (down n.+1 h))) (indexedExchange Y n q Hq r Hr a b x)
  = indexedExchange Z n q Hq r Hr a b (f n.+2 h x)
    • (f_equal (indexedFace Z n r (Hr ↕ Hq) b) (indexedFaceMap n.+1 q.+1 (⇑ Hq) a h x)
       • indexedFaceMap n r (Hr ↕ Hq) b (down n.+1 h) (indexedFace Y n.+1 q.+1 (⇑ Hq) a x))).

Definition rawToIndexedCell n (h: B n) (x: (Extraction.g Y).(G0) n): packedCarrier Z n :=
  f n h ((globalToPackedComparison Y).(C.comparisonCell) n x).

Definition rawToIndexedFace n q (Hq: q <= n) a (h: B n.+1)
  (x: (Extraction.g Y).(G0) n.+1):
  indexedFace Z n q Hq a (rawToIndexedCell n.+1 h x) =
    rawToIndexedCell n (down n h) ((Extraction.g Y).(GFace) n q Hq a x) :=
  indexedFaceMap n q Hq a h ((globalToPackedComparison Y).(C.comparisonCell) n.+1 x)
    • f_equal (f n (down n h)) ((globalToPackedComparison Y).(C.comparisonFace) n q Hq a x).

Lemma rawToIndexedExchange n q (Hq: q <= n) r (Hr: r <= q) a b
  (h: B n.+2) (x: (Extraction.g Y).(G0) n.+2):
  (f_equal (indexedFace Z n q Hq a) (rawToIndexedFace n.+1 r (Hr ↕ ↑ Hq) b h x)
    • rawToIndexedFace n q Hq a (down n.+1 h) ((Extraction.g Y).(GFace) n.+1 r (Hr ↕ ↑ Hq) b x))
    • f_equal (rawToIndexedCell n (down n (down n.+1 h)))
        ((Extraction.g Y).(GFaceCoh) n q Hq r Hr a b x)
  = indexedExchange Z n q Hq r Hr a b (rawToIndexedCell n.+2 h x)
    • (f_equal (indexedFace Z n r (Hr ↕ Hq) b) (rawToIndexedFace n.+1 q.+1 (⇑ Hq) a h x)
       • rawToIndexedFace n r (Hr ↕ Hq) b (down n.+1 h)
           ((Extraction.g Y).(GFace) n.+1 q.+1 (⇑ Hq) a x)).
Proof.
  now exact (composeFaceSquare
    ((globalToPackedComparison Y).(C.comparisonCell) n)
    ((globalToPackedComparison Y).(C.comparisonCell) n.+1)
    ((globalToPackedComparison Y).(C.comparisonCell) n.+2)
    (f n (down n (down n.+1 h))) (f n.+1 (down n.+1 h)) (f n.+2 h)
    ((Extraction.g Y).(GFace) n q Hq a) ((Extraction.g Y).(GFace) n r (Hr ↕ Hq) b)
    ((Extraction.g Y).(GFace) n.+1 r (Hr ↕ ↑ Hq) b) ((Extraction.g Y).(GFace) n.+1 q.+1 (⇑ Hq) a)
    (indexedFace Y n q Hq a) (indexedFace Y n r (Hr ↕ Hq) b)
    (indexedFace Y n.+1 r (Hr ↕ ↑ Hq) b) (indexedFace Y n.+1 q.+1 (⇑ Hq) a)
    (indexedFace Z n q Hq a) (indexedFace Z n r (Hr ↕ Hq) b)
    (indexedFace Z n.+1 r (Hr ↕ ↑ Hq) b) (indexedFace Z n.+1 q.+1 (⇑ Hq) a)
    ((globalToPackedComparison Y).(C.comparisonFace) n q Hq a)
    ((globalToPackedComparison Y).(C.comparisonFace) n r (Hr ↕ Hq) b)
    ((globalToPackedComparison Y).(C.comparisonFace) n.+1 r (Hr ↕ ↑ Hq) b)
    ((globalToPackedComparison Y).(C.comparisonFace) n.+1 q.+1 (⇑ Hq) a)
    (indexedFaceMap n q Hq a (down n.+1 h)) (indexedFaceMap n r (Hr ↕ Hq) b (down n.+1 h))
    (indexedFaceMap n.+1 r (Hr ↕ ↑ Hq) b h) (indexedFaceMap n.+1 q.+1 (⇑ Hq) a h)
    ((Extraction.g Y).(GFaceCoh) n q Hq r Hr a b)
    (indexedExchange Y n q Hq r Hr a b) (indexedExchange Z n q Hq r Hr a b) x
    ((globalToPackedComparison Y).(C.comparisonCoh) n q Hq r Hr a b x)
    (indexedExchangeMap n q Hq r Hr a b h ((globalToPackedComparison Y).(C.comparisonCell) n.+2 x))).
Defined.

Definition readoutCell n (h: B n) (x: (Extraction.g Y).(G0) n): (Extraction.g Z).(G0) n :=
  packedReadout Z n (rawToIndexedCell n h x).

Definition readoutFace n q (Hq: q <= n) a (h: B n.+1) (x: (Extraction.g Y).(G0) n.+1):
  (Extraction.g Z).(GFace) n q Hq a (readoutCell n.+1 h x) =
    readoutCell n (down n h) ((Extraction.g Y).(GFace) n q Hq a x) :=
  packedNormalizedReadoutFace Z n q Hq a (rawToIndexedCell n.+1 h x)
    • f_equal (packedReadout Z n) (rawToIndexedFace n q Hq a h x).

Lemma readoutExchange n q (Hq: q <= n) r (Hr: r <= q) a b
  (h: B n.+2) (x: (Extraction.g Y).(G0) n.+2):
  (f_equal ((Extraction.g Z).(GFace) n q Hq a) (readoutFace n.+1 r (Hr ↕ ↑ Hq) b h x)
    • readoutFace n q Hq a (down n.+1 h) ((Extraction.g Y).(GFace) n.+1 r (Hr ↕ ↑ Hq) b x))
    • f_equal (readoutCell n (down n (down n.+1 h)))
        ((Extraction.g Y).(GFaceCoh) n q Hq r Hr a b x)
  = (Extraction.g Z).(GFaceCoh) n q Hq r Hr a b (readoutCell n.+2 h x)
    • (f_equal ((Extraction.g Z).(GFace) n r (Hr ↕ Hq) b) (readoutFace n.+1 q.+1 (⇑ Hq) a h x)
       • readoutFace n r (Hr ↕ Hq) b (down n.+1 h)
           ((Extraction.g Y).(GFace) n.+1 q.+1 (⇑ Hq) a x)).
Proof.
  now exact (composeFaceSquare
    (rawToIndexedCell n (down n (down n.+1 h)))
    (rawToIndexedCell n.+1 (down n.+1 h)) (rawToIndexedCell n.+2 h)
    (packedReadout Z n) (packedReadout Z n.+1) (packedReadout Z n.+2)
    ((Extraction.g Y).(GFace) n q Hq a) ((Extraction.g Y).(GFace) n r (Hr ↕ Hq) b)
    ((Extraction.g Y).(GFace) n.+1 r (Hr ↕ ↑ Hq) b) ((Extraction.g Y).(GFace) n.+1 q.+1 (⇑ Hq) a)
    (indexedFace Z n q Hq a) (indexedFace Z n r (Hr ↕ Hq) b)
    (indexedFace Z n.+1 r (Hr ↕ ↑ Hq) b) (indexedFace Z n.+1 q.+1 (⇑ Hq) a)
    ((Extraction.g Z).(GFace) n q Hq a) ((Extraction.g Z).(GFace) n r (Hr ↕ Hq) b)
    ((Extraction.g Z).(GFace) n.+1 r (Hr ↕ ↑ Hq) b) ((Extraction.g Z).(GFace) n.+1 q.+1 (⇑ Hq) a)
    (rawToIndexedFace n q Hq a (down n.+1 h)) (rawToIndexedFace n r (Hr ↕ Hq) b (down n.+1 h))
    (rawToIndexedFace n.+1 r (Hr ↕ ↑ Hq) b h) (rawToIndexedFace n.+1 q.+1 (⇑ Hq) a h)
    (packedNormalizedReadoutFace Z n q Hq a) (packedNormalizedReadoutFace Z n r (Hr ↕ Hq) b)
    (packedNormalizedReadoutFace Z n.+1 r (Hr ↕ ↑ Hq) b)
    (packedNormalizedReadoutFace Z n.+1 q.+1 (⇑ Hq) a)
    ((Extraction.g Y).(GFaceCoh) n q Hq r Hr a b)
    (indexedExchange Z n q Hq r Hr a b) ((Extraction.g Z).(GFaceCoh) n q Hq r Hr a b) x
    (rawToIndexedExchange n q Hq r Hr a b h x)
    (packedNormalizedReadoutExchange Z n q Hq r Hr a b (rawToIndexedCell n.+2 h x))).
Defined.

Definition boundedReadoutMap:
  PresentationMap (boundPresentation B down (Extraction.g Y))
    (boundPresentation B down (Extraction.g Z)) :=
  boundPresentationMap B down (Extraction.g Y) (Extraction.g Z)
    readoutCell readoutFace readoutExchange.

End BoundedReadout.
Section SharedPrefix.
Context {N} (Y Z: νGpds)
  (prefixPath: (νGpdPack N Y).1 = (νGpdPack N Z).1).

Definition sharedPrefixCell n (h: n.+1 <= N) (x: packedCarrier Y n):
  packedCarrier Z n :=
  prefixCellTransport (earlierPrefixPath Y Z prefixPath n.+1 h) x.

Definition sharedPrefixCellEquiv n (h: n.+1 <= N):
  Equiv (packedCarrier Y n) (packedCarrier Z n) :=
  prefixCellTransportEquiv (earlierPrefixPath Y Z prefixPath n.+1 h).

Definition sharedPrefixFace n q (Hq: q <= n) a
  (h: n.+2 <= N) (x: packedCarrier Y n.+1):
  indexedFace Z n q Hq a (sharedPrefixCell n.+1 h x) =
    sharedPrefixCell n (↓ h) (indexedFace Y n q Hq a x) :=
  prefixFaceMap (earlierPrefixPath Y Z prefixPath n.+2 h)
    (earlierPrefixPath Y Z prefixPath n.+1 (↓ h))
    (earlierPrefixPathBond Y Z prefixPath n.+1 h) q Hq a x.

Definition sharedPrefixExchange n q (Hq: q <= n) r (Hr: r <= q) a b
  (h: n.+3 <= N) (x: packedCarrier Y n.+2):
  (f_equal (indexedFace Z n q Hq a)
      (sharedPrefixFace n.+1 r (Hr ↕ ↑ Hq) b h x)
    • sharedPrefixFace n q Hq a (↓ h)
        (indexedFace Y n.+1 r (Hr ↕ ↑ Hq) b x))
    • f_equal (sharedPrefixCell n (↓ (↓ h))) (indexedExchange Y n q Hq r Hr a b x)
  = indexedExchange Z n q Hq r Hr a b (sharedPrefixCell n.+2 h x)
    • (f_equal (indexedFace Z n r (Hr ↕ Hq) b)
        (sharedPrefixFace n.+1 q.+1 (⇑ Hq) a h x)
      • sharedPrefixFace n r (Hr ↕ Hq) b (↓ h)
          (indexedFace Y n.+1 q.+1 (⇑ Hq) a x)) :=
  prefixExchangeMap (earlierPrefixPath Y Z prefixPath n.+3 h)
    (earlierPrefixPath Y Z prefixPath n.+2 (↓ h))
    (earlierPrefixPath Y Z prefixPath n.+1 (↓ (↓ h)))
    (earlierPrefixPathBond Y Z prefixPath n.+2 h)
    (earlierPrefixPathBond Y Z prefixPath n.+1 (↓ h)) q Hq r Hr a b x.

Definition sharedPrefixReadoutCellEquiv n (h: n.+1 <= N):
  Equiv ((Extraction.g Y).(G0) n) ((Extraction.g Z).(G0) n) :=
  compEquiv ((globalToPackedComparison Y).(C.comparisonCell) n)
    (compEquiv (sharedPrefixCellEquiv n h) (packedReadout Z n)).

End SharedPrefix.

Local Definition symSym {T: Type} {x y: T} (p: x = y): eq_sym (eq_sym p) = p.
Proof. now destruct p. Defined.

Local Definition rightPathInduction {T: Type} (y: T)
  (P: forall x, x = y -> Type) (base: P y eq_refl): forall x p, P x p :=
  fun x p => rew [fun q: x = y => P x q] (symSym p) in
    match eq_sym p as q in (_ = z) return P z (eq_sym q) with
    | eq_refl => base
    end.

Definition fillerFaceMap {n} (B: (νGpdAt n.+1).(prefix))
  (E F: νFrame B -> HGpd) (α: forall d, E d -> F d)
  q (Hq: q <= n) a (x: prefixCell (B; E)):
  prefixFace (B; E) q Hq a x = prefixFace (B; F) q Hq a (x.1; α x.1 x.2).
Proof.
  destruct n as [|n].
  - now exact (LayerMap.prefixFillerFaceMapOne B E F α q Hq a x).
  - now exact (LayerMap.prefixFillerFaceMap B E F α q Hq a x).
Defined.

Definition prefixTopProjection {n} (B: (νGpdAt n).(prefix)) (E: νFrame B -> HGpd)
  {U V: (νGpdAt n.+1).(prefix)} (p: U = (B; E)) (q: V = unitExtension B)
  (x: prefixCell U): prefixCell V :=
  prefixCellTransport (eq_sym q) ((prefixCellTransport p x).1; tt).

Definition prefixTopBase {n} (B: (νGpdAt n).(prefix)) (E: νFrame B -> HGpd)
  {U V: (νGpdAt n.+1).(prefix)} (p: U = (B; E)) (q: V = unitExtension B):
  U.1 = V.1 := projT1_eq p • eq_sym (projT1_eq q).

Definition prefixTopProjectionFace {n} (B: (νGpdAt n.+1).(prefix)) (E: νFrame B -> HGpd):
  forall U (p: U = ((B; E): (νGpdAt n.+2).(prefix)))
    V (q: V = unitExtension B) j (Hj: j <= n) a (x: prefixCell U),
  prefixFace V j Hj a (prefixTopProjection B E p q x) =
    prefixCellTransport (prefixTopBase B E p q) (prefixFace U j Hj a x).
Proof.
  refine (rightPathInduction ((B; E): (νGpdAt n.+2).(prefix)) _ _).
  refine (rightPathInduction (unitExtension B) _ _).
  intros j Hj a x.
  now exact (eq_sym (fillerFaceMap B E (fun _ => gunit) (fun _ _ => tt) j Hj a x)).
Defined.

Definition prefixTopFaceMap {n} (B: (νGpdAt n.+1).(prefix)) (E: νFrame B -> HGpd)
  {U V: (νGpdAt n.+2).(prefix)} (p: U = (B; E)) (q: V = unitExtension B)
  (middle: U.1 = V.1) (h: prefixTopBase B E p q = middle)
  j (Hj: j <= n) a (x: prefixCell U):
  prefixFace V j Hj a (prefixTopProjection B E p q x) =
    prefixCellTransport middle (prefixFace U j Hj a x) :=
  prefixTopProjectionFace B E U p V q j Hj a x
    • f_equal (fun e => prefixCellTransport e (prefixFace U j Hj a x)) h.

Local Lemma reverseTopSquare {T: Type} {a b c d: T}
  (u: a = c) (v: b = d) (p: a = b) (q: c = d)
  (h: p • v = u • q): eq_sym u • p = q • eq_sym v.
Proof.
  destruct u, v.
  change (p • eq_refl = eq_refl • q) in h.
  change (eq_refl • p = q • eq_refl).
  now exact (eq_trans_refl_l p • eq_sym (eq_trans_refl_r p)
    • h • eq_trans_refl_l q • eq_sym (eq_trans_refl_r q)).
Defined.

Lemma prefixTopExchangeMap {n} (B: (νGpdAt n.+2).(prefix)) (E: νFrame B -> HGpd):
  forall U (p: U = ((B; E): (νGpdAt n.+3).(prefix)))
    V (q: V = unitExtension B)
    (middle: U.1 = V.1) (lower: U.1.1 = V.1.1)
    (hm: prefixTopBase B E p q = middle) (hl: projT1_eq middle = lower)
    j (Hj: j <= n) r (Hr: r <= j) a b (x: prefixCell U),
  (f_equal (prefixFace V.1 j Hj a)
      (prefixTopFaceMap B E p q middle hm r (Hr ↕ ↑ Hj) b x)
    • prefixFaceMap middle lower hl j Hj a (prefixFace U r (Hr ↕ ↑ Hj) b x))
    • f_equal (prefixCellTransport lower) (prefixExchange U j Hj r Hr a b x)
  = prefixExchange V j Hj r Hr a b (prefixTopProjection B E p q x)
    • (f_equal (prefixFace V.1 r (Hr ↕ Hj) b)
        (prefixTopFaceMap B E p q middle hm j.+1 (⇑ Hj) a x)
      • prefixFaceMap middle lower hl r (Hr ↕ Hj) b (prefixFace U j.+1 (⇑ Hj) a x)).
Proof.
  refine (rightPathInduction ((B; E): (νGpdAt n.+3).(prefix)) _ _).
  refine (rightPathInduction (unitExtension B) _ _).
  intros middle lower hm hl j Hj r Hr a b x. destruct hm, hl.
  cbn [prefixTopFaceMap prefixTopProjectionFace rightPathInduction symSym
    prefixTopProjection prefixTopBase prefixFaceMap prefixFaceTransport prefixCellTransport fillerFaceMap].
  rewrite f_equal_id.
  repeat rewrite eq_trans_refl_l.
  repeat rewrite eq_trans_refl_r.
  rewrite 2 fEqualSym.
  now exact (reverseTopSquare
    (f_equal (prefixFace B j Hj a)
      (@LayerMap.prefixFillerFaceMap n B E (fun _ => gunit) (fun _ _ => tt)
        r (Hr ↕ ↑ Hj) b x))
    (f_equal (prefixFace B r (Hr ↕ Hj) b)
      (@LayerMap.prefixFillerFaceMap n B E (fun _ => gunit) (fun _ _ => tt)
        j.+1 (⇑ Hj) a x))
    (prefixExchange (B; E) j Hj r Hr a b x)
    (prefixExchange (unitExtension B) j Hj r Hr a b (x.1; tt))
    (@LayerMap.prefixFillerExchangeMap n B E (fun _ => gunit) (fun _ _ => tt)
      j Hj r Hr a b x)).
Defined.

Section CollapseTop.
Context {n} (X: (νGpdAt n).(prefix)) (E: νFrame X -> HGpd).
Local Abbreviation Y := (completePrefix ((X; E): (νGpdAt n.+1).(prefix))).
Local Abbreviation Z := (completePrefix X).

Definition collapseBasePath: (νGpdPack n Y).1 = (νGpdPack n Z).1 :=
  projT1_eq (completionPack ((X; E): (νGpdAt n.+1).(prefix)))
    • eq_sym (projT1_eq (packedUnitPrefix X)).

Definition collapseIndexedTop (t: packedCarrier Y n): packedCarrier Z n :=
  prefixCellTransport (eq_sym (packedUnitPrefix X))
    ((prefixCellTransport (completionPack ((X; E): (νGpdAt n.+1).(prefix))) t).1; tt).

Definition collapseTopFaceLaw:
  BoundedMap.TopFace (packedFaceStructure Y) (packedFaceStructure Z)
    (sharedPrefixCell Y Z collapseBasePath) collapseIndexedTop.
Proof.
  unfold collapseBasePath, collapseIndexedTop.
  destruct n as [|k].
  - now exact tt.
  - intros q Hq a x.
    pose (Yk := completePrefix ((X; E): (νGpdAt k.+2).(prefix))).
    pose (Zk := completePrefix X).
    pose (bk := (projT1_eq (completionPack ((X; E): (νGpdAt k.+2).(prefix)))
        • eq_sym (projT1_eq (packedUnitPrefix X)):
      (νGpdPack k.+1 Yk).1 = (νGpdPack k.+1 Zk).1)).
    now exact (prefixTopFaceMap X E
      (completionPack ((X; E): (νGpdAt k.+2).(prefix))) (packedUnitPrefix X)
      (earlierPrefixPath Yk Zk bk k.+1 leR_refl)
      (eq_sym (earlierPrefixPathAt Yk Zk bk)) q Hq a x).
Defined.

Definition collapseTopExchangeLaw:
  BoundedMap.TopExchange (packedFaceStructure Y) (packedFaceStructure Z)
    (packedFaceCoherence Y) (packedFaceCoherence Z)
    (sharedPrefixCell Y Z collapseBasePath) (sharedPrefixFace Y Z collapseBasePath)
    collapseIndexedTop collapseTopFaceLaw.
Proof.
  unfold collapseTopFaceLaw, collapseBasePath, collapseIndexedTop.
  destruct n as [|[|k]].
  - now exact tt.
  - now exact tt.
  - intros q Hq r Hr a b x.
    pose (Yk := completePrefix ((X; E): (νGpdAt k.+3).(prefix))).
    pose (Zk := completePrefix X).
    pose (bk := (projT1_eq (completionPack ((X; E): (νGpdAt k.+3).(prefix)))
        • eq_sym (projT1_eq (packedUnitPrefix X)):
      (νGpdPack k.+2 Yk).1 = (νGpdPack k.+2 Zk).1)).
    now exact (prefixTopExchangeMap X E
      (νGpdPack k.+3 Yk).1 (completionPack ((X; E): (νGpdAt k.+3).(prefix)))
      (νGpdPack k.+3 Zk).1 (packedUnitPrefix X)
      (earlierPrefixPath Yk Zk bk k.+2 leR_refl)
      (earlierPrefixPath Yk Zk bk k.+1 (↓ leR_refl))
      (eq_sym (earlierPrefixPathAt Yk Zk bk))
      (earlierPrefixPathBond Yk Zk bk k.+1 leR_refl) q Hq r Hr a b x).
Defined.

Definition collapseCells :=
  BoundedMap.extendCell (packedFaceStructure Y) (packedFaceStructure Z) n
    (sharedPrefixCell Y Z collapseBasePath) collapseIndexedTop.
Definition collapseFaces :=
  BoundedMap.extendFace (packedFaceStructure Y) (packedFaceStructure Z) n
    (sharedPrefixCell Y Z collapseBasePath) (sharedPrefixFace Y Z collapseBasePath)
    collapseIndexedTop collapseTopFaceLaw.
Definition collapseExchanges :=
  BoundedMap.extendExchange (packedFaceStructure Y) (packedFaceStructure Z)
    (packedFaceCoherence Y) (packedFaceCoherence Z) n
    (sharedPrefixCell Y Z collapseBasePath) (sharedPrefixFace Y Z collapseBasePath)
    (sharedPrefixExchange Y Z collapseBasePath) collapseIndexedTop
    collapseTopFaceLaw collapseTopExchangeLaw.

Definition collapsePresentationMap:
  PresentationMap (cutPresentation n.+1 (Extraction.g Y))
    (cutPresentation n.+1 (Extraction.g Z)) :=
  boundedReadoutMap Y Z (fun k => k.+1 <= n.+1) (fun k h => ↓ h)
    collapseCells collapseFaces collapseExchanges.

Definition collapseDiagramMap:
  DiagramMap (restrictDiagram n.+1 (indexedDiagram Y))
    (restrictDiagram n.+1 (indexedDiagram Z)) :=
  cutPresentationDiagramMap n.+1 (Extraction.g Y) (Extraction.g Z)
    collapsePresentationMap.

Definition collapseInputEquiv:
  Equiv (prefixCell ((X; E): (νGpdAt n.+1).(prefix))) ((Extraction.g Y).(G0) n) :=
  compEquiv
    (prefixCellTransportEquiv (eq_sym (completionPack ((X; E): (νGpdAt n.+1).(prefix)))))
    (packedReadout Y n).

Definition collapseReadoutTop (t: (Extraction.g Y).(G0) n): (Extraction.g Z).(G0) n :=
  packedReadout Z n (collapseIndexedTop ((globalToPackedComparison Y).(C.comparisonCell) n t)).

Local Lemma prefixCellTransportCancel {k} {U V: (νGpdAt k.+1).(prefix)}
  (p: U = V) (t: prefixCell V):
  prefixCellTransport p (prefixCellTransport (eq_sym p) t) = t.
Proof. now destruct p. Defined.

Lemma collapseTopCell (t: prefixCell ((X; E): (νGpdAt n.+1).(prefix))):
  collapseReadoutTop (collapseInputEquiv t) = coherentUnitCellEquiv X (t.1; tt).
Proof.
  change (packedReadout Z n (collapseIndexedTop
    (invEq (packedReadout Y n) (packedReadout Y n
      (prefixCellTransport (eq_sym (completionPack ((X; E): (νGpdAt n.+1).(prefix)))) t))))
    = coherentUnitCellEquiv X (t.1; tt)).
  rewrite retEq. unfold collapseIndexedTop.
  rewrite prefixCellTransportCancel. now reflexivity.
Defined.

Lemma collapseTopMatchingMap (t: prefixCell ((X; E): (νGpdAt n.+1).(prefix))):
  matchingMap (restrictDiagram n.+1 (indexedDiagram Z))
      (collapseReadoutTop (collapseInputEquiv t)) = frameMatchingMap X t.1.
Proof.
  now exact (f_equal (matchingMap
    (restrictDiagram n.+1 (indexedDiagram Z))) (collapseTopCell t)).
Defined.
Lemma collapseDiagramTopCell (x: (Extraction.g Y).(G0) n):
  collapseDiagramMap.(mapCell) None x = collapseReadoutTop x.
Proof.
  change (packedReadout Z n
    (BoundedMap.extendCell (packedFaceStructure Y) (packedFaceStructure Z) n
      (sharedPrefixCell Y Z collapseBasePath) collapseIndexedTop n leR_refl
      ((globalToPackedComparison Y).(C.comparisonCell) n x)) = collapseReadoutTop x).
  now exact (f_equal (packedReadout Z n)
    (BoundedMap.extendCellTopPoint (packedFaceStructure Y) (packedFaceStructure Z) n
      (sharedPrefixCell Y Z collapseBasePath) collapseIndexedTop
      ((globalToPackedComparison Y).(C.comparisonCell) n x))).
Defined.

Lemma collapseDiagramLowerCell (i: Index n)
  (x: (Extraction.g Y).(G0) (rank i)):
  collapseDiagramMap.(mapCell) (Some i) x =
    sharedPrefixReadoutCellEquiv Y Z collapseBasePath (rank i)
      (rankBound i) x.
Proof.
  change (packedReadout Z (rank i)
    (BoundedMap.extendCell (packedFaceStructure Y) (packedFaceStructure Z) n
      (sharedPrefixCell Y Z collapseBasePath) collapseIndexedTop (rank i)
      (↑ (rankBound i))
      ((globalToPackedComparison Y).(C.comparisonCell) (rank i) x)) =
    packedReadout Z (rank i)
      (sharedPrefixCell Y Z collapseBasePath (rank i)
        (rankBound i)
        ((globalToPackedComparison Y).(C.comparisonCell) (rank i) x))).
  now exact (f_equal (packedReadout Z (rank i))
    (BoundedMap.extendCellBelowPoint (packedFaceStructure Y) (packedFaceStructure Z) n
      (sharedPrefixCell Y Z collapseBasePath) collapseIndexedTop (rank i)
      (rankBound i)
      ((globalToPackedComparison Y).(C.comparisonCell) (rank i) x))).
Defined.

Definition collapseDiagramLowerEquiv (i: Index n):
  Equiv ((Extraction.g Y).(G0) (rank i))
    ((Extraction.g Z).(G0) (rank i)).
Proof.
  pose (e := sharedPrefixReadoutCellEquiv Y Z collapseBasePath (rank i)
    (rankBound i)).
  refine (qinvEquiv (collapseDiagramMap.(mapCell) (Some i)) (invEq e) _ _).
  - intro x. now exact (f_equal (invEq e) (collapseDiagramLowerCell i x) • retEq e x).
  - intro y. now exact (collapseDiagramLowerCell i (invEq e y) • secEq e y).
Defined.

Lemma collapseDiagramLowerIsEquiv (i: Index n):
  IsEquiv (collapseDiagramMap.(mapCell) (Some i)).
Proof. now exact (collapseDiagramLowerEquiv i).(eqvIsEquiv). Defined.

Lemma collapseDiagramTopMatchingMap (t: prefixCell ((X; E): (νGpdAt n.+1).(prefix))):
  matchingMap (restrictDiagram n.+1 (indexedDiagram Z))
    (collapseDiagramMap.(mapCell) None (collapseInputEquiv t)) =
      frameMatchingMap X t.1.
Proof.
  now exact (f_equal (matchingMap
    (restrictDiagram n.+1 (indexedDiagram Z)))
    (collapseDiagramTopCell (collapseInputEquiv t)) • collapseTopMatchingMap t).
Defined.

Definition finiteDiagramExtension:
  extendByMatchingMap arity (finiteDiagram X)
    (prefixCell ((X; E): (νGpdAt n.+1).(prefix)))
    (fun t => frameMatchingMap X t.1) =
  finiteDiagram ((X; E): (νGpdAt n.+1).(prefix)) :=
  extensionEqFromDiagramMap collapseDiagramMap
    collapseInputEquiv (fun t => frameMatchingMap X t.1)
    collapseDiagramTopMatchingMap collapseDiagramLowerIsEquiv.

End CollapseTop.

End IndexedDiagramCausalityOn.
