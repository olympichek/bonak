(** Finite-prefix data underlying the canonical extracted coherent diagram. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Funext Notation RewLemmas
  FinitePrefix Limit SequentialLimit TelescopeCompletion LeSProp NatLemmas PathSquares.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Presheaf.Gpd Require Import Presentation Comparison.
From Bonak.Reedy.Gpd Require Import Reedy Bounded.
From Bonak.Equiv.Gpd Require Import Face Diagram Causality PositionExtraction.

Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module IndexedDiagramPrefixOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (D: IndexedDiagramSig A Core Faces).
Import A.
Module Export Diagram := D.
Module Readout := DiagramFacesOn A Core Faces D.
Module Frame := FrameCausalityOn A Core Faces.
Module Causality := Frame.Causality.
Module Position := PositionExtractionOn A Core Faces D.Extraction.
Module Comparisons := GpdComparison A.

(** The relative descent uses transparent arithmetic at residual levels
    zero, one and two, while retaining the extraction's original chains. *)
Definition packedState (Y: νGpds) n: Position.Partial.PartialState 0 n :=
  (n; ((νGpdPack n Y).1; ((νGpdPack n Y).2;
    Readout.descChain Y (Readout.descPack Y n)))).

Fixpoint selectedDescPack (Y: νGpds) (n: nat): Position.Relative.Desc Y n (packedState Y n) :=
  match n with
  | 0 => Position.Relative.DescZ Y
  | S n => Position.Relative.DescS Y (selectedDescPack Y n)
  end.

Definition selectedTotal (Y: νGpds) n:
  Extraction.gF0 Y n = prefixCell (νGpdPack (S n) Y).1 :=
  Position.Relative.descTotal Y (selectedDescPack Y n).

Fixpoint composeChain2 {P K} {top: DepsCohs2 P K}
  {p k} {mid: DepsCohs2 p k} {p' k'} {bot: DepsCohs2 p' k'}
  (a: DepsCohs2Chain top mid) (b: DepsCohs2Chain mid bot):
  DepsCohs2Chain top bot :=
  match b with
  | DepsCohs2ChainNil => a
  | DepsCohs2ChainCons b => DepsCohs2ChainCons (composeChain2 a b)
  end.

(** A canonical complete descent depends only on its starting data. *)
Fixpoint bottomChain2 {P}: forall K (dc: DepsCohs2 P K),
  {k: nat &T {d: DepsCohs2 0 k &T DepsCohs2Chain dc d}} :=
  match P with
  | 0 => fun K dc => (K; (dc; DepsCohs2ChainNil))
  | S P => fun K dc =>
      let s := bottomChain2 (S K) (proj1DepsCohs2 dc) in
      (s.1; (s.2.1; composeChain2 (DepsCohs2ChainCons DepsCohs2ChainNil) s.2.2))
  end.

Fixpoint bottomChain3 {P}: forall K (dc: DepsCohs3 P K),
  {k: nat &T {d: DepsCohs3 0 k &T DepsCohs3Chain dc d}} :=
  match P with
  | 0 => fun K dc => (K; (dc; DepsCohs3ChainNil))
  | S P => fun K dc =>
      let s := bottomChain3 (S K) (proj1DepsCohs3 dc) in
      (s.1; (s.2.1; cohs3ChainCompose (DepsCohs3ChainCons DepsCohs3ChainNil) s.2.2))
  end.

Lemma chain3ComposeLength {P K} {top: DepsCohs3 P K}
  {p k} {mid: DepsCohs3 p k} {p' k'} {bot: DepsCohs3 p' k'}
  (a: DepsCohs3Chain top mid) (b: DepsCohs3Chain mid bot):
  cohs3ChainLen (cohs3ChainCompose a b) = (cohs3ChainLen b + cohs3ChainLen a)%nat.
Proof. induction b; cbn [cohs3ChainCompose cohs3ChainLen]; [now reflexivity|now rewrite IHb]. Defined.

Lemma bottomChain3Length P K (dc: DepsCohs3 P K):
  cohs3ChainLen (bottomChain3 K dc).2.2 = P.
Proof.
  revert K dc; induction P as [|P IH]; intros K dc.
  - now reflexivity.
  - cbn [bottomChain3]. rewrite chain3ComposeLength, IH.
    cbn [cohs3ChainLen]. now rewrite <- plus_n_Sm, <- plus_n_O.
Defined.

(** Complete descent has a prescribed offset. The arithmetic transports
    below concern natural-number indices, not paths between cells. *)
Lemma bottomChain3Offset P K (dc: DepsCohs3 P K):
  (bottomChain3 K dc).1 = (P + K)%nat.
Proof.
  revert K dc; induction P as [|P IH]; intros K dc.
  - now reflexivity.
  - cbn [bottomChain3]. now exact (IH (S K) (proj1DepsCohs3 dc)
      • eq_sym (plus_n_Sm P K)).
Defined.

Definition completeChain3 {P} (dc: DepsCohs3 P 0):
  {d: DepsCohs3 0 P &T DepsCohs3Chain dc d} :=
  rew [fun k => {d: DepsCohs3 0 k &T DepsCohs3Chain dc d}]
    (bottomChain3Offset P 0 dc • eq_sym (plus_n_O P))
    in (bottomChain3 0 dc).2.

Local Lemma sameNatFiber {B: nat -> Type} {n} {x y: B n}
  (e: ((n; x): {k: nat &T B k}) = (n; y)): x = y.
Proof.
  pose proof (projT2_eq e) as h.
  rewrite (natUIP (projT1_eq e) eq_refl) in h. now exact h.
Defined.

Lemma bottomChain2Offset P K (dc: DepsCohs2 P K):
  (bottomChain2 K dc).1 = (P + K)%nat.
Proof.
  revert K dc; induction P as [|P IH]; intros K dc.
  - now reflexivity.
  - cbn [bottomChain2]. now exact (IH (S K) (proj1DepsCohs2 dc)
      • eq_sym (plus_n_Sm P K)).
Defined.

Definition completeChain2 {P} (dc: DepsCohs2 P 0):
  {d: DepsCohs2 0 P &T DepsCohs2Chain dc d} :=
  rew [fun k => {d: DepsCohs2 0 k &T DepsCohs2Chain dc d}]
    (bottomChain2Offset P 0 dc • eq_sym (plus_n_O P))
    in (bottomChain2 0 dc).2.

Lemma completeChain3Length {P} (dc: DepsCohs3 P 0):
  cohs3ChainLen (completeChain3 dc).2 = P.
Proof.
  pose proof (bottomChain3Length P 0 dc) as length.
  unfold completeChain3.
  generalize (bottomChain3Offset P 0 dc • eq_sym (plus_n_O P)).
  destruct (bottomChain3 0 dc) as [k [d c]] eqn:h; cbn in *.
  intro e; destruct e. now exact length.
Defined.

Lemma completeChain3Unique {P} (dc: DepsCohs3 P 0)
  (s: {d: DepsCohs3 0 P &T DepsCohs3Chain dc d})
  (h: cohs3ChainLen s.2 = P): s = completeChain3 dc.
Proof.
  now exact (sameNatFiber (sameNatFiber
    (chain3PackEqLen s.2 (completeChain3 dc).2
      (h • eq_sym (completeChain3Length dc))))).
Defined.

Lemma descChainNormalize (Y: νGpds) n:
  Readout.descChain Y (Readout.descPack Y n)
    = completeChain3 (Extraction.νDepsCohs3At (νGpdPack n Y).2).
Proof.
  now exact (completeChain3Unique
    (Extraction.νDepsCohs3At (νGpdPack n Y).2)
    (Readout.descChain Y (Readout.descPack Y n))
    (Readout.descChainLen Y (Readout.descPack Y n))).
Defined.

(** Face and exchange data at a tower position are already stored in
    its prefixes through the source cell of the operation. *)
Definition prefixCohs {n} (X: (νGpdAt (S n)).(prefix)): DepsCohs n 0 := {|
  _deps := toDepsRestr (νDataAt X.1).(restrFrames);
  _extraDeps := TopRestrDep X.2;
  _restrPaintings := (νDataAt X.1).(restrPaintings) X.2;
  _cohs := (νDataAt X.1).(cohFrames) X.2;
|}.

Definition prefixCohs2 {n} (X: (νGpdAt n.+2).(prefix)): DepsCohs2 n 0 := {|
  _depsCohs := prefixCohs X.1;
  _extraDepsCohs := TopCohDep X.2;
  _cohPaintings := (νDataAt X.1.1).(cohPaintings) X.1.2 X.2;
  _coh2Frames := (νDataAt X.1.1).(coh2Frames) X.1.2 X.2;
|}.

Definition prefixThird {n} (X: (νGpdAt n.+3).(prefix)):
  mkFrame (mkDepsRestr (depsCohs := mkDepsCohs (prefixCohs2 X.1))) -> HGpd.
Proof. now exact X.2. Defined.

Definition prefixCohs3 {n} (X: (νGpdAt n.+3).(prefix)): DepsCohs3 n 0.
Proof.
  unshelve econstructor.
  - now exact (prefixCohs2 X.1).
  - now exact (TopCoh2Dep (depsCohs2 := prefixCohs2 X.1) (prefixThird X)).
  - now exact ((νDataAt X.1.1.1).(coh2Paintings) X.1.1.2 X.1.2 (prefixThird X)).
Defined.

Definition prefixFace {n} (X: (νGpdAt n.+2).(prefix))
  q (Hq: q <= n) a (x: prefixCell X): prefixCell X.1 :=
  faceDeep (completeChain2 (prefixCohs2 X)).2 q Hq a x.1 x.2.

(** Adjacent face actions and their selected exchanges are observations
    of the prefix through their source cell. No later filler remains. *)
Definition prefixChainedData {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.ChainedFaceData (prefixCohs3 X) :=
  Causality.canonicalChainedFaceData (completeChain3 (prefixCohs3 X)).

Definition prefixLocalData {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.LocalFaceData (prefixCohs3 X) n :=
  Causality.eraseChainedFaceData (prefixChainedData X).

Definition prefixLowerChain {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.lowerChain (prefixChainedData X) = completeChain2 (prefixCohs2 X.1) :=
  Causality.chain2EndpointPackEq _ _.

Definition prefixUpperChain {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.upperChain (prefixChainedData X) = completeChain2 (prefixCohs2 X) :=
  Causality.chain2EndpointPackEq _ _.

Definition prefixLocalLower {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.lowerFace (prefixLocalData X) = prefixFace X.1 :=
  f_equal (@Causality.lowerChainFace n (prefixCohs3 X)) (prefixLowerChain X).

Definition normalizedPrefixChainedData {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.ChainedFaceData (prefixCohs3 X) :=
  Causality.changeChainedData (prefixChainedData X)
    (completeChain2 (prefixCohs2 X.1)) (completeChain2 (prefixCohs2 X))
    (prefixLowerChain X) (prefixUpperChain X).

Definition prefixExchange {n} (X: (νGpdAt n.+3).(prefix)):
  forall q (Hq: q <= n) r (Hr: r <= q) a b (x: prefixCell X),
  prefixFace X.1 q Hq a (prefixFace X r (Hr ↕ ↑ Hq) b x) =
    prefixFace X.1 r (Hr ↕ Hq) b (prefixFace X q.+1 (⇑ Hq) a x) :=
  Causality.chainedExchange (normalizedPrefixChainedData X).

Definition prefixChainedDataNormalize {n} (X: (νGpdAt n.+3).(prefix)):
  prefixChainedData X = normalizedPrefixChainedData X :=
  Causality.changeChainedDataEq (prefixChainedData X)
    (completeChain2 (prefixCohs2 X.1)) (completeChain2 (prefixCohs2 X))
    (prefixLowerChain X) (prefixUpperChain X).

Definition normalizedPrefixLocalData {n} (X: (νGpdAt n.+3).(prefix)):
  Causality.LocalFaceData (prefixCohs3 X) n :=
  Causality.eraseChainedFaceData (normalizedPrefixChainedData X).

Definition prefixLocalDataNormalize {n} (X: (νGpdAt n.+3).(prefix)):
  prefixLocalData X = normalizedPrefixLocalData X :=
  f_equal Causality.eraseChainedFaceData (prefixChainedDataNormalize X).

Lemma extractedChainedData (Y: νGpds) n:
  Causality.rawChainedFaceData (Extraction.νExt3At (νGpdPack n Y).2)
    (Readout.descChain Y (Readout.descPack Y n)) =
  normalizedPrefixChainedData (νGpdPack n.+3 Y).1.
Proof.
  refine (Causality.chainedFaceDataNormalize _ _ • _).
  refine (f_equal Causality.canonicalChainedFaceData (descChainNormalize Y n) • _).
  now exact (prefixChainedDataNormalize (νGpdPack n.+3 Y).1).
Defined.

(** Reading the original extraction at its packed positions preserves the
    selected exchange square, before any finite-prefix normalization. *)
Definition packedReadout (Y: νGpds) n:
  Equiv (prefixCell (νGpdPack (S n) Y).1) (Extraction.gF0 Y n) :=
  rewEquiv GDom (eq_sym (selectedTotal Y n)).

Definition packedRawData (Y: νGpds) n:
  Causality.ChainedFaceData (Extraction.νDepsCohs3At (νGpdPack n Y).2) :=
  Causality.rawChainedFaceData (Extraction.νExt3At (νGpdPack n Y).2)
    (Readout.descChain Y (Readout.descPack Y n)).

Definition packedRawFace (Y: νGpds) n q (Hq: q <= n) a
  (x: prefixCell (νGpdPack n.+2 Y).1): prefixCell (νGpdPack n.+1 Y).1 :=
  Causality.lowerChainFace (Causality.lowerChain (packedRawData Y n)) q Hq a x.

Definition packedRawExchange (Y: νGpds) n q (Hq: q <= n)
  r (Hr: r <= q) a b (x: prefixCell (νGpdPack n.+3 Y).1):
  packedRawFace Y n q Hq a (packedRawFace Y n.+1 r (Hr ↕ ↑ Hq) b x) =
    packedRawFace Y n r (Hr ↕ Hq) b (packedRawFace Y n.+1 q.+1 (⇑ Hq) a x) :=
  Causality.chainedExchange (packedRawData Y n) q Hq r Hr a b x.

Definition packedRawFaceNormalize (Y: νGpds) n q (Hq: q <= n) a
  (x: prefixCell (νGpdPack n.+2 Y).1):
  packedRawFace Y n q Hq a x = prefixFace (νGpdPack n.+2 Y).1 q Hq a x :=
  f_equal (fun c: {d: DepsCohs2 0 n &T
      DepsCohs2Chain (Extraction.νDepsCohs2At (νGpdPack n Y).2) d} =>
    faceDeep c.2 q Hq a x.1 x.2)
    (Causality.chain2EndpointPackEq
      (Causality.lowerChain (packedRawData Y n))
      (completeChain2 (prefixCohs2 (νGpdPack n.+2 Y).1))).

Lemma packedRawExchangeNormalize (Y: νGpds) n q (Hq: q <= n)
  r (Hr: r <= q) a b (x: prefixCell (νGpdPack n.+3 Y).1):
  (f_equal (packedRawFace Y n q Hq a)
      (packedRawFaceNormalize Y n.+1 r (Hr ↕ ↑ Hq) b x)
    • packedRawFaceNormalize Y n q Hq a
        (prefixFace (νGpdPack n.+3 Y).1 r (Hr ↕ ↑ Hq) b x))
    • prefixExchange (νGpdPack n.+3 Y).1 q Hq r Hr a b x
  = packedRawExchange Y n q Hq r Hr a b x
    • (f_equal (packedRawFace Y n r (Hr ↕ Hq) b)
        (packedRawFaceNormalize Y n.+1 q.+1 (⇑ Hq) a x)
      • packedRawFaceNormalize Y n r (Hr ↕ Hq) b
          (prefixFace (νGpdPack n.+3 Y).1 q.+1 (⇑ Hq) a x)).
Proof.
  pose proof (Causality.chainedDataPathSquareSource
    (packedRawData Y n) (normalizedPrefixChainedData (νGpdPack n.+3 Y).1)
    (extractedChainedData Y n) q Hq r Hr a b x) as h.
  rewrite 2 Causality.chainedDataPathLower, 2 Causality.chainedDataPathUpper in h.
  now exact h.
Defined.

Definition packedReadoutFace (Y: νGpds) n q (Hq: q <= n) a
  (x: prefixCell (νGpdPack n.+2 Y).1):
  (Extraction.g Y).(GFace) n q Hq a (packedReadout Y n.+1 x) =
    packedReadout Y n (packedRawFace Y n q Hq a x) :=
  Position.Relative.descFaceG Y (selectedDescPack Y n) 0 q Hq Hq a x.

Lemma packedReadoutExchange (Y: νGpds) n q (Hq: q <= n)
  r (Hr: r <= q) a b (x: prefixCell (νGpdPack n.+3 Y).1):
  (f_equal ((Extraction.g Y).(GFace) n q Hq a)
      (packedReadoutFace Y n.+1 r (Hr ↕ ↑ Hq) b x)
    • packedReadoutFace Y n q Hq a
        (packedRawFace Y n.+1 r (Hr ↕ ↑ Hq) b x))
    • f_equal (packedReadout Y n) (packedRawExchange Y n q Hq r Hr a b x)
  = (Extraction.g Y).(GFaceCoh) n q Hq r Hr a b (packedReadout Y n.+2 x)
    • (f_equal ((Extraction.g Y).(GFace) n r (Hr ↕ Hq) b)
        (packedReadoutFace Y n.+1 q.+1 (⇑ Hq) a x)
      • packedReadoutFace Y n r (Hr ↕ Hq) b
          (packedRawFace Y n.+1 q.+1 (⇑ Hq) a x)).
Proof.
  now exact (Position.Relative.descFaceGCoh Y (selectedDescPack Y n)
    0 q Hq r Hr a b x).
Defined.

Definition packedNormalizedReadoutFace (Y: νGpds) n q (Hq: q <= n) a
  (x: prefixCell (νGpdPack n.+2 Y).1):
  (Extraction.g Y).(GFace) n q Hq a (packedReadout Y n.+1 x) =
    packedReadout Y n (prefixFace (νGpdPack n.+2 Y).1 q Hq a x) :=
  packedReadoutFace Y n q Hq a x
    • f_equal (packedReadout Y n) (packedRawFaceNormalize Y n q Hq a x).

Lemma packedNormalizedReadoutExchange (Y: νGpds) n q (Hq: q <= n)
  r (Hr: r <= q) a b (x: prefixCell (νGpdPack n.+3 Y).1):
  (f_equal ((Extraction.g Y).(GFace) n q Hq a)
      (packedNormalizedReadoutFace Y n.+1 r (Hr ↕ ↑ Hq) b x)
    • packedNormalizedReadoutFace Y n q Hq a
        (prefixFace (νGpdPack n.+3 Y).1 r (Hr ↕ ↑ Hq) b x))
    • f_equal (packedReadout Y n)
        (prefixExchange (νGpdPack n.+3 Y).1 q Hq r Hr a b x)
  = (Extraction.g Y).(GFaceCoh) n q Hq r Hr a b (packedReadout Y n.+2 x)
    • (f_equal ((Extraction.g Y).(GFace) n r (Hr ↕ Hq) b)
        (packedNormalizedReadoutFace Y n.+1 q.+1 (⇑ Hq) a x)
      • packedNormalizedReadoutFace Y n r (Hr ↕ Hq) b
          (prefixFace (νGpdPack n.+3 Y).1 q.+1 (⇑ Hq) a x)).
Proof.
  refine (PathSquares.composeFaceSquare
    (fun x => x) (fun x => x) (fun x => x)
    (packedReadout Y n) (packedReadout Y n.+1) (packedReadout Y n.+2)
    (prefixFace (νGpdPack n.+2 Y).1 q Hq a)
    (prefixFace (νGpdPack n.+2 Y).1 r (Hr ↕ Hq) b)
    (prefixFace (νGpdPack n.+3 Y).1 r (Hr ↕ ↑ Hq) b)
    (prefixFace (νGpdPack n.+3 Y).1 q.+1 (⇑ Hq) a)
    (packedRawFace Y n q Hq a) (packedRawFace Y n r (Hr ↕ Hq) b)
    (packedRawFace Y n.+1 r (Hr ↕ ↑ Hq) b)
    (packedRawFace Y n.+1 q.+1 (⇑ Hq) a)
    ((Extraction.g Y).(GFace) n q Hq a)
    ((Extraction.g Y).(GFace) n r (Hr ↕ Hq) b)
    ((Extraction.g Y).(GFace) n.+1 r (Hr ↕ ↑ Hq) b)
    ((Extraction.g Y).(GFace) n.+1 q.+1 (⇑ Hq) a)
    (packedRawFaceNormalize Y n q Hq a)
    (packedRawFaceNormalize Y n r (Hr ↕ Hq) b)
    (packedRawFaceNormalize Y n.+1 r (Hr ↕ ↑ Hq) b)
    (packedRawFaceNormalize Y n.+1 q.+1 (⇑ Hq) a)
    (packedReadoutFace Y n q Hq a) (packedReadoutFace Y n r (Hr ↕ Hq) b)
    (packedReadoutFace Y n.+1 r (Hr ↕ ↑ Hq) b)
    (packedReadoutFace Y n.+1 q.+1 (⇑ Hq) a)
    (prefixExchange (νGpdPack n.+3 Y).1 q Hq r Hr a b)
    (packedRawExchange Y n q Hq r Hr a b)
    ((Extraction.g Y).(GFaceCoh) n q Hq r Hr a b) x _
    (packedReadoutExchange Y n q Hq r Hr a b x)).
  rewrite f_equal_id. now exact (packedRawExchangeNormalize Y n q Hq r Hr a b x).
Defined.

Definition packedNormalizedComparison (Y: νGpds):
  Comparisons.FaceComparison
    (fun n => prefixCell (νGpdPack n.+1 Y).1) (Extraction.g Y).(G0)
    (fun n => prefixFace (νGpdPack n.+2 Y).1) (Extraction.g Y).(GFace)
    (fun n => prefixExchange (νGpdPack n.+3 Y).1) (Extraction.g Y).(GFaceCoh) :=
  @Comparisons.Build_FaceComparison _ _ _ _ _ _ (packedReadout Y)
    (packedNormalizedReadoutFace Y) (packedNormalizedReadoutExchange Y).

Definition globalToPackedComparison (Y: νGpds) :=
  Comparisons.inverseComparison (packedNormalizedComparison Y).

Definition indexedPackedChain (Y: νGpds):
  SequentialLimit νGpdTel.(stage) (fun n => @bond νGpdTel n) :=
  ((fun n => (νGpdPack n Y).1); fun _ => eq_refl).

Definition earlierPrefixPath {N} (Y Z: νGpds)
  (e: (νGpdPack N Y).1 = (νGpdPack N Z).1) m (h: m <= N):
  (νGpdPack m Y).1 = (νGpdPack m Z).1 :=
  takeStageChainPath N νGpdTel (indexedPackedChain Y) (indexedPackedChain Z) e m h.

Lemma earlierPrefixPathAt {N} (Y Z: νGpds)
  (e: (νGpdPack N Y).1 = (νGpdPack N Z).1):
  earlierPrefixPath Y Z e N leR_refl = e.
Proof. now exact (takeStageChainPathAt N νGpdTel
  (indexedPackedChain Y) (indexedPackedChain Z) e). Defined.

Lemma earlierPrefixPathBond {N} (Y Z: νGpds)
  (e: (νGpdPack N Y).1 = (νGpdPack N Z).1) m (h: m.+1 <= N):
  projT1_eq (earlierPrefixPath Y Z e m.+1 h) = earlierPrefixPath Y Z e m (↓ h).
Proof.
  pose proof (takeStageChainPathBond N νGpdTel
    (indexedPackedChain Y) (indexedPackedChain Z) e m h) as square.
  change (projT1_eq (earlierPrefixPath Y Z e m.+1 h) • eq_refl =
    eq_refl • earlierPrefixPath Y Z e m (↓ h)) in square.
  now rewrite eq_trans_refl_l, eq_trans_refl_r in square.
Defined.

(** A path of stored prefixes acts coherently on their indexed generators. *)
Definition prefixCellTransport {n} {X Y: (νGpdAt n.+1).(prefix)} (p: X = Y)
  (x: prefixCell X): prefixCell Y :=
  rew [fun X => GDom (prefixCell X)] p in x.

Definition prefixCellTransportEquiv {n} {X Y: (νGpdAt n.+1).(prefix)} (p: X = Y):
  Equiv (prefixCell X) (prefixCell Y) :=
  rewEquiv (fun X => GDom (prefixCell X)) p.

Definition prefixFaceTransport {n} {X Y: (νGpdAt n.+2).(prefix)} (p: X = Y)
  q (Hq: q <= n) a (x: prefixCell X):
  prefixFace Y q Hq a (prefixCellTransport p x) =
    prefixCellTransport (projT1_eq p) (prefixFace X q Hq a x).
Proof. now destruct p. Defined.

Definition prefixFaceMap {n} {X Y: (νGpdAt n.+2).(prefix)}
  (p: X = Y) (lower: X.1 = Y.1) (h: projT1_eq p = lower)
  q (Hq: q <= n) a (x: prefixCell X):
  prefixFace Y q Hq a (prefixCellTransport p x) =
    prefixCellTransport lower (prefixFace X q Hq a x) :=
  prefixFaceTransport p q Hq a x
    • f_equal (fun e => prefixCellTransport e (prefixFace X q Hq a x)) h.

Lemma prefixExchangeMap {n} {X Y: (νGpdAt n.+3).(prefix)}
  (p: X = Y) (middle: X.1 = Y.1) (lower: X.1.1 = Y.1.1)
  (hm: projT1_eq p = middle) (hl: projT1_eq middle = lower)
  q (Hq: q <= n) r (Hr: r <= q) a b (x: prefixCell X):
  (f_equal (prefixFace Y.1 q Hq a)
      (prefixFaceMap p middle hm r (Hr ↕ ↑ Hq) b x)
    • prefixFaceMap middle lower hl q Hq a
        (prefixFace X r (Hr ↕ ↑ Hq) b x))
    • f_equal (prefixCellTransport lower) (prefixExchange X q Hq r Hr a b x)
  = prefixExchange Y q Hq r Hr a b (prefixCellTransport p x)
    • (f_equal (prefixFace Y.1 r (Hr ↕ Hq) b)
        (prefixFaceMap p middle hm q.+1 (⇑ Hq) a x)
      • prefixFaceMap middle lower hl r (Hr ↕ Hq) b
          (prefixFace X q.+1 (⇑ Hq) a x)).
Proof.
  destruct hm, hl, p.
  cbn [prefixFaceMap prefixFaceTransport prefixCellTransport].
  rewrite f_equal_id, eq_trans_refl_l, eq_trans_refl_r. now reflexivity.
Defined.

Definition coherentUnitCellEquiv {n} (X: (νGpdAt n).(prefix)):
  Equiv (prefixCell (unitExtension X)) (Extraction.gF0 (completePrefix X) n) :=
  compEquiv
    (rewEquiv (fun Y: (νGpdAt n.+1).(prefix) => GDom (prefixCell Y))
      (eq_sym (packedUnitPrefix X)))
    (packedReadout (completePrefix X) n).

Definition frameMatchingMap {n} (X: (νGpdAt n).(prefix)) (d: νFrame X):
  MatchingObject (finiteDiagram X) :=
  matchingMap (restrictDiagram (S n) (indexedDiagram (completePrefix X)))
    (coherentUnitCellEquiv X (d; tt)).

Lemma frameMatchingMapIsEquiv {n} (X: (νGpdAt n).(prefix))
  (H: IsEquiv (matchingMap
    (restrictDiagram (S n) (indexedDiagram (completePrefix X))))):
  IsEquiv (frameMatchingMap X).
Proof.
  now exact (compEquiv (symEquiv (unitPrefixProjectionEquiv X))
    (compEquiv (coherentUnitCellEquiv X)
      {| eqvFun := matchingMap
          (restrictDiagram (S n) (indexedDiagram (completePrefix X)));
        eqvIsEquiv := H |})).(eqvIsEquiv).
Defined.

End IndexedDiagramPrefixOn.
