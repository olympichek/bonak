(** Finite diagrams of indexed ν-groupoids. A cell at rank [k] is read
    from the stored prefix of height [S k]. Deleting a coordinate descends
    one prefix, so that two deletions compare in the same stored fiber. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Logic.Eqdep_dec Arith.PeanoNat Lia.
From Bonak.Lib Require Import HSet HGpd SigT Notation LeSProp Funext Equiv RewLemmas
  CohShapes FinitePrefix.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor Transformation.
From Bonak.Reedy.Gpd Require Import Reedy Bounded Matching ExtensionMap.
From Bonak.Equiv.Gpd Require Import Face Diagram DiagramCausality PathAlgebra.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PrefixPosition.

(** A witness gives a computation rule for taking one more projection.
    At a fixed rank any two witnesses agree. *)

Inductive Position (N: nat): nat -> Type :=
| here: Position N N
| below {k}: Position N (S k) -> Position N k.
Arguments here {N}.
Arguments below {N k} _.

Fixpoint distance {N k} (i: Position N k): nat :=
  match i with here => 0 | below j => S (distance j) end.

Lemma distanceRank {N k} (i: Position N k): distance i + k = N.
Proof.
  induction i; [now reflexivity | cbn in *; now lia].
Defined.

Local Definition topAt {N k} (p: N = k): Position N k :=
  match p with eq_refl => here end.

Local Definition positionCases {N k} (i: Position N k):
  {e: N = k &T i = topAt e} + {j: Position N (S k) &T i = below j}.
Proof.
  destruct i as [|k j].
  - left. now exists eq_refl.
  - right. now exists j.
Defined.

Lemma positionUnique {N k} (i j: Position N k): i = j.
Proof.
  revert j. induction i as [|k i IH]; intro j;
    destruct (positionCases j) as [[e ->]|[p ->]].
  - rewrite (Eqdep_dec.UIP_dec Nat.eq_dec e eq_refl). now reflexivity.
  - exfalso. pose proof (distanceRank p). now lia.
  - exfalso. pose proof (distanceRank i). now lia.
  - now exact (f_equal below (IH p)).
Defined.

Definition positionSet N k: HSet :=
  {| Dom := Position N k; UIP := fun x y => eq_hprop_UIP positionUnique |}.

Fixpoint reach {M N} (root: Position M N) {k} (i: Position N k): Position M k :=
  match i with here => root | below j => below (reach root j) end.

Fixpoint positionOfIndex {n} (i: Index n): Position n (S (rank i)).
Proof.
  destruct n as [|n]; [now destruct i | ].
  destruct i as [j|].
  - now exact (reach (below here) (positionOfIndex n j)).
  - now exact here.
Defined.

End PrefixPosition.

Module StoredDiagramOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (D: IndexedDiagramSig A Core Faces).
Module LayerMap := IndexedLayerCausalityOn A Core Faces D.
Module Export Prefix := LayerMap.Prefix.
Import A PrefixPosition.

Local Definition transferHex {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g} (u: Comparisons.FaceComparison G H f g c d):
  GCoh2Type arity d -> GCoh2Type arity c.
Proof.
  destruct u as [e phi sq]. revert g d phi sq.
  pattern H, e. apply hgpdFamilyEquivInd. intros g d phi sq.
  change (forall n q (h: q <= n) a x, g n q h a x = f n q h a x) in phi.
  revert c sq.
  pattern f, phi. apply (homInd5S (I1 := nat) (I2 := fun _ => nat)
    (I3 := fun n q => q <= n) (I4 := fun _ _ _ => arity)
    (I5 := fun n _ _ _ => G (S n)) (B := fun n _ _ _ _ => G n) g).
  intros c sq. assert (h: c = d).
  { apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q. apply spropFunext; intro h.
    apply functional_extensionality_dep; intro r. apply spropFunext; intro hr.
    apply functional_extensionality_dep; intro a. apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro x.
    pose proof (sq n q h r hr a b x) as s. cbn [f_equal] in s.
    rewrite f_equal_id, eq_trans_refl_l, eq_trans_refl_r in s. now exact s. }
  now destruct h.
Defined.

(** The hexagon is a property of the stored faces and exchanges. Its proof
    can therefore use the tower completed above this one prefix. *)

Definition PrefixHexagon n (X: (νGpdAt (S n.+3)).(prefix)) :=
  forall q (Hq: q <= n) r (Hr: r <= q) s (Hs: s <= r) a b c (x: prefixCell X),
  hexagonal_coherence
    (prefixFace X.1.1 q Hq a) (prefixFace X.1.1 s (Hs ↕ (Hr ↕ Hq)) c)
    (prefixFace X.1.1 r (Hr ↕ Hq) b)
    (prefixExchange X r (Hr ↕ ↑ Hq) s Hs b c x)
    (prefixExchange X q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b x)
    (prefixExchange X q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) a c x)
    (prefixExchange X.1 q Hq s (Hs ↕ Hr) a c
      (prefixFace X r.+1 (⇑ (Hr ↕ ↑ Hq)) b x))
    (prefixExchange X.1 q Hq r Hr a b (prefixFace X s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) c x))
    (prefixExchange X.1 r (Hr ↕ Hq) s Hs b c (prefixFace X q.+2 (⇑ (⇑ Hq)) a x)).

Definition packedHex (Y: νGpds) :=
  transferHex (packedNormalizedComparison Y)
    (Extraction.g Y).(GFaceCoh2).

Definition storedHex {n} (X: (νGpdAt (S n.+3)).(prefix)): PrefixHexagon n X :=
  eq_rect _ (PrefixHexagon n)
    (packedHex (completePrefix X) n)
    _ (completionPack X).

Fixpoint stageAt {N} (X: (νGpdAt N).(prefix)) {k} (i: Position N k): (νGpdAt k).(prefix) :=
  match i in Position _ k return (νGpdAt k).(prefix) with
  | here => X
  | below j => (stageAt X j).1
  end.

(** A position supplies the source prefix of a cell. [below] makes the
    common position of a composite of faces compute by projection. *)

Definition observed {N} (X: (νGpdAt N).(prefix)) k: HGpd :=
  {i: hgpdOfHSet (positionSet N (S k)) & prefixCell (stageAt X i)}.

Definition tag {N} {X: (νGpdAt N).(prefix)} {k} (i: Position N (S k))
  (x: prefixCell (stageAt X i)): observed X k := (i; x).

Definition face {N} (X: (νGpdAt N).(prefix)) n q (h: q <= n) a
  (z: observed X (S n)): observed X n :=
  tag (below z.1) (prefixFace (stageAt X z.1) q h a z.2).

Definition exchange {N} (X: (νGpdAt N).(prefix)) n q (h: q <= n) r (hr: r <= q) a b
  (z: observed X n.+2):
  face X n q h a (face X n.+1 r (hr ↕ ↑ h) b z) =
  face X n r (hr ↕ h) b (face X n.+1 q.+1 (⇑ h) a z) :=
  f_equal (tag (below (below z.1))) (prefixExchange (stageAt X z.1) q h r hr a b z.2).

Local Lemma taggedFaceAp {N} {X: (νGpdAt N).(prefix)} n q (h: q <= n) a
  (i: Position N n.+2) {x y: prefixCell (stageAt X i)} (p: x = y):
  f_equal (face X n q h a) (f_equal (@tag N X _ i) p) =
  f_equal (@tag N X _ (below i)) (f_equal (prefixFace (stageAt X i) q h a) p).
Proof. now destruct p. Defined.

Definition taggedHex {N} (X: (νGpdAt N).(prefix)): GCoh2Type arity (exchange X).
Proof.
  intros n q h r hr s hs a b c [i x].
  unfold hexagonal_coherence, exchange.
  rewrite 3 taggedFaceAp.
  cbn [FaceStructure.SFace face tag projT1 projT2 stageAt].
  apply (hexMap (@tag N X n (below (below (below i))))).
  now exact (storedHex (stageAt X i) q h r hr s hs a b c x).
Defined.

Definition presentation {N} (X: (νGpdAt N).(prefix)): νGpdPresentation arity :=
  {| G0 := observed X; GFace := face X; GFaceCoh := exchange X;
     GFaceCoh2 := taggedHex X |}.

Definition prefixDiagram {N} (X: (νGpdAt N).(prefix)): Diagram arity N :=
  restrictDiagram N (toPsfTot arity (presentation X)).

(** A map of the final filler family induces the identity on the parent
    prefix. Its effects on the top face and exchange are the corresponding
    naturality laws for a filler map. *)

Inductive FillerMap {n} (U: (νGpdAt (S n)).(prefix)): (νGpdAt (S n)).(prefix) -> Type :=
| same: FillerMap U U
| change (F: νFrame U.1 -> HGpd) (alpha: forall d, U.2 d -> F d): FillerMap U (U.1; F).
Arguments same {n U}.
Arguments change {n U} F alpha.

Definition PrefixMap n: (νGpdAt n).(prefix) -> (νGpdAt n).(prefix) -> Type :=
  match n with 0 => @eq _ | S k => @FillerMap k end.

Definition identityLayerMap {n} (U: (νGpdAt n).(prefix)): PrefixMap n U U.
Proof. destruct n; [now reflexivity | now exact same]. Defined.

Definition parentMap {n} {U V: (νGpdAt n.+1).(prefix)} (e: FillerMap U V):
  PrefixMap n U.1 V.1.
Proof. destruct e; now exact (identityLayerMap U.1). Defined.

Definition cellMap {n} {U V: (νGpdAt n.+1).(prefix)} (e: FillerMap U V):
  prefixCell U -> prefixCell V.
Proof.
  destruct e as [|F alpha].
  - now exact (fun x => x).
  - now exact (fun x => (x.1; alpha x.1 x.2)).
Defined.

Definition fillerFaces {n} (B: (νGpdAt n.+1).(prefix)) (E F: νFrame B -> HGpd)
  (alpha: forall d, E d -> F d) q (h: q <= n) a (x: prefixCell (B; E)):
  prefixFace (B; E) q h a x = prefixFace (B; F) q h a (x.1; alpha x.1 x.2).
Proof.
  destruct n.
  - now exact (LayerMap.prefixFillerFaceMapOne B E F alpha q h a x).
  - now exact (LayerMap.prefixFillerFaceMap B E F alpha q h a x).
Defined.

Definition cellMapFace {n} {U V: (νGpdAt n.+2).(prefix)} (e: FillerMap U V)
  q (h: q <= n) a (x: prefixCell U):
  prefixFace V q h a (cellMap e x) = cellMap (parentMap e) (prefixFace U q h a x).
Proof.
  destruct e as [|F alpha].
  - now reflexivity.
  - now exact (eq_sym (fillerFaces U.1 U.2 F alpha q h a x)).
Defined.

Local Lemma turnSquare {T} {a b c d: T} (p: a = b) (u: a = c) (v: b = d) (q: c = d)
  (h: p • v = u • q): eq_sym u • p = q • eq_sym v.
Proof.
  destruct u, v. now exact (eq_trans_refl_l p • eq_sym (eq_trans_refl_r p)
    • h • eq_trans_refl_l q • eq_sym (eq_trans_refl_r q)).
Defined.

Lemma cellMapExchange {n} {U V: (νGpdAt n.+3).(prefix)} (e: FillerMap U V)
  q (h: q <= n) r (hr: r <= q) a b (x: prefixCell U):
  (f_equal (prefixFace V.1 q h a) (cellMapFace e r (hr ↕ ↑ h) b x)
    • cellMapFace (parentMap e) q h a (prefixFace U r (hr ↕ ↑ h) b x))
    • f_equal (cellMap (parentMap (parentMap e))) (prefixExchange U q h r hr a b x) =
  prefixExchange V q h r hr a b (cellMap e x)
    • (f_equal (prefixFace V.1 r (hr ↕ h) b) (cellMapFace e q.+1 (⇑ h) a x)
      • cellMapFace (parentMap e) r (hr ↕ h) b (prefixFace U q.+1 (⇑ h) a x)).
Proof.
  destruct e as [|F alpha].
  - cbn [cellMapFace parentMap identityLayerMap cellMap f_equal].
    rewrite f_equal_id. now rewrite eq_trans_refl_l, eq_trans_refl_r.
  - cbn [cellMapFace parentMap identityLayerMap cellMap fillerFaces].
    rewrite f_equal_id, 2 eq_trans_refl_r, <- 2 eq_sym_f_equal.
    apply turnSquare.
    now exact (@LayerMap.prefixFillerExchangeMap n U.1 U.2 F alpha q h r hr a b x).
Defined.

Fixpoint mapAt {M N} {X: (νGpdAt N).(prefix)} {Z: (νGpdAt M).(prefix)}
  {root: Position M N} (m: PrefixMap N X (stageAt Z root)) {k} (i: Position N k):
  PrefixMap k (stageAt X i) (stageAt Z (reach root i)) :=
  match i with here => m | below j => parentMap (mapAt m j) end.

(** To map out of a stored presentation, give the map and its two
    naturality laws at each position. *)

Section Eliminate.
Context {N} (X: (νGpdAt N).(prefix)) (Q: νGpdPresentation arity).
Context (u: forall k (i: Position N (S k)), prefixCell (stageAt X i) -> Q.(G0) k).
Context (phi: forall n (i: Position N n.+2) q (h: q <= n) a x,
  Q.(GFace) n q h a (u n.+1 i x) =
  u n (below i) (prefixFace (stageAt X i) q h a x)).
Context (square: forall n (i: Position N n.+3) q (h: q <= n) r (hr: r <= q) a b x,
  (f_equal (Q.(GFace) n q h a) (phi n.+1 i r (hr ↕ ↑ h) b x) •
   phi n (below i) q h a (prefixFace (stageAt X i) r (hr ↕ ↑ h) b x)) •
  f_equal (u n (below (below i))) (prefixExchange (stageAt X i) q h r hr a b x) =
  Q.(GFaceCoh) n q h r hr a b (u n.+2 i x) •
    (f_equal (Q.(GFace) n r (hr ↕ h) b) (phi n.+1 i q.+1 (⇑ h) a x) •
     phi n (below i) r (hr ↕ h) b (prefixFace (stageAt X i) q.+1 (⇑ h) a x))).

Definition eliminateCell k (z: observed X k) := u k z.1 z.2.

Local Lemma eliminateAp n (i: Position N n.+1) {x y: prefixCell (stageAt X i)} (p: x = y):
  f_equal (eliminateCell n) (f_equal (@tag N X n i) p) = f_equal (u n i) p.
Proof. now destruct p. Defined.

Definition eliminate: PresentationMap (presentation X) Q.
Proof.
  refine (@Build_PresentationMap arity (presentation X) Q eliminateCell
    (fun n q h a z => phi n z.1 q h a z.2) _).
  intros n q h r hr a b [i x]. cbn [presentation GFaceCoh GFace].
  unfold exchange. rewrite eliminateAp. now apply square.
Defined.

End Eliminate.

Definition tagEquiv {N} {X: (νGpdAt N).(prefix)} {k} (i: Position N k.+1):
  Equiv (prefixCell (stageAt X i)) (observed X k).
Proof.
  refine (qinvEquiv (@tag N X k i)
    (fun z => eq_rect _ (fun j => GDom (prefixCell (stageAt X j))) z.2 _
      (positionUnique z.1 i)) _ _).
  - intro x. rewrite ((positionSet N k.+1).(UIP) (h := positionUnique i i) (g := eq_refl)).
    now reflexivity.
  - intros [j x]. cbn [projT1 projT2]. now destruct (positionUnique j i).
Defined.

Definition CellIsEquiv n: forall {U V: (νGpdAt n).(prefix)}, PrefixMap n U V -> Type :=
  match n with
  | 0 => fun U V e => unit
  | S k => fun U V e => IsEquiv (cellMap e)
  end.

Lemma identityCellIsEquiv {n} (U: (νGpdAt n).(prefix)): CellIsEquiv n (identityLayerMap U).
Proof. destruct n; [now exact tt | now exact idEquiv.(eqvIsEquiv)]. Defined.

Lemma parentCellIsEquiv {n} {U V: (νGpdAt n.+1).(prefix)} (e: FillerMap U V):
  CellIsEquiv n (parentMap e).
Proof. destruct e; now apply identityCellIsEquiv. Defined.

(** Moving the root of a descent and mapping its filler propagate to
    every position by taking parents. *)

Section Map.
Context {M N} {X: (νGpdAt N).(prefix)} {Z: (νGpdAt M).(prefix)}
  {root: Position M N} (m: PrefixMap N X (stageAt Z root)).

Local Abbreviation positionMap i := (@mapAt M N X Z root m _ i).

Definition imageCell k (i: Position N k.+1) (x: prefixCell (stageAt X i)): observed Z k :=
  tag (reach root i) (cellMap (positionMap i) x).

Definition imageFace n (i: Position N n.+2) q (h: q <= n) a x:
  face Z n q h a (imageCell n.+1 i x) = imageCell n (below i) (prefixFace (stageAt X i) q h a x) :=
  f_equal (@tag M Z n (below (reach root i)))
    (cellMapFace (positionMap i) q h a x).

Local Lemma imageAp n (i: Position N n.+1) {x y: prefixCell (stageAt X i)} (p: x = y):
  f_equal (imageCell n i) p =
  f_equal (tag (reach root i)) (f_equal (cellMap (positionMap i)) p).
Proof. now destruct p. Defined.

Lemma imageSquare n (i: Position N n.+3) q (h: q <= n) r (hr: r <= q) a b x:
  (f_equal (face Z n q h a) (imageFace n.+1 i r (hr ↕ ↑ h) b x) •
   imageFace n (below i) q h a (prefixFace (stageAt X i) r (hr ↕ ↑ h) b x)) •
  f_equal (imageCell n (below (below i))) (prefixExchange (stageAt X i) q h r hr a b x) =
  exchange Z n q h r hr a b (imageCell n.+2 i x) •
    (f_equal (face Z n r (hr ↕ h) b) (imageFace n.+1 i q.+1 (⇑ h) a x) •
     imageFace n (below i) r (hr ↕ h) b (prefixFace (stageAt X i) q.+1 (⇑ h) a x)).
Proof.
  unfold imageFace, exchange. rewrite 2 taggedFaceAp, imageAp.
  cbn [imageCell tag projT1 projT2 reach stageAt mapAt].
  apply (@hexMap _ _ (@tag M Z n (below (below (reach root i))))).
  now apply cellMapExchange.
Defined.

Definition induced := eliminate X (presentation Z) imageCell imageFace imageSquare.

Definition diagramMapAt k := restrictTransformation k (X := toPsfTot arity (presentation X))
  (Y := toPsfTot arity (presentation Z)) (generatedTransformation induced).

Lemma inheritedCellIsEquiv {k} (i: Position N k):
  (k = N -> CellIsEquiv N m) -> CellIsEquiv k (positionMap i).
Proof.
  destruct i; intro atRoot.
  - now apply (atRoot eq_refl).
  - now apply parentCellIsEquiv.
Defined.

Definition inducedCellIsEquiv {k} (i: Position N k.+1)
  (ok: CellIsEquiv k.+1 (positionMap i)):
  IsEquiv (induced.(gMapCell) k).
Proof.
  pose (e := {| eqvFun := cellMap (positionMap i); eqvIsEquiv := ok |}).
  now exact (equivOfSquare (@tagEquiv N X k i) idEquiv
    (compEquiv e (@tagEquiv M Z k (reach root i)))
    (induced.(gMapCell) k) (fun _ => eq_refl)).(eqvIsEquiv).
Defined.

End Map.

(** One auxiliary rank of unit fillers makes each frame the boundary of
    a distinguished top cell. Restriction gives the finite readout. The
    boundary of the distinguished cell computes the frame comparison. *)

Definition storedDiagram {n} (X: (νGpdAt n).(prefix)): Diagram arity n :=
  truncateDiagram (prefixDiagram (unitExtension X)).

Definition storedBoundary {n} (X: (νGpdAt n).(prefix)) (d: νFrame X):
  MatchingObject (storedDiagram X) :=
  matchingMap (prefixDiagram (unitExtension X)) (@tag _ (unitExtension X) n here (d; tt)).

Definition weakenEq {n} (X: (νGpdAt n).(prefix)): prefixDiagram X = storedDiagram X.
Proof.
  pose (m := identityLayerMap X).
  apply (diagramMapEq (@diagramMapAt n.+1 n X (unitExtension X) (below here) m n)).
  intro i.
  apply (@inducedCellIsEquiv n.+1 n X (unitExtension X) (below here) m _ (positionOfIndex i)).
  now apply inheritedCellIsEquiv; intros _; apply identityCellIsEquiv.
Defined.

Section Extension.
Context {n} (X: (νGpdAt n).(prefix)) (E: νFrame X -> HGpd).
Local Abbreviation U := ((X; E): (νGpdAt n.+1).(prefix)).
Local Abbreviation V := (unitExtension X).

Local Definition collapse: FillerMap U V := change (fun _ => gunit) (fun _ _ => tt).

Definition storedDiagramExtension:
  extendByMatchingMap arity (storedDiagram X) (prefixCell U) (fun t => storedBoundary X t.1)
    = storedDiagram U.
Proof.
  refine (_ • weakenEq U).
  apply (extensionEqFromDiagramMap (@diagramMapAt n.+1 n.+1 U V here collapse n.+1)
    (@tagEquiv n.+1 U n here) (fun t => storedBoundary X t.1)).
  - now intros [d e].
  - intro i.
    apply (@inducedCellIsEquiv n.+1 n.+1 U V here collapse _
      (positionOfIndex (Some i: Index n.+1))).
    apply inheritedCellIsEquiv. intro h. exfalso.
    pose proof (rankLt i). cbn [rank] in h. now lia.
Defined.

End Extension.

(** Compare a single stored prefix with the corresponding ranks of an
    arbitrary tower extending it. A step down projects the same equality
    of prefixes, including on the chosen exchange paths. *)

Definition packedPresentation (Y: νGpds): νGpdPresentation arity :=
  {| G0 k := prefixCell (νGpdPack k.+1 Y).1;
     GFace k := prefixFace (νGpdPack k.+2 Y).1;
     GFaceCoh k := prefixExchange (νGpdPack k.+3 Y).1;
     GFaceCoh2 := packedHex Y |}.

Definition packedProjection (Y: νGpds): PresentationMap (packedPresentation Y) (Extraction.g Y) :=
  @Build_PresentationMap _ (packedPresentation Y) (Extraction.g Y)
    (packedReadout Y) (packedNormalizedReadoutFace Y) (packedNormalizedReadoutExchange Y).

Section Completed.
Context {N} (X: (νGpdAt N).(prefix)) (Y: νGpds) (root: X = (νGpdPack N Y).1).

Fixpoint packedPath {k} (i: Position N k): stageAt X i = (νGpdPack k Y).1 :=
  match i with here => root | below j => projT1_eq (packedPath j) end.

Definition toPacked: PresentationMap (presentation X) (packedPresentation Y).
Proof.
  apply (eliminate X (packedPresentation Y)
    (fun k i => prefixCellTransport (packedPath i))
    (fun n i => prefixFaceMap (packedPath i) (packedPath (below i)) eq_refl)).
  intros n i. now exact (prefixExchangeMap (packedPath i) _ _ eq_refl eq_refl).
Defined.

Definition completionComparison :=
  composeDiagramMap
    (restrictTransformation N (X := toPsfTot arity (presentation X))
      (Y := toPsfTot arity (packedPresentation Y)) (generatedTransformation toPacked))
    (restrictTransformation N (X := toPsfTot arity (packedPresentation Y))
      (Y := indexedDiagram Y) (generatedTransformation (packedProjection Y))).

Definition completedDiagramEq: prefixDiagram X = restrictDiagram N (indexedDiagram Y).
Proof.
  apply (diagramMapEq completionComparison). intro i.
  pose (j := positionOfIndex i).
  now exact (equivOfSquare (@tagEquiv N X _ j) idEquiv
    (compEquiv (prefixCellTransportEquiv (packedPath j)) (packedReadout Y (rank i)))
    (completionComparison.(mapCell) i) (fun x => eq_refl)).(eqvIsEquiv).
Defined.

End Completed.

Definition boundaryIsEquiv {n} (X: (νGpdAt n).(prefix))
  (complete: IsEquiv (matchingMap (restrictDiagram (S n) (indexedDiagram (completePrefix X))))):
  IsEquiv (storedBoundary X).
Proof.
  pose (p := completedDiagramEq (unitExtension X) (completePrefix X)
    (eq_sym (packedUnitPrefix X))).
  pose (m := eq_rect _ (fun D: Diagram arity n.+1 => IsEquiv (matchingMap D))
    complete _ (eq_sym p)).
  pose (e := {| eqvFun := matchingMap (prefixDiagram (unitExtension X)); eqvIsEquiv := m |}).
  now exact (compEquiv (symEquiv (unitPrefixProjectionEquiv X))
    (compEquiv (@tagEquiv n.+1 (unitExtension X) n here) e)).(eqvIsEquiv).
Defined.

End StoredDiagramOn.
