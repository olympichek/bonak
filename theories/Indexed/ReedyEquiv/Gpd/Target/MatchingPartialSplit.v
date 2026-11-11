(** The partial matching split: the partial matching objects of a shifted
    prefix are equivalent to matching steps of the next prefix. Readouts of
    matching values along partial actions, truncated residual comparisons,
    and the kept residual presentation. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Funext Notation RewLemmas
  LeSProp CohShapes FinitePrefix.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas
  LocallyDiscretePseudofunctor.
From Bonak.Presheaf Require Import νSemiShape WordTensor.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Pseudofunctor.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Cone.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift Pullback.
From Bonak.Indexed.ReedyEquiv.Gpd.Target Require Import ShiftedPrefix
  PullbackReindex MatchingSplit.

Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations FinitePrefix WordTensor GpdCone.

(** Recursive matching data in residual coordinates. *)
Set Keyed Unification.

Local Lemma exchangeNaturalityAlgebra {T: Type}
  {x0 x1 x2 x3 y0 y1 y2 y3: T}
  (f1: x0 = x1) (fe: x1 = x2) (f2: x3 = x2)
  (g1: y0 = y1) (ge: y1 = y2) (g2: y3 = y2)
  (a: x0 = y0) (a': x3 = y3) (h1: x1 = y1) (h2: x2 = y2)
  (c1: f1 • h1 = a • g1) (ce: fe • h2 = h1 • ge)
  (c2: f2 • h2 = a' • g2):
  a • (g1 • (ge • eq_sym g2)) = (f1 • (fe • eq_sym f2)) • a'.
Proof.
  destruct f1, fe, f2, a, g1, ge, g2.
  cbn in c1, ce, c2 |- *.
  rewrite eq_trans_refl_l in c1, ce, c2.
  now rewrite <- c2, ce, c1.
Defined.

Section TransformationFaces.
Context {A: HSet} (P Q: PathDiagramFamily (Op (νSemiShape A)))
  (b: forall k, P.(pfObj) k -> Q.(pfObj) k).
Local Abbreviation PD := (pathData _ _ P.(pfStr)).
Local Abbreviation QD := (pathData _ _ Q.(pfStr)).
Context
  (alpha: forall {k l} (u: Word A k l) (x: P.(pfObj) l),
    b k (PD.(phom) u x) = QD.(phom) u (b l x))
  (alphaComp: forall {k l m} (u: Word A k l) (v: Word A l m) (x: P.(pfObj) m),
    f_equal (b k) (PD.(pcomp) v u x) • alpha (wcomp v u) x =
      alpha u (PD.(phom) v x)
        • (f_equal (QD.(phom) u) (alpha v x) • QD.(pcomp) v u (b m x))).

#[local] Arguments alpha {k l} _ _.
#[local] Arguments alphaComp {k l m} _ _ _.

Local Lemma alphaArrow {k l} {u v: Word A k l} (e: u = v) (x: P.(pfObj) l):
  f_equal (b k) (phomEq PD e x) • alpha v x =
    alpha u x • phomEq QD e (b l x).
Proof.
  destruct e. now apply eq_trans_refl_l.
Defined.

Lemma diagramTransformationFaceCoh n q (Hq: q <= n) r (Hr: r <= q)
  (a c: A) (x: P.(pfObj) (S (S n))):
  (alpha (wgen n q a) ((ofPsfTot A P).(GFace) (S n) r (Hr ↕ (↑ Hq)) c x)
    • f_equal ((ofPsfTot A Q).(GFace) n q Hq a) (alpha (wgen (S n) r c) x))
    • (ofPsfTot A Q).(GFaceCoh) n q Hq r Hr a c (b (S (S n)) x) =
  f_equal (b n) ((ofPsfTot A P).(GFaceCoh) n q Hq r Hr a c x)
    • (alpha (wgen n r c) ((ofPsfTot A P).(GFace) (S n) (S q) (⇑ Hq) a x)
      • f_equal ((ofPsfTot A Q).(GFace) n r (Hr ↕ Hq) c)
          (alpha (wgen (S n) (S q) a) x)).
Proof.
  cbn [ofPsfTot ofPsf GFace GFaceCoh ofPsfFace ofPsfCoh].
  unfold ofPsfFace, ofPsfCoh.
  rewrite 2 eq_trans_map_distr, fEqualSym.
  apply (exchangeNaturalityAlgebra
    (f_equal (b n) (PD.(pcomp) (wgen (S n) r c) (wgen n q a) x))
    (f_equal (b n) (phomEq PD (wgenExchange n q Hq r Hr a c) x))
    (f_equal (b n) (PD.(pcomp) (wgen (S n) (S q) a) (wgen n r c) x))
    (QD.(pcomp) (wgen (S n) r c) (wgen n q a) (b (S (S n)) x))
    (phomEq QD (wgenExchange n q Hq r Hr a c) (b (S (S n)) x))
    (QD.(pcomp) (wgen (S n) (S q) a) (wgen n r c) (b (S (S n)) x))
    _ _ (alpha (wcomp (wgen (S n) r c) (wgen n q a)) x)
    (alpha (wcomp (wgen (S n) (S q) a) (wgen n r c)) x)).
  - refine (alphaComp _ _ x • _). now apply eq_sym, eqTransAssoc.
  - now apply alphaArrow.
  - refine (alphaComp _ _ x • _). now apply eq_sym, eqTransAssoc.
Defined.
End TransformationFaces.

Definition matchingBoundaryFace {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) n q (Hq: q <= n) (a: A)
  (x: (ofPsfTot A (wholeCellDiagram p F)).(G0) (S n)) :=
  eq_sym (boundaryNatural p F (wgen n q a) x).

Lemma matchingBoundaryFaceCoh {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A)))
  n q (Hq: q <= n) r (Hr: r <= q) (a c: A)
  (x: (ofPsfTot A (wholeCellDiagram p F)).(G0) (S (S n))):
  (matchingBoundaryFace p F n q Hq a
      ((ofPsfTot A (wholeCellDiagram p F)).(GFace) (S n) r (Hr ↕ (↑ Hq)) c x)
    • f_equal ((MatchingPartialPresentation p F).(GFace) n q Hq a)
      (matchingBoundaryFace p F (S n) r (Hr ↕ (↑ Hq)) c x))
    • (MatchingPartialPresentation p F).(GFaceCoh) n q Hq r Hr a c
      (partialBoundary p F (S (S n)) x) =
  f_equal (partialBoundary p F n)
    ((ofPsfTot A (wholeCellDiagram p F)).(GFaceCoh) n q Hq r Hr a c x)
    • (matchingBoundaryFace p F n r (Hr ↕ Hq) c
      ((ofPsfTot A (wholeCellDiagram p F)).(GFace) (S n) (S q) (⇑ Hq) a x)
      • f_equal ((MatchingPartialPresentation p F).(GFace) n r (Hr ↕ Hq) c)
        (matchingBoundaryFace p F (S n) (S q) (⇑ Hq) a x)).
Proof.
  exact (diagramTransformationFaceCoh (wholeCellDiagram p F) (MatchingPartialDiagram p F)
    (partialBoundary p F) (fun k l u x => boundaryNaturality p F u x)
    (fun k l m u v x => partialBoundaryComp p F u v x) n q Hq r Hr a c x).
Defined.

Lemma matchingBoundaryForwardCoh {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A)))
  n q (Hq: q <= n) r (Hr: r <= q) (a c: A)
  (x: (ofPsfTot A (wholeCellDiagram p F)).(G0) (S (S n))):
  (f_equal ((MatchingPartialPresentation p F).(GFace) n q Hq a)
      (boundaryNatural p F (wgen (S n) r c) x)
    • boundaryNatural p F (wgen n q a)
      ((ofPsfTot A (wholeCellDiagram p F)).(GFace) (S n) r (Hr ↕ (↑ Hq)) c x))
    • f_equal (partialBoundary p F n)
      ((ofPsfTot A (wholeCellDiagram p F)).(GFaceCoh) n q Hq r Hr a c x) =
  (MatchingPartialPresentation p F).(GFaceCoh) n q Hq r Hr a c
      (partialBoundary p F (S (S n)) x)
    • (f_equal ((MatchingPartialPresentation p F).(GFace) n r (Hr ↕ Hq) c)
        (boundaryNatural p F (wgen (S n) (S q) a) x)
      • boundaryNatural p F (wgen n r c)
        ((ofPsfTot A (wholeCellDiagram p F)).(GFace) (S n) (S q) (⇑ Hq) a x)).
Proof.
  apply inverseSquare.
  rewrite 2 inverseComposite, <- 2 fEqualSym.
  now exact (matchingBoundaryFaceCoh p F n q Hq r Hr a c x).
Defined.

Definition residualShiftPresentation {A: HSet} := @GpdCone.residualShiftPresentation A.

Section PartialSplit.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation Q := (MatchingPartialPresentation p F).
Local Abbreviation C := (wholeCellDiagram p F).

Definition MatchingStep (k: nat): HGpd :=
  gsigT (A := Q.(G0) (S k)) (fun w =>
    gforall a: A, gsigT (A := C.(pfObj) k) (fun t =>
      hgpdOfHSet (hpaths (Q.(GFace) k 0 leR_O a w) (partialBoundary p F k t)))).

Definition matchingStepBridge (k: nat):
  Equiv (SplitMatching (shiftedPrefix (S p) k F)) (MatchingStep k) :=
  sigTEquiv (shiftPrefixBridge p k F) (fun b =>
    piEquiv (fun a => sigTEquivSnd (fun t =>
      prependPathEquiv (eq_sym (shiftPrefixTopFace p k F a b))))).

Local Opaque matchingStepBridge matchingSplitEquiv SplitMatching MatchingObject shiftedPrefix.

Definition matchingPartialSplitEquiv (k: nat):
  Equiv (MatchingObject (shiftedPrefix (S p) k F)) (MatchingStep k) :=
  @compEquiv (MatchingObject (shiftedPrefix (S p) k F))
    (SplitMatching (shiftedPrefix (S p) k F)) (MatchingStep k)
    (matchingSplitEquiv (shiftedPrefix (S p) k F)) (matchingStepBridge k).

Local Transparent matchingStepBridge matchingSplitEquiv.

Local Transparent SplitMatching MatchingObject shiftedPrefix.

Definition matchingStepFace (k q: nat) (Hq: q <= k) (e: A)
  (s: MatchingStep (S k)): MatchingStep k :=
  (Q.(GFace) (S k) (S q) (⇑ Hq) e s.1; fun a =>
    ((pathData _ _ C.(pfStr)).(phom) (wgen k q e) (s.2 a).1;
      eq_sym (Q.(GFaceCoh) k q Hq 0 leR_O e a s.1)
        • (f_equal (Q.(GFace) k q Hq e) (s.2 a).2
          • boundaryNatural p F (wgen k q e) (s.2 a).1))).

Local Abbreviation CP := (ofPsfTot A C).

Definition MatchingStepPresentation: νGpdPresentation A :=
  conePresentation Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x)
    (matchingBoundaryForwardCoh p F).

Definition matchingStepBoundary k:
  (residualShiftPresentation CP).(G0) k -> MatchingStepPresentation.(G0) k :=
  coneBoundary Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x) k.

Definition matchingStepBoundaryFace k q (Hq: q <= k) a x:
  matchingStepBoundary k ((residualShiftPresentation CP).(GFace) k q Hq a x) =
    MatchingStepPresentation.(GFace) k q Hq a (matchingStepBoundary (S k) x) :=
  coneBoundaryFace Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x)
    (matchingBoundaryForwardCoh p F) k q Hq a x.

Lemma matchingStepExchangeBase k q (Hq: q <= k) r (Hr: r <= q) a c
  (u: MatchingStep (S (S k))):
  f_equal (fun z: MatchingStep k => z.1)
    (MatchingStepPresentation.(GFaceCoh) k q Hq r Hr a c u) =
    Q.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u.1.
Proof.
  now exact (coneExchangeBase Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x)
    (matchingBoundaryForwardCoh p F) k q Hq r Hr a c u).
Defined.

Lemma matchingStepExchangeCell k q (Hq: q <= k) r (Hr: r <= q) a c
  (u: MatchingStep (S (S k))) d:
  f_equal (fun z: MatchingStep k => (z.2 d).1)
    (MatchingStepPresentation.(GFaceCoh) k q Hq r Hr a c u) =
    CP.(GFaceCoh) k q Hq r Hr a c (u.2 d).1.
Proof.
  now exact (coneExchangeCell Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x)
    (matchingBoundaryForwardCoh p F) k q Hq r Hr a c u d).
Defined.

Lemma matchingStepBoundaryFaceBase k q (Hq: q <= k) a (x: CP.(G0) (S (S k))):
  f_equal (fun z: MatchingStep k => z.1) (matchingStepBoundaryFace k q Hq a x) =
    eq_sym (boundaryNatural p F (wgen (S k) (S q) a) x).
Proof.
  now exact (coneBoundaryFaceBase Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x)
    (matchingBoundaryForwardCoh p F) k q Hq a x).
Defined.

Lemma matchingStepBoundaryFaceCell k q (Hq: q <= k) a
  (x: CP.(G0) (S (S k))) d:
  f_equal (fun z: MatchingStep k => (z.2 d).1) (matchingStepBoundaryFace k q Hq a x) =
    eq_sym (CP.(GFaceCoh) k q Hq 0 leR_O a d x).
Proof.
  now exact (coneBoundaryFaceCell Q CP (partialBoundary p F)
    (fun k q Hq a x => boundaryNatural p F (wgen k q a) x)
    (matchingBoundaryForwardCoh p F) k q Hq a x d).
Defined.

End PartialSplit.

(** Values of matching relations, arrows, compositors and exchanges of the
    partial matching presentation at each index and word. *)

Section PullbackReadout.
Context {A: HSet} (p: nat) (C: Category) (F: PathDiagramFamily C).
Local Abbreviation MD := (pathData _ _ (matchingPullbackDiagram (A := A) p C F).(pfStr)).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).

Lemma matchingRelationValue
  {U V V' W: Functor (PrefixCategory A p) C}
  (alpha: NatTrans U V) (beta: NatTrans V W)
  (alpha': NatTrans U V') (beta': NatTrans V' W)
  (e: compNatTrans alpha beta = compNatTrans alpha' beta')
  (b: MatchingObject (pullbackDiagram U F)) i g
  (E: alpha.(ncomp) i ⨟ beta.(ncomp) i = alpha'.(ncomp) i ⨟ beta'.(ncomp) i):
  f_equal (fun z => matchingValue z i g)
    (diagramRelation MD alpha beta alpha' beta' e b) =
  diagramRelation FD (alpha.(ncomp) i) (beta.(ncomp) i)
    (alpha'.(ncomp) i) (beta'.(ncomp) i) E (matchingValue b i g).
Proof.
  unfold diagramRelation. rewrite 2 eq_trans_map_distr, fEqualSym.
  refine (transCongR (matchingCompositionValue p C F U V W alpha beta b i g) _ • _).
  refine (transCongL _ (transCongR
    (matchingDiagramArrowValue p C F U W e b i g E) _ ) • _).
  now exact (transCongL _ (transCongL _ (f_equal (@eq_sym _ _ _)
    (matchingCompositionValue p C F U V' W alpha' beta' b i g)))).
Defined.
End PullbackReadout.

Section Readout.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation MD := (pathData _ _ (MatchingPartialDiagram p F).(pfStr)).

Lemma matchingPartialArrowValue {k l} {u v: Word A k l} (e: u = v)
  (b: MatchingObject (shiftedPrefix p l F)) i g:
  f_equal (fun z => matchingValue z i g) (phomEq MD e b) =
    phomEq (pathData _ _ (wholeCellDiagram (rank i) F).(pfStr)) e
      (matchingValue b i g).
Proof. now destruct e. Defined.

Lemma matchingPartialCompReadout {k l m} (u: Word A k l) (v: Word A l m)
  (b: MatchingObject (shiftedPrefix p m F)) i g:
  f_equal (fun z => matchingValue z i g) (MD.(pcomp) v u b) =
    (pathData _ _ (wholeCellDiagram (rank i) F).(pfStr)).(pcomp) v u
      (matchingValue b i g).
Proof.
  refine (matchingPartialCompValue p F u v b i g • _).
  unfold wholeCellDiagram. rewrite pullbackCompPoint.
  cbn [wholeCellFunctor fcomp]. now rewrite eq_sym_involutive.
Defined.

Lemma matchingPartialExchangeReadout k q (Hq: q <= k) r (Hr: r <= q) a b
  (m: (MatchingPartialPresentation p F).(G0) (S (S k))) i g:
  f_equal (fun z => matchingValue z i g)
    ((MatchingPartialPresentation p F).(GFaceCoh) k q Hq r Hr a b m) =
  (ofPsfTot A (wholeCellDiagram (rank i) F)).(GFaceCoh) k q Hq r Hr a b
    (matchingValue m i g).
Proof.
  change (f_equal (fun z => matchingValue z i g)
    (ofPsfCoh A _ MD k q Hq r Hr a b m) =
    ofPsfCoh A _ (pathData _ _ (wholeCellDiagram (rank i) F).(pfStr))
      k q Hq r Hr a b (matchingValue m i g)).
  unfold ofPsfCoh. rewrite 2 eq_trans_map_distr, fEqualSym.
  refine (transCongR
    (matchingPartialCompReadout (wgen k q a) (wgen (S k) r b) m i g) _ • _).
  refine (transCongL _ (transCongR
    (matchingPartialArrowValue (wgenExchange k q Hq r Hr a b) m i g) _) • _).
  now exact (transCongL _ (transCongL _ (f_equal (@eq_sym _ _ _)
    (matchingPartialCompReadout (wgen k r b) (wgen (S k) (S q) a) m i g)))).
Defined.

End Readout.

(** Values comparing the truncated residual matching map with the residual
    matching map. *)

Section ResidualTruncation.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).

Context {k l: nat} (u: Word A k l).
Local Abbreviation Gamma := (residualMap (S p) F u).
Local Abbreviation X := (baseDiagram (shiftedPrefix (S p) l F)).
Local Abbreviation Y := (baseDiagram (shiftedPrefix (S p) k F)).

Definition truncatedResidualValue (b: MatchingObject (shiftedPrefix p l F)) i g:
  matchingValue (mapMatching (truncateMap Gamma) b) i g =
    (pathData _ _ F.(pfStr)).(phom) (residualWord (rank i) u) (matchingValue b i g) :=
  mapMatchingValue (truncateMap Gamma) b i g
    • pullbackMapCell F (shiftPrefixFunctor A (S p) l)
        (shiftPrefixFunctor A (S p) k) (residualNat (S p) u)
        (Some i) (matchingValue b i g).

Definition truncatedResidualValues (b: MatchingObject (shiftedPrefix p l F)):
  ComparisonValues Y (mapMatching (truncateMap Gamma) b) (residualMatching p F u b) :=
  fun i g => truncatedResidualValue b i g • eq_sym (residualMatchingValue p F u b i g).

End ResidualTruncation.

(** The truncated residual comparison values are reflexivities at a common
    carrier. *)

Section ResidualFlat.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Context {k l: nat} (u: Word A k l).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Definition commonValue (b: MatchingObject (shiftedPrefix p l F))
  (i: Index p) (g: Word A (rank i) p) :=
  FD.(phom) (residualWord (rank i) u) (matchingValue b i g).

Lemma truncatedResidualValuesRefl (b: MatchingObject (shiftedPrefix p l F))
  (i: Index p) (g: Word A (rank i) p):
  @eq (commonValue b i g = commonValue b i g)
    (truncatedResidualValues p F u b i g) eq_refl.
Proof. now reflexivity. Defined.
End ResidualFlat.

(** The truncated residual matching map agrees with the residual matching
    map, compatibly with naturality and matching paths. *)

Section ResidualCoherence.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Context {k l: nat} (u: Word A k l).
Local Abbreviation Gamma := (residualMap (S p) F u).
Local Abbreviation Y := (baseDiagram (shiftedPrefix (S p) k F)).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).

Lemma truncatedResidualNaturality {i j: Index p}
  (f: Word A (rank i) (rank j)) (x: F.(pfObj) (rank j + l)):
  @eq (FD.(phom) (residualWord (rank i) u) (FD.(phom) (paddedWord l f) x)
    = FD.(phom) (paddedWord k f) (FD.(phom) (residualWord (rank j) u) x))
    (Gamma.(mapNatural) (i := Some i) (j := Some j) f x)
    ((residualMap p F u).(mapNatural) (i := i) (j := j) f x).
Proof.
  refine (pullbackMapNatural F (shiftPrefixFunctor A (S p) l)
    (shiftPrefixFunctor A (S p) k) (residualNat (S p) u)
    (i := Some i) (j := Some j) f x • _).
  refine (_ • eq_sym (pullbackMapNatural F (shiftPrefixFunctor A p l)
    (shiftPrefixFunctor A p k) (residualNat p u) (i := i) (j := j) f x)).
  now reflexivity.
Defined.

Lemma truncatedResidualPaths (b: MatchingObject (shiftedPrefix p l F))
  {i j: Index p} (f: Word A (rank i) (rank j)) (g: Word A (rank j) p):
  @eq (FD.(phom) (paddedWord k f)
      (FD.(phom) (residualWord (rank j) u) (matchingValue b j g))
    = FD.(phom) (residualWord (rank i) u) (matchingValue b i (wcomp g f)))
    (matchingPath (mapMatching (truncateMap Gamma) b) (i := i) (j := j) f g)
    (matchingPath (residualMatching p F u b) (i := i) (j := j) f g).
Proof.
  change ((eq_sym (Gamma.(mapNatural) (i := Some i) (j := Some j) f
      (matchingValue b j g))
    • f_equal (Gamma.(mapCell) (Some i)) (matchingPath b f g)) =
    (eq_sym ((residualMap p F u).(mapNatural) (i := i) (j := j) f
      (matchingValue b j g))
    • f_equal ((residualMap p F u).(mapCell) i) (matchingPath b f g))).
  refine (f_equal2 (fun n z => eq_sym n • z)
    (truncatedResidualNaturality f (matchingValue b j g)) _).
  now reflexivity.
Defined.

Definition truncatedResidualSquares (b: MatchingObject (shiftedPrefix p l F)):
  @ComparisonSquares A p Y (mapMatching (truncateMap Gamma) b)
    (residualMatching p F u b) (truncatedResidualValues p F u b).
Proof.
  intros i j f g.
  rewrite (truncatedResidualValuesRefl p F u b j g),
    (truncatedResidualValuesRefl p F u b i (wcomp g f)).
  pose proof (truncatedResidualPaths b f g) as paths.
  lazymatch type of paths with
  | @eq ?T ?left ?right =>
      lazymatch T with
      | @eq ?C ?x ?y =>
          now exact (@eq_trans T
            (@eq_trans C x x y (@eq_refl C x) right) right left
            (@eq_trans_refl_l C x y right) (@eq_sym T left right paths))
      end
  end.
Defined.

Definition truncatedResidualComparison (b: MatchingObject (shiftedPrefix p l F)) :=
  matchingHomotopy Y (b := mapMatching (truncateMap Gamma) b)
    (c := residualMatching p F u b) (truncatedResidualValues p F u b)
    (truncatedResidualSquares b).

Lemma truncatedResidualComparisonValue (b: MatchingObject (shiftedPrefix p l F))
  (i: Index p) (g: Word A (rank i) p):
  @eq (FD.(phom) (residualWord (rank i) u) (matchingValue b i g)
    = FD.(phom) (residualWord (rank i) u) (matchingValue b i g))
    (f_equal (fun z => matchingValue z i g) (truncatedResidualComparison b)) eq_refl.
Proof.
  unfold truncatedResidualComparison.
  refine (matchingHomotopyValue Y
    (b := mapMatching (truncateMap Gamma) b)
    (c := residualMatching p F u b) (truncatedResidualValues p F u b)
    (truncatedResidualSquares b) i g • _).
  now exact (truncatedResidualValuesRefl p F u b i g).
Defined.
End ResidualCoherence.

(** The kept residual matching maps form a map of presentations with face
    coherence. *)

Section KeptResidual.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation MD := (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F).
Local Abbreviation U := (shiftedResidualFunctor A p).
Local Abbreviation P := (MatchingPartialPresentation (S p) F).
Definition keptResidualPresentation: νGpdPresentation A := ofPsfTot A (pullbackDiagram U MD).
Local Abbreviation D := keptResidualPresentation.

Definition keptResidualMap k (m: P.(G0) k): D.(G0) k :=
  matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F
    (keepMatching (shiftedPrefix (S p) k F) m).

Definition keptResidualFace k q (Hq: q <= k) a (m: P.(G0) (S k)):
  keptResidualMap k (P.(GFace) k q Hq a m) =
    D.(GFace) k q Hq a (keptResidualMap (S k) m) :=
  f_equal (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F)
    (eq_sym (keepMap (residualMap (S p) F (wgen k q a)) m))
  • matchingCompositeNatural (shiftFunctor A p)
      (shiftPrefixFunctor A (S p) (S k)) (shiftPrefixFunctor A (S p) k) F
      (residualNat (S p) (wgen k q a))
      (keepMatching (shiftedPrefix (S p) (S k) F) m).

Lemma keptResidualFaceValue k q (Hq: q <= k) a (m: P.(G0) (S k)) i g:
  f_equal (fun z => matchingValue z i g) (keptResidualFace k q Hq a m) = eq_refl.
Proof.
  unfold keptResidualFace. rewrite eq_trans_map_distr.
  refine (transCongR (matchingCompMapPath (shiftFunctor A p)
    (shiftPrefixFunctor A (S p) k) F
    (eq_sym (keepMap (residualMap (S p) F (wgen k q a)) m)) i g) _ • _).
  refine (transCongR (fEqualSym
    (fun z: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F)) => matchingValue z i g)
    (keepMap (residualMap (S p) F (wgen k q a)) m)) _ • _).
  refine (transCongR (f_equal (@eq_sym _ _ _)
    (keepMapValue (residualMap (S p) F (wgen k q a)) m i g)) _ • _).
  refine (transCongL _ (matchingCompositeNaturalValue (shiftFunctor A p)
    (shiftPrefixFunctor A (S p) (S k)) (shiftPrefixFunctor A (S p) k) F
    (residualNat (S p) (wgen k q a))
    (keepMatching (shiftedPrefix (S p) (S k) F) m) i g) • _).
  now reflexivity.
Defined.

Lemma keptResidualMapPath k {m n: P.(G0) k} (h: m = n) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (keptResidualMap k) h) =
    f_equal (fun z => matchingValue z (raiseIndex i) (keepToTop g)) h.
Proof. now destruct h. Defined.

Lemma keptResidualActionPath k q (Hq: q <= k) a {m n: D.(G0) (S k)} (h: m = n) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (D.(GFace) k q Hq a) h) =
    f_equal ((pathData _ _ F.(pfStr)).(phom) (residualWord (rank (raiseIndex i)) (wgen k q a)))
      (f_equal (fun z => matchingValue z i g) h).
Proof. now destruct h. Defined.

Lemma keptResidualExchangeValue k q (Hq: q <= k) r (Hr: r <= q) a b
  (m: D.(G0) (S (S k))) i g:
  f_equal (fun z => matchingValue z i g) (D.(GFaceCoh) k q Hq r Hr a b m) =
    (ofPsfTot A (wholeCellDiagram (rank (raiseIndex i)) F)).(GFaceCoh)
      k q Hq r Hr a b (matchingValue m i g).
Proof.
  pose (v := wgen (S k) r b). pose (u := wgen k q a).
  pose (v' := wgen (S k) (S q) a). pose (u' := wgen k r b).
  pose (e := wgenExchange k q Hq r Hr a b).
  pose (E := functorRelation U v u v' u' e).
  pose (E' := functorRelation (wholeCellFunctor A (rank (raiseIndex i))) v u v' u' e).
  change (f_equal (fun z => matchingValue z i g)
    (diagramRelation (pathData _ _ (pullbackDiagram U MD).(pfStr)) v u v' u' e m) =
    diagramRelation (pathData _ _ (wholeCellDiagram (rank (raiseIndex i)) F).(pfStr))
      v u v' u' e (matchingValue m i g)).
  refine (f_equal (fun h => f_equal (fun z => matchingValue z i g) h)
    (pullbackDiagramRelation U MD v u v' u' e E m) • _).
  refine (matchingRelationValue p (Op (νSemiShape A)) F
    (U.(fhom) v) (U.(fhom) u) (U.(fhom) v') (U.(fhom) u') E m i g E' • _).
  now exact (eq_sym (pullbackDiagramRelation (wholeCellFunctor A (rank (raiseIndex i))) F
    v u v' u' e E' (matchingValue m i g))).
Defined.

Lemma keptResidualFaceCoh k q (Hq: q <= k) r (Hr: r <= q) a b
  (m: P.(G0) (S (S k))):
  (keptResidualFace k q Hq a (P.(GFace) (S k) r (Hr ↕ ↑ Hq) b m)
    • f_equal (D.(GFace) k q Hq a) (keptResidualFace (S k) r (Hr ↕ ↑ Hq) b m))
    • D.(GFaceCoh) k q Hq r Hr a b (keptResidualMap (S (S k)) m) =
  f_equal (keptResidualMap k) (P.(GFaceCoh) k q Hq r Hr a b m)
    • (keptResidualFace k r (Hr ↕ Hq) b (P.(GFace) (S k) (S q) (⇑ Hq) a m)
      • f_equal (D.(GFace) k r (Hr ↕ Hq) b) (keptResidualFace (S k) (S q) (⇑ Hq) a m)).
Proof.
  apply (matchingPathExt (pullbackDiagram (U.(fobj) k) F)); intros i g.
  rewrite 4 eq_trans_map_distr.
  rewrite (keptResidualActionPath k q Hq a
    (keptResidualFace (S k) r (Hr ↕ ↑ Hq) b m) i g).
  rewrite (keptResidualActionPath k r (Hr ↕ Hq) b
    (keptResidualFace (S k) (S q) (⇑ Hq) a m) i g).
  rewrite (keptResidualFaceValue k q Hq a
    (P.(GFace) (S k) r (Hr ↕ ↑ Hq) b m) i g).
  rewrite (keptResidualFaceValue (S k) r (Hr ↕ ↑ Hq) b m i g).
  rewrite (keptResidualFaceValue k r (Hr ↕ Hq) b
    (P.(GFace) (S k) (S q) (⇑ Hq) a m) i g).
  rewrite (keptResidualFaceValue (S k) (S q) (⇑ Hq) a m i g).
  rewrite (keptResidualMapPath k (P.(GFaceCoh) k q Hq r Hr a b m) i g).
  rewrite (keptResidualExchangeValue k q Hq r Hr a b
    (keptResidualMap (S (S k)) m) i g).
  rewrite (matchingPartialExchangeReadout (S p) F k q Hq r Hr a b m
    (raiseIndex i) (keepToTop g)).
  cbn [f_equal]. now rewrite eq_trans_refl_l, eq_trans_refl_r.
Defined.
End KeptResidual.

Unset Keyed Unification.
