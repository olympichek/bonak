(** Shifted prefixes of a diagram on the semi-shape category: the top-face
    maps of a shifted diagram, the prefixes of ranks below p with k retained
    coordinates, their partial matching objects and boundaries, and the
    residual presentation of the partial matching objects. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.PeanoNat.
From Bonak.Lib Require Import HSet HGpd SigT Notation RewLemmas FinitePrefix
  Funext LeSProp NatLemmas.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas
  LocallyDiscretePseudofunctor Pseudonatural.
From Bonak.Presheaf Require Import νSemiShape WordTensor WordAction
  GeneratorCoherence.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift Pullback.

Set Primitive Projections.
Set Printing Projections.
Import FinitePrefix WordTensor Logic.EqNotations.

(** Top faces induce coherent maps between shifted and lower boundaries. *)

Section TopFace.
Context {A: HSet} {n} (X: Diagram A (S n)).

Definition topFaceNaturality (a: A) {i j: Index n}
  (f: Word A (rank i) (rank j)) (x: cells (shiftDiagram X) j):
  restrict (baseDiagram X) f (topFace X a j x)
  = topFace X a i (restrict (shiftDiagram X) f x) :=
  restrictComp X (i := Some i) (j := Some j) (k := raiseIndex j)
    f (topFaceWord j a) x
  • (phomEq (diagramData X) (a := raiseIndex j) (b := Some i)
       (eq_sym (topFaceWordNatural f a)) x
     • eq_sym (restrictComp X (i := Some i) (j := raiseIndex i)
         (k := raiseIndex j) (topFaceWord i a) (keepWord f) x)).

Local Lemma restrictCompLeftUnit {i j: Index (S n)}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank j))
  (e: g = wid (rank j)) (h: wcomp g f = f) (x: cells X j):
  restrictComp X f g x • phomEq (diagramData X) h x =
    f_equal (restrict X f) (phomEq (diagramData X) e x • restrictId X j x).
Proof.
  subst g.
  unfold phomEq at 2; cbn [f_equal].
  rewrite eq_trans_refl_l.
  unfold restrictComp.
  pose proof (pcompUnitLPt (diagramData X) (pathUnitL _ _ X.(pfStr))
    j i f h x) as u.
  change ((diagramData X).(pcomp) (wid (rank j)) f x =
    f_equal (restrict X f) (restrictId X j x) • eq_sym (phomEq (diagramData X) h x)) in u.
  rewrite u.
  now apply transSymCancelR2.
Defined.

Lemma topFaceNaturalityUnit (a: A) (i: Index n) (x: cells (shiftDiagram X) i):
  topFaceNaturality a (wid (rank i)) x
    • f_equal (topFace X a i) (restrictId (shiftDiagram X) i x)
  = restrictId (baseDiagram X) i (topFace X a i x).
Proof.
  rewrite shiftRestrictId.
  change (topFaceNaturality a (wid (rank i)) x
    • f_equal (restrict X (i := Some i) (j := raiseIndex i) (topFaceWord i a))
      (phomEq (diagramData X) (keepWordId i) x
        • restrictId X (raiseIndex i) x) =
      restrictId X (Some i) (topFace X a i x)).
  rewrite <- (restrictCompLeftUnit (i := Some i) (j := raiseIndex i) (topFaceWord i a) (keepWord (wid (rank i)))
    (keepWordId i) (topFaceWordNatural (wid (rank i)) a • wcompIdr (topFaceWord i a)) x).
  unfold topFaceNaturality.
  rewrite eqTransAssoc, transCancelMid2.
  unfold phomEq.
  refine (transCongL _ (mappedInverseCancel
    (fun w: Word A (rank i) (rank (raiseIndex i)) =>
      restrict X (i := Some i) (j := raiseIndex i) w x)
    (topFaceWordNatural (wid (rank i)) a) (wcompIdr (topFaceWord i a))) • _).
  pose proof (pcompUnitRPt (diagramData X) (pathUnitR _ _ X.(pfStr))
    (raiseIndex i) (Some i) (topFaceWord i a) (wcompIdr (topFaceWord i a)) x) as u.
  change (restrictComp X (i := Some i) (j := Some i) (k := raiseIndex i)
      (wid (rank i)) (topFaceWord i a) x =
    restrictId X (Some i) (topFace X a i x) •
      eq_sym (f_equal (fun w => restrict X (i := Some i) (j := raiseIndex i) w x)
        (wcompIdr (topFaceWord i a)))) in u.
  rewrite u. now apply transSymCancelR2.
Defined.

Lemma topFaceMapUnit (a: A) (i: Index n) (x: cells (shiftDiagram X) i):
  f_equal (topFace X a i) (restrictId (shiftDiagram X) i x) =
    eq_sym (topFaceNaturality a (wid (rank i)) x)
      • restrictId (baseDiagram X) i (topFace X a i x).
Proof.
  apply (transCancelL (topFaceNaturality a (wid (rank i)) x)).
  rewrite transSymCancelL.
  now apply topFaceNaturalityUnit.
Defined.

Local Lemma shiftTopTriangle (a: A) {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: cells (shiftDiagram X) k):
  psfComp3 (diagramData X) (a := raiseIndex k) (b := raiseIndex j)
    (c := raiseIndex i) (d := Some i) (keepWord g) (keepWord f) (topFaceWord i a) x
    • phomEq (diagramData X) (a := raiseIndex k) (b := Some i)
      (f_equal (fun u => wcomp u (topFaceWord i a)) (keepWordComp f g)) x
  = f_equal (topFace X a i) (restrictComp (shiftDiagram X) f g x)
      • restrictComp X (i := Some i) (j := raiseIndex i) (k := raiseIndex k)
          (topFaceWord i a) (keepWord (wcomp g f)) x.
Proof.
  rewrite shiftRestrictComp, mapTrans.
  unfold psfComp3. rewrite 2 eqTransAssoc.
  apply transCongL. symmetry.
  now exact (pcompNatLCanonical (diagramData X) (a := raiseIndex k)
    (b := raiseIndex i) (c := Some i) (keepWordComp f g) (topFaceWord i a) x).
Defined.

Lemma topFaceNaturalityComp (a: A) {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: cells (shiftDiagram X) k):
  f_equal (restrict (baseDiagram X) f) (topFaceNaturality a g x)
    • (topFaceNaturality a f (restrict (shiftDiagram X) g x)
      • f_equal (topFace X a i) (restrictComp (shiftDiagram X) f g x))
  = restrictComp (baseDiagram X) f g (topFace X a k x)
      • topFaceNaturality a (wcomp g f) x.
Proof.
  unfold topFaceNaturality, phomEq.
  change (restrict (baseDiagram X) f) with
    ((diagramData X).(phom) (a := Some j) (b := Some i) f).
  change (restrict (shiftDiagram X) g x) with
    ((diagramData X).(phom) (a := raiseIndex k) (b := raiseIndex j) (keepWord g) x).
  refine (transCongR (pcompWhiskerL (diagramData X)
    (a := raiseIndex k) (c := Some j) (d := Some i)
    (eq_sym (topFaceWordNatural g a)) f x
    (restrictComp X (i := Some j) (j := Some k) (k := raiseIndex k)
      g (topFaceWord k a) x)
    (restrictComp X (i := Some j) (j := raiseIndex j) (k := raiseIndex k)
      (topFaceWord j a) (keepWord g) x)) _ • _).
  refine (transCongL _ (transCongR (pcompWhiskerR (diagramData X) (pathAssoc _ _ X.(pfStr))
    (a := raiseIndex k) (b := raiseIndex j) (c := Some j) (c' := raiseIndex i) (d := Some i)
    (keepWord g)
    (v := topFaceWord j a) (w := f) (v' := keepWord f) (w' := topFaceWord i a)
    (eq_sym (topFaceWordNatural f a)) x) _) • _).
  refine (conjugatePaste _ _ _ _ _ _ _ _ (shiftTopTriangle a f g x) • _).
  pose proof (psfAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr))
    (a := raiseIndex k) (b := Some k) (c := Some j) (d := Some i)
    (topFaceWord k a) g f x) as assoc.
  change (psfComp3 (diagramData X) (a := raiseIndex k) (b := Some k)
    (c := Some j) (d := Some i) (topFaceWord k a) g f x
    • phomEq (diagramData X) (a := raiseIndex k) (b := Some i)
      ((PrefixCategory A (S n)).(Category.cassoc)
        (a := raiseIndex k) (b := Some k) (c := Some j) (d := Some i)
        (topFaceWord k a) g f) x =
    restrictComp (baseDiagram X) f g (topFace X a k x)
      • restrictComp X (i := Some i) (j := Some k) (k := raiseIndex k)
          (wcomp g f) (topFaceWord k a) x) in assoc.
  rewrite <- (eqTransAssoc
    (restrictComp (baseDiagram X) f g (topFace X a k x))
    (restrictComp X (i := Some i) (j := Some k) (k := raiseIndex k)
      (wcomp g f) (topFaceWord k a) x)).
  rewrite <- assoc.
  fold (psfComp3 (diagramData X) (a := raiseIndex k) (b := Some k)
    (c := Some j) (d := Some i) (topFaceWord k a) g f x).
  rewrite (eqTransAssoc
    (psfComp3 (diagramData X) (a := raiseIndex k) (b := Some k)
      (c := Some j) (d := Some i) (topFaceWord k a) g f x)
    (phomEq (diagramData X) (a := raiseIndex k) (b := Some i)
      ((PrefixCategory A (S n)).(Category.cassoc)
        (a := raiseIndex k) (b := Some k) (c := Some j) (d := Some i)
        (topFaceWord k a) g f) x)).
  apply transCongL.
  rewrite <- (eqTransAssoc _ _
    (eq_sym (restrictComp X (i := Some i) (j := raiseIndex i) (k := raiseIndex k)
      (topFaceWord i a) (keepWord (wcomp g f)) x))).
  apply transCongR.
  unfold phomEq.
  now exact (fEqualUIP
    (@UIP (wordSet (A := A) (rank i) (rank (raiseIndex k))))
    (fun w => restrict X (i := Some i) (j := raiseIndex k) w x)
    _ _ _ _ _ eq_refl).
Defined.

Lemma topFaceMapComp (a: A) {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: cells (shiftDiagram X) k):
  f_equal (topFace X a i) (restrictComp (shiftDiagram X) f g x)
    • eq_sym (topFaceNaturality a (wcomp g f) x) =
    eq_sym (topFaceNaturality a f (restrict (shiftDiagram X) g x))
      • (f_equal (restrict (baseDiagram X) f) (eq_sym (topFaceNaturality a g x))
        • restrictComp (baseDiagram X) f g (topFace X a k x)).
Proof.
  rewrite fEqualSym.
  now exact (reversePasting _ _ _ _ _ (topFaceNaturalityComp a f g x)).
Defined.

Definition topFaceDiagramMap (a: A): DiagramMap (shiftDiagram X) (baseDiagram X) := {|
  mapCell := topFace X a;
  mapNatural i j f x := eq_sym (topFaceNaturality a f x);
  mapUnit := topFaceMapUnit a;
  mapComp i j k f g x := topFaceMapComp a f g x;
|}.

Definition topFaceMatching (a: A) (b: MatchingObject (shiftDiagram X)):
  MatchingObject (baseDiagram X) :=
  mapMatching (topFaceDiagramMap a) b.

Lemma topFaceMatchingPath (a: A) (b: MatchingObject (shiftDiagram X)) {i j}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  matchingPath (topFaceMatching a b) f g =
    topFaceNaturality a f (matchingValue b j g)
      • f_equal (topFace X a i) (matchingPath b f g).
Proof.
  change (eq_sym (eq_sym (topFaceNaturality a f (matchingValue b j g)))
    • f_equal (topFace X a i) (matchingPath b f g) =
      topFaceNaturality a f (matchingValue b j g)
        • f_equal (topFace X a i) (matchingPath b f g)).
  now rewrite eq_sym_involutive.
Defined.

End TopFace.

(** Residual-coordinate maps on fixed-height coherent matching objects. *)

(** The first [p] processed ranks, with [k] additional retained coordinates. *)
Definition shiftPrefixFunctor (A: HSet) (p k: nat):
  Functor (PrefixCategory A p) (Op (νSemiShape A)) := {|
  fobj i := rank i + k;
  fhom i j f := paddedWord k f;
  fid i := paddedId k (rank i);
  fcomp i j l f g := eq_sym (paddedComp k g f);
|}.

Definition residualNat {A: HSet} (p: nat) {k l: nat} (u: Word A k l):
  NatTrans (shiftPrefixFunctor A p l) (shiftPrefixFunctor A p k).
Proof.
  refine {| ncomp i := residualWord (rank i) u |}.
  intros i j f.
  now exact (paddedResidual f u).
Defined.

Lemma residualNatId (A: HSet) (p k: nat):
  residualNat p (wid (A := A) k) = idNatTrans (shiftPrefixFunctor A p k).
Proof.
  apply natTransEq; intro i.
  now exact (residualId (rank i) k).
Defined.

Lemma residualNatComp {A: HSet} (p: nat) {k l m: nat}
  (u: Word A k l) (v: Word A l m):
  compNatTrans (residualNat p v) (residualNat p u)
    = residualNat p (wcomp v u).
Proof.
  apply natTransEq; intro i.
  now exact (residualComp (rank i) u v).
Defined.

Definition residualFunctor (A: HSet) (p: nat):
  Functor (Op (νSemiShape A))
    (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) := {|
  fobj := shiftPrefixFunctor A p;
  fhom k l u := residualNat p u;
  fid k := residualNatId A p k;
  fcomp k l m u v := eq_sym (residualNatComp p v u);
|}.

Definition shiftedPrefix {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))): Diagram A p :=
  pullbackDiagram (shiftPrefixFunctor A p k) F.

Definition wholeCellFunctor (A: HSet) (p: nat):
  Functor (Op (νSemiShape A)) (Op (νSemiShape A)) := {|
  fobj k := p + k;
  fhom k l u := residualWord p u;
  fid k := residualId p k;
  fcomp k l m u v := eq_sym (residualComp p v u);
|}.

Definition wholeCellDiagram {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  PathDiagramFamily (Op (νSemiShape A)) :=
  pullbackDiagram (wholeCellFunctor A p) F.

Definition MatchingPartialDiagram {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  PathDiagramFamily (Op (νSemiShape A)) :=
  pullbackDiagram (residualFunctor A p)
    (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F).

Definition MatchingPartialPresentation {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))): νGpdPresentation A :=
  ofPsfTot A (MatchingPartialDiagram p F).

(** Restricting a whole cell supplies its partial matching boundary. *)
Definition partialBoundary {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (k: nat)
  (x: F.(pfObj) (p + k)): MatchingObject (shiftedPrefix p k F) :=
  matchingMap (shiftedPrefix (S p) k F) x.

Definition residualMap {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l):
  DiagramMap (shiftedPrefix p l F) (shiftedPrefix p k F) :=
  pullbackMap F (shiftPrefixFunctor A p l) (shiftPrefixFunctor A p k) (residualNat p u).

Definition residualMatching {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l):
  MatchingObject (shiftedPrefix p l F) -> MatchingObject (shiftedPrefix p k F) :=
  mapMatching (residualMap p F u).

Lemma residualMatchingValue {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (b: MatchingObject (shiftedPrefix p l F)) i f:
  matchingValue (residualMatching p F u b) i f =
    (pathData _ _ F.(pfStr)).(phom) (residualWord (rank i) u) (matchingValue b i f).
Proof. now reflexivity. Defined.

Definition boundaryNaturalValues {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (x: F.(pfObj) (p + l)):
  ComparisonValues (shiftedPrefix p k F)
    (residualMatching p F u (partialBoundary p F l x))
    (partialBoundary p F k ((pathData _ _ F.(pfStr)).(phom) (residualWord p u) x)) :=
  fun i g => (residualMap (S p) F u).(mapNatural) (i := Some i) (j := None) g x.

Lemma boundaryNaturalSquares {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (x: F.(pfObj) (p + l)):
  ComparisonSquares (shiftedPrefix p k F) (boundaryNaturalValues p F u x).
Proof.
  intros i j f g. symmetry.
  change ((eq_sym ((residualMap (S p) F u).(mapNatural)
      (i := Some i) (j := Some j) f
      (restrict (shiftedPrefix (S p) l F) (i := Some j) (j := None) g x))
    • f_equal ((residualMap (S p) F u).(mapCell) (Some i))
        (restrictComp (shiftedPrefix (S p) l F)
          (i := Some i) (j := Some j) (k := None) f g x))
      • (residualMap (S p) F u).(mapNatural)
          (i := Some i) (j := None) (wcomp g f) x =
    f_equal (restrict (shiftedPrefix (S p) k F) (i := Some i) (j := Some j) f)
      ((residualMap (S p) F u).(mapNatural) (i := Some j) (j := None) g x)
      • restrictComp (shiftedPrefix (S p) k F)
          (i := Some i) (j := Some j) (k := None) f g
          ((residualMap (S p) F u).(mapCell) None x)).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ ((residualMap (S p) F u).(mapComp)
    (i := Some i) (j := Some j) (k := None) f g x) • _).
  now apply eq_trans_sym_cancel_l.
Defined.

Definition boundaryNatural {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (x: F.(pfObj) (p + l)):
  residualMatching p F u (partialBoundary p F l x) =
    partialBoundary p F k ((pathData _ _ F.(pfStr)).(phom) (residualWord p u) x) :=
  matchingHomotopy (shiftedPrefix p k F) (boundaryNaturalValues p F u x)
    (boundaryNaturalSquares p F u x).

Lemma boundaryNaturalValue {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (x: F.(pfObj) (p + l)) i g:
  f_equal (fun b => matchingValue b i g) (boundaryNatural p F u x) =
    (residualMap (S p) F u).(mapNatural) (i := Some i) (j := None) g x.
Proof.
  now exact (matchingHomotopyValue (shiftedPrefix p k F)
    (boundaryNaturalValues p F u x) (boundaryNaturalSquares p F u x) i g).
Defined.

Section MatchingEvaluation.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation MP := (MatchingPartialDiagram p F).
Local Abbreviation MD := (pathData _ _ MP.(pfStr)).

Lemma matchingPartialCompValue {k l m} (u: Word A k l) (v: Word A l m)
  (b: MatchingObject (shiftedPrefix p m F)) i g:
  f_equal (fun z => matchingValue z i g) (MD.(pcomp) v u b) =
    FD.(pcomp) (residualWord (rank i) v) (residualWord (rank i) u) (matchingValue b i g)
      • phomEq FD (residualComp (rank i) u v) (matchingValue b i g).
Proof.
  unfold MatchingPartialDiagram.
  rewrite pullbackCompPoint, eq_trans_map_distr.
  change (f_equal (fun z => matchingValue z i g)
      (matchingComposition p (Op (νSemiShape A)) F
        (shiftPrefixFunctor A p m) (shiftPrefixFunctor A p l)
        (shiftPrefixFunctor A p k) (residualNat p v) (residualNat p u) b)
    • f_equal (fun z => matchingValue z i g)
      (phomEq (matchingDiagramData p (Op (νSemiShape A)) F)
        (eq_sym ((residualFunctor A p).(fcomp) v u)) b) =
    FD.(pcomp) (residualWord (rank i) v) (residualWord (rank i) u) (matchingValue b i g)
      • phomEq FD (residualComp (rank i) u v) (matchingValue b i g)).
  refine (transCongR
    (matchingCompositionValue p (Op (νSemiShape A)) F
      (shiftPrefixFunctor A p m) (shiftPrefixFunctor A p l) (shiftPrefixFunctor A p k)
      (residualNat p v) (residualNat p u) b i g) _ • _).
  now exact (transCongL _
    (matchingDiagramArrowValue p (Op (νSemiShape A)) F
      (shiftPrefixFunctor A p m) (shiftPrefixFunctor A p k)
      (eq_sym ((residualFunctor A p).(fcomp) v u)) b i g (residualComp (rank i) u v))).
Defined.

Lemma residualMatchingMapPath {k l} (u: Word A k l)
  {b c: MatchingObject (shiftedPrefix p l F)} (e: b = c) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (residualMatching p F u) e) =
    f_equal (FD.(phom) (residualWord (rank i) u))
      (f_equal (fun z => matchingValue z i g) e).
Proof. now destruct e. Defined.

Lemma partialBoundaryMapPath k {x y: F.(pfObj) (p + k)} (e: x = y) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (partialBoundary p F k) e) =
    f_equal (FD.(phom) (paddedWord k g)) e.
Proof. now destruct e. Defined.

Definition boundaryNaturality {k l} (u: Word A k l) (x: F.(pfObj) (p + l)):
  partialBoundary p F k (FD.(phom) (residualWord p u) x) =
    residualMatching p F u (partialBoundary p F l x) :=
  eq_sym (boundaryNatural p F u x).

Lemma boundaryNaturalityValue {k l} (u: Word A k l)
  (x: F.(pfObj) (p + l)) i g:
  f_equal (fun z => matchingValue z i g) (boundaryNaturality u x) =
    pullbackNaturality F (shiftPrefixFunctor A (S p) l)
      (shiftPrefixFunctor A (S p) k) (residualNat (S p) u)
      (i := Some i) (j := None) g x.
Proof.
  unfold boundaryNaturality. rewrite fEqualSym, boundaryNaturalValue.
  change (eq_sym (eq_sym
    (pullbackNaturality F (shiftPrefixFunctor A (S p) l)
      (shiftPrefixFunctor A (S p) k) (residualNat (S p) u)
      (i := Some i) (j := None) g x)) =
    pullbackNaturality F (shiftPrefixFunctor A (S p) l)
      (shiftPrefixFunctor A (S p) k) (residualNat (S p) u)
      (i := Some i) (j := None) g x).
  now rewrite eq_sym_involutive.
Defined.

Lemma partialBoundaryComp {k l m} (u: Word A k l) (v: Word A l m)
  (x: F.(pfObj) (p + m)):
  f_equal (partialBoundary p F k)
      ((pathData _ _ (wholeCellDiagram p F).(pfStr)).(pcomp) v u x)
    • boundaryNaturality (wcomp v u) x =
    boundaryNaturality u (FD.(phom) (residualWord p v) x)
      • (f_equal (residualMatching p F u) (boundaryNaturality v x)
        • MD.(pcomp) v u (partialBoundary p F m x)).
Proof.
  apply matchingPathExt; intros i g.
  rewrite 3 eq_trans_map_distr, partialBoundaryMapPath,
    residualMatchingMapPath, boundaryNaturalityValue.
  refine (transCongL _ (boundaryNaturalityValue (wcomp v u) x i g) • _).
  refine (_ • eq_sym (transCongL _ (transCongR
    (f_equal (fun e => f_equal (FD.(phom) (residualWord (rank i) u)) e)
      (boundaryNaturalityValue v x i g)) _))).
  refine (_ • eq_sym (transCongL _ (transCongL _
    (matchingPartialCompValue u v (partialBoundary p F m x) i g)))).
  unfold wholeCellDiagram.
  rewrite pullbackCompPoint, eq_trans_map_distr.
  change ((f_equal (FD.(phom) (paddedWord k g))
      (FD.(pcomp) (residualWord p v) (residualWord p u) x)
    • f_equal (FD.(phom) (paddedWord k g))
      (phomEq FD (eq_sym (eq_sym (residualComp p u v))) x))
    • pullbackNaturality F (shiftPrefixFunctor A (S p) m)
      (shiftPrefixFunctor A (S p) k) (residualNat (S p) (wcomp v u))
      (i := Some i) (j := None) g x =
    pullbackNaturality F (shiftPrefixFunctor A (S p) l)
      (shiftPrefixFunctor A (S p) k) (residualNat (S p) u)
      (i := Some i) (j := None) g (FD.(phom) (residualWord p v) x)
      • (f_equal (FD.(phom) (residualWord (rank i) u))
          (pullbackNaturality F (shiftPrefixFunctor A (S p) m)
            (shiftPrefixFunctor A (S p) l) (residualNat (S p) v)
            (i := Some i) (j := None) g x)
        • (FD.(pcomp) (residualWord (rank i) v) (residualWord (rank i) u)
            (FD.(phom) (paddedWord m g) x)
          • phomEq FD (residualComp (rank i) u v) (FD.(phom) (paddedWord m g) x)))).
  rewrite eq_sym_involutive, eqTransAssoc.
  refine (transCongL _
    (pullbackNaturalityEqComponents F
      (shiftPrefixFunctor A (S p) m) (shiftPrefixFunctor A (S p) k)
      (residualNatComp (S p) u v) (i := Some i) (j := None) g x
      (residualComp (rank i) u v) (residualComp p u v)) • _).
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR
    (pullbackNaturalityVertical F
      (shiftPrefixFunctor A (S p) m) (shiftPrefixFunctor A (S p) l)
      (shiftPrefixFunctor A (S p) k) (residualNat (S p) v) (residualNat (S p) u)
      (i := Some i) (j := None) g x) _ • _).
  now rewrite 2 eqTransAssoc.
Defined.

End MatchingEvaluation.

(** Generating faces and selected exchanges after retaining a fixed coordinate
    prefix. *)

Local Fixpoint addBound (p: nat) {q k: nat} (h: q <= k): p + q <= p + k :=
  match p with 0 => h | S p => ⇑ (addBound p h) end.

Definition residualPresentation {A: HSet} (p: nat) (P: νGpdPresentation A):
  νGpdPresentation A := ofPsfTot A (wholeCellDiagram p (toPsfTot A P)).

Local Lemma exchangeCompose {T: Type} {a b c d e f: T}
  (p: a = b) (q: d = e) (u: b = c) (v: c = f) (w: e = f):
  (p • u) • (v • eq_sym (q • w)) = p • ((u • (v • eq_sym w)) • eq_sym q).
Proof. now destruct p, q, u, v, w. Defined.

Section Presentation.
Context {A: HSet} (P: νGpdPresentation A).
Local Abbreviation D := (gpdStr P).

Local Definition shiftedFaceAt {m n: nat} (e: n = S m) q (Hq: q <= m) a
  (x: P.(G0) n): P.(G0) m :=
  P.(GFace) m q Hq a (rew [fun k => P.(G0) k] e in x).

Local Definition shiftedExchangeAt {m0 m1 m2: nat}
  (e1: m1 = S m0) (e2: m2 = S m1)
  q (Hq: q <= m0) r (Hr: r <= q) qTop (HqTop: qTop <= m1) (HrTop: r <= m1)
  (eTop: qTop = S q) a c (x: P.(G0) m2):
  shiftedFaceAt e1 q Hq a (shiftedFaceAt e2 r HrTop c x) =
    shiftedFaceAt e1 r (Hr ↕ Hq) c (shiftedFaceAt e2 qTop HqTop a x).
Proof.
  subst qTop. subst m1. subst m2.
  now exact (P.(GFaceCoh) m0 q Hq r Hr a c x).
Defined.

Local Lemma applyWordInputCast {i j k: nat} (e: j = k)
  (w: Word A i j) (x: P.(G0) j):
  applyW j w D x = applyW k (wordCast eq_refl e w) D (rew [fun k => P.(G0) k] e in x).
Proof. now destruct e. Defined.

Local Definition wordFaceCompare {m n: nat} (e: n = S m)
  q (Hq: q <= m) a (w: Word A m n)
  (ew: wordCast eq_refl e w = wgen m q a) (x: P.(G0) n):
  applyW n w D x = shiftedFaceAt e q Hq a x :=
  applyWordInputCast e w x
    • (f_equal (fun u => applyW (S m) u D (rew [fun k => P.(G0) k] e in x)) ew
      • applyWgen A D m q Hq a (rew [fun k => P.(G0) k] e in x)).

Local Lemma wordFaceCompareRefl m q (Hq: q <= m) a (x: P.(G0) (S m)):
  wordFaceCompare eq_refl q Hq a (wgen m q a) eq_refl x = applyWgen A D m q Hq a x.
Proof.
  unfold wordFaceCompare, applyWordInputCast. cbn [eq_rect f_equal].
  now rewrite 2 eq_trans_refl_l.
Defined.

Local Definition interpretedExchange {m0 m1 m2: nat}
  (v: Word A m0 m1) (u: Word A m1 m2)
  (v': Word A m0 m1) (u': Word A m1 m2)
  (e: wcomp u v = wcomp u' v') (x: P.(G0) m2):
  applyW m1 v D (applyW m2 u D x) = applyW m1 v' D (applyW m2 u' D x) :=
  applyWComp m2 m1 m0 u v D (gpdCoh P) x
    • (f_equal (fun w => applyW m2 w D x) e
      • eq_sym (applyWComp m2 m1 m0 u' v' D (gpdCoh P) x)).

Local Lemma wordFaceExchange {m0 m1 m2: nat}
  (e1: m1 = S m0) (e2: m2 = S m1)
  q (Hq: q <= m0) r (Hr: r <= q) qTop (HqTop: qTop <= m1) (HrTop: r <= m1)
  (eTop: qTop = S q) a c
  (v: Word A m0 m1) (u: Word A m1 m2)
  (v': Word A m0 m1) (u': Word A m1 m2)
  (ev: wordCast eq_refl e1 v = wgen m0 q a)
  (eu: wordCast eq_refl e2 u = wgen m1 r c)
  (ev': wordCast eq_refl e1 v' = wgen m0 r c)
  (eu': wordCast eq_refl e2 u' = wgen m1 qTop a)
  (e: wcomp u v = wcomp u' v') (x: P.(G0) m2):
  interpretedExchange v u v' u' e x
    • (wordFaceCompare e1 r (Hr ↕ Hq) c v' ev' (applyW m2 u' D x)
      • f_equal (shiftedFaceAt e1 r (Hr ↕ Hq) c)
          (wordFaceCompare e2 qTop HqTop a u' eu' x)) =
  (wordFaceCompare e1 q Hq a v ev (applyW m2 u D x)
    • f_equal (shiftedFaceAt e1 q Hq a) (wordFaceCompare e2 r HrTop c u eu x))
    • shiftedExchangeAt e1 e2 q Hq r Hr qTop HqTop HrTop eTop a c x.
Proof.
  subst qTop. subst m1. subst m2.
  cbn [wordCast] in ev, eu, ev', eu'.
  subst v u v' u'.
  replace e with (wgenExchange m0 q Hq r Hr a c)
    by now apply (wordSet (A := A) m0 (S (S m0))).(UIP).
  rewrite 4 wordFaceCompareRefl.
  now exact (applyWgenCoh A m0 D (gpdCoh P) q Hq r Hr a c x).
Defined.

Definition shiftedFace (p k q: nat) (Hq: q <= k) a
  (x: P.(G0) (p + S k)): P.(G0) (p + k) :=
  shiftedFaceAt (Nat.add_succ_r p k) (p + q) (addBound p Hq) a x.

Definition shiftedExchange (p k q: nat) (Hq: q <= k) r (Hr: r <= q) a c
  (x: P.(G0) (p + S (S k))):
  shiftedFace p k q Hq a (shiftedFace p (S k) r (Hr ↕ ↑ Hq) c x) =
    shiftedFace p k r (Hr ↕ Hq) c (shiftedFace p (S k) (S q) (⇑ Hq) a x) :=
  shiftedExchangeAt (Nat.add_succ_r p k) (Nat.add_succ_r p (S k))
    (p + q) (addBound p Hq) (p + r) (addBound p Hr)
    (p + S q) (addBound p (⇑ Hq)) (addBound p (Hr ↕ ↑ Hq))
    (Nat.add_succ_r p q) a c x.

Definition faceGen (p k q: nat) (Hq: q <= k) a
  (x: (residualPresentation p P).(G0) (S k)):
  (residualPresentation p P).(GFace) k q Hq a x = shiftedFace p k q Hq a x :=
  wordFaceCompare (Nat.add_succ_r p k) (p + q) (addBound p Hq) a
    (residualWord p (wgen k q a)) (residualGen p k q Hq a) x.

Local Lemma faceExchangeUnfold (p k q: nat) (Hq: q <= k) r (Hr: r <= q) a c
  (e: wcomp (residualWord p (wgen (S k) r c)) (residualWord p (wgen k q a)) =
      wcomp (residualWord p (wgen (S k) (S q) a)) (residualWord p (wgen k r c)))
  (x: (residualPresentation p P).(G0) (S (S k))):
  (residualPresentation p P).(GFaceCoh) k q Hq r Hr a c x =
  interpretedExchange (residualWord p (wgen k q a)) (residualWord p (wgen (S k) r c))
    (residualWord p (wgen k r c)) (residualWord p (wgen (S k) (S q) a)) e x.
Proof.
  unfold residualPresentation, ofPsfTot, ofPsf.
  cbn [GFaceCoh]. unfold ofPsfCoh, wholeCellDiagram.
  rewrite 2 pullbackCompPoint.
  change ((applyWComp (p + S (S k)) (p + S k) (p + k)
      (residualWord p (wgen (S k) r c)) (residualWord p (wgen k q a)) D (gpdCoh P) x
    • f_equal (fun w => applyW (p + S (S k)) w D x)
      (eq_sym (eq_sym (residualComp p (wgen k q a) (wgen (S k) r c)))))
    • (f_equal (fun w => applyW (p + S (S k)) (residualWord p w) D x)
        (wgenExchange k q Hq r Hr a c)
      • eq_sym (applyWComp (p + S (S k)) (p + S k) (p + k)
          (residualWord p (wgen (S k) (S q) a)) (residualWord p (wgen k r c)) D (gpdCoh P) x
        • f_equal (fun w => applyW (p + S (S k)) w D x)
          (eq_sym (eq_sym (residualComp p (wgen k r c) (wgen (S k) (S q) a)))))) =
    interpretedExchange (residualWord p (wgen k q a)) (residualWord p (wgen (S k) r c))
      (residualWord p (wgen k r c)) (residualWord p (wgen (S k) (S q) a)) e x).
  rewrite 2 eq_sym_involutive.
  unfold interpretedExchange.
  refine (exchangeCompose _ _ _ _ _ • _).
  apply transCongL. apply transCongR.
  refine (transCongL _ (transCongL _
    (eq_sym (fEqualSym (fun w => applyW (p + S (S k)) w D x)
      (residualComp p (wgen k r c) (wgen (S k) (S q) a))))) • _).
  refine (transCongL _ (transCongR
    (eq_sym (f_equal_compose (residualWord p)
      (fun w => applyW (p + S (S k)) w D x) (wgenExchange k q Hq r Hr a c))) _) • _).
  now exact (fEqualUIP (@UIP (wordSet (A := A) (p + k) (p + S (S k))))
    (fun w => applyW (p + S (S k)) w D x) _ _ _ e eq_refl eq_refl).
Defined.

Lemma faceGenCoh (p: nat):
  GSqType A (residualPresentation p P).(GFaceCoh) (shiftedExchange p) (faceGen p).
Proof.
  intros k q Hq r Hr a c x.
  pose (e := residualComp p (wgen k q a) (wgen (S k) r c)
    • (f_equal (residualWord p) (wgenExchange k q Hq r Hr a c)
      • eq_sym (residualComp p (wgen k r c) (wgen (S k) (S q) a)))).
  rewrite (faceExchangeUnfold p k q Hq r Hr a c e x).
  now exact (wordFaceExchange (Nat.add_succ_r p k) (Nat.add_succ_r p (S k))
    (p + q) (addBound p Hq) (p + r) (addBound p Hr)
    (p + S q) (addBound p (⇑ Hq)) (addBound p (Hr ↕ ↑ Hq))
    (Nat.add_succ_r p q) a c
    (residualWord p (wgen k q a)) (residualWord p (wgen (S k) r c))
    (residualWord p (wgen k r c)) (residualWord p (wgen (S k) (S q) a))
    (residualGen p k q Hq a) (residualGen p (S k) r (Hr ↕ ↑ Hq) c)
    (residualGen p k r (Hr ↕ Hq) c) (residualGen p (S k) (S q) (⇑ Hq) a) e x).
Defined.

End Presentation.
