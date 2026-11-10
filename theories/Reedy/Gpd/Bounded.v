(** Maps between bounded presentations act on their retained finite diagrams. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Funext Notation RewLemmas LeSProp FinitePrefix.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagram Pseudonatural LocallyDiscretePseudofunctor
  PathDiagramTransformation.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presheaf.Gpd Require Import Pseudofunctor Bounded Transformation.
From Bonak.Reedy.Gpd Require Import Reedy Matching ExtensionMap.
Set Primitive Projections.
Set Printing Projections.


(** A diagram on the whole semi-shape category restricts to the ranks below
    [n]. *)
Definition restrictDiagram {A: HSet} n (X: PathDiagramFamily (Op (νSemiShape A))):
  Diagram A n :=
  @Build_PathDiagramFamily (PrefixCategory A n) (fun i => X.(pfObj) (rank i))
    (@Build_PathDiagram (PrefixCategory A n) (fun i => X.(pfObj) (rank i))
      (@Build_PathDiagramData (PrefixCategory A n) (fun i => X.(pfObj) (rank i))
        (fun i j f => (pathData _ _ X.(pfStr)).(phom) f)
        (fun i => (pathData _ _ X.(pfStr)).(pid) (rank i))
        (fun i j k f g => (pathData _ _ X.(pfStr)).(pcomp) f g))
      (fun i j f => pathUnitL _ _ X.(pfStr) (rank i) (rank j) f)
      (fun i j f => pathUnitR _ _ X.(pfStr) (rank i) (rank j) f)
      (fun i j k l f g h => pathAssoc _ _ X.(pfStr)
        (rank i) (rank j) (rank k) (rank l) f g h)).

Definition restrictTransformation {A: HSet} n
  {X Y: PathDiagramFamily (Op (νSemiShape A))}
  (α: Pseudonatural (expandPseudofunctor X) (expandPseudofunctor Y)):
  DiagramMap (restrictDiagram n X) (restrictDiagram n Y) :=
  @Build_DiagramMap A n (restrictDiagram n X) (restrictDiagram n Y)
    (fun i => α.(pnComponent) (rank i))
    (fun i j f x => (α.(pnNaturality) (a := rank j) (b := rank i) f).(isoHom) x)
    (fun i x => pseudonaturalUnitPoint X Y α (rank i) x)
    (fun i j k f g x => pseudonaturalCompPoint X Y α
      (i := rank k) (j := rank j) (k := rank i) g f x).

Definition rankBound {n} (i: Index n): leR (S (rank i)) n.
Proof.
  revert i. induction n as [|n IH]; intro i.
  - now destruct i.
  - destruct i as [i|]; cbn.
    + now exact (↑ (IH i)).
    + now exact leR_refl.
Defined.

Definition cutProjectionPresentation {A: HSet} N (P: νGpdPresentation A):
  PresentationMap (cutPresentation N P) P.
Proof.
  refine (@Build_PresentationMap A (cutPresentation N P) P
    (fun n z => z.2) (fun n q Hq a z => eq_refl) _).
  intros n q Hq r Hr a b z.
  change (eq_refl • f_equal (fun z: cutCell N P n => z.2)
    (boundFaceCoh (fun k => leR (S k) N) (fun k h => ↓ h) P n q Hq r Hr a b z) =
    P.(GFaceCoh) n q Hq r Hr a b z.2).
  exact (eq_trans_refl_l _ •
    boundFaceCohProject (fun k => leR (S k) N) (fun k h => ↓ h) P n q Hq r Hr a b z).
Defined.

Definition cutProjection {A: HSet} N (P: νGpdPresentation A):
  DiagramMap (restrictDiagram N (toPsfTot A (cutPresentation N P)))
    (restrictDiagram N (toPsfTot A P)) :=
  restrictTransformation N (X := toPsfTot A (cutPresentation N P)) (Y := toPsfTot A P)
    (generatedTransformation (cutProjectionPresentation N P)).

Local Lemma inverseCompAlgebra {T: Type} {v0 v1 v2 v3 v4 v5: T}
  (a: v0 = v1) (b: v2 = v3) (c: v3 = v1) (d: v2 = v4)
  (e: v4 = v5) (q: v1 = v5) (t: v0 = v2)
  (nat: t • b = a • eq_sym c) (coh: d • e = b • (c • q)):
  q • eq_sym e = eq_sym a • (t • d).
Proof.
  destruct a, b, c, d, e.
  change (t = eq_refl) in nat.
  rewrite 3 eq_trans_refl_l in coh.
  now rewrite nat, <- coh.
Defined.

Section Inclusion.
Context {A: HSet} (N: nat) (P: νGpdPresentation A).
Local Abbreviation Raw := (restrictDiagram N (toPsfTot A P)).
Local Abbreviation Cut := (restrictDiagram N (toPsfTot A (cutPresentation N P))).
Local Abbreviation π := (cutProjection N P).
Local Abbreviation B := (fun k => leR (S k) N).

Definition includeCell (i: Index N) (x: cells Raw i): cells Cut i :=
  boundInclude B P (rank i) (rankBound i) x.

Lemma includePathProject {i: Index N} {x y: cells Raw i} (p: x = y):
  f_equal (fun z: cells Cut i => z.2) (f_equal (includeCell i) p) = p.
Proof.
  exact (f_equal_compose (includeCell i) (fun z: cells Cut i => z.2) p • f_equal_id p).
Defined.

Definition boxPath {i: Index N} {x y: cells Cut i} (p: x.2 = y.2): x = y.
Proof.
  destruct x as [[h] x], y as [[h'] y].
  now exact (f_equal (boundInclude B P (rank i) h) p).
Defined.

Lemma boxPathProject {i: Index N} {x y: cells Cut i} (p: x.2 = y.2):
  f_equal (fun z: cells Cut i => z.2) (boxPath (i := i) (x := x) (y := y) p) = p.
Proof.
  destruct x as [[h] x], y as [[h'] y].
  exact (f_equal_compose (boundInclude B P (rank i) h)
    (fun z: cells Cut i => z.2) p • f_equal_id p).
Defined.

Definition includeNatural {i j: Index N}
  (f: Word A (rank i) (rank j)) (x: cells Raw j):
  includeCell i (restrict Raw f x) = restrict Cut f (includeCell j x) :=
  boxPath (i := i) (x := includeCell i (restrict Raw (i := i) (j := j) f x))
    (y := restrict Cut (i := i) (j := j) f (includeCell j x))
    (eq_sym (π.(mapNatural) (i := i) (j := j) f (includeCell j x))).

Lemma includeNaturalProject {i j: Index N}
  (f: Word A (rank i) (rank j)) (x: cells Raw j):
  f_equal (fun z: cells Cut i => z.2) (includeNatural f x) =
    eq_sym (π.(mapNatural) (i := i) (j := j) f (includeCell j x)).
Proof.
  now exact (boxPathProject (i := i)
    (x := includeCell i (restrict Raw (i := i) (j := j) f x))
    (y := restrict Cut (i := i) (j := j) f (includeCell j x))
    (eq_sym (π.(mapNatural) (i := i) (j := j) f (includeCell j x)))).
Defined.

Lemma projectionPathNatural {i j: Index N}
  (f: Word A (rank i) (rank j)) {x y: cells Cut j} (p: x = y):
  f_equal (fun z: cells Cut i => z.2) (f_equal (restrict Cut f) p)
    • π.(mapNatural) (i := i) (j := j) f y = π.(mapNatural) (i := i) (j := j) f x
      • f_equal (restrict Raw f) (f_equal (fun z: cells Cut j => z.2) p).
Proof. destruct p. now apply eq_trans_refl_l. Defined.

Lemma includeUnit (i: Index N) (x: cells Raw i):
  f_equal (includeCell i) (restrictId Raw i x) =
    includeNatural (wid (rank i)) x • restrictId Cut i (includeCell i x).
Proof.
  apply (boundPathInjective B P (k := rank i)).
  refine (includePathProject (i := i) (restrictId Raw i x) • _).
  refine (_ • eq_sym (eq_trans_map_distr (fun z: cells Cut i => z.2)
    (includeNatural (i := i) (j := i) (wid (rank i)) x)
    (restrictId Cut i (includeCell i x)))).
  refine (_ • eq_sym (transCongR
    (includeNaturalProject (i := i) (j := i) (wid (rank i)) x)
    (f_equal (fun z: cells Cut i => z.2) (restrictId Cut i (includeCell i x))))).
  apply (transCancelL (π.(mapNatural) (i := i) (j := i) (wid (rank i)) (includeCell i x))).
  refine (eq_sym (π.(mapUnit) i (includeCell i x)) • _).
  now symmetry; apply transSymCancelL.
Defined.

Lemma includeComp {i j k: Index N}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)) (x: cells Raw k):
  f_equal (includeCell i) (restrictComp Raw f g x) • includeNatural (wcomp g f) x =
    includeNatural f (restrict Raw g x)
      • (f_equal (restrict Cut f) (includeNatural g x)
        • restrictComp Cut f g (includeCell k x)).
Proof.
  apply (boundPathInjective B P (k := rank i)).
  rewrite 3 eq_trans_map_distr.
  refine (f_equal2 (fun p q => p • q)
    (includePathProject (i := i) (restrictComp Raw (i := i) (j := j) (k := k) f g x))
    (includeNaturalProject (i := i) (j := k) (wcomp g f) x) • _).
  refine (_ • eq_sym (transCongR
    (includeNaturalProject (i := i) (j := j) f (restrict Raw (i := j) (j := k) g x)) _)).
  eapply inverseCompAlgebra with
    (b := π.(mapNatural) (i := i) (j := j) f
      (restrict Cut (i := j) (j := k) g (includeCell k x)))
    (c := f_equal (restrict Raw (i := i) (j := j) f)
      (π.(mapNatural) (i := j) (j := k) g (includeCell k x))).
  - refine (projectionPathNatural (i := i) (j := j) f (includeNatural (i := j) (j := k) g x) • _).
    apply transCongL.
    refine (f_equal (fun p => f_equal (restrict Raw f) p) (includeNaturalProject (i := j) (j := k) g x) • _).
    now exact (fEqualSym (restrict Raw (i := i) (j := j) f)
      (π.(mapNatural) (i := j) (j := k) g (includeCell k x))).
  - now exact (π.(mapComp) (i := i) (j := j) (k := k) f g (includeCell k x)).
Defined.

Definition cutInclusion: DiagramMap Raw Cut :=
  @Build_DiagramMap A N Raw Cut includeCell
    (fun i j f x => includeNatural (i := i) (j := j) f x) includeUnit
    (fun i j k f g x => includeComp (i := i) (j := j) (k := k) f g x).
End Inclusion.

Definition cutPresentationDiagramMap {A: HSet} N (P Q: νGpdPresentation A)
  (M: PresentationMap (cutPresentation N P) (cutPresentation N Q)):
  DiagramMap (restrictDiagram N (toPsfTot A P)) (restrictDiagram N (toPsfTot A Q)) :=
  composeDiagramMap
    (composeDiagramMap (cutInclusion N P)
      (restrictTransformation N (X := toPsfTot A (cutPresentation N P))
        (Y := toPsfTot A (cutPresentation N Q)) (generatedTransformation M)))
    (cutProjection N Q).

