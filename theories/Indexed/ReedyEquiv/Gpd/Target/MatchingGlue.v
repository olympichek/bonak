(** Gluing a matching object of a diagram from a matching object of its shift
    and top cells joined by top-face paths: the glued values and comparison
    paths, their unit and composition laws, and the gluing comparisons. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Notation RewLemmas FinitePrefix.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift.
From Bonak.Indexed.ReedyEquiv.Gpd.Target Require Import ShiftedPrefix.

Set Primitive Projections.
Set Printing Projections.
Import FinitePrefix.

(** Gluing matching comparison paths from retained and constant-coordinate
    branches. *)

Section Gluing.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).
Context (b: MatchingObject (shiftDiagram X)) (y: A -> cells X None).
Context (q: forall a (i: Index n) (g: Word A (rank i) n),
  topFace X a i (matchingValue b i g) = restrict X (i := Some i) (j := None) g (y a)).

Definition gluedValues: MatchingValues X := mergeValues X b.1 y.

Definition glueSkipPath (i j: Index (S n))
  (f: Word A (rank i) (rank j)) a (g: Word A (rank j) n):
  restrict X f (gluedValues j (wskip a g)) = gluedValues i (wcomp (wskip a g) f) :=
  restrictComp X (i := i) (j := j) (k := None) f g (y a).

Definition keepCompositeValue {i j: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  gluedValues (raiseIndex i) (wcomp (keepToTop g) (keepWord f))
    = matchingValue b i (wcomp g f) :=
  f_equal (gluedValues (raiseIndex i)) (keepToTopComp f g)
    • mergeValuesKeep X b.1 y i (wcomp g f).

Definition glueKeepPath (i j: Index n)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  restrict X (keepWord f) (gluedValues (raiseIndex j) (keepToTop g)) =
    gluedValues (raiseIndex i) (wcomp (keepToTop g) (keepWord f)) :=
  f_equal (restrict X (i := raiseIndex i) (j := raiseIndex j) (keepWord f))
    (mergeValuesKeep X b.1 y j g)
    • (matchingPath b f g • eq_sym (keepCompositeValue f g)).

Definition mixedPathCore (i j: Index n) a
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f) (matchingValue b j g) =
    restrict X (i := Some i) (j := None) (wcomp g f) (y a) :=
  eq_sym (restrictComp X (i := Some i) (j := Some j) (k := raiseIndex j)
    f (topFaceWord j a) (matchingValue b j g)
    • phomEq (diagramData X) (a := raiseIndex j) (b := Some i)
      (mixedWordFactor a f) (matchingValue b j g))
  • (f_equal (restrict X (i := Some i) (j := Some j) f) (q a j g)
    • restrictComp X (i := Some i) (j := Some j) (k := None) f g (y a)).

Definition glueMixedPath (i j: Index n) a
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  restrict X (mixedWord a f) (gluedValues (raiseIndex j) (keepToTop g)) =
    gluedValues (Some i) (wcomp (keepToTop g) (mixedWord a f)) :=
  f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
    (mergeValuesKeep X b.1 y j g)
    • (mixedPathCore i j a f g
      • eq_sym (f_equal (gluedValues (Some i)) (mixedToTopComp a f g))).

Definition gluedPaths: MatchingPaths X gluedValues :=
  composableWordsElim
    (fun i j f g => restrict X f (gluedValues j g) = gluedValues i (wcomp g f))
    glueSkipPath glueMixedPath glueKeepPath.

Lemma gluedPathsSkip i j f a g:
  gluedPaths i j f (wskip a g) = glueSkipPath i j f a g.
Proof.
  now exact (composableWordsElimSkip _ glueSkipPath glueMixedPath glueKeepPath i j f a g).
Defined.

Lemma gluedPathsKeep i j f g:
  gluedPaths (raiseIndex i) (raiseIndex j) (keepWord f) (keepToTop g) = glueKeepPath i j f g.
Proof.
  now exact (composableWordsElimKeep _ glueSkipPath glueMixedPath glueKeepPath i j f g).
Defined.

Lemma gluedPathsMixed i j a f g:
  gluedPaths (Some i) (raiseIndex j) (mixedWord a f) (keepToTop g) = glueMixedPath i j a f g.
Proof.
  now exact (composableWordsElimMixed _ glueSkipPath glueMixedPath glueKeepPath i j a f g).
Defined.

Lemma glueMixedNormalized i j a f g:
  gluedPaths (Some i) (raiseIndex j) (mixedWord a f) (keepToTop g)
    • f_equal (gluedValues (Some i)) (mixedToTopComp a f g) =
  f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
    (mergeValuesKeep X b.1 y j g) • mixedPathCore i j a f g.
Proof.
  rewrite gluedPathsMixed. unfold glueMixedPath.
  rewrite eqTransAssoc, transSymCancelR2. now reflexivity.
Defined.

Definition keptGlueValues: MatchingValues (shiftDiagram X) :=
  fun i g => gluedValues (raiseIndex i) (keepToTop g).
Definition keptGluePaths: MatchingPaths (shiftDiagram X) keptGlueValues :=
  fun i j f g => gluedPaths (raiseIndex i) (raiseIndex j) (keepWord f) (keepToTop g)
    • f_equal (gluedValues (raiseIndex i)) (keepToTopComp f g).

Lemma keptGlueSquares (i j: Index n) (f: Word A (rank i) (rank j))
  (g: Word A (rank j) n):
  f_equal (restrict (shiftDiagram X) f) (mergeValuesKeep X b.1 y j g)
    • matchingPath b f g =
  keptGluePaths i j f g • mergeValuesKeep X b.1 y i (wcomp g f).
Proof.
  unfold keptGluePaths. rewrite gluedPathsKeep.
  rewrite eqTransAssoc.
  change (f_equal (restrict (shiftDiagram X) f) (mergeValuesKeep X b.1 y j g)
      • matchingPath b f g = glueKeepPath i j f g • keepCompositeValue f g).
  unfold glueKeepPath. rewrite eqTransAssoc, transSymCancelR2. now reflexivity.
Defined.

Definition keptGlueLaws: MatchingLaws (shiftDiagram X) keptGluePaths :=
  matchingLawsOfSquares (shiftDiagram X) keptGlueValues b.1 keptGluePaths b.2.1
    (mergeValuesKeep X b.1 y) keptGlueSquares b.2.2.

Lemma glueUnitSkip (i: Index (S n)) a (g: Word A (rank i) n):
  gluedPaths i i (wid (rank i)) (wskip a g) =
  restrictId X i (gluedValues i (wskip a g))
    • eq_sym (f_equal (gluedValues i) (wcompIdr (wskip a g))).
Proof.
  rewrite gluedPathsSkip.
  refine (pcompUnitRPt (diagramData X) (pathUnitR _ _ X.(pfStr))
    None i g (wcompIdr g) (y a) • _).
  apply f_equal. apply f_equal.
  refine (eq_sym (f_equal_compose (wskip a) (gluedValues i) (wcompIdr g)) • _).
  apply f_equal. now apply (wordSet (A := A) (rank i) (S n)).(UIP).
Defined.

Local Lemma glueUnitFromLoop (i: Index (S n)) (g: Word A (rank i) (S n))
  (f: Word A (rank i) (rank i)) (e: f = wid (rank i)) (h: wcomp g f = g)
  (H: gluedPaths i i f g • f_equal (gluedValues i) h =
    phomEq (diagramData X) (a := i) (b := i) e (gluedValues i g)
      • restrictId X i (gluedValues i g)):
  gluedPaths i i (wid (rank i)) g = restrictId X i (gluedValues i g)
    • eq_sym (f_equal (gluedValues i) (wcompIdr g)).
Proof.
  subst f.
  replace h with (wcompIdr g) in H
    by now apply (wordSet (A := A) (rank i) (S n)).(UIP).
  cbn [phomEq f_equal] in H. rewrite eq_trans_refl_l in H.
  apply (transCancelR _ _ (f_equal (gluedValues i) (wcompIdr g))).
  rewrite transSymCancelR2. now exact H.
Defined.

Lemma glueUnitKeep (i: Index n) (g: Word A (rank i) n):
  gluedPaths (raiseIndex i) (raiseIndex i) (wid (rank (raiseIndex i))) (keepToTop g) =
  restrictId X (raiseIndex i) (gluedValues (raiseIndex i) (keepToTop g))
    • eq_sym (f_equal (gluedValues (raiseIndex i)) (wcompIdr (keepToTop g))).
Proof.
  apply (glueUnitFromLoop (raiseIndex i) (keepToTop g) (keepWord (wid (rank i)))
    (keepWordId i) (keepToTopComp (wid (rank i)) g
      • f_equal (keepToTop (A := A) (i := i)) (wcompIdr g))).
  pose proof (keptGlueLaws.1 i g) as H.
  unfold keptGluePaths in H. rewrite shiftRestrictId in H.
  pose (D := f_equal (keptGlueValues i) (wcompIdr g)).
  assert (e: f_equal (gluedValues (raiseIndex i))
      (keepToTopComp (wid (rank i)) g • f_equal (keepToTop (A := A) (i := i)) (wcompIdr g)) =
    f_equal (gluedValues (raiseIndex i)) (keepToTopComp (wid (rank i)) g) • D).
  { rewrite eq_trans_map_distr. apply f_equal.
    now exact (f_equal_compose (keepToTop (A := A) (i := i)) (gluedValues (raiseIndex i)) (wcompIdr g)). }
  refine (f_equal (fun z => gluedPaths (raiseIndex i) (raiseIndex i)
    (keepWord (wid (rank i))) (keepToTop g) • z) e • _).
  refine (eq_sym (eqTransAssoc _ _ D) • f_equal (fun z => z • D) H • _).
  now apply transSymCancelR2.
Defined.

Definition gluedUnitLaw: MatchingUnit X gluedPaths :=
  topWordElim
    (fun i g => gluedPaths i i (wid (rank i)) g = restrictId X i (gluedValues i g)
      • eq_sym (f_equal (gluedValues i) (wcompIdr g)))
    glueUnitSkip glueUnitKeep.

Definition GlueComp (i j k: Index (S n))
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) (S n)): Type :=
  f_equal (restrict X f) (gluedPaths j k g h)
    • (gluedPaths i j f (wcomp h g)
      • f_equal (gluedValues i) (eq_sym (wcompAssoc h g f))) =
  restrictComp X f g (gluedValues k h) • gluedPaths i k (wcomp g f) h.

(** Composite words may be replaced by chosen normal forms before checking
    a matching composition law. Source-word equality is an h-proposition. *)
Lemma glueCompNormalized (i j k: Index (S n))
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) (S n))
  (fg: Word A (rank i) (rank k)) (hg: Word A (rank j) (S n))
  (out: Word A (rank i) (S n))
  (efg: wcomp g f = fg) (ehg: wcomp h g = hg)
  (el: wcomp hg f = out) (er: wcomp h fg = out)
  (H: f_equal (restrict X f)
      (gluedPaths j k g h • f_equal (gluedValues j) ehg)
    • (gluedPaths i j f hg • f_equal (gluedValues i) el) =
    (restrictComp X f g (gluedValues k h)
      • phomEq (diagramData X) (a := k) (b := i) efg (gluedValues k h))
    • (gluedPaths i k fg h • f_equal (gluedValues i) er)):
  GlueComp i j k f g h.
Proof.
  subst fg. subst hg. revert er H. destruct el. intros er H.
  replace er with (wcompAssoc h g f) in H
    by now apply (wordSet (A := A) (rank i) (S n)).(UIP).
  change (f_equal (restrict X f) (gluedPaths j k g h)
      • gluedPaths i j f (wcomp h g) =
    restrictComp X f g (gluedValues k h)
      • (gluedPaths i k (wcomp g f) h
        • f_equal (gluedValues i) (wcompAssoc h g f))) in H.
  unfold GlueComp.
  rewrite <- eqTransAssoc, H, eqTransAssoc, fEqualSym, transSymCancelR.
  now reflexivity.
Defined.

Lemma glueCompKeep (i j k: Index n)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) n):
  GlueComp (raiseIndex i) (raiseIndex j) (raiseIndex k)
    (keepWord f) (keepWord g) (keepToTop h).
Proof.
  apply (glueCompNormalized (raiseIndex i) (raiseIndex j) (raiseIndex k)
    (keepWord f) (keepWord g) (keepToTop h)
    (keepWord (wcomp g f)) (keepToTop (wcomp h g)) (keepToTop (wcomp h (wcomp g f)))
    (keepWordComp f g) (keepToTopComp g h)
    (keepToTopComp f (wcomp h g)
      • f_equal (keepToTop (A := A) (i := i)) (eq_sym (wcompAssoc h g f)))
    (keepToTopComp (wcomp g f) h)).
  pose proof (keptGlueLaws.2 i j k f g h) as H.
  unfold keptGluePaths, keptGlueValues in H. rewrite shiftRestrictComp in H.
  assert (e: f_equal (gluedValues (raiseIndex i))
      (keepToTopComp f (wcomp h g)
        • f_equal (keepToTop (A := A) (i := i)) (eq_sym (wcompAssoc h g f))) =
    f_equal (gluedValues (raiseIndex i)) (keepToTopComp f (wcomp h g))
      • f_equal (fun w => gluedValues (raiseIndex i) (keepToTop w))
          (eq_sym (wcompAssoc h g f))).
  { rewrite eq_trans_map_distr. apply f_equal.
    now exact (f_equal_compose (keepToTop (A := A) (i := i))
      (gluedValues (raiseIndex i)) (eq_sym (wcompAssoc h g f))). }
  rewrite e.
  rewrite <- (eqTransAssoc
    (gluedPaths (raiseIndex i) (raiseIndex j) (keepWord f) (keepToTop (wcomp h g)))
    (f_equal (gluedValues (raiseIndex i)) (keepToTopComp f (wcomp h g)))
    (f_equal (fun w => gluedValues (raiseIndex i) (keepToTop w))
      (eq_sym (wcompAssoc h g f)))).
  now exact H.
Defined.

Lemma glueCompSkip (i j k: Index (S n))
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  a (h: Word A (rank k) n):
  f_equal (restrict X f) (gluedPaths j k g (wskip a h))
    • (gluedPaths i j f (wcomp (wskip a h) g)
      • f_equal (gluedValues i) (eq_sym (wcompAssoc (wskip a h) g f))) =
  restrictComp X f g (gluedValues k (wskip a h))
    • gluedPaths i k (wcomp g f) (wskip a h).
Proof.
  change (wcomp (wskip a h) g) with (wskip a (wcomp h g)).
  rewrite 3 gluedPathsSkip.
  refine (_ • pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr))
    None k j i h g f (eq_sym (wcompAssoc h g f)) (y a)).
  apply f_equal. apply f_equal.
  refine (_ • f_equal_compose (wskip a) (gluedValues i) (eq_sym (wcompAssoc h g f))).
  apply f_equal. now apply (wordSet (A := A) (rank i) (S n)).(UIP).
Defined.

End Gluing.

(** Gluing recovers the prescribed mixed comparison paths. *)

Section Beta.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).
Context (b: MatchingObject (shiftDiagram X)) (y: A -> cells X None).
Context (q: forall a (i: Index n) (g: Word A (rank i) n),
  topFace X a i (matchingValue b i g) = restrict X (i := Some i) (j := None) g (y a)).

Local Lemma unitRightNormalized (i j: Index (S n))
  (f: Word A (rank i) (rank j)) (x: cells X j):
  restrictComp X (i := i) (j := i) (k := j) (wid (rank i)) f x
    • f_equal (fun w => restrict X (i := i) (j := j) w x) (wcompIdr f)
  = restrictId X i (restrict X f x).
Proof.
  refine (transCongR (pcompUnitRPt (diagramData X) (pathUnitR _ _ X.(pfStr))
    j i f (wcompIdr f) x) _ • _).
  unfold phomEq. now apply transSymCancelR2.
Defined.

Local Lemma unitLeftNormalized (i j: Index (S n))
  (f: Word A (rank i) (rank j)) (x: cells X j):
  restrictComp X (i := i) (j := j) (k := j) f (wid (rank j)) x
    • f_equal (fun w => restrict X (i := i) (j := j) w x) (wcompIdl f)
  = f_equal (restrict X (i := i) (j := j) f) (restrictId X j x).
Proof.
  refine (transCongR (pcompUnitLPt (diagramData X) (pathUnitL _ _ X.(pfStr))
    j i f (wcompIdl f) x) _ • _).
  unfold phomEq. now apply transSymCancelR2.
Defined.

Local Lemma skipValuePath (i: Index (S n)) a
  {g h: Word A (rank i) n} (e: g = h):
  f_equal (gluedValues X b y i) (f_equal (wskip a) e) =
    f_equal (fun w => restrict X (i := i) (j := None) w (y a)) e.
Proof. now destruct e. Defined.

Lemma mixedPathCoreIdentity (i: Index n) a (g: Word A (rank i) n):
  mixedPathCore X b y q i i a (wid (rank i)) g
    • f_equal (fun w => restrict X (i := Some i) (j := None) w (y a)) (wcompIdr g)
  = q a i g.
Proof.
  unfold mixedPathCore.
  replace (mixedWordFactor (i := i) (j := i) a (wid (rank i)))
    with (wcompIdr (topFaceWord i a))
    by now apply (wordSet (A := A) (rank i) (rank (raiseIndex i))).(UIP).
  unfold phomEq.
  rewrite unitRightNormalized.
  rewrite 2 eqTransAssoc, unitRightNormalized.
  refine (transCongL _ (homotopyNat
    (restrict X (i := Some i) (j := Some i) (wid (rank i)))
    (fun z => z) (restrictId X (Some i)) (q a i g)) • _).
  rewrite f_equal_id. now apply eq_trans_sym_cancel_l.
Defined.

Lemma gluedMixedComparisonBeta a (i: Index n) (g: Word A (rank i) n)
  (e: wcomp (keepToTop g) (topFaceWord i a) = wskip a g):
  gluedPaths X b y q (Some i) (raiseIndex i) (topFaceWord i a) (keepToTop g)
    • f_equal (gluedValues X b y (Some i)) e =
  f_equal (topFace X a i) (mergeValuesKeep X b.1 y i g) • q a i g.
Proof.
  replace e with
    (mixedToTopComp (i := i) (j := i) a (wid (rank i)) g • f_equal (wskip a) (wcompIdr g))
    by now apply (wordSet (A := A) (rank i) (S n)).(UIP).
  rewrite eq_trans_map_distr, <- eqTransAssoc.
  refine (transCongR (glueMixedNormalized X b y q i i a (wid (rank i)) g) _ • _).
  rewrite eqTransAssoc, skipValuePath, mixedPathCoreIdentity.
  now reflexivity.
Defined.

Lemma gluedSkippedComparisonBeta a (i: Index n) (g: Word A (rank i) n):
  gluedPaths X b y q (Some i) None g (wskip a (wid n))
    • f_equal (gluedValues X b y (Some i)) (skippedWord a g) =
  f_equal (restrict X (i := Some i) (j := None) g) (restrictId X None (y a)).
Proof.
  refine (transCongR (gluedPathsSkip X b y q (Some i) None g a (wid n)) _ • _).
  unfold glueSkipPath, skippedWord.
  refine (transCongL _ (skipValuePath (Some i) a (wcompIdl g)) • _).
  now exact (unitLeftNormalized (Some i) None g (y a)).
Defined.

End Beta.

(** Composition of mixed matching paths from their compatibility squares. *)

Local Lemma conjugateCancellation {T: Type} {a b c d: T}
  (p: a = b) (q: d = c) (r: c = b):
  (p • (eq_sym r • eq_sym q)) • (q • r) = p.
Proof. now destruct p, q, r. Defined.


Local Lemma coneCompAlgebra {T: Type} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11: T}
  (r: x0 = x1) (si1: x1 = x2) (si0: x0 = x3) (t: x3 = x2)
  (a1: x2 = x4) (ni: x3 = x5) (a0: x5 = x6) (c0: x6 = x4)
  (c1: x4 = x7) (ea: x7 = x8) (d0: x6 = x9) (d1: x9 = x8)
  (d2: x5 = x10) (a2: x10 = x9) (c2: x0 = x11) (si2: x11 = x10)
  (Hn: r • si1 = si0 • t)
  (Hq: t • a1 = ni • (a0 • c0))
  (Ha: c0 • (c1 • ea) = d0 • d1)
  (Hp: a0 • d0 = d2 • a2)
  (Ht: si0 • (ni • d2) = c2 • si2):
  r • ((si1 • (a1 • c1)) • ea) = c2 • (si2 • (a2 • d1)).
Proof.
  destruct r, si1, si0, a1, ni, a0, c1, ea, d0, d2, c2.
  cbn in Hn, Hq, Ha, Hp, Ht |- *.
  rewrite eq_trans_refl_l in Hn. rewrite <- Hn in Hq.
  rewrite 2 eq_trans_refl_l in Hq. rewrite <- Hq in Ha.
  rewrite eq_trans_refl_l in Ha, Hp, Ht.
  rewrite <- Ha, <- Hp, <- Ht. now reflexivity.
Defined.

Section Kernel.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).

Definition mixedFactor {i j: Index n} a
  (f: Word A (rank i) (rank j)) (x: cells X (raiseIndex j)) :=
  restrictComp X (i := Some i) (j := Some j) (k := raiseIndex j)
    f (topFaceWord j a) x
    • phomEq (diagramData X) (a := raiseIndex j) (b := Some i)
      (mixedWordFactor a f) x.

Lemma mixedTriangle (i j k: Index n) a (f: Word A (rank i) (rank j))
  (g: Word A (rank j) (rank k))
  (e: wcomp (keepWord g) (mixedWord a f) = mixedWord a (wcomp g f))
  (x: cells X (raiseIndex k)):
  eq_sym (mixedFactor a f (restrict (shiftDiagram X) g x))
    • (f_equal (restrict X (i := Some i) (j := Some j) f)
        (eq_sym (topFaceNaturality X a g x))
      • restrictComp X (i := Some i) (j := Some j) (k := Some k)
          f g (topFace X a k x)) =
  (restrictComp X (i := Some i) (j := raiseIndex j) (k := raiseIndex k)
      (mixedWord a f) (keepWord g) x
    • phomEq (diagramData X) (a := raiseIndex k) (b := Some i) e x)
    • eq_sym (mixedFactor a (wcomp g f) x).
Proof.
  rewrite fEqualSym.
  apply eq_sym, reversePasting.
  pose (out := eq_sym (wcompAssoc (topFaceWord k a) g f)
    • mixedWordFactor a (wcomp g f)).
  pose proof (pcompPaste (diagramData X) (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr)))
    (a := raiseIndex k) (b := raiseIndex j) (c := Some j) (d := Some i)
    (keepWord g) (topFaceWord j a) f (topFaceWordNatural g a)
    (mixedWordFactor a f) out e x) as P.
  pose proof (pcompPaste (diagramData X) (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr)))
    (a := raiseIndex k) (b := Some k) (c := Some j) (d := Some i)
    (topFaceWord k a) g f eq_refl eq_refl out
    (mixedWordFactor a (wcomp g f)) x) as Q.
  cbn [phomEq f_equal] in Q.
  rewrite 2 eq_trans_refl_r in Q.
  unfold mixedFactor.
  change (restrict (shiftDiagram X) g x) with
    (restrict X (i := raiseIndex j) (j := raiseIndex k) (keepWord g) x).
  refine (transCongL _ (eq_sym P) • _).
  rewrite <- eqTransAssoc, <- eq_trans_map_distr.
  assert (E: topFaceNaturality X a g x
      • (restrictComp X (i := Some j) (j := raiseIndex j) (k := raiseIndex k)
          (topFaceWord j a) (keepWord g) x
        • phomEq (diagramData X) (a := raiseIndex k) (b := Some j)
          (topFaceWordNatural g a) x) =
    restrictComp X (i := Some j) (j := Some k) (k := raiseIndex k)
      g (topFaceWord k a) x).
  { unfold topFaceNaturality, phomEq. rewrite fEqualSym.
    now apply conjugateCancellation. }
  refine (transCongR (f_equal
    (fun t => f_equal (restrict X (i := Some i) (j := Some j) f) t) E) _ • _).
  now exact Q.
Defined.

Context (b: MatchingObject (shiftDiagram X)) (y: A -> cells X None)
  (q: forall a (i: Index n) (g: Word A (rank i) n),
    topFace X a i (matchingValue b i g) = restrict X (i := Some i) (j := None) g (y a)).

Lemma finalMixedKernel (i j k: Index n) a (f: Word A (rank i) (rank j))
  (g: Word A (rank j) (rank k)) (h: Word A (rank k) n)
  (e: wcomp (keepWord g) (mixedWord a f) = mixedWord a (wcomp g f))
  (Hq: f_equal (restrict X (i := Some j) (j := Some k) g) (q a k h)
    • restrictComp X (i := Some j) (j := Some k) (k := None) g h (y a) =
    (topFaceNaturality X a g (matchingValue b k h)
      • f_equal (topFace X a j) (matchingPath b g h))
    • q a j (wcomp h g)):
  f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
      (matchingPath b g h)
    • (mixedPathCore X b y q i j a f (wcomp h g)
      • phomEq (diagramData X) (a := None) (b := Some i)
        (eq_sym (wcompAssoc h g f)) (y a)) =
  (restrictComp X (i := Some i) (j := raiseIndex j) (k := raiseIndex k)
      (mixedWord a f) (keepWord g) (matchingValue b k h)
    • phomEq (diagramData X) (a := raiseIndex k) (b := Some i) e (matchingValue b k h))
    • mixedPathCore X b y q i k a (wcomp g f) h.
Proof.
  unfold mixedPathCore. fold (@mixedFactor i j a f). fold (@mixedFactor i k a (wcomp g f)).
  eapply coneCompAlgebra with
    (si0 := eq_sym (mixedFactor a f (restrict (shiftDiagram X) g (matchingValue b k h))))
    (t := f_equal (restrict X (i := Some i) (j := Some j) f)
      (f_equal (topFace X a j) (matchingPath b g h)))
    (ni := f_equal (restrict X (i := Some i) (j := Some j) f)
      (eq_sym (topFaceNaturality X a g (matchingValue b k h))))
    (a0 := f_equal (restrict X (i := Some i) (j := Some j) f)
      (f_equal (restrict X (i := Some j) (j := Some k) g) (q a k h)))
    (c0 := f_equal (restrict X (i := Some i) (j := Some j) f)
      (restrictComp X (i := Some j) (j := Some k) (k := None) g h (y a)))
    (d0 := restrictComp X (i := Some i) (j := Some j) (k := Some k) f g
      (restrict X (i := Some k) (j := None) h (y a)))
    (d2 := restrictComp X (i := Some i) (j := Some j) (k := Some k) f g
      (topFace X a k (matchingValue b k h))).
  - rewrite f_equal_compose.
    now exact (homotopyNat _ _ (fun z => eq_sym (mixedFactor a f z)) (matchingPath b g h)).
  - rewrite <- 3 eq_trans_map_distr. apply f_equal.
    apply (transCancelL (topFaceNaturality X a g (matchingValue b k h))).
    rewrite transSymCancelL, <- eqTransAssoc. now symmetry.
  - now exact (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr))
      None (Some k) (Some j) (Some i) h g f (eq_sym (wcompAssoc h g f)) (y a)).
  - now exact (pcompNatPt (diagramData X) (a := Some k) (b := Some j) (c := Some i)
      g f (q a k h)).
  - now exact (mixedTriangle i j k a f g e (matchingValue b k h)).
Defined.
End Kernel.

(** Matching composition with an arrow between retained indices followed by
    a mixed word. *)

Local Lemma inverseTriangle {T: Type} {a b c d: T}
  (p: a = b) (q: b = c) (r: a = d) (s: d = c)
  (h: p • q = r • s): eq_sym p • r = q • eq_sym s.
Proof.
  apply (transCancelL p). rewrite transSymCancelL.
  rewrite <- eqTransAssoc, h. now symmetry; apply transSymCancelR.
Defined.

Local Lemma pathGrid {T: Type} {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3: T}
  (e: a0 = a1) (c: a1 = a2) (d: a2 = a3) (p: a3 = a4) (r: a4 = a5)
  (s: a0 = b0) (e': b0 = b1) (k: b1 = b2) (q: b2 = b3)
  (s': a1 = b1) (p0: a2 = b2) (p2: a3 = b3) (p': b3 = a5)
  (he: e • s' = s • e') (hc: c • p0 = s' • k)
  (hq: d • p2 = p0 • q) (hp: p • r = p2 • p'):
  (e • (c • (d • p))) • r = s • (e' • (k • (q • p'))).
Proof.
  destruct e, c, d, p, r, s, e', k, q.
  cbn in he, hc, hq, hp |- *.
  rewrite eq_trans_refl_l in he. subst s'.
  rewrite eq_trans_refl_l in hc. subst p0.
  rewrite eq_trans_refl_l in hq. subst p2.
  rewrite eq_trans_refl_l in hp. rewrite <- hp. now reflexivity.
Defined.

Section Gluing.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).
Context (b: MatchingObject (shiftDiagram X)) (y: A -> cells X None).
Context (q: forall a (i: Index n) (g: Word A (rank i) n),
  topFace X a i (matchingValue b i g) = restrict X (i := Some i) (j := None) g (y a)).

Lemma glueCompMixedRetained (i j k: Index n)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) n) (a: A):
  GlueComp X b y q (Some i) (Some j) (raiseIndex k) f (mixedWord a g) (keepToTop h).
Proof.
  apply (glueCompNormalized X b y q (Some i) (Some j) (raiseIndex k)
    f (mixedWord a g) (keepToTop h)
    (mixedWord a (wcomp g f)) (wskip a (wcomp h g)) (wskip a (wcomp h (wcomp g f)))
    (mixedWordCompRetained a f g) (mixedToTopComp a g h)
    (f_equal (wskip a) (eq_sym (wcompAssoc h g f)))
    (mixedToTopComp a (wcomp g f) h)).
  rewrite 2 glueMixedNormalized.
  refine (transCongL _ (transCongR
    (gluedPathsSkip X b y q (Some i) (Some j) f a (wcomp h g)) _) • _).
  unfold glueSkipPath.
  refine (transCongL _ (transCongL _
    (f_equal_compose (wskip a) (gluedValues X b y (Some i))
      (eq_sym (wcompAssoc h g f)))) • _).
  unfold mixedPathCore.
  rewrite 3 eq_trans_map_distr.
  eapply pathGrid with
    (s' := restrictComp X (i := Some i) (j := Some j) (k := raiseIndex k)
      f (mixedWord a g) (matchingValue b k h)
      • phomEq (diagramData X) (a := raiseIndex k) (b := Some i)
          (mixedWordCompRetained a f g) (matchingValue b k h))
    (p0 := restrictComp X (i := Some i) (j := Some j) (k := Some k)
      f g (topFace X a k (matchingValue b k h)))
    (p2 := restrictComp X (i := Some i) (j := Some j) (k := Some k)
      f g (restrict X (i := Some k) (j := None) h (y a))).
  - rewrite f_equal_compose.
    now exact (homotopyNat
      (fun z => restrict X (i := Some i) (j := Some j) f
        (restrict X (i := Some j) (j := raiseIndex k) (mixedWord a g) z))
      (restrict X (i := Some i) (j := raiseIndex k) (mixedWord a (wcomp g f)))
      (fun z => restrictComp X (i := Some i) (j := Some j) (k := raiseIndex k)
        f (mixedWord a g) z
        • phomEq (diagramData X) (a := raiseIndex k) (b := Some i)
          (mixedWordCompRetained a f g) z)
      (mergeValuesKeep X b.1 y k h)).
  - rewrite fEqualSym. apply inverseTriangle.
    now exact (pcompPaste (diagramData X)
      (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr)))
      (a := raiseIndex k) (b := Some k) (c := Some j) (d := Some i)
      (topFaceWord k a) g f (mixedWordFactor a g) eq_refl
      (mixedWordCompRetained a f g) (mixedWordFactor a (wcomp g f)) (matchingValue b k h)).
  - now exact (pcompNatPt (diagramData X) (a := Some k) (b := Some j) (c := Some i)
      g f (q a k h)).
  - now exact (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr))
      None (Some k) (Some j) (Some i) h g f (eq_sym (wcompAssoc h g f)) (y a)).
Defined.

End Gluing.

(** The remaining mixed pasting law for coherent matching gluing. *)

Local Lemma pasteSquares {T: Type} {x0 x1 x2 x3 x4 u v w: T}
  (a: x0 = x1) (b: x1 = x2) (c: x2 = x3) (d: x3 = x4)
  (e: x0 = u) (f: u = x2) (g: u = v) (h: v = x4)
  (i: x0 = w) (j: w = v)
  (p: a • b = e • f) (q: f • (c • d) = g • h) (r: e • g = i • j):
  a • (b • (c • d)) = i • (j • h).
Proof.
  rewrite <- (eqTransAssoc a b (c • d)), p, eqTransAssoc, q.
  rewrite <- eqTransAssoc, r. now apply eqTransAssoc.
Defined.

Section Gluing.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).
Context (b: MatchingObject (shiftDiagram X)) (y: A -> cells X None).
Context (q: forall a (i: Index n) (g: Word A (rank i) n),
  topFace X a i (matchingValue b i g) = restrict X (i := Some i) (j := None) g (y a)).

Lemma glueCompMixedLast (i j k: Index n) a
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) n)
  (K: f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
      (matchingPath b g h)
    • (mixedPathCore X b y q i j a f (wcomp h g)
      • phomEq (diagramData X) (a := None) (b := Some i)
        (eq_sym (wcompAssoc h g f)) (y a)) =
    (restrictComp X (i := Some i) (j := raiseIndex j) (k := raiseIndex k)
      (mixedWord a f) (keepWord g) (matchingValue b k h)
      • phomEq (diagramData X) (a := raiseIndex k) (b := Some i)
        (mixedWordComp a f g) (matchingValue b k h))
    • mixedPathCore X b y q i k a (wcomp g f) h):
  GlueComp X b y q (Some i) (raiseIndex j) (raiseIndex k)
    (mixedWord a f) (keepWord g) (keepToTop h).
Proof.
  apply (glueCompNormalized X b y q (Some i) (raiseIndex j) (raiseIndex k)
    (mixedWord a f) (keepWord g) (keepToTop h)
    (mixedWord a (wcomp g f)) (keepToTop (wcomp h g)) (wskip a (wcomp h (wcomp g f)))
    (mixedWordComp a f g) (keepToTopComp g h)
    (mixedToTopComp a f (wcomp h g) • f_equal (wskip a) (eq_sym (wcompAssoc h g f)))
    (mixedToTopComp a (wcomp g f) h)).
  rewrite (eq_trans_map_distr (gluedValues X b y (Some i))
    (mixedToTopComp a f (wcomp h g))
    (f_equal (wskip a) (eq_sym (wcompAssoc h g f)))).
  refine (transCongL _ (transCongL _ (transCongL _
    (f_equal_compose (wskip a) (gluedValues X b y (Some i))
      (eq_sym (wcompAssoc h g f))))) • _).
  refine (transCongL _ (eq_sym (eqTransAssoc
    (gluedPaths X b y q (Some i) (raiseIndex j) (mixedWord a f) (keepToTop (wcomp h g)))
    (f_equal (gluedValues X b y (Some i)) (mixedToTopComp a f (wcomp h g)))
    (phomEq (diagramData X) (a := None) (b := Some i) (eq_sym (wcompAssoc h g f)) (y a)))) • _).
  rewrite 2 glueMixedNormalized.
  refine (transCongL _ (eqTransAssoc
    (f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
      (mergeValuesKeep X b.1 y j (wcomp h g)))
    (mixedPathCore X b y q i j a f (wcomp h g))
    (phomEq (diagramData X) (a := None) (b := Some i) (eq_sym (wcompAssoc h g f)) (y a))) • _).
  eapply pasteSquares with
    (e := f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
      (f_equal (restrict X (i := raiseIndex j) (j := raiseIndex k) (keepWord g))
        (mergeValuesKeep X b.1 y k h)))
    (f := f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
      (matchingPath b g h)).
  - rewrite <- 2 eq_trans_map_distr.
    now exact (f_equal
      (fun p => f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f)) p)
      (eq_sym (keptGlueSquares X b y q j k g h))).
  - now exact K.
  - rewrite f_equal_compose.
    now exact (homotopyNat
      (fun z => restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f)
        (restrict X (i := raiseIndex j) (j := raiseIndex k) (keepWord g) z))
      (restrict X (i := Some i) (j := raiseIndex k) (mixedWord a (wcomp g f)))
      (fun z => restrictComp X (i := Some i) (j := raiseIndex j) (k := raiseIndex k)
        (mixedWord a f) (keepWord g) z
        • phomEq (diagramData X) (a := raiseIndex k) (b := Some i) (mixedWordComp a f g) z)
      (mergeValuesKeep X b.1 y k h)).
Defined.

Definition BranchSquares: Type := forall a (i j: Index n)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n),
  f_equal (restrict X (i := Some i) (j := Some j) f) (q a j g)
    • restrictComp X (i := Some i) (j := Some j) (k := None) f g (y a) =
  (topFaceNaturality X a f (matchingValue b j g)
    • f_equal (topFace X a i) (matchingPath b f g)) • q a i (wcomp g f).

Definition gluedCompLaw (s: BranchSquares): MatchingComp X (gluedPaths X b y q).
Proof.
  intros i j k f g h. revert i j f g.
  refine (topWordElim
    (fun k h => forall i j f g, GlueComp X b y q i j k f g h)
    (fun k a h i j f g => glueCompSkip X b y q i j k f g a h) _ k h).
  clear k h. intros k h i j f g. revert i f.
  refine (raisedWordElim k
    (fun j g => forall i f, GlueComp X b y q i j (raiseIndex k) f g (keepToTop h)) _ _ j g).
  - clear j g. intros j a g [i|] f.
    + now exact (glueCompMixedRetained X b y q i j k f g h a).
    + exfalso. now exact (noWordAbove (rankLt j) f).
  - clear j g. intros j g i f.
    refine (raisedWordElim j
      (fun i f => GlueComp X b y q i (raiseIndex j) (raiseIndex k)
        f (keepWord g) (keepToTop h)) _ _ i f).
    + clear i f. intros i a f. apply glueCompMixedLast.
      now exact (finalMixedKernel X b y q i j k a f g h (mixedWordComp a f g) (s a j k g h)).
    + clear i f. intros i f. now exact (glueCompKeep X b y q i j k f g h).
Defined.

Definition glueFromComparison (s: BranchSquares): MatchingObject X :=
  (gluedValues X b y; (gluedPaths X b y q; (gluedUnitLaw X b y q; gluedCompLaw s))).
End Gluing.

Section BoundaryPaths.
Context {A: HSet} {n: nat} (X: Diagram A (S n))
  (b: MatchingObject (shiftDiagram X)) (y: A -> cells X None)
  (p: forall a, topFaceMatching X a b = matchingMap X (y a)).
Definition gluingComparison a (i: Index n) (g: Word A (rank i) n):
  topFace X a i (matchingValue b i g) = restrict X (i := Some i) (j := None) g (y a) :=
  f_equal (fun z => matchingValue z i g) (p a).

Lemma gluingSquares: BranchSquares X b y gluingComparison.
Proof.
  intros a i j f g.
  pose proof (matchingPathSquares (baseDiagram X) (p a) i j f g) as H.
  change (f_equal (restrict (baseDiagram X) f) (gluingComparison a j g)
      • matchingPath (matchingMap X (y a)) f g =
    matchingPath (topFaceMatching X a b) f g • gluingComparison a i (wcomp g f)) in H.
  rewrite topFaceMatchingPath in H. now exact H.
Defined.

Definition glueMatching: MatchingObject X :=
  glueFromComparison X b y gluingComparison gluingSquares.

End BoundaryPaths.
