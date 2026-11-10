(** The split of a matching object into the matching object of its kept faces
    and its top faces, the inverse gluing, the resulting equivalence, and its
    naturality in maps of diagrams. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation RewLemmas
  FinitePrefix HomotopyPullback.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift Pullback
  ShiftedPrefix MatchingGlue.

Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations FinitePrefix.

(** Decomposing a coherent boundary along its last coordinate. *)

Lemma keepTopFaceWord {A: HSet} {n} {i: Index n}
  (g: Word A (rank i) n) (a: A):
  wcomp (keepToTop g) (topFaceWord i a) = wskip a g.
Proof.
  unfold keepToTop, topFaceWord. rewrite castWordComp.
  cbn [castWord]. now rewrite wcomp_keep_skip, wcompIdr.
Defined.

Definition attachmentEq {I W T B: Type} (r: I -> W -> B) (d: T -> B) :=
  @HomotopyPullback.attachmentEq I W T B r d.

Definition attachmentEqBase {I W T B: Type} (r: I -> W -> B) (d: T -> B) :=
  @HomotopyPullback.attachmentEqBase I W T B r d.

Definition attachmentEqTop {I W T B: Type} (r: I -> W -> B) (d: T -> B) :=
  @HomotopyPullback.attachmentEqTop I W T B r d.

Section MixedBranch.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).

Local Lemma matchingPathNaturalLeft (m: MatchingObject X) {i j}
  {f f': Word A (rank i) (rank j)} (e: f = f') (g: Word A (rank j) (S n)):
  f_equal (fun u => restrict X u (matchingValue m j g)) e • matchingPath m f' g
  = matchingPath m f g
    • f_equal (matchingValue m i) (f_equal (fun u => wcomp g u) e).
Proof. destruct e. now exact (eq_trans_refl_l _). Defined.

Local Lemma matchingCompFlat (m: MatchingObject X) {i j k}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) (S n)):
  f_equal (restrict X f) (matchingPath m g h) • matchingPath m f (wcomp h g)
  = restrictComp X f g (matchingValue m k h)
    • (matchingPath m (wcomp g f) h
      • f_equal (matchingValue m i) (wcompAssoc h g f)).
Proof.
  apply (transCancelR _ _ (f_equal (matchingValue m i) (eq_sym (wcompAssoc h g f)))).
  rewrite eqTransAssoc, matchingComp, fEqualSym.
  rewrite <- eqTransAssoc, transSymCancelR.
  now reflexivity.
Defined.

Local Lemma matchingCompTransport (m: MatchingObject X) {i j k}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) (S n)) {h': Word A (rank j) (S n)}
  {out: Word A (rank i) (S n)} (e: wcomp h g = h') (e': wcomp h' f = out):
  f_equal (restrict X f)
    (matchingPath m g h • f_equal (matchingValue m j) e)
    • (matchingPath m f h' • f_equal (matchingValue m i) e')
  = restrictComp X f g (matchingValue m k h)
    • (matchingPath m (wcomp g f) h
      • f_equal (matchingValue m i)
          (wcompAssoc h g f • (f_equal (fun u => wcomp u f) e • e'))).
Proof.
  rewrite eq_trans_map_distr, eqTransAssoc.
  rewrite <- (eqTransAssoc _ (matchingPath m f h') _).
  refine (transCongL _ (transCongR (matchingPathNatural X m f e) _) • _).
  rewrite <- 2 eqTransAssoc.
  refine (transCongR (transCongR (matchingCompFlat m f g h) _) _ • _).
  rewrite 3 eqTransAssoc, <- 2 eq_trans_map_distr.
  now reflexivity.
Defined.

Local Lemma matchingFactorPath (m: MatchingObject X) {i j k}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) (S n)) {u: Word A (rank i) (rank k)}
  {h': Word A (rank j) (S n)} {out: Word A (rank i) (S n)}
  (factor: wcomp g f = u) (tail: wcomp h g = h')
  (endLeft: wcomp h' f = out) (endRight: wcomp h u = out):
  (restrictComp X f g (matchingValue m k h)
    • phomEq (diagramData X) factor (matchingValue m k h))
    • (matchingPath m u h • f_equal (matchingValue m i) endRight)
  = f_equal (restrict X f)
      (matchingPath m g h • f_equal (matchingValue m j) tail)
    • (matchingPath m f h' • f_equal (matchingValue m i) endLeft).
Proof.
  refine (_ • eq_sym (matchingCompTransport m f g h tail endLeft)).
  rewrite eqTransAssoc, <- (eqTransAssoc _ (matchingPath m u h) _).
  unfold phomEq.
  refine (transCongL _ (transCongR (matchingPathNaturalLeft m factor h) _) • _).
  rewrite eqTransAssoc, <- eq_trans_map_distr.
  apply transCongL. apply transCongL. apply f_equal.
  now apply (wordSet (A := A) (rank i) (S n)).(UIP).
Defined.

Definition mixedComparisonValue (m: MatchingObject X) (a: A)
  (i: Index n) (g: Word A (rank i) n):
  topFace X a i (matchingValue m (raiseIndex i) (keepToTop g))
  = matchingValue (skippedMatching X m a) i g :=
  matchingPath m (i := Some i) (j := raiseIndex i)
    (topFaceWord i a) (keepToTop g)
  • f_equal (matchingValue m (Some i)) (keepTopFaceWord g a).

Definition keptComparisonPath (m: MatchingObject X) {i j: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  restrict (shiftDiagram X) f
    (matchingValue m (raiseIndex j) (keepToTop g))
  = matchingValue m (raiseIndex i) (keepToTop (wcomp g f)) :=
  matchingPath m (keepWord f) (keepToTop g)
  • f_equal (matchingValue m (raiseIndex i)) (keepToTopComp f g).

Lemma mixedComparisonSquares (m: MatchingObject X) (a: A)
  (i j: Index n) (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  f_equal (restrict (baseDiagram X) f) (mixedComparisonValue m a j g)
    • matchingPath (skippedMatching X m a) f g
  = (topFaceNaturality X a f (matchingValue m (raiseIndex j) (keepToTop g))
      • f_equal (topFace X a i) (keptComparisonPath m f g))
    • mixedComparisonValue m a i (wcomp g f).
Proof.
  unfold mixedComparisonValue, keptComparisonPath, topFaceNaturality.
  change (restrict (baseDiagram X) f) with
    (restrict X (i := Some i) (j := Some j) f).
  change (matchingPath (skippedMatching X m a) f g) with
    (matchingPath m (i := Some i) (j := Some j) f (wskip a g)).
  refine (matchingCompTransport m (i := Some i) (j := Some j)
    (k := raiseIndex j) f (topFaceWord j a) (keepToTop g)
    (keepTopFaceWord g a) eq_refl • _).
  symmetry. rewrite eqTransAssoc.
  refine (transCongL _ (matchingCompTransport m (i := Some i)
    (j := raiseIndex i) (k := raiseIndex j) (topFaceWord i a) (keepWord f)
    (keepToTop g) (keepToTopComp f g) (keepTopFaceWord (wcomp g f) a)) • _).
  rewrite eqTransAssoc.
  apply transCongL.
  rewrite transCancelMid2, <- eqTransAssoc.
  unfold phomEq.
  refine (transCongR (matchingPathNaturalLeft m (i := Some i) (j := raiseIndex j)
    (eq_sym (topFaceWordNatural f a)) (keepToTop g)) _ • _).
  rewrite eqTransAssoc, <- eq_trans_map_distr.
  apply transCongL. apply f_equal.
  now apply (wordSet (A := A) (rank i) (S n)).(UIP).
Defined.

Definition mixedComparison (m: MatchingObject X) (a: A):
  topFaceMatching X a (keepMatching X m) = skippedMatching X m a.
Proof.
  refine (matchingHomotopy (baseDiagram X)
    (b := topFaceMatching X a (keepMatching X m)) (c := skippedMatching X m a)
    (mixedComparisonValue m a) _).
  intros i j f g.
  rewrite topFaceMatchingPath, keepMatchingPath.
  now exact (mixedComparisonSquares m a i j f g).
Defined.

Lemma mixedComparisonValueBeta (m: MatchingObject X) a i g:
  f_equal (fun z => matchingValue z i g) (mixedComparison m a) =
    mixedComparisonValue m a i g.
Proof. now apply matchingHomotopyValue. Defined.

Definition SplitMatching: HGpd :=
  gsigT (A := MatchingObject (shiftDiagram X)) (fun b =>
    gforall a: A, gsigT (A := cells X None) (fun y =>
      hgpdOfHSet (hpaths (topFaceMatching X a b) (matchingMap X y)))).

Definition splitMatching (m: MatchingObject X): SplitMatching :=
  (keepMatching X m; fun a =>
    (skippedTop X m a; mixedComparison m a • eq_sym (skippedBoundary X m a))).

Lemma splitMatchingPathValue (m: MatchingObject X) a i g:
  f_equal (fun z => matchingValue z i g) ((splitMatching m).2 a).2 =
    mixedComparisonValue m a i g • eq_sym (skippedValueComparison X m a (Some i) g).
Proof.
  change (f_equal (fun z => matchingValue z i g)
      (mixedComparison m a • eq_sym (skippedBoundary X m a)) =
      mixedComparisonValue m a i g • eq_sym (skippedValueComparison X m a (Some i) g)).
  rewrite eq_trans_map_distr, fEqualSym, mixedComparisonValueBeta, skippedBoundaryValue.
  now reflexivity.
Defined.

Local Definition normalizedValues (m: MatchingObject X): MatchingValues X :=
  mergeValues X (keepMatching X m).1 (skippedTop X m).

Local Definition normalizationComparison (m: MatchingObject X):
  forall (i: Index (S n)) (f: Word A (rank i) (S n)),
    normalizedValues m i f = matchingValue m i f :=
  topWordElim
    (fun i f => normalizedValues m i f = matchingValue m i f)
    (fun i a f => skippedValueComparison X m a i f)
    (fun i f => mergeValuesKeep X (keepMatching X m).1 (skippedTop X m) i f).

Local Lemma normalizationComparisonSkip (m: MatchingObject X) i a f:
  normalizationComparison m i (wskip a f) = skippedValueComparison X m a i f.
Proof. unfold normalizationComparison. now exact (topWordElimSkip (A := A) (n := n) _ _ _ i a f). Defined.

Local Lemma normalizationComparisonKeep (m: MatchingObject X) i f:
  normalizationComparison m (raiseIndex i) (keepToTop f) =
    mergeValuesKeep X (keepMatching X m).1 (skippedTop X m) i f.
Proof. unfold normalizationComparison. now exact (topWordElimKeep (A := A) (n := n) _ _ _ i f). Defined.

Local Lemma cancelCompositeSuffix {T: Type} {a b c d: T}
  (p: a = b) (e: b = c) (h: d = b):
  ((p • e) • eq_sym (h • e)) • h = p.
Proof. now destruct h, e. Defined.

Local Lemma normalizationKeepSquare (m: MatchingObject X) {i j: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  f_equal (restrict X (i := raiseIndex i) (j := raiseIndex j) (keepWord f))
      (normalizationComparison m (raiseIndex j) (keepToTop g))
    • matchingPath m (keepWord f) (keepToTop g)
  = (f_equal (restrict X (i := raiseIndex i) (j := raiseIndex j) (keepWord f))
       (normalizationComparison m (raiseIndex j) (keepToTop g))
      • (matchingPath (keepMatching X m) f g
        • eq_sym (f_equal (normalizedValues m (raiseIndex i)) (keepToTopComp f g)
          • normalizationComparison m (raiseIndex i) (keepToTop (wcomp g f)))))
    • normalizationComparison m (raiseIndex i) (wcomp (keepToTop g) (keepWord f)).
Proof.
  rewrite keepMatchingPath.
  rewrite (homotopyNat (normalizedValues m (raiseIndex i)) (matchingValue m (raiseIndex i))
    (normalizationComparison m (raiseIndex i)) (keepToTopComp f g)).
  rewrite eqTransAssoc.
  apply transCongL. now symmetry; apply cancelCompositeSuffix.
Defined.

Local Lemma mixedRetractionAlgebra {T: Type} {x0 x1 x2 x3 x4 x5 x6 x7: T}
  (c: x0 = x1) (p: x1 = x2) (e: x2 = x3) (u: x0 = x4)
  (s: x5 = x4) (d: x5 = x6) (hs: x6 = x3) (v: x7 = x6)
  (hc: x7 = x2) (ps: x4 = x3)
  (factor: c • (p • e) = u • ps) (skip: s • ps = d • hs)
  (natural: v • hs = hc • e):
  (eq_sym c • ((u • eq_sym s) • (d • eq_sym v))) • hc = p.
Proof.
  destruct c, u, s, d, v, hc, e.
  cbn in factor, skip, natural |- *.
  rewrite 2 eq_trans_refl_l in factor, skip.
  rewrite eq_trans_refl_l in natural.
  now exact (eq_sym (factor • (skip • natural))).
Defined.

Local Definition normalizationAttachment (m: MatchingObject X) a i g :=
  mixedComparisonValue m a i g • eq_sym (skippedValueComparison X m a (Some i) g).

Local Lemma normalizationMixedSquare (m: MatchingObject X) (i j: Index n) a
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
      (normalizationComparison m (raiseIndex j) (keepToTop g))
    • matchingPath m (mixedWord a f) (keepToTop g)
  = (f_equal (restrict X (i := Some i) (j := raiseIndex j) (mixedWord a f))
       (normalizationComparison m (raiseIndex j) (keepToTop g))
     • (eq_sym (restrictComp X (i := Some i) (j := Some j) (k := raiseIndex j)
         f (topFaceWord j a) (matchingValue m (raiseIndex j) (keepToTop g))
         • phomEq (diagramData X) (a := raiseIndex j) (b := Some i)
           (mixedWordFactor a f) (matchingValue m (raiseIndex j) (keepToTop g)))
       • (f_equal (restrict X (i := Some i) (j := Some j) f)
           (normalizationAttachment m a j g)
         • (restrictComp X (i := Some i) (j := Some j) (k := None)
             f g (skippedTop X m a)
           • eq_sym (f_equal (normalizedValues m (Some i)) (mixedToTopComp a f g))))))
    • normalizationComparison m (Some i) (wcomp (keepToTop g) (mixedWord a f)).
Proof.
  rewrite eqTransAssoc. apply transCongL. symmetry.
  unfold normalizationAttachment. rewrite eq_trans_map_distr, fEqualSym.
  eapply mixedRetractionAlgebra with
    (hs := normalizationComparison m (Some i) (wskip a (wcomp g f))).
  - now exact (matchingFactorPath m (i := Some i) (j := Some j)
      (k := raiseIndex j) f (topFaceWord j a) (keepToTop g)
      (mixedWordFactor a f) (keepTopFaceWord g a) eq_refl (mixedToTopComp a f g)).
  - rewrite normalizationComparisonSkip.
    now exact (skippedValueSquares X m a (Some i) (Some j) f g).
  - now exact (homotopyNat (normalizedValues m (Some i)) (matchingValue m (Some i))
      (normalizationComparison m (Some i)) (mixedToTopComp a f g)).
Defined.

Local Definition normalizedPaths (m: MatchingObject X): MatchingPaths X (normalizedValues m) :=
  gluedPaths X (keepMatching X m) (skippedTop X m)
    (normalizationAttachment m).

Local Lemma normalizationSquares (m: MatchingObject X):
  forall i j f g,
    f_equal (restrict X (i := i) (j := j) f) (normalizationComparison m j g)
      • matchingPath m f g =
    normalizedPaths m i j f g • normalizationComparison m i (wcomp g f).
Proof.
  refine (composableWordsElim (A := A) (n := n) _ _ _ _).
  - intros i j f a g.
    unfold normalizedPaths. rewrite gluedPathsSkip.
    change (wcomp (wskip a g) f) with (wskip a (wcomp g f)).
    rewrite (normalizationComparisonSkip m j a g),
      (normalizationComparisonSkip m i a (wcomp g f)).
    now exact (skippedValueSquares X m a i j f g).
  - intros i j a f g.
    unfold normalizedPaths. rewrite gluedPathsMixed.
    unfold glueMixedPath.
    rewrite <- (normalizationComparisonKeep m j g).
    refine (normalizationMixedSquare m i j a f g • _).
    apply transCongR. apply transCongL.
    unfold mixedPathCore.
    now rewrite 2 eqTransAssoc.
  - intros i j f g.
    unfold normalizedPaths. rewrite gluedPathsKeep.
    unfold glueKeepPath, keepCompositeValue.
    rewrite <- (normalizationComparisonKeep m j g),
      <- (normalizationComparisonKeep m i (wcomp g f)).
    now exact (normalizationKeepSquare m f g).
Defined.

Definition unsplitMatching (s: SplitMatching): MatchingObject X :=
  glueMatching X s.1 (fun a => (s.2 a).1)
    (fun a => (s.2 a).2).

Local Definition splitComparison (s: SplitMatching) a i g :=
  f_equal (fun z => matchingValue z i g) (s.2 a).2.

Lemma unsplitMatchingKeep (s: SplitMatching):
  keepMatching X (unsplitMatching s) = s.1.
Proof.
  refine (matchingHomotopy (shiftDiagram X)
    (b := keepMatching X (unsplitMatching s)) (c := s.1)
    (mergeValuesKeep X s.1.1 (fun a => (s.2 a).1)) _).
  intros i j f g. rewrite keepMatchingPath.
  now exact (keptGlueSquares X s.1
    (fun a => (s.2 a).1) (splitComparison s) i j f g).
Defined.

Lemma unsplitMatchingKeepValue (s: SplitMatching) i g:
  f_equal (fun b => matchingValue b i g) (unsplitMatchingKeep s) =
    mergeValuesKeep X s.1.1 (fun a => (s.2 a).1) i g.
Proof. now apply matchingHomotopyValue. Defined.

Lemma unsplitMatchingTop (s: SplitMatching) a:
  skippedTop X (unsplitMatching s) a = (s.2 a).1.
Proof. now exact (restrictId X None (s.2 a).1). Defined.

Local Lemma unsplitMixedValue (s: SplitMatching) a i g:
  mixedComparisonValue (unsplitMatching s) a i g =
    f_equal (topFace X a i) (mergeValuesKeep X s.1.1 (fun a => (s.2 a).1) i g)
      • splitComparison s a i g.
Proof.
  now exact (gluedMixedComparisonBeta X s.1
    (fun a => (s.2 a).1) (splitComparison s) a i g (keepTopFaceWord g a)).
Defined.

Local Lemma unsplitSkippedValue (s: SplitMatching) a i g:
  skippedValueComparison X (unsplitMatching s) a (Some i) g =
    f_equal (restrict X (i := Some i) (j := None) g) (unsplitMatchingTop s a).
Proof.
  now exact (gluedSkippedComparisonBeta X s.1
    (fun a => (s.2 a).1) (splitComparison s) a i g).
Defined.

Local Lemma topFaceAp {b c: MatchingObject (shiftDiagram X)} (e: b = c) a i g:
  f_equal (fun z => matchingValue z i g) (f_equal (topFaceMatching X a) e) =
    f_equal (topFace X a i) (f_equal (fun z => matchingValue z i g) e).
Proof. now destruct e. Defined.

Local Lemma boundaryAp {x y: cells X None} (e: x = y) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (matchingMap X) e) =
    f_equal (restrict X (i := Some i) (j := None) g) e.
Proof. now destruct e. Defined.

Lemma splitUnsplit (s: SplitMatching): splitMatching (unsplitMatching s) = s.
Proof.
  refine (attachmentEq (fun a b => topFaceMatching X a b) (matchingMap X)
    (splitMatching (unsplitMatching s)) s
    (unsplitMatchingKeep s) (unsplitMatchingTop s) _).
  intro a. apply (matchingPathExt (baseDiagram X)); intros i g.
  rewrite 2 eq_trans_map_distr, topFaceAp, boundaryAp.
  refine (transCongR (f_equal (fun p => f_equal (topFace X a i) p)
    (unsplitMatchingKeepValue s i g)) _ • _).
  refine (_ • eq_sym (transCongR (splitMatchingPathValue (unsplitMatching s) a i g) _)).
  symmetry.
  refine (transCongR (f_equal2 (fun p q => p • eq_sym q)
    (unsplitMixedValue s a i g) (unsplitSkippedValue s a i g)) _ • _).
  now apply transSymCancelR2.
Defined.

Lemma unsplitSplit (m: MatchingObject X): unsplitMatching (splitMatching m) = m.
Proof.
  assert (e: splitComparison (splitMatching m) = normalizationAttachment m).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro g.
    now apply splitMatchingPathValue. }
  refine (matchingHomotopy X (b := unsplitMatching (splitMatching m)) (c := m)
    (normalizationComparison m) _).
  intros i j f g.
  change (f_equal (restrict X f) (normalizationComparison m j g) • matchingPath m f g =
    gluedPaths X (keepMatching X m) (skippedTop X m)
      (splitComparison (splitMatching m)) i j f g
      • normalizationComparison m i (wcomp g f)).
  rewrite e. now exact (normalizationSquares m i j f g).
Defined.

Definition matchingSplitEquiv: Equiv (MatchingObject X) SplitMatching :=
  qinvEquiv splitMatching unsplitMatching unsplitSplit splitUnsplit.

End MixedBranch.

(** Readout of a prefix path prepended to the attachment of a split matching
    object. *)

Lemma splitAttachmentPrependReadout {A: HSet} {n: nat}
  (X: Diagram A (S n)) (m: MatchingObject X) (a: A)
  (y: MatchingObject (baseDiagram X))
  (e: y = topFaceMatching X a (splitMatching X m).1)
  (i: Index n) (g: Word A (rank i) n):
  f_equal (fun z => matchingValue z i g)
    (e • ((splitMatching X m).2 a).2) =
  f_equal (fun z => matchingValue z i g) e
    • f_equal (fun z => matchingValue z i g) ((splitMatching X m).2 a).2.
Proof.
  now exact (mapTrans (fun z => matchingValue z i g)
    e ((splitMatching X m).2 a).2).
Defined.

(** Naturality of the recursive matching decomposition under coherent diagram
    maps. *)
Set Keyed Unification.

Local Lemma mapSquareAlgebra {T: Type} {a b c d e f g h i j: T}
  (cx1: a = g) (cx2: f = h) (cy1: c = i) (cy2: d = j)
  (nf: a = b) (nrj: b = c) (nri: f = e) (nk: e = d)
  (ex: g = h) (ey: i = j) (ng: g = i) (nh: h = j)
  (m1: cx1 • ng = nf • (nrj • cy1))
  (m2: cx2 • nh = nri • (nk • cy2)) (natural: ex • nh = ng • ey):
  nf • (nrj • (cy1 • (ey • eq_sym cy2))) =
    (cx1 • (ex • eq_sym cx2)) • (nri • nk).
Proof.
  destruct cx1, nf, nrj, cy1, ex, cx2, nri, nk, cy2.
  cbn in m1, m2, natural |- *.
  rewrite eq_trans_refl_l in m1, m2.
  rewrite m1, m2, 2 eq_trans_refl_l in natural.
  rewrite 3 eq_trans_refl_l.
  now exact (eq_sym natural).
Defined.

Local Lemma reverseSquare {T: Type} {a b c d e f: T}
  (ab: a = b) (bc: b = c) (cd: c = d)
  (ae: a = e) (ef: e = f) (fd: f = d)
  (h: ab • (bc • cd) = ae • (ef • fd)):
  eq_sym bc • (eq_sym ab • ae) = cd • (eq_sym fd • eq_sym ef).
Proof.
  destruct ab, bc, ae, ef, fd.
  cbn in h |- *. rewrite 2 eq_trans_refl_l in h.
  now exact (eq_sym h).
Defined.

Local Lemma tailSquare {T: Type} {u0 u1 u2 u3 u4 v0 v1 v2: T}
  (a: u0 = u1) (b: u1 = u2) (c: u2 = u3) (j: u3 = u4)
  (d: u0 = v0) (e: v0 = v1) (f: v1 = u3) (g: v1 = v2) (h: v2 = u4)
  (square: a • (b • c) = d • (e • f)) (natural: g • h = f • j):
  a • (b • (c • j)) = (d • (e • g)) • h.
Proof.
  rewrite <- (eqTransAssoc b c j), <- (eqTransAssoc a (b • c) j), square.
  rewrite 2 eqTransAssoc, <- natural.
  now rewrite 2 eqTransAssoc.
Defined.

Lemma mapMatchingAp {A: HSet} {n} {X Y: Diagram A n} (F: DiagramMap X Y)
  {b c: MatchingObject X} (e: b = c) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (mapMatching F) e) =
    f_equal (F.(mapCell) i) (f_equal (fun z => matchingValue z i g) e).
Proof. now destruct e. Defined.

Lemma mapMatchingWordPath {A: HSet} {n} {X Y: Diagram A n}
  (F: DiagramMap X Y) (m: MatchingObject X) (i: Index n)
  {f g: Word A (rank i) n} (e: f = g):
  f_equal (matchingValue (mapMatching F m) i) e =
    f_equal (F.(mapCell) i) (f_equal (matchingValue m i) e).
Proof. now destruct e. Defined.

Section Naturality.
Context {A: HSet} {n} {X Y: Diagram A (S n)} (F: DiagramMap X Y).

Lemma topFaceMapSquare (a: A) {i j: Index n}
  (f: Word A (rank i) (rank j)) (x: cells (shiftDiagram X) j):
  F.(mapNatural) (i := Some i) (j := Some j) f (topFace X a j x)
    • (f_equal (restrict Y (i := Some i) (j := Some j) f)
        (F.(mapNatural) (i := Some j) (j := raiseIndex j) (topFaceWord j a) x)
      • topFaceNaturality Y a f (F.(mapCell) (raiseIndex j) x)) =
  f_equal (F.(mapCell) (Some i)) (topFaceNaturality X a f x)
    • (F.(mapNatural) (i := Some i) (j := raiseIndex i) (topFaceWord i a)
        (restrict (shiftDiagram X) f x)
      • f_equal (topFace Y a i)
          (F.(mapNatural) (i := raiseIndex i) (j := raiseIndex j) (keepWord f) x)).
Proof.
  unfold topFaceNaturality. rewrite 2 eq_trans_map_distr, fEqualSym.
  eapply mapSquareAlgebra.
  - now exact (F.(mapComp) (i := Some i) (j := Some j) (k := raiseIndex j)
      f (topFaceWord j a) x).
  - now exact (F.(mapComp) (i := Some i) (j := raiseIndex i) (k := raiseIndex j)
      (topFaceWord i a) (keepWord f) x).
  - now exact (mapArrowPath F (i := Some i) (j := raiseIndex j)
      (eq_sym (topFaceWordNatural f a)) x).
Defined.

Definition topFaceMapValues (a: A) (b: MatchingObject (shiftDiagram X)):
  ComparisonValues (baseDiagram Y)
    (topFaceMatching Y a (mapMatching (shiftMap F) b))
    (mapMatching (truncateMap F) (topFaceMatching X a b)) :=
  fun i g => eq_sym (F.(mapNatural) (i := Some i) (j := raiseIndex i)
    (topFaceWord i a) (matchingValue b i g)).

Lemma topFaceMapSquares (a: A) (b: MatchingObject (shiftDiagram X)):
  ComparisonSquares (baseDiagram Y) (topFaceMapValues a b).
Proof.
  intros i j f g.
  pose proof (mapMatchingPath (truncateMap F) (topFaceMatching X a b)
    (i := i) (j := j) f g) as hmap.
  pose proof (topFaceMatchingPath X a b (i := i) (j := j) f g) as hsource.
  pose proof (topFaceMatchingPath Y a (mapMatching (shiftMap F) b)
    (i := i) (j := j) f g) as htarget.
  pose proof (mapMatchingPath (shiftMap F) b (i := i) (j := j) f g) as hshift.
  unfold baseDiagram in hmap, hsource, htarget, hshift |- *.
  rewrite hmap, hsource, htarget, hshift.
  unfold topFaceMapValues.
  cbn [truncateMap shiftMap reindexMap mapNatural mapCell].
  rewrite 2 eq_trans_map_distr, 2 fEqualSym.
  eapply tailSquare.
  - apply reverseSquare.
    now exact (topFaceMapSquare a f (matchingValue b j g)).
  - rewrite 2 f_equal_compose.
    now exact (homotopyNat _ _
      (fun x => eq_sym (F.(mapNatural) (i := Some i) (j := raiseIndex i) (topFaceWord i a) x))
      (matchingPath b f g)).
Defined.

Definition topFaceMapNatural (a: A) (b: MatchingObject (shiftDiagram X)):
  topFaceMatching Y a (mapMatching (shiftMap F) b) =
    mapMatching (truncateMap F) (topFaceMatching X a b) :=
  matchingHomotopy (baseDiagram Y)
    (b := topFaceMatching Y a (mapMatching (shiftMap F) b))
    (c := mapMatching (truncateMap F) (topFaceMatching X a b))
    (topFaceMapValues a b) (topFaceMapSquares a b).

Lemma topFaceMapNaturalValue (a: A) (b: MatchingObject (shiftDiagram X)) i g:
  f_equal (fun z => matchingValue z i g) (topFaceMapNatural a b) =
    eq_sym (F.(mapNatural) (i := Some i) (j := raiseIndex i)
      (topFaceWord i a) (matchingValue b i g)).
Proof.
  unfold topFaceMapNatural.
  now exact (matchingHomotopyValue (baseDiagram Y)
    (b := topFaceMatching Y a (mapMatching (shiftMap F) b))
    (c := mapMatching (truncateMap F) (topFaceMatching X a b))
    (topFaceMapValues a b) (topFaceMapSquares a b) i g).
Defined.

Definition splitMap (s: SplitMatching X): SplitMatching Y :=
  (mapMatching (shiftMap F) s.1; fun a =>
    (F.(mapCell) None (s.2 a).1;
      topFaceMapNatural a s.1
        • (f_equal (mapMatching (truncateMap F)) (s.2 a).2
          • mapBoundary F (s.2 a).1))).

Lemma mixedComparisonMapValue (m: MatchingObject X) a i g:
  mixedComparisonValue Y (mapMatching F m) a i g =
    eq_sym (F.(mapNatural) (i := Some i) (j := raiseIndex i)
      (topFaceWord i a) (matchingValue m (raiseIndex i) (keepToTop g)))
    • f_equal (F.(mapCell) (Some i)) (mixedComparisonValue X m a i g).
Proof.
  unfold mixedComparisonValue. rewrite mapMatchingPath.
  rewrite (mapMatchingWordPath F m (Some i) (keepTopFaceWord g a)).
  refine (eqTransAssoc _ _ _ • transCongL _ _).
  now exact (eq_sym (eq_trans_map_distr (F.(mapCell) (Some i))
    (matchingPath m (i := Some i) (j := raiseIndex i)
      (topFaceWord i a) (keepToTop g))
    (f_equal (matchingValue m (Some i)) (keepTopFaceWord g a)))).
Defined.

Lemma skippedComparisonMapValue (m: MatchingObject X) a i g:
  skippedValueComparison Y (mapMatching F m) a (Some i) g =
    eq_sym (F.(mapNatural) (i := Some i) (j := None) g (skippedTop X m a))
    • f_equal (F.(mapCell) (Some i)) (skippedValueComparison X m a (Some i) g).
Proof.
  unfold skippedValueComparison. rewrite mapMatchingPath.
  rewrite (mapMatchingWordPath F m (Some i) (skippedWord a g)).
  refine (eqTransAssoc _ _ _ • transCongL _ _).
  now exact (eq_sym (eq_trans_map_distr (F.(mapCell) (Some i))
    (matchingPath m (i := Some i) (j := None) g (wskip a (wid n)))
    (f_equal (matchingValue m (Some i)) (skippedWord a g)))).
Defined.

Local Lemma mapAttachmentAlgebra {B C: Type} (f: B -> C)
  {b c z: B} {u v: C} (m: b = z) (s: c = z) (p: u = f b) (t: f c = v):
  (p • f_equal f m) • eq_sym (eq_sym t • f_equal f s) =
    p • (f_equal f (m • eq_sym s) • t).
Proof.
  destruct m, s. cbn [f_equal].
  rewrite 2 eq_trans_refl_r, eq_sym_involutive.
  now rewrite eq_trans_refl_l.
Defined.

Definition splitNaturalityValue (m: MatchingObject X) a i g :=
  eq_sym (F.(mapNatural) (i := Some i) (j := raiseIndex i)
    (topFaceWord i a) (matchingValue m (raiseIndex i) (keepToTop g)))
  • (f_equal (F.(mapCell) (Some i))
      (f_equal (fun z => matchingValue z i g) ((splitMatching X m).2 a).2)
    • F.(mapNatural) (i := Some i) (j := None) g (skippedTop X m a)).

Lemma splitMapPathValue (m: MatchingObject X) a i g:
  f_equal (fun z => matchingValue z i g) ((splitMap (splitMatching X m)).2 a).2 =
    splitNaturalityValue m a i g.
Proof.
  change (f_equal (fun z: MatchingObject (baseDiagram Y) => matchingValue z i g)
    (topFaceMapNatural a (keepMatching X m)
      • (f_equal (mapMatching (truncateMap F)) ((splitMatching X m).2 a).2
        • mapBoundary F (skippedTop X m a))) = splitNaturalityValue m a i g).
  unfold splitNaturalityValue.
  refine (eq_trans_map_distr
    (fun z: MatchingObject (baseDiagram Y) => matchingValue z i g)
    (topFaceMapNatural a (keepMatching X m))
    (f_equal (mapMatching (truncateMap F)) ((splitMatching X m).2 a).2
      • mapBoundary F (skippedTop X m a)) • _).
  refine (transCongR (topFaceMapNaturalValue a (keepMatching X m) i g) _ • transCongL _ _).
  refine (eq_trans_map_distr
    (fun z: MatchingObject (baseDiagram Y) => matchingValue z i g)
    (f_equal (mapMatching (truncateMap F)) ((splitMatching X m).2 a).2)
    (mapBoundary F (skippedTop X m a)) • _).
  now exact (transCongR (mapMatchingAp (truncateMap F) ((splitMatching X m).2 a).2 i g) _
    • transCongL _ (mapBoundaryValue F (skippedTop X m a) i g)).
Defined.

Lemma mappedSplitPathValue (m: MatchingObject X) a i g:
  f_equal (fun z => matchingValue z i g) ((splitMatching Y (mapMatching F m)).2 a).2 =
    splitNaturalityValue m a i g.
Proof.
  refine (splitMatchingPathValue Y (mapMatching F m) a i g • _).
  refine (f_equal2 (fun p q => p • eq_sym q)
    (mixedComparisonMapValue m a i g) (skippedComparisonMapValue m a i g) • _).
  refine (mapAttachmentAlgebra (F.(mapCell) (Some i))
    (mixedComparisonValue X m a i g) (skippedValueComparison X m a (Some i) g)
    _ _ • _).
  unfold splitNaturalityValue.
  refine (transCongL _ (transCongR
    (f_equal (fun p => f_equal (F.(mapCell) (Some i)) p)
      (eq_sym (splitMatchingPathValue X m a i g))) _)).
Defined.

Local Lemma topFaceProjection {b c: MatchingObject (shiftDiagram Y)}
  (e: b = c) a i g:
  f_equal (fun z => matchingValue z i g) (f_equal (topFaceMatching Y a) e) =
    f_equal (topFace Y a i) (f_equal (fun z => matchingValue z i g) e).
Proof. now destruct e. Defined.

Lemma keptFaceValue (m: MatchingObject X) a i g:
  f_equal (fun z => matchingValue z i g)
    (f_equal (topFaceMatching Y a) (eq_sym (keepMap F m))) = eq_refl.
Proof.
  rewrite topFaceProjection, fEqualSym.
  refine (f_equal (fun p => f_equal (topFace Y a i) (eq_sym p))
    (keepMapValue F m i g) • _).
  now reflexivity.
Defined.

Lemma splitNaturality (m: MatchingObject X):
  splitMatching Y (mapMatching F m) = splitMap (splitMatching X m).
Proof.
  refine (attachmentEq (fun a b => topFaceMatching Y a b) (matchingMap Y)
    (splitMatching Y (mapMatching F m)) (splitMap (splitMatching X m))
    (eq_sym (keepMap F m)) (fun _ => eq_refl) _).
  intro a. apply (matchingPathExt (baseDiagram Y)); intros i g.
  rewrite eq_trans_map_distr.
  refine (transCongR (keptFaceValue m a i g) _ • _).
  refine (eq_trans_refl_l _ • _).
  now exact (splitMapPathValue m a i g • eq_sym (mappedSplitPathValue m a i g)).
Defined.

Lemma splitNaturalityBase (m: MatchingObject X):
  projT1_eq (splitNaturality m) = eq_sym (keepMap F m).
Proof. unfold splitNaturality. now apply attachmentEqBase. Defined.

Lemma splitNaturalityTop (m: MatchingObject X) a:
  f_equal (fun s: SplitMatching Y => (s.2 a).1) (splitNaturality m) = eq_refl.
Proof.
  unfold splitNaturality.
  now exact (attachmentEqTop (fun a b => topFaceMatching Y a b) (matchingMap Y)
    (splitMatching Y (mapMatching F m)) (splitMap (splitMatching X m))
    (eq_sym (keepMap F m)) (fun _ => eq_refl) _ a).
Defined.

End Naturality.

Unset Keyed Unification.
