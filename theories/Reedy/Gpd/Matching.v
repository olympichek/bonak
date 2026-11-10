(** Matching objects of diagrams of homotopy groupoids: comparisons and paths
    between them, repacking along changed diagram laws, and the action of
    diagram maps. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Contractible Funext Notation
  RewLemmas FinitePrefix.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra.

Set Primitive Projections.
Set Printing Projections.
Import FinitePrefix.

(** Paths of coherent matching objects preserve their comparison paths. *)

Section MatchingPaths.
Context {A: HSet} {n: nat} (X: Diagram A n).

Definition ComparisonValues (b c: MatchingObject X): Type :=
  forall (i: Index n) (f: Word A (rank i) n), matchingValue b i f = matchingValue c i f.
Definition ComparisonSquares {b c: MatchingObject X} (h: ComparisonValues b c): Type :=
  forall (i j: Index n) (f: Word A (rank i) (rank j)) (g: Word A (rank j) n),
    f_equal (restrict X f) (h j g) • matchingPath c f g =
      matchingPath b f g • h i (wcomp g f).
Definition MatchingComparison (b c: MatchingObject X): Type :=
  {h: ComparisonValues b c &T ComparisonSquares h}.

Lemma comparisonSquaresProp {b c: MatchingObject X} (h: ComparisonValues b c)
  (p q: ComparisonSquares h): p = q.
Proof.
  repeat (apply functional_extensionality_dep; intro).
  now apply (cells X _).(GUIP).
Defined.

Definition comparisonRefl (b: MatchingObject X): MatchingComparison b b.
Proof.
  exists (fun i f => eq_refl). intros i j f g.
  now exact (eq_trans_refl_l (matchingPath b f g)).
Defined.

(** Coherence is preserved by a pointwise change of boundary values when
    the comparison squares account for the change of overlap paths. *)
Lemma matchingLawsOfSquares (v w: MatchingValues X)
  (p: MatchingPaths X v) (q: MatchingPaths X w)
  (h: forall i f, v i f = w i f)
  (s: forall i j f g,
    f_equal (restrict X (i := i) (j := j) f) (h j g) • q i j f g =
      p i j f g • h i (wcomp g f)) (l: MatchingLaws X q): MatchingLaws X p.
Proof.
  revert q s l.
  refine (homInd2 (I1 := Index n) (I2 := fun i => Word A (rank i) n)
    (B := fun i _ => cells X i) v
    (fun w h => forall (q: MatchingPaths X w),
      (forall i j f g,
        f_equal (restrict X (i := i) (j := j) f) (h j g) • q i j f g =
          p i j f g • h i (wcomp g f)) ->
      MatchingLaws X q -> MatchingLaws X p) _ w h).
  intros q s l.
  assert (e: p = q).
  { apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro j.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    specialize (s i j f g). cbn [f_equal] in s.
    rewrite eq_trans_refl_l in s. now exact (eq_sym s). }
  now destruct e.
Defined.

Definition comparisonContract (b: MatchingObject X):
  Contr {c: MatchingObject X &T MatchingComparison b c}.
Proof.
  exists (b; comparisonRefl b).
  intros [[c [cp cl]] [h H]]. destruct b as [b [bp bl]].
  change (forall i f, b i f = c i f) in h.
  revert cp cl H.
  refine (homInd2 (I1 := Index n) (I2 := fun i => Word A (rank i) n)
    (B := fun i _ => cells X i) b
    (fun c h => forall (cp: MatchingPaths X c) (cl: MatchingLaws X cp)
      (H: @ComparisonSquares (b; (bp; bl)) (c; (cp; cl)) h),
      (((b; (bp; bl)); comparisonRefl (b; (bp; bl))):
        {z: MatchingObject X &T MatchingComparison (b; (bp; bl)) z}) =
      ((c; (cp; cl)); (h; H))) _ c h).
  intros cp cl H.
  assert (e: bp = cp).
  { apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro j.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    specialize (H i j f g).
    change (eq_refl • cp i j f g = bp i j f g • eq_refl) in H.
    rewrite eq_trans_refl_l in H. now exact (eq_sym H). }
  destruct e. destruct (Reedy.matchingLawsHProp X bp bl cl).
  apply f_equal. refine (eq_existT_curried eq_refl _).
  now apply comparisonSquaresProp.
Defined.

(** This identity system identifies boundary paths with compatible pointwise
    paths. Its square condition records the effect on all overlap paths. *)
Definition matchingPathEquiv (b c: MatchingObject X):
  Equiv (b = c) (MatchingComparison b c) :=
  identitySystemEquiv b (MatchingComparison b) (comparisonRefl b) (comparisonContract b) c.

Lemma matchingPathEquivValue {b c: MatchingObject X} (p: b = c) i f:
  (matchingPathEquiv b c p).1 i f = f_equal (fun z => matchingValue z i f) p.
Proof. now destruct p. Defined.

Lemma matchingPathSquares {b c: MatchingObject X} (p: b = c):
  ComparisonSquares (fun i f => f_equal (fun z => matchingValue z i f) p).
Proof.
  destruct p. intros i j f g. now exact (eq_trans_refl_l (matchingPath b f g)).
Defined.

Definition matchingHomotopy {b c: MatchingObject X}
  (h: ComparisonValues b c) (s: ComparisonSquares h): b = c :=
  invEq (matchingPathEquiv b c) (h; s).

Lemma matchingHomotopyComparison {b c: MatchingObject X}
  (h: ComparisonValues b c) (s: ComparisonSquares h):
  matchingPathEquiv b c (matchingHomotopy h s) = (h; s).
Proof. now apply secEq. Defined.

Lemma matchingHomotopyValue {b c: MatchingObject X}
  (h: ComparisonValues b c) (s: ComparisonSquares h) i f:
  f_equal (fun z => matchingValue z i f) (matchingHomotopy h s) = h i f.
Proof.
  refine (eq_sym (matchingPathEquivValue (matchingHomotopy h s) i f) • _).
  now exact (f_equal (fun z: MatchingComparison b c => z.1 i f)
    (matchingHomotopyComparison h s)).
Defined.
Lemma matchingPathExt {b c: MatchingObject X} (p q: b = c)
  (h: forall i f, f_equal (fun z => matchingValue z i f) p =
    f_equal (fun z => matchingValue z i f) q): p = q.
Proof.
  apply (eqvInj (matchingPathEquiv b c)).
  assert (e: (matchingPathEquiv b c p).1 = (matchingPathEquiv b c q).1).
  { apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro f.
    now exact (matchingPathEquivValue p i f
      • (h i f • eq_sym (matchingPathEquivValue q i f))). }
  refine (eq_existT_curried e _).
  now apply comparisonSquaresProp.
Defined.

End MatchingPaths.

Local Lemma appendSquare {T: Type} {v0 v1 v2 v3 v4 w: T}
  (p: v0 = v1) (q: v1 = v2) (r: v2 = v3) (s: v3 = v4)
  (t: v0 = w) (u: w = v3) (e: p • (q • r) = t • u):
  p • (q • (r • s)) = t • (u • s).
Proof.
  rewrite <- (eqTransAssoc q r s), <- (eqTransAssoc p (q • r) s), e.
  now apply eqTransAssoc.
Defined.

(** The constant-coordinate branch is a cone with a distinguished top cell. *)
Section SkippedBranch.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).

Definition skippedMatching (m: MatchingObject X) (a: A):
  MatchingObject (truncateDiagram X).
Proof.
  exists (fun i g => matchingValue m (Some i) (wskip a g)).
  exists (fun i j f g => matchingPath m (i := Some i) (j := Some j) f (wskip a g)).
  split.
  - intros i g.
    refine (matchingUnit m (Some i) (wskip a g) • _).
    apply f_equal. apply f_equal.
    refine (_ • f_equal_compose (wskip a) (matchingValue m (Some i)) (wcompIdr g)).
    apply f_equal. now apply (wordSet (A := A) (rank i) (S n)).(UIP).
  - intros i j k f g h.
    refine (_ • matchingComp m (i := Some i) (j := Some j) (k := Some k) f g (wskip a h)).
    apply f_equal. apply f_equal.
    refine (eq_sym (f_equal_compose (wskip a) (matchingValue m (Some i))
      (eq_sym (wcompAssoc h g f))) • _).
    apply f_equal. now apply (wordSet (A := A) (rank i) (S n)).(UIP).
Defined.

Definition skippedTop (m: MatchingObject X) (a: A): cells X None :=
  matchingValue m None (wskip a (wid n)).

Definition skippedWord {k} (a: A) (f: Word A k n):
  wcomp (wskip a (wid n)) f = wskip a f := f_equal (wskip a) (wcompIdl f).

Definition skippedComparison (m: MatchingObject X) (a: A):
  ComparisonValues (truncateDiagram X)
    (matchingMap X (skippedTop m a)) (skippedMatching m a) :=
  fun i f => matchingPath m (i := Some i) (j := None) f (wskip a (wid n))
    • f_equal (matchingValue m (Some i)) (skippedWord a f).

Lemma matchingPathNatural {A': HSet} {N} (D: Diagram A' N) (m: MatchingObject D)
  {i j} (f: Word A' (rank i) (rank j)) {g h: Word A' (rank j) N} (e: g = h):
  f_equal (restrict D f) (f_equal (matchingValue m j) e) • matchingPath m f h
    = matchingPath m f g • f_equal (matchingValue m i) (f_equal (fun u => wcomp u f) e).
Proof. destruct e. now exact (eq_trans_refl_l _). Defined.

Lemma skippedComparisonSquares (m: MatchingObject X) (a: A):
  ComparisonSquares (truncateDiagram X) (skippedComparison m a).
Proof.
  intros i j f g.
  change (f_equal (restrict X (i := Some i) (j := Some j) f)
      (matchingPath m (i := Some j) (j := None) g (wskip a (wid n))
        • f_equal (matchingValue m (Some j)) (skippedWord a g))
    • matchingPath m (i := Some i) (j := Some j) f (wskip a g) =
    restrictComp X (i := Some i) (j := Some j) (k := None) f g (skippedTop m a)
    • (matchingPath m (i := Some i) (j := None) (wcomp g f) (wskip a (wid n))
      • f_equal (matchingValue m (Some i)) (skippedWord a (wcomp g f)))).
  rewrite eq_trans_map_distr, eqTransAssoc, matchingPathNatural.
  assert (e: f_equal (fun u => wcomp u f) (skippedWord a g) =
    eq_sym (wcompAssoc (wskip a (wid n)) g f) • skippedWord a (wcomp g f)).
  { now apply (wordSet (A := A) (rank i) (S n)).(UIP). }
  refine (f_equal (fun z =>
    f_equal (restrict X (i := Some i) (j := Some j) f)
      (matchingPath m (i := Some j) (j := None) g (wskip a (wid n)))
    • (matchingPath m (i := Some i) (j := Some j) f (wcomp (wskip a (wid n)) g)
      • f_equal (matchingValue m (Some i)) z)) e • _).
  rewrite eq_trans_map_distr.
  apply appendSquare.
  now exact (matchingComp m (i := Some i) (j := Some j) (k := None)
    f g (wskip a (wid n))).
Defined.

Definition skippedBoundary (m: MatchingObject X) (a: A):
  matchingMap X (skippedTop m a) = skippedMatching m a :=
  matchingHomotopy (truncateDiagram X) (skippedComparison m a) (skippedComparisonSquares m a).

Lemma skippedBoundaryValue (m: MatchingObject X) (a: A) i f:
  f_equal (fun z => matchingValue z i f) (skippedBoundary m a) =
  skippedComparison m a i f.
Proof. now apply matchingHomotopyValue. Defined.
End SkippedBranch.

(** Matching objects with fixed object and arrow data, compared across
    diagram laws. *)

Section MatchingLawRepack.
Context {A: HSet} {n: nat} (O: Index n -> HGpd)
  (h: forall i j, Word A (rank j) (rank i) -> O i -> O j)
  (u0 u1: forall i, h i i (wid (rank i)) = (fun x => x))
  (c0 c1: forall i j k (f: Word A (rank j) (rank i))
    (g: Word A (rank k) (rank j)) x,
    h j k g (h i j f x) = h i k (wcomp f g) x).

Local Definition D0: PathDiagramData (PrefixCategory A n) O :=
  @Build_PathDiagramData (PrefixCategory A n) O h u0 c0.
Local Definition D1: PathDiagramData (PrefixCategory A n) O :=
  @Build_PathDiagramData (PrefixCategory A n) O h u1 c1.

Context (l0: PathDiagramUnitL _ _ D0) (r0: PathDiagramUnitR _ _ D0)
  (a0: PathDiagramAssoc _ _ D0)
  (l1: PathDiagramUnitL _ _ D1) (r1: PathDiagramUnitR _ _ D1)
  (a1: PathDiagramAssoc _ _ D1).

Local Definition X: Diagram A n :=
  @Build_PathDiagramFamily (PrefixCategory A n) O
    (@Build_PathDiagram (PrefixCategory A n) O D0 l0 r0 a0).
Local Definition Y: Diagram A n :=
  @Build_PathDiagramFamily (PrefixCategory A n) O
    (@Build_PathDiagram (PrefixCategory A n) O D1 l1 r1 a1).

Context (unitEqual: forall i (x: O i), pidPt D0 i x = pidPt D1 i x)
  (compEqual: forall i j k (f: Word A (rank j) (rank i))
    (g: Word A (rank k) (rank j)) x, c0 i j k f g x = c1 i j k f g x).

Definition matchingLawRepack (b: MatchingObject X): MatchingObject Y.
Proof.
  exists b.1. exists b.2.1. split.
  - intros i g. now exact (matchingUnit b i g • transCongR
      (unitEqual i (matchingValue b i g))
      (eq_sym (f_equal (matchingValue b i) (wcompIdr g)))).
  - intros i j k f g h0. now exact (matchingComp b f g h0 • transCongR
      (compEqual k j i g f (matchingValue b k h0))
      (matchingPath b (wcomp g f) h0)).
Defined.

End MatchingLawRepack.

(** Coherent maps of diagrams act on matching objects and their paths. *)

Record DiagramMap {A: HSet} {n} {X Y: Diagram A n} := {
  mapCell i: cells X i -> cells Y i;
  mapNatural {i j} (f: Word A (rank i) (rank j)) (x: cells X j):
    mapCell i (restrict X (i := i) (j := j) f x)
      = restrict Y (i := i) (j := j) f (mapCell j x);
  mapUnit i (x: cells X i):
    f_equal (mapCell i) (restrictId X i x) =
      mapNatural (wid (rank i)) x • restrictId Y i (mapCell i x);
  mapComp {i j k} (f: Word A (rank i) (rank j))
    (g: Word A (rank j) (rank k)) (x: cells X k):
    f_equal (mapCell i) (restrictComp X (i := i) (j := j) (k := k) f g x)
      • mapNatural (wcomp g f) x =
      mapNatural f (restrict X (i := j) (j := k) g x)
      • (f_equal (restrict Y (i := i) (j := j) f) (mapNatural g x)
        • restrictComp Y (i := i) (j := j) (k := k) f g (mapCell k x));
}.
Arguments DiagramMap {A n} X Y.

Local Lemma mapConeCompAlgebra {T: Type} {V U S K J L W G Z: T}
  (mf: V = U) (mg: U = S) (mf': K = J) (u: V = K) (v: U = J)
  (q: K = L) (a: L = Z) (h: V = W) (w: W = Z) (mfg: W = G) (c: S = G)
  (nat: u • mf' = mf • v)
  (old: u • (q • a) = h • w)
  (map: h • mfg = mf • (mg • c)):
  eq_sym mg • (v • (eq_sym mf' • (q • a))) = c • (eq_sym mfg • w).
Proof.
  destruct mf, mg, u, mf', q, h, mfg, a.
  cbn in nat, old, map |- *.
  rewrite eq_trans_refl_l in nat, old.
  rewrite 2 eq_trans_refl_l in map.
  now rewrite <- nat, <- old, <- map.
Defined.

Section Action.
Context {A: HSet} {n} {X Y: Diagram A n} (F: DiagramMap X Y).

Definition mapValues (b: MatchingObject X): MatchingValues Y :=
  fun i f => F.(mapCell) i (matchingValue b i f).

Definition mapPaths (b: MatchingObject X): MatchingPaths Y (mapValues b) :=
  fun i j f g => eq_sym (F.(mapNatural) f (matchingValue b j g))
    • f_equal (F.(mapCell) i) (matchingPath b f g).

Lemma mapUnitLaw (b: MatchingObject X): MatchingUnit Y (mapPaths b).
Proof.
  intros i g.
  change (eq_sym (F.(mapNatural) (wid (rank i)) (matchingValue b i g))
      • f_equal (F.(mapCell) i) (matchingPath b (wid (rank i)) g)
    = restrictId Y i (F.(mapCell) i (matchingValue b i g))
      • eq_sym (f_equal (fun f => F.(mapCell) i (matchingValue b i f)) (wcompIdr g))).
  rewrite matchingUnit, eq_trans_map_distr, fEqualSym, f_equal_compose, F.(mapUnit).
  rewrite <- eq_trans_assoc.
  now apply inverseCancel.
Defined.

Lemma mapCompLaw (b: MatchingObject X): MatchingComp Y (mapPaths b).
Proof.
  intros i j k f g h.
  unfold mapPaths, mapValues.
  rewrite eq_trans_map_distr, fEqualSym.
  rewrite <- (f_equal_compose (matchingValue b i) (F.(mapCell) i)
    (eq_sym (wcompAssoc h g f))).
  rewrite <- 2 eq_trans_assoc.
  eapply mapConeCompAlgebra with
    (u := f_equal (F.(mapCell) i) (f_equal (restrict X f) (matchingPath b g h)))
    (h := f_equal (F.(mapCell) i) (restrictComp X f g (matchingValue b k h))).
  - pose proof (homotopyNat
      (fun x => F.(mapCell) i (restrict X (i := i) (j := j) f x))
      (fun x => restrict Y (i := i) (j := j) f (F.(mapCell) j x))
      (F.(mapNatural) f) (matchingPath b g h)) as e.
    rewrite <- (f_equal_compose (restrict X f) (F.(mapCell) i) (matchingPath b g h)) in e.
    rewrite <- (f_equal_compose (F.(mapCell) j) (restrict Y f) (matchingPath b g h)) in e.
    now exact e.
  - rewrite <- 3 eq_trans_map_distr.
    now apply f_equal, matchingComp.
  - now apply F.(mapComp).
Defined.

Definition mapMatching (b: MatchingObject X): MatchingObject Y :=
  (mapValues b; (mapPaths b; (mapUnitLaw b; mapCompLaw b))).

Lemma mapMatchingValue (b: MatchingObject X) i f:
  matchingValue (mapMatching b) i f = F.(mapCell) i (matchingValue b i f).
Proof. now reflexivity. Defined.

Lemma mapMatchingPath (b: MatchingObject X) {i j}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  matchingPath (mapMatching b) f g =
    eq_sym (F.(mapNatural) f (matchingValue b j g))
      • f_equal (F.(mapCell) i) (matchingPath b f g).
Proof. now reflexivity. Defined.

End Action.

(** Mapping a cell's boundary agrees with taking the boundary of its image.
    Its component paths are the map's chosen naturality comparisons. *)
Section Boundary.
Context {A: HSet} {n} {X Y: Diagram A (S n)} (F: DiagramMap X Y).

Definition truncateMap: DiagramMap (truncateDiagram X) (truncateDiagram Y) :=
  @Build_DiagramMap A n (truncateDiagram X) (truncateDiagram Y)
    (fun i => F.(mapCell) (Some i))
    (fun i j f x => F.(mapNatural) (i := Some i) (j := Some j) f x)
    (fun i x => F.(mapUnit) (Some i) x)
    (fun i j k f g x => F.(mapComp) (i := Some i) (j := Some j) (k := Some k) f g x).

Definition mapBoundaryValues (x: cells X None):
  ComparisonValues (truncateDiagram Y)
    (mapMatching truncateMap (matchingMap X x))
    (matchingMap Y (F.(mapCell) None x)) :=
  fun i g => F.(mapNatural) (i := Some i) (j := None) g x.

Lemma mapBoundarySquares (x: cells X None):
  ComparisonSquares (truncateDiagram Y) (mapBoundaryValues x).
Proof.
  intros i j f g. symmetry.
  change ((eq_sym (F.(mapNatural) (i := Some i) (j := Some j) f
      (restrict X (i := Some j) (j := None) g x))
    • f_equal (F.(mapCell) (Some i))
        (restrictComp X (i := Some i) (j := Some j) (k := None) f g x))
      • F.(mapNatural) (i := Some i) (j := None) (wcomp g f) x =
    f_equal (restrict Y (i := Some i) (j := Some j) f)
      (F.(mapNatural) (i := Some j) (j := None) g x)
      • restrictComp Y (i := Some i) (j := Some j) (k := None) f g
          (F.(mapCell) None x)).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (F.(mapComp) (i := Some i) (j := Some j) (k := None) f g x) • _).
  now apply inverseCancel.
Defined.

Definition mapBoundary (x: cells X None):
  mapMatching truncateMap (matchingMap X x) =
    matchingMap Y (F.(mapCell) None x) :=
  matchingHomotopy (truncateDiagram Y) (mapBoundaryValues x) (mapBoundarySquares x).

Lemma mapBoundaryValue (x: cells X None) i g:
  f_equal (fun b => matchingValue b i g) (mapBoundary x) =
    F.(mapNatural) (i := Some i) (j := None) g x.
Proof.
  now exact (matchingHomotopyValue (truncateDiagram Y)
    (mapBoundaryValues x) (mapBoundarySquares x) i g).
Defined.

End Boundary.
