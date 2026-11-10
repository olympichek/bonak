(** Coherent maps of boundaries extend to maps of the adjoining layers. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation RewLemmas FinitePrefix.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import LocallyDiscretePseudofunctor HGpdDiagramEq
  Pseudonatural PathDiagramTransformation.
From Bonak.Reedy.Gpd Require Import Reedy Matching Extension.
Set Primitive Projections.
Set Printing Projections.


Definition diagramMapTransformation {A: HSet} {n} {X Y: Diagram A n}
  (F: DiagramMap X Y) :=
  pathDiagramTransformation X Y F.(mapCell)
    (fun i j f x => F.(mapNatural) (i := j) (j := i) f x)
    F.(mapUnit)
    (fun i j k f g x => F.(mapComp) (i := k) (j := j) (k := i) g f x).

Definition diagramMapEq {A: HSet} {n} {X Y: Diagram A n}
  (F: DiagramMap X Y) (e: forall i, IsEquiv (F.(mapCell) i)): X = Y :=
  eqvInj (locallyDiscretePseudofunctorEquiv (PrefixCategory A n))
    (hgpdPseudofunctorEq (diagramMapTransformation F) e).

Local Lemma cancelBoundarySquare {T: Type} {x y z w v: T}
  (m: x = y) (p: x = z) (q: y = w) (r: w = v) (h: z = v)
  (s: q • r = (eq_sym m • p) • h): p • h = m • (q • r).
Proof.
  destruct m. cbn in s |- *. rewrite eq_trans_refl_l in s.
  now exact (eq_sym s • eq_sym (eq_trans_refl_l (q • r))).
Defined.

Section Extension.
Context {A: HSet} {n} {X Y: Diagram A n} (F: DiagramMap X Y)
  {T U: HGpd} (e: T -> U) (b: T -> MatchingObject X) (c: U -> MatchingObject Y)
  (h: forall t, mapMatching F (b t) = c (e t)).
Local Abbreviation EX := (extendByMatchingMap A X T b).
Local Abbreviation EY := (extendByMatchingMap A Y U c).

Definition extensionCell (i: Index (S n)): cells EX i -> cells EY i :=
  match i with Some i => F.(mapCell) i | None => e end.

Definition extensionNatural {i j: Index (S n)}
  (f: Word A (rank i) (rank j)) (x: cells EX j):
  extensionCell i (restrict EX f x) = restrict EY f (extensionCell j x).
Proof.
  destruct i as [i|], j as [j|].
  - now exact (F.(mapNatural) f x).
  - now exact (f_equal (fun z => matchingValue z i f) (h x)).
  - exfalso. now exact (noWordAbove (rankLt j) f).
  - now reflexivity.
Defined.

Lemma extensionUnit (i: Index (S n)) (x: cells EX i):
  f_equal (extensionCell i) (restrictId EX i x) =
    extensionNatural (wid (rank i)) x • restrictId EY i (extensionCell i x).
Proof.
  destruct i as [i|].
  - now exact (F.(mapUnit) i x).
  - now reflexivity.
Defined.

Lemma extensionComp {i j k: Index (S n)}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)) (x: cells EX k):
  f_equal (extensionCell i) (restrictComp EX f g x) • extensionNatural (wcomp g f) x =
    extensionNatural f (restrict EX g x) •
      (f_equal (restrict EY f) (extensionNatural g x) •
        restrictComp EY f g (extensionCell k x)).
Proof.
  destruct i as [i|], j as [j|], k as [k|].
  - now exact (F.(mapComp) f g x).
  - change (f_equal (F.(mapCell) i) (matchingPath (b x) f g)
      • f_equal (fun z => matchingValue z i (wcomp g f)) (h x) =
      F.(mapNatural) f (matchingValue (b x) j g) •
        (f_equal (restrict Y f) (f_equal (fun z => matchingValue z j g) (h x))
          • matchingPath (c (e x)) f g)).
    apply cancelBoundarySquare.
    now exact (matchingPathSquares Y (h x) i j f g).
  - exfalso. now exact (noWordAbove (rankLt k) g).
  - change (f_equal (F.(mapCell) i)
        (f_equal (matchingValue (b x) i)
          (eq_sym (f_equal (fun u => wcomp u f) (wordEndId n g) • wcompIdl f)))
      • f_equal (fun z => matchingValue z i (wcomp g f)) (h x) =
      f_equal (fun z => matchingValue z i f) (h x) •
        (eq_refl • f_equal (matchingValue (c (e x)) i)
          (eq_sym (f_equal (fun u => wcomp u f) (wordEndId n g) • wcompIdl f)))).
    rewrite eq_trans_refl_l, f_equal_compose.
    now exact (homotopyNat
      (fun w => F.(mapCell) i (matchingValue (b x) i w))
      (matchingValue (c (e x)) i)
      (fun w => f_equal (fun z => matchingValue z i w) (h x))
      (eq_sym (f_equal (fun u => wcomp u f) (wordEndId n g) • wcompIdl f))).
  - exfalso. now exact (noWordAbove (rankLt j) f).
  - exfalso. now exact (noWordAbove (rankLt j) f).
  - exfalso. now exact (noWordAbove (rankLt k) g).
  - now reflexivity.
Defined.

Definition extensionMap: DiagramMap EX EY :=
  @Build_DiagramMap A (S n) EX EY extensionCell
    (fun i j f x => extensionNatural f x) extensionUnit
    (fun i j k f g x => extensionComp f g x).

Definition extensionMapEq (ef: forall i, IsEquiv (F.(mapCell) i))
  (ee: IsEquiv e): EX = EY.
Proof.
  apply (diagramMapEq extensionMap). intros [i|].
  - now exact (ef i).
  - now exact ee.
Defined.
End Extension.

(** A comparison with equivalences below the top rank identifies a diagram
    with the extension specified by its transported boundary. *)
Definition extensionEqFromBoundaryMap {A: HSet} {n}
  {X: Diagram A (S n)} {Y: Diagram A n}
  (F: DiagramMap (truncateDiagram X) Y) {T: HGpd}
  (e: Equiv T (cells X None)) (b: T -> MatchingObject Y)
  (h: forall t, mapMatching F (matchingMap X (e t)) = b t)
  (ef: forall i, IsEquiv (F.(mapCell) i)):
  extendByMatchingMap A Y T b = X.
Proof.
  pose (hi := fun x =>
    f_equal (fun z => mapMatching F (matchingMap X z)) (eq_sym (secEq e x))
      • h (invEq e x)).
  now exact (eq_sym (extensionMapEq F (invEq e) (matchingMap X) b hi ef
      (symEquiv e).(eqvIsEquiv)) • extendBoundaryEq X).
Defined.

Definition extensionEqFromDiagramMap {A: HSet} {n}
  {X Y: Diagram A (S n)} (F: DiagramMap X Y) {T: HGpd}
  (e: Equiv T (cells X None)) (b: T -> MatchingObject (truncateDiagram Y))
  (h: forall t, matchingMap Y (F.(mapCell) None (e t)) = b t)
  (ef: forall i, IsEquiv (F.(mapCell) (Some i))):
  extendByMatchingMap A (truncateDiagram Y) T b = X :=
  extensionEqFromBoundaryMap (truncateMap F) e b
    (fun t => mapBoundary F (e t) • h t) ef.

(** Composition retains the components and pastes the chosen naturality paths. *)
Local Lemma mapCompositionPasting {T: Type} {a b c d e f g h: T}
  (p: a = b) (q: b = c) (r: c = d) (s: d = e)
  (u: c = f) (v: f = g) (w: g = e) (t: b = h) (z: h = f)
  (first: r • s = u • (v • w)) (second: q • u = t • z):
  (p • (q • r)) • s = (p • t) • ((z • v) • w).
Proof.
  rewrite (eqTransAssoc p (q • r) s), (eqTransAssoc q r s), first.
  rewrite <- (eqTransAssoc q u (v • w)), second.
  rewrite (eqTransAssoc t z (v • w)), <- (eqTransAssoc p t (z • (v • w))).
  now rewrite <- (eqTransAssoc z v w).
Defined.

Definition composeDiagramMap {A: HSet} {n: nat} {X Y Z: Diagram A n}
  (F: DiagramMap X Y) (G: DiagramMap Y Z): DiagramMap X Z.
Proof.
  refine (@Build_DiagramMap A n X Z
    (fun i x => G.(mapCell) i (F.(mapCell) i x))
    (fun i j f x => f_equal (G.(mapCell) i) (F.(mapNatural) (i := i) (j := j) f x)
      • G.(mapNatural) (i := i) (j := j) f (F.(mapCell) j x)) _ _).
  - intros i x.
    refine (eq_sym (f_equal_compose (F.(mapCell) i) (G.(mapCell) i) (restrictId X i x)) • _).
    refine (f_equal (fun p => f_equal (G.(mapCell) i) p) (F.(mapUnit) i x) • _).
    refine (@eq_trans_map_distr _ _ _ _ _ (G.(mapCell) i)
      (F.(mapNatural) (i := i) (j := i) (wid (rank i)) x)
      (restrictId Y i (F.(mapCell) i x)) • _).
    refine (transCongL _ (G.(mapUnit) i (F.(mapCell) i x)) • _).
    now symmetry; apply eqTransAssoc.
  - intros i j k f g x.
    refine (transCongR (eq_sym (f_equal_compose (F.(mapCell) i) (G.(mapCell) i)
      (restrictComp X (i := i) (j := j) (k := k) f g x))) _ • _).
    refine (eq_sym (eqTransAssoc _ _ _) • _).
    refine (transCongR (eq_sym (@eq_trans_map_distr _ _ _ _ _ (G.(mapCell) i)
      (f_equal (F.(mapCell) i) (restrictComp X (i := i) (j := j) (k := k) f g x))
      (F.(mapNatural) (i := i) (j := k) (wcomp g f) x))) _ • _).
    refine (transCongR (f_equal (fun p => f_equal (G.(mapCell) i) p)
      (F.(mapComp) (i := i) (j := j) (k := k) f g x)) _ • _).
    rewrite 3 eq_trans_map_distr.
    eapply mapCompositionPasting.
    + now exact (G.(mapComp) (i := i) (j := j) (k := k) f g (F.(mapCell) k x)).
    + refine (transCongR
        (f_equal_compose (restrict Y (i := i) (j := j) f) (G.(mapCell) i)
          (F.(mapNatural) (i := j) (j := k) g x)) _ • _).
      refine (homotopyNat
        (fun y => G.(mapCell) i (restrict Y (i := i) (j := j) f y))
        (fun y => restrict Z (i := i) (j := j) f (G.(mapCell) j y))
        (G.(mapNatural) (i := i) (j := j) f)
        (F.(mapNatural) (i := j) (j := k) g x) • _).
      now exact (transCongL _ (eq_sym
        (f_equal_compose (G.(mapCell) j) (restrict Z (i := i) (j := j) f)
          (F.(mapNatural) (i := j) (j := k) g x)))).
Defined.

