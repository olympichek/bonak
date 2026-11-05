(** Diagrams of homotopy groupoids on the semi-shape category and their
    homotopy matching objects. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Notation RewLemmas FinitePrefix HGpd.
From Bonak.Category Require Import Category Full.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy Require Export MatchingSystem.

Set Primitive Projections.
Set Printing Projections.

Definition PrefixCategory (A: HSet) (n: nat): Category :=
  fullCategory (Op (νSemiShape A)) (@rank n).

Definition Diagram (A: HSet) (n: nat): Type :=
  PathDiagramFamily (PrefixCategory A n).

Definition cells {A n} (X: Diagram A n) (i: Index n): HGpd := X.(pfObj) i.
Definition diagramData {A n} (X: Diagram A n) := pathData _ _ X.(pfStr).

Definition restrict {A n} (X: Diagram A n) {i j}
  (f: Word A (rank i) (rank j)): cells X j -> cells X i :=
  (diagramData X).(phom) f.

Definition restrictId {A n} (X: Diagram A n) i (x: cells X i):
  restrict X (wid (rank i)) x = x := pidPt (diagramData X) i x.

Definition restrictComp {A n} (X: Diagram A n) {i j k}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)) (x: cells X k):
  restrict X f (restrict X g x) = restrict X (wcomp g f) x :=
  (diagramData X).(pcomp) g f x.

Section Matching.
Context {A: HSet} {n: nat} (X: Diagram A n).

Definition MatchingValues: HGpd :=
  gforall (i: Index n) (f: Word A (rank i) n), cells X i.

Definition MatchingPaths (b: MatchingValues): HSet :=
  hforall (i j: Index n) (f: Word A (rank i) (rank j))
    (g: Word A (rank j) n),
    hpaths (restrict X f (b j g)) (b i (wcomp g f)).

Definition MatchingUnit {b: MatchingValues} (p: MatchingPaths b): HSet :=
  hforall (i: Index n) (g: Word A (rank i) n),
    hEq (p i i (wid (rank i)) g)
      (restrictId X i (b i g) • eq_sym (f_equal (b i) (wcompIdr g))).

Definition MatchingComp {b: MatchingValues} (p: MatchingPaths b): HSet :=
  hforall (i j k: Index n) (f: Word A (rank i) (rank j))
    (g: Word A (rank j) (rank k)) (h: Word A (rank k) n),
    @hEq (hpaths (restrict X f (restrict X g (b k h)))
      (b i (wcomp h (wcomp g f))))
      (f_equal (restrict X f) (p j k g h)
      • (p i j f (wcomp h g) • f_equal (b i) (eq_sym (wcompAssoc h g f))))
      (restrictComp X f g (b k h) • p i k (wcomp g f) h).

Definition MatchingLaws {b: MatchingValues} (p: MatchingPaths b): HSet :=
  hsigT (A := MatchingUnit p) (fun _ => MatchingComp p).

(** The matching object is a pseudolimit over the proper faces. Comparison
    paths are retained. Their unit and associativity equations are propositions
    because each cell type is a homotopy groupoid. *)
Definition MatchingObject: HGpd :=
  gsigT (A := MatchingValues) (fun b =>
    hgpdOfHSet (hsigT (A := MatchingPaths b) (fun p => MatchingLaws p))).

Definition matchingValue (b: MatchingObject) (i: Index n)
  (f: Word A (rank i) n): cells X i := b.1 i f.

Definition matchingPath (b: MatchingObject) {i j}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  restrict X f (matchingValue b j g) = matchingValue b i (wcomp g f) :=
  b.2.1 i j f g.

Definition matchingUnit (b: MatchingObject) (i: Index n) (g: Word A (rank i) n):
  matchingPath b (wid (rank i)) g
    = restrictId X i (matchingValue b i g)
      • eq_sym (f_equal (matchingValue b i) (wcompIdr g)) := b.2.2.1 i g.

Definition matchingComp (b: MatchingObject) {i j k}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (h: Word A (rank k) n):
  f_equal (restrict X f) (matchingPath b g h)
    • (matchingPath b f (wcomp h g)
      • f_equal (matchingValue b i) (eq_sym (wcompAssoc h g f)))
    = restrictComp X f g (matchingValue b k h)
      • matchingPath b (wcomp g f) h := b.2.2.2 i j k f g h.

Local Lemma matchingUnitHProp {b: MatchingValues} (p: MatchingPaths b):
  IsHProp (MatchingUnit p).
Proof.
  intros u v. apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro g.
  now apply (cells X i).(GUIP).
Defined.

Local Lemma matchingCompHProp {b: MatchingValues} (p: MatchingPaths b):
  IsHProp (MatchingComp p).
Proof.
  intros u v. apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply functional_extensionality_dep; intro k.
  apply functional_extensionality_dep; intro f.
  apply functional_extensionality_dep; intro g.
  apply functional_extensionality_dep; intro h.
  now apply (cells X i).(GUIP).
Defined.

Local Lemma matchingLawsHProp {b: MatchingValues} (p: MatchingPaths b):
  IsHProp (MatchingLaws p).
Proof.
  intros [u v] [u' v'].
  destruct (matchingUnitHProp p u u').
  apply f_equal. now apply matchingCompHProp.
Defined.

(** Boundary equality preserves both the face values and their comparison
    paths. Only the proofs of the coherence equations are discarded. *)
Lemma matchingExt (b c: MatchingObject) (e: b.1 = c.1)
  (p: rew [MatchingPaths] e in b.2.1 = c.2.1): b = c.
Proof.
  destruct b as [b [bp bl]], c as [c [cp cl]]; cbn in e, p.
  destruct e. cbn in p. destruct p.
  now destruct (matchingLawsHProp bp bl cl).
Defined.

End Matching.

Arguments matchingValue {A n X} b i f.
Arguments matchingPath {A n X} b {i j} f g.
Arguments matchingUnit {A n X} b i g.
Arguments matchingComp {A n X} b {i j k} f g h.

Definition truncateDiagram {A n} (X: Diagram A (S n)): Diagram A n.
Proof.
  refine (@Build_PathDiagramFamily (PrefixCategory A n)
    (fun i: Index n => cells X (Some i)) _).
  refine (@Build_PathDiagram (PrefixCategory A n)
    (fun i: Index n => cells X (Some i))
    (@Build_PathDiagramData (PrefixCategory A n)
      (fun i: Index n => cells X (Some i))
      (fun i j f => restrict X (i := Some j) (j := Some i) f)
      (fun i => (diagramData X).(pid) (Some i))
      (fun i j k f g => (diagramData X).(pcomp)
        (a := Some i) (b := Some j) (c := Some k) f g)) _ _ _).
  - now intros i j f; exact ((pathUnitL _ _ X.(pfStr)) (Some i) (Some j) f).
  - now intros i j f; exact ((pathUnitR _ _ X.(pfStr)) (Some i) (Some j) f).
  - now intros i j k l f g h;
      exact ((pathAssoc _ _ X.(pfStr)) (Some i) (Some j) (Some k) (Some l) f g h).
Defined.

(** Restricting a top cell supplies the boundary comparisons. Their laws
    are the pointwise unit and associativity laws of the diagram. *)
Definition matchingMap {A n} (X: Diagram A (S n)) (x: cells X None):
  MatchingObject (truncateDiagram X).
Proof.
  exists (fun i f => restrict X (i := Some i) (j := None) f x).
  exists (fun i j f g => restrictComp X (i := Some i) (j := Some j)
    (k := None) f g x).
  split.
  - intros i g.
    now exact (pcompUnitRPt (diagramData X) (pathUnitR _ _ X.(pfStr))
      None (Some i) g (wcompIdr g) x).
  - intros i j k f g h.
    now exact (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr))
      None (Some k) (Some j) (Some i) h g f (eq_sym (wcompAssoc h g f)) x).
Defined.

Definition emptyDiagram (A: HSet): Diagram A 0.
Proof.
  refine (@Build_PathDiagramFamily (PrefixCategory A 0)
    (fun _ => gunit)
    (@Build_PathDiagram (PrefixCategory A 0) (fun _ => gunit)
      (@Build_PathDiagramData (PrefixCategory A 0) (fun _ => gunit)
        (fun _ _ _ x => x) (fun _ => eq_refl)
        (fun _ _ _ _ _ _ => eq_refl)) _ _ _));
    now intros [].
Defined.

Section Construction.
Context (A: HSet).

Definition matchingMapCells {n} (X: Diagram A n) (T: HGpd)
  (i: Index (S n)): HGpd :=
  match i with Some i => cells X i | None => T end.

Definition matchingMapRestrict {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X) (i j: Index (S n)):
  Word A (rank i) (rank j) -> matchingMapCells X T j -> matchingMapCells X T i.
Proof.
  destruct i as [i|], j as [j|]; cbn.
  - now exact (@restrict A n X i j).
  - now exact (fun f x => matchingValue (b x) i f).
  - intro f. now wordAboveAbsurd.
  - now exact (fun _ x => x).
Defined.

Local Definition topComposite (n: nat) (g: Word A n n) {k}
  (f: Word A k n): wcomp g f = f :=
  f_equal (fun u => wcomp u f) (wordEndId n g) • wcompIdl f.

Definition matchingMapComp {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X) (i j k: Index (S n))
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: matchingMapCells X T k):
  matchingMapRestrict X T b i j f (matchingMapRestrict X T b j k g x)
  = matchingMapRestrict X T b i k (wcomp g f) x.
Proof.
  destruct i as [i|], j as [j|], k as [k|]; cbn [matchingMapRestrict];
    try now wordAboveAbsurd.
  - now exact (restrictComp X f g x).
  - now exact (matchingPath (b x) f g).
  - refine (f_equal (matchingValue (b x) i) (eq_sym _)).
    now exact (topComposite n g f).
  - now reflexivity.
Defined.

Definition matchingMapData {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramData (PrefixCategory A (S n))
    (matchingMapCells X T).
Proof.
  refine (@Build_PathDiagramData (PrefixCategory A (S n))
    (matchingMapCells X T)
    (fun i j f => matchingMapRestrict X T b j i f) _
    (fun i j k f g => matchingMapComp X T b k j i g f)).
  intros [i|].
  - now exact ((pathData _ _ X.(pfStr)).(pid) i).
  - now reflexivity.
Defined.

Local Lemma matchingMapUnitLPointwise {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramUnitL _ _ (matchingMapData X T b).
Proof.
  apply pathDiagramUnitLOfPt.
  intros [i|] [j|] f x; try now wordAboveAbsurd.
  - now exact (pcompUnitLPt (diagramData X) (pathUnitL _ _ X.(pfStr))
      i j f (wcompIdl f) x).
  - change (f_equal (matchingValue (b x) j)
      (eq_sym (f_equal (fun u => wcomp u f) (wordEndId n (wid n)) • wcompIdl f))
      = eq_refl • eq_sym (f_equal (matchingValue (b x) j) (wcompIdl f))).
    rewrite ((wordSet n n).(UIP) (h := wordEndId n (wid n)) (g := eq_refl)).
    cbn [f_equal]. rewrite 2 eq_trans_refl_l, fEqualSym.
    now reflexivity.
  - change (eq_refl = eq_refl •
      eq_sym (f_equal (fun _: Word A n n => x) (wcompIdl f))).
    rewrite fEqualConst. now reflexivity.
Defined.

Local Lemma matchingMapUnitRPointwise {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramUnitR _ _ (matchingMapData X T b).
Proof.
  apply pathDiagramUnitROfPt.
  intros [i|] [j|] f x; try now wordAboveAbsurd.
  - now exact (pcompUnitRPt (diagramData X) (pathUnitR _ _ X.(pfStr))
      i j f (wcompIdr f) x).
  - now exact (matchingUnit (b x) j f).
  - change (eq_refl = eq_refl •
      eq_sym (f_equal (fun _: Word A n n => x) (wcompIdr f))).
    rewrite fEqualConst. now reflexivity.
Defined.

Local Lemma matchingPathNaturality {n} (X: Diagram A n)
  (b: MatchingObject X) {i j} (f: Word A (rank i) (rank j))
  {g h: Word A (rank j) n} (e: g = h):
  f_equal (restrict X f) (f_equal (matchingValue b j) e)
    • matchingPath b f h
  = matchingPath b f g
    • f_equal (matchingValue b i) (f_equal (fun w => wcomp w f) e).
Proof. destruct e. now exact (eq_trans_refl_l _). Defined.

Local Lemma matchingMapAssocPointwise {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramAssoc _ _ (matchingMapData X T b).
Proof.
  apply pathDiagramAssocOfPt.
  intros [i|] [j|] [k|] [l|] f g h x; try now wordAboveAbsurd.
  - now exact (pcompAssocPt (diagramData X) (pathAssoc _ _ X.(pfStr))
      i j k l f g h (eq_sym (wcompAssoc f g h)) x).
  - now exact (matchingComp (b x) h g f).
  - change (f_equal (restrict X h)
      (f_equal (matchingValue (b x) k) (eq_sym (topComposite n f g)))
      • (matchingPath (b x) h (wcomp f g)
        • f_equal (matchingValue (b x) l) (eq_sym (wcompAssoc f g h)))
      = matchingPath (b x) h g
        • f_equal (matchingValue (b x) l) (eq_sym (topComposite n f (wcomp g h)))).
    rewrite <- eqTransAssoc, matchingPathNaturality, eqTransAssoc.
    rewrite <- eq_trans_map_distr.
    apply f_equal. apply f_equal. now apply (wordSet _ _).(UIP).
  - change (eq_refl •
      (f_equal (matchingValue (b x) l) (eq_sym (topComposite n (wcomp f g) h))
        • f_equal (matchingValue (b x) l) (eq_sym (wcompAssoc f g h)))
      = f_equal (matchingValue (b x) l) (eq_sym (topComposite n g h))
        • f_equal (matchingValue (b x) l) (eq_sym (topComposite n f (wcomp g h)))).
    rewrite eq_trans_refl_l, <- 2 eq_trans_map_distr.
    apply f_equal. now apply (wordSet _ _).(UIP).
  - change (eq_refl • (eq_refl •
      f_equal (fun _: Word A n n => x) (eq_sym (wcompAssoc f g h)))
      = eq_refl • eq_refl).
    rewrite fEqualConst. now reflexivity.
Defined.

(** Keeping the original law proofs on earlier ranks makes truncation of
    an extension definitionally equal to its input diagram. *)
Definition matchingMapUnitL {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramUnitL _ _ (matchingMapData X T b).
Proof.
  intros [i|] [j|] f.
  - now exact (pathUnitL _ _ X.(pfStr) i j f).
  - now exact (matchingMapUnitLPointwise X T b (Some i) None f).
  - now exact (matchingMapUnitLPointwise X T b None (Some j) f).
  - now exact (matchingMapUnitLPointwise X T b None None f).
Defined.

Definition matchingMapUnitR {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramUnitR _ _ (matchingMapData X T b).
Proof.
  intros [i|] [j|] f.
  - now exact (pathUnitR _ _ X.(pfStr) i j f).
  - now exact (matchingMapUnitRPointwise X T b (Some i) None f).
  - now exact (matchingMapUnitRPointwise X T b None (Some j) f).
  - now exact (matchingMapUnitRPointwise X T b None None f).
Defined.

Definition matchingMapAssoc {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X):
  PathDiagramAssoc _ _ (matchingMapData X T b).
Proof.
  intros [i|] [j|] [k|] [l|] f g h;
    try (now exact (pathAssoc _ _ X.(pfStr) i j k l f g h));
    now apply matchingMapAssocPointwise.
Defined.

Definition extendByMatchingMap {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X): Diagram A (S n) :=
  @Build_PathDiagramFamily (PrefixCategory A (S n)) (matchingMapCells X T)
    (@Build_PathDiagram (PrefixCategory A (S n)) (matchingMapCells X T)
      (matchingMapData X T b) (matchingMapUnitL X T b)
      (matchingMapUnitR X T b) (matchingMapAssoc X T b)).

Definition gpdSystem: MatchingSystem := {|
  matchingStages := {|
    PartialDiagram := Diagram A;
    truncate n := @truncateDiagram A n;
    emptyPartial := emptyDiagram A;
  |};
  Cell := HGpd;
  CellMap T B := T -> B;
  CellFamily B := B -> HGpd;
  familyTotal B E := hgpdTotalMap B E;
  Matching n X := MatchingObject X;
  extendByMap n := extendByMatchingMap;
|}.

End Construction.

Definition AugmentedSemiSimplicialGpdMatchingSeq := MatchingSeq (gpdSystem hunit).
Definition SemiCubicalGpdMatchingSeq := MatchingSeq (gpdSystem hbool).
