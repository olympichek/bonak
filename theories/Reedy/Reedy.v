(** H-set diagrams on the semi-shape category and their matching objects. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Univalence FinitePrefix.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy Require Export MatchingSystem.

Set Primitive Projections.
Set Printing Projections.

(** A contravariant diagram on the first [n] ranks. [restrict] is its action
    on morphisms. *)
Record Diagram {A: HSet} {n: nat} := {
  cells: Index n -> HSet;
  restrict {i j}: Word A (rank i) (rank j) -> cells j -> cells i;
  restrictId i (x: cells i): restrict (wid (rank i)) x = x;
  restrictComp {i j k} (f: Word A (rank i) (rank j))
    (g: Word A (rank j) (rank k)) (x: cells k):
    restrict f (restrict g x) = restrict (wcomp g f) x;
}.

Arguments Diagram A n : clear implicits.

Section Construction.
Context (A: HSet).

Definition matchingData {n} (X: Diagram A n): HSet :=
  hforall (i: Index n) (f: Word A (rank i) n), X.(cells) i.

(** A boundary assigns a cell to every proper face, compatibly with
    restriction along all maps between those faces. Dependent products
    and equality in h-sets keep the matching object an h-set. *)
Definition MatchingObject {n} (X: Diagram A n): HSet :=
  { b: matchingData X &
    hforall (i j: Index n) (f: Word A (rank i) (rank j))
      (g: Word A (rank j) n),
      hEq (X.(restrict) f (b j g)) (b i (wcomp g f)) }.

Lemma matchingExt {n} {X: Diagram A n} (b c: MatchingObject X)
  (H: forall i f, b.1 i f = c.1 i f): b = c.
Proof.
  destruct b as [b hb], c as [c hc]; cbn in H.
  assert (e: b = c).
  { apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro f. now apply H. }
  destruct e. apply f_equal.
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply functional_extensionality_dep; intro f.
  apply functional_extensionality_dep; intro g. now apply (X.(cells) i).(UIP).
Defined.

Definition emptyDiagram: Diagram A 0.
Proof.
  refine {| cells := fun i: Index 0 => match i with end;
    restrict := fun (i j: Index 0) => match i with end |}.
  - now intros [].
  - now intros [].
Defined.

Definition matchingMapCells {n} (X: Diagram A n) (T: HSet) (i: Index (S n)): HSet :=
  match i with Some i => X.(cells) i | None => T end.

Definition matchingMapRestrict {n} (X: Diagram A n) (T: HSet)
  (b: T -> MatchingObject X) (i j: Index (S n)):
  Word A (rank i) (rank j) -> matchingMapCells X T j -> matchingMapCells X T i.
Proof.
  destruct i as [i|], j as [j|]; cbn.
  - now exact (X.(restrict) (i := i) (j := j)).
  - now exact (fun f x => (b x).1 i f).
  - intro f. now wordAboveAbsurd.
  - now exact (fun _ x => x).
Defined.

Definition extendByMatchingMap {n} (X: Diagram A n) (T: HSet)
  (b: T -> MatchingObject X): Diagram A (S n).
Proof.
  refine {| cells := matchingMapCells X T; restrict := matchingMapRestrict X T b |}.
  - intros [i|] x; cbn [matchingMapRestrict].
    + now exact (X.(restrictId) i x).
    + now reflexivity.
  - intros [i|] [j|] [k|] f g x; cbn [matchingMapRestrict]; try now wordAboveAbsurd.
    + now exact (X.(restrictComp) f g x).
    + now exact ((b x).2 i j f g).
    + rewrite (wordEndId n g), wcompIdl. now reflexivity.
    + now reflexivity.
Defined.

Definition truncateDiagram {n} (X: Diagram A (S n)): Diagram A n := {|
  cells i := X.(cells) (Some i);
  restrict i j f := X.(restrict) (i := Some i) (j := Some j) f;
  restrictId i x := X.(restrictId) (Some i) x;
  restrictComp i j k f g x :=
    X.(restrictComp) (i := Some i) (j := Some j) (k := Some k) f g x;
|}.

Definition hsetSystem: MatchingSystem := {|
  matchingStages := {|
    PartialDiagram := Diagram A;
    truncate n := truncateDiagram;
    emptyPartial := emptyDiagram;
  |};
  Cell := HSet;
  CellMap T B := T -> B;
  CellFamily B := B -> HSet;
  familyTotal B E := hsetTotalMap B E;
  Matching n X := MatchingObject X;
  extendByMap n := extendByMatchingMap;
|}.

End Construction.

Definition AugmentedSemiSimplicialMatchingSeq := MatchingSeq (hsetSystem hunit).
Definition SemiCubicalMatchingSeq := MatchingSeq (hsetSystem hbool).
