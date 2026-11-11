(** Restriction of coherent diagrams and their transformations to finite prefixes. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet FinitePrefix.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagram Pseudonatural LocallyDiscretePseudofunctor
  PathDiagramTransformation.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy Matching.
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
