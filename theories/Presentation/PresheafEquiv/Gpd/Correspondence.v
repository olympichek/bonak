(** Groupoid-valued face presentations are equivalent to pseudofunctors
    from the locally discrete opposite ν-semi-shape category to [HGpdBicat].

    The inverse translations restrict to generating cofaces and interpret
    faces along words. [ofToPseudofunctor] and [toOfPseudofunctor] identify
    their composites with the identity. The family of levels is preserved
    definitionally in both directions. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation.

From Bonak.Lib Require Import Equiv.
From Bonak Require Import Univalence.

From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Bicategory LocallyDiscrete Pseudofunctor.
From Bonak.Category Require Import Groupoid.
From Bonak.Category.Bicategory Require Import HGpdUniv.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presentation.PresheafEquiv.Gpd Require Export Roundtrip.

From Bonak.Category.Bicategory Require Import HGpdBicat.
From Bonak.Category.Bicategory Require Import Groupoids.

Set Primitive Projections.
Set Printing Projections.

Section CorrespondenceGpd.
Context (A: HSet).

Definition pshGpdEquivPsf:
  Equiv (νGpdPresentation A) (Pseudofunctor (locallyDiscrete (Op (νSemiShape A))) HGpdBicat) :=
  qinvEquiv (toPseudofunctor A) (ofPseudofunctor A)
    (ofToPseudofunctor A) (toOfPseudofunctor A).

End CorrespondenceGpd.

(** The groupoid-level correspondence as an equality of types, by
    univalence. *)

Definition pshGpdEqPsf (A: HSet):
  νGpdPresentation A = Pseudofunctor (locallyDiscrete (Op (νSemiShape A))) HGpdBicat :=
  ua (pshGpdEquivPsf A).

(** The same correspondence with the target read as the bicategory of
    univalent groupoids, through the identification of the two targets. *)

Definition pshGpdEqPsfGpd (A: HSet):
  νGpdPresentation A = Pseudofunctor (locallyDiscrete (Op (νSemiShape A))) UnivGpdBicat :=
  pshGpdEqPsf A
  • f_equal (fun T: Bicategory => Pseudofunctor (locallyDiscrete (Op (νSemiShape A))) T) hgpdBicatEqUnivGpdBicat.

(** The augmented semi-simplicial and semi-cubical instances. *)

Definition simplicialPresheafGpdEqPsf:
  AugmentedSemiSimplicialGpdPresentation
  = Pseudofunctor (locallyDiscrete (Op (νSemiShape hunit))) HGpdBicat :=
  pshGpdEqPsf hunit.

Definition cubicalPresheafGpdEqPsf:
  SemiCubicalGpdPresentation = Pseudofunctor (locallyDiscrete (Op (νSemiShape hbool))) HGpdBicat :=
  pshGpdEqPsf hbool.

Definition simplicialPresheafGpdEqPsfGpd:
  AugmentedSemiSimplicialGpdPresentation
  = Pseudofunctor (locallyDiscrete (Op (νSemiShape hunit))) UnivGpdBicat :=
  pshGpdEqPsfGpd hunit.

Definition cubicalPresheafGpdEqPsfGpd:
  SemiCubicalGpdPresentation = Pseudofunctor (locallyDiscrete (Op (νSemiShape hbool))) UnivGpdBicat :=
  pshGpdEqPsfGpd hbool.
