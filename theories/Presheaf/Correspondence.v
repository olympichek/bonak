(** The equivalence between face presentations and set-valued functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet.
From Bonak.Lib Require Import Equiv Univalence.
From Bonak.Category Require Import Category HSetCat CategoryEq.
From Bonak.Presheaf Require Import SemiSimplicialShape.
From Bonak.Presheaf Require Export Roundtrip.

Set Primitive Projections.
Set Printing Projections.

Section Correspondence.

Definition pshEquivFunctor:
  Equiv SSSetPresentation (Functor (Op SemiSimplicialShape) HSetCat) :=
  qinvEquiv toFunctor ofFunctor ofToFunctor toOfFunctor.

End Correspondence.

(** The set-level correspondence as an equality of types, by univalence. *)

Definition pshEqFunctor:
  SSSetPresentation = Functor (Op SemiSimplicialShape) HSetCat :=
  ua pshEquivFunctor.

(** The correspondence for augmented semi-simplicial sets. *)

Definition simplicialPresheafEqFunctor:
  AugmentedSemiSimplicialPresentation =
  Functor (Op SemiSimplicialShape) HSetCat := pshEqFunctor.
