(** Strict groupoid face presentations and presheaves describe the same type. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Equiv Univalence.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presheaf.StrictGpd Require Export Roundtrip.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition pshEquivFunctor (A: HSet):
  Equiv (νStrictGpdPresentation A) (Functor (Op (νSemiShape A)) HSetGroupoidCat) :=
  qinvEquiv toFunctor ofFunctor ofToFunctor toOfFunctor.

Definition pshEqFunctor (A: HSet):
  νStrictGpdPresentation A = Functor (Op (νSemiShape A)) HSetGroupoidCat :=
  ua (pshEquivFunctor A).

Definition simplicialPresheafEqFunctor:
  AugmentedSemiSimplicialStrictGpdPresentation
  = Functor (Op (νSemiShape hunit)) HSetGroupoidCat :=
  pshEqFunctor hunit.

Definition cubicalPresheafEqFunctor:
  SemiCubicalStrictGpdPresentation = Functor (Op (νSemiShape hbool)) HSetGroupoidCat :=
  pshEqFunctor hbool.
