(** Matching sequences with latching lifts classify ν-shape presheaves. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Equiv Univalence SequentialLimit.
From Bonak.Category Require Import Category HSetCat SequentialFunctor.
From Bonak.Presheaf.Dgn Require Import νShape.
From Bonak.Reedy.Dgn Require Import Reedy Extension.

Set Primitive Projections.
Set Printing Projections.

Definition diagramLimitEquivFunctor (A: HSet):
  Equiv (SequentialLimit (Diagram A) (fun n => @truncateDiagram A n))
    (Functor (Op (νShape A)) HSetCat) :=
  finiteFunctorLimitEquiv (Op (νShape A)) HSetCat (fun n => n).

Definition matchingSeqEquivFunctor (A: HSet):
  Equiv (MatchingSeq (dgnSystem A)) (Functor (Op (νShape A)) HSetCat) :=
  compEquiv (matchingSeqEquivDiagramLimit (dgnSystem A) (dgnLaws A))
    (diagramLimitEquivFunctor A).

Definition matchingSeqEqFunctor (A: HSet):
  MatchingSeq (dgnSystem A) = Functor (Op (νShape A)) HSetCat :=
  ua (matchingSeqEquivFunctor A).

Definition simplicialDgnMatchingSeqEqFunctor:
  SimplicialDgnMatchingSeq = Functor (Op (νShape hunit)) HSetCat :=
  matchingSeqEqFunctor hunit.

Definition cubicalDgnMatchingSeqEqFunctor:
  CubicalDgnMatchingSeq = Functor (Op (νShape hbool)) HSetCat :=
  matchingSeqEqFunctor hbool.
