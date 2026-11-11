(** Strictification of the ν-groupoid towers. The completion of indexed
    strict ν-groupoids is the completion of matching sequences of strict
    groupoids, transported along the equivalences between the towers and
    matching sequences. It is merely surjective exactly when sets cover
    1-types. The simplicial and the cubical instance share their arity
    between the strict and the weak tower. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Truncation.
From Bonak.Presheaf.Strictification Require Import DiagramCompletion Transport.
From Bonak.Reedy Require Import Strictification.
From Bonak.Indexed.StrictGpd Require Import Layer νStrictGpd.
From Bonak.Indexed.Gpd Require Import Layer νGpd.
From Bonak.Indexed.ReedyEquiv.StrictGpd Require ReedyCorrespondence.
From Bonak.Indexed.ReedyEquiv.Gpd Require ReedyCorrespondence.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module IndexedStrictification (Tr: PropositionalTruncation)
  (Complete: CompletionDiagramsSig Tr).
  Import Tr.
  Module Reedy := ReedyStrictification Tr Complete.
  Module Covers := Reedy.Covers.
  Module CT := CompletionTransport Tr.

  Module Simplicial.
    Local Abbreviation strictEquiv :=
      StrictGpd.ReedyCorrespondence.ReedyCorrespondenceSimplicial.νStrictGpdsEquivMatchingSeq.
    Local Abbreviation weakEquiv :=
      ReedyEquiv.Gpd.ReedyCorrespondence.ReedyCorrespondenceSimplicial.νGpdsEquivMatchingSeq.

    Definition completeνStrictGpds:
      νStrictGpdSimplicial.νStrictGpds -> νGpdSimplicial.νGpds :=
      CT.transportMap strictEquiv weakEquiv
        (Reedy.completeMatchingSeq SimplicialLayer.arity).

    Definition completeνStrictGpdsSurjectiveCoverEquiv:
      Equiv (forall Q: νGpdSimplicial.νGpds,
        merely {P: νStrictGpdSimplicial.νStrictGpds &T completeνStrictGpds P = Q})
        Covers.SetsCover1Types :=
      compEquiv
        (CT.transportMapSurjectiveEquiv strictEquiv weakEquiv
          (Reedy.completeMatchingSeq SimplicialLayer.arity))
        (Reedy.completeMatchingSeqSurjectiveCoverEquiv SimplicialLayer.arity).
  End Simplicial.

  Module Cubical.
    Local Abbreviation strictEquiv :=
      StrictGpd.ReedyCorrespondence.ReedyCorrespondenceCubical.νStrictGpdsEquivMatchingSeq.
    Local Abbreviation weakEquiv :=
      ReedyEquiv.Gpd.ReedyCorrespondence.ReedyCorrespondenceCubical.νGpdsEquivMatchingSeq.

    Definition completeνStrictGpds:
      νStrictGpdCubical.νStrictGpds -> νGpdCubical.νGpds :=
      CT.transportMap strictEquiv weakEquiv
        (Reedy.completeMatchingSeq CubicalLayer.arity).

    Definition completeνStrictGpdsSurjectiveCoverEquiv:
      Equiv (forall Q: νGpdCubical.νGpds,
        merely {P: νStrictGpdCubical.νStrictGpds &T completeνStrictGpds P = Q})
        Covers.SetsCover1Types :=
      compEquiv
        (CT.transportMapSurjectiveEquiv strictEquiv weakEquiv
          (Reedy.completeMatchingSeq CubicalLayer.arity))
        (Reedy.completeMatchingSeqSurjectiveCoverEquiv CubicalLayer.arity).
  End Cubical.
End IndexedStrictification.
