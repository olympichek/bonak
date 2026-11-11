(** Strictification of matching sequences. The completion of matching
    sequences of strict groupoids is the completion of strict diagrams on
    the semi-shape category, transported along the equivalences between
    matching sequences and presheaves. It is merely surjective exactly
    when sets cover 1-types. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Truncation.
From Bonak.Presheaf.Strictification Require Import DiagramCompletion
  Strictification Transport.
From Bonak.Reedy Require Import MatchingSystem.
From Bonak.Reedy.StrictGpd Require Import Reedy.
From Bonak.Reedy.Gpd Require Import Reedy.
From Bonak.Reedy.PresheafEquiv.StrictGpd Require Import Correspondence.
From Bonak.Reedy.PresheafEquiv.Gpd Require Import Correspondence.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module ReedyStrictification (Tr: PropositionalTruncation)
  (Complete: CompletionDiagramsSig Tr).
  Import Tr.
  Module Presheaf := PresheafStrictification Tr Complete.
  Module Covers := Presheaf.Covers.
  Module CT := CompletionTransport Tr.

  Definition completeMatchingSeq (arity: HSet):
    MatchingSeq (strictGpdSystem arity) -> MatchingSeq (gpdSystem arity) :=
    CT.transportMap (matchingSeqEquivFunctor arity)
      (matchingSeqEquivPseudofunctor arity) Complete.completeDiagram.

  Definition completeMatchingSeqSurjectiveCoverEquiv (arity: HSet):
    Equiv (forall Q: MatchingSeq (gpdSystem arity),
      merely {P: MatchingSeq (strictGpdSystem arity) &T
        completeMatchingSeq arity P = Q})
      Covers.SetsCover1Types :=
    compEquiv (CT.transportMapSurjectiveEquiv (matchingSeqEquivFunctor arity)
      (matchingSeqEquivPseudofunctor arity) Complete.completeDiagram)
      (Presheaf.completeDiagramSurjectiveCoverEquiv arity).
End ReedyStrictification.
