(** Strictification of groupoid face presentations. The completion of
    strict groupoid presentations is the completion of strict diagrams on
    the semi-shape category, transported along the equivalences between
    presentations and presheaves. It is merely surjective exactly when
    sets cover 1-types. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Truncation.
From Bonak.Presheaf.Strictification Require Import DiagramCompletion
  Strictification Transport.
From Bonak.Presentation.PresheafEquiv.StrictGpd Require Import Correspondence.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Correspondence.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module PresentationStrictification (Tr: PropositionalTruncation)
  (Complete: CompletionDiagramsSig Tr).
  Import Tr.
  Module Presheaf := PresheafStrictification Tr Complete.
  Module Covers := Presheaf.Covers.
  Module CT := CompletionTransport Tr.

  Definition completePresentation (arity: HSet):
    νStrictGpdPresentation arity -> νGpdPresentation arity :=
    CT.transportMap (pshEquivFunctor arity) (pshGpdEquivPsf arity)
      Complete.completeDiagram.

  Definition completePresentationSurjectiveCoverEquiv (arity: HSet):
    Equiv (forall Q: νGpdPresentation arity,
      merely {P: νStrictGpdPresentation arity &T completePresentation arity P = Q})
      Covers.SetsCover1Types :=
    compEquiv (CT.transportMapSurjectiveEquiv (pshEquivFunctor arity)
      (pshGpdEquivPsf arity) Complete.completeDiagram)
      (Presheaf.completeDiagramSurjectiveCoverEquiv arity).
End PresentationStrictification.
