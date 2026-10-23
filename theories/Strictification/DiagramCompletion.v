(** Completing each level of a strict groupoid diagram gives a weak diagram
    of 1-types. The comparison cells and their coherence are inherited from
    the completion pseudofunctor. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Truncation.
From Bonak.Category Require Import Category Groupoid.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Groupoid Require Import SetBased.
From Bonak.Category.Bicategory Require Import Groupoids.
From Bonak.Category.Groupoid Require Import CompletionPseudofunctor.
From Bonak.Category.Bicategory Require Import PseudofunctorOps LocallyDiscrete Full PathGroupoid
  HGpd2Cat UnivGpd2Cat.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module CompletionDiagrams (Tr: PropositionalTruncation).
  Module C := CompletionPseudofunctor Tr.
  Module A := C.A.
  Module P := A.B.C.

  Definition completeDiagram {S: Category} (F: Functor S HSetGroupoidCat):
    Pseudofunctor (locallyDiscrete S) HGpd2Cat :=
    composePseudofunctor
      (composePseudofunctor
        (structureMapPseudofunctor (locallyDiscreteFunctor F))
        (structureMapPseudofunctor hsetGroupoidDiscreteInclusion))
      (composePseudofunctor C.completionPseudofunctor
        (composePseudofunctor
          (structureMapPseudofunctor
            (fullInclusion UnivGpd2Cat (fun G: HSetGroupoid => P.completedPaths G)))
          (structureMapPseudofunctor classify))).

  Lemma completeDiagramObj {S: Category} (F: Functor S HSetGroupoidCat) (a: S.(CObj)):
    (completeDiagram F).(psObj) a = P.classifying (F.(fobj) a).
  Proof. now apply classifyPiOne. Defined.

  Lemma completeDiagramHom {S: Category} (F: Functor S HSetGroupoidCat)
    {a b: S.(CObj)} (f: S.(CHom) a b) (x: P.classifying (F.(fobj) a)):
    (completeDiagram F).(psStr).(psData).(psHom) f x = (A.liftFunctor (F.(fhom) f)).(fobj) x.
  Proof. now reflexivity. Defined.

  Definition completeDiagramUnit {S: Category} (F: Functor S HSetGroupoidCat)
    {a b: S.(CObj)} (f: S.(CHom) a b) (x: F.(fobj) a):
    (P.pathCompletionUnit (F.(fobj) b)).(fobj) ((F.(fhom) f).(fobj) x)
    = (completeDiagram F).(psStr).(psData).(psHom) f
        ((P.pathCompletionUnit (F.(fobj) a)).(fobj) x) :=
    homToId ((A.liftUnit (F.(fhom) f)).(ncomp) x).
End CompletionDiagrams.

(** A shared completion instance keeps comparison proofs attached to the
    same completion choices as the diagram they describe. *)
Module Type CompletionDiagramsSig (Tr: PropositionalTruncation).
  Include CompletionDiagrams Tr.
End CompletionDiagramsSig.
