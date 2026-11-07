(** Matching sequences of strict groupoids classify functors into them. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Equiv Univalence SequentialLimit.
From Bonak.Category Require Import SequentialFunctor.
From Bonak.Category.Groupoid Require Import Strict.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.StrictGpd Require Import Reedy Extension.

Set Primitive Projections.
Set Printing Projections.

Section Comparison.
Context (A: HSet).

Definition diagramFunctor {n} (X: Diagram A n):
  FunctorPrefix (Op (νSemiShape A)) StrictGroupoidCat (fun n => n) n := {|
  fobj := X.(cells); fhom i j f := X.(restrict) f;
  fid i := X.(restrictId) i;
  fcomp i j k f g := eq_sym (X.(restrictComp) g f);
|}.

Definition functorDiagram {n}
  (F: FunctorPrefix (Op (νSemiShape A)) StrictGroupoidCat (fun n => n) n):
  Diagram A n := {|
  cells := F.(fobj); restrict i j f := F.(fhom) (a := j) (b := i) f;
  restrictId i := F.(fid) i;
  restrictComp i j k f g := eq_sym (F.(fcomp) g f);
|}.

Definition diagramEquivFunctor n:
  Equiv (Diagram A n)
    (FunctorPrefix (Op (νSemiShape A)) StrictGroupoidCat (fun n => n) n).
Proof.
  refine (qinvEquiv diagramFunctor functorDiagram _ _).
  - intro X. now exact (diagramEq A (functorDiagram (diagramFunctor X)) X eq_refl eq_refl).
  - intro F. apply (functorEq (diagramFunctor (functorDiagram F)) F eq_refl). now intros.
Defined.

Definition diagramLimitEquivFunctor:
  Equiv (SequentialLimit (Diagram A) (fun n => @truncateDiagram A n))
    (Functor (Op (νSemiShape A)) StrictGroupoidCat).
Proof.
  refine (compEquiv (sequentialLimitEquiv (fun n => @truncateDiagram A n)
    (fun n => @truncateFunctor (Op (νSemiShape A)) StrictGroupoidCat (fun n => n) n)
    diagramEquivFunctor (fun _ _ => eq_refl)) _).
  now exact (compEquiv
    (finiteFunctorLimitEquiv (Op (νSemiShape A)) StrictGroupoidCat (fun n => n))
    (fullShapeFunctorEquiv A StrictGroupoidCat)).
Defined.

Definition matchingSeqEquivFunctor:
  Equiv (MatchingSeq (strictGpdSystem A))
    (Functor (Op (νSemiShape A)) StrictGroupoidCat) :=
  compEquiv (matchingSeqEquivDiagramLimit (strictGpdSystem A)
    (matchingExtensionLaws (strictGpdSystem A) (strictGpdLaws A)))
    diagramLimitEquivFunctor.

Definition matchingSeqEqFunctor:
  MatchingSeq (strictGpdSystem A) = Functor (Op (νSemiShape A)) StrictGroupoidCat :=
  ua matchingSeqEquivFunctor.

End Comparison.

Definition simplicialMatchingSeqEqFunctor:
  AugmentedSemiSimplicialStrictGpdMatchingSeq
  = Functor (Op (νSemiShape hunit)) StrictGroupoidCat :=
  matchingSeqEqFunctor hunit.

Definition cubicalMatchingSeqEqFunctor:
  SemiCubicalStrictGpdMatchingSeq
  = Functor (Op (νSemiShape hbool)) StrictGroupoidCat :=
  matchingSeqEqFunctor hbool.
