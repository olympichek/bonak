(** Matching sequences of h-sets classify functors into h-sets. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet Equiv Univalence SequentialLimit.
From Bonak.Category Require Import CategoryEq HSetCat SequentialFunctor.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Set Require Import Reedy Extension.

Set Primitive Projections.
Set Printing Projections.

Section Comparison.
Context (A: HSet).

Definition diagramFunctor {n} (X: Diagram A n):
  FunctorPrefix (Op (νSemiShape A)) HSetCat (fun n => n) n := {|
  fobj := X.(cells);
  fhom i j f := X.(restrict) f;
  fid i := functional_extensionality_dep _ _ (X.(restrictId) i);
  fcomp i j k f g := functional_extensionality_dep _ _
    (fun x => eq_sym (X.(restrictComp) g f x));
|}.

Definition functorDiagram {n}
  (F: FunctorPrefix (Op (νSemiShape A)) HSetCat (fun n => n) n): Diagram A n := {|
  cells := F.(fobj);
  restrict i j f := F.(fhom) (a := j) (b := i) f;
  restrictId i x := fhomIdPt F i x;
  restrictComp i j k f g x := fhomCompPt F g f x;
|}.

Definition diagramEquivFunctor n:
  Equiv (Diagram A n) (FunctorPrefix (Op (νSemiShape A)) HSetCat (fun n => n) n).
Proof.
  refine (qinvEquiv diagramFunctor functorDiagram _ _).
  - intro X. now exact (diagramEq A (functorDiagram (diagramFunctor X)) X eq_refl eq_refl).
  - intro F. apply (functorEq (diagramFunctor (functorDiagram F)) F eq_refl). now intros.
Defined.

Definition diagramLimitEquivFunctor:
  Equiv (SequentialLimit (Diagram A) (fun n => @truncateDiagram A n))
    (Functor (Op (νSemiShape A)) HSetCat).
Proof.
  refine (compEquiv (sequentialLimitEquiv (fun n => @truncateDiagram A n)
    (fun n => @truncateFunctor (Op (νSemiShape A)) HSetCat (fun n => n) n)
    diagramEquivFunctor (fun _ _ => eq_refl)) _).
  now exact (compEquiv
    (finiteFunctorLimitEquiv (Op (νSemiShape A)) HSetCat (fun n => n))
    (fullShapeFunctorEquiv A HSetCat)).
Defined.

Definition matchingSeqEquivFunctor:
  Equiv (MatchingSeq (hsetSystem A)) (Functor (Op (νSemiShape A)) HSetCat) :=
  compEquiv (matchingSeqEquivDiagramLimit (hsetSystem A)
    (matchingExtensionLaws (hsetSystem A) (hsetLaws A)))
    diagramLimitEquivFunctor.

Definition matchingSeqEqFunctor:
  MatchingSeq (hsetSystem A) = Functor (Op (νSemiShape A)) HSetCat :=
  ua matchingSeqEquivFunctor.

End Comparison.

Definition simplicialMatchingSeqEqFunctor:
  AugmentedSemiSimplicialMatchingSeq = Functor (Op (νSemiShape hunit)) HSetCat :=
  matchingSeqEqFunctor hunit.

Definition cubicalMatchingSeqEqFunctor:
  SemiCubicalMatchingSeq = Functor (Op (νSemiShape hbool)) HSetCat :=
  matchingSeqEqFunctor hbool.
