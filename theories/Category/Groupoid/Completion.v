Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Category Groupoid HSetCat UnivalenceFacts FunctorUnivalence
  Yoneda Completion.
From Bonak.Category.Groupoid Require Import WeakEquivalence.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Import PathGroupoid.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** The Rezk completion of a groupoid is again a groupoid: invertibility
    descends from represented arrows through mere representability. *)
Module GroupoidCompletion (T: PropositionalTruncation).
  Import T.
  Module W := WeakEquivalences T.
  Import W W.TF.
  Set Universe Polymorphism.

  Module Base := CategoryCompletion T.

  Definition completionCategory (G: Groupoid): Category := Base.completionCategory G.
  Definition completionUnivalence (G: Groupoid):
    IsUnivalentCategory (completionCategory G) := Base.completionUnivalence G.

  Definition representedArrowInvertible (G: Groupoid)
    (P Q: Functor (Op G) HSetCat) (a b: G.(CObj))
    (i: Iso (functorCategory (Op G) HSetCat) (representable G a) P)
    (j: Iso (functorCategory (Op G) HSetCat) (representable G b) Q)
    (α: NatTrans P Q): @IsInvertible (functorCategory (Op G) HSetCat) P Q α.
  Proof.
    destruct (categoryIsoPath (functorCategoryUnivalence hsetCategoryUnivalence) i).
    destruct (categoryIsoPath (functorCategoryUnivalence hsetCategoryUnivalence) j).
    rewrite <- (yonedaEvaluateSec α).
    now exact (functorIso (yoneda G)
      (@Build_Iso G a b (yonedaEvaluate α)
        (G.(groupoidInvertibility) a b (yonedaEvaluate α)))).(isoInvertible).
  Defined.

  Definition completionInvertibility (G: Groupoid): IsGroupoid (completionCategory G).
  Proof.
    intros [P p] [Q q] α.
    assert (i: @IsInvertible (functorCategory (Op G) HSetCat) P Q α).
    { refine (trRec (@isInvertibleProp _ _ _ _) _ p).
      intros [a u]. refine (trRec (@isInvertibleProp _ _ _ _) _ q).
      intros [b v]. now exact (representedArrowInvertible G P Q a b u v α). }
    now exact (@Build_IsInvertible (completionCategory G) (P; p) (Q; q) α
      (inverse i) (inverseR i) (inverseL i)).
  Defined.

  Definition completion (G: Groupoid): UnivalentGroupoid :=
    {| underlyingGroupoid := {| gcat := completionCategory G;
         groupoidInvertibility := completionInvertibility G |};
       groupoidUnivalence := completionUnivalence G |}.

  Definition completionUnit (G: Groupoid): Functor G (completion G) :=
    Base.completionUnit G.

  Definition completionUnitWeak (G: Groupoid): IsWeakEquivalence (completionUnit G).
  Proof.
    refine (@Build_IsWeakEquivalence G (completion G) (completionUnit G)
      (yonedaFullyFaithful G) _).
    intros [P p]. refine (trMap _ p).
    intros [a i]. now exact (a; i.(isoHom)).
  Defined.
End GroupoidCompletion.

Unset Universe Minimization ToSet.

(** Univalence identifies a groupoid with the paths in its object 1-type. *)
Definition groupoidToPaths (U: UnivalentGroupoid): Functor U (pathGpd (gobj U)) := {|
  fobj a := a;
  fhom a b f := homToId f;
  fid := homToIdId;
  fcomp a b c f g := homToIdComp f g;
|}.

Definition groupoidToPathsFullyFaithful (U: UnivalentGroupoid):
  FullyFaithful (groupoidToPaths U).
Proof.
  intros a b. unshelve refine (@Build_IsEquiv _ _ _ _ _ _ _).
  - now exact (@idToHom U a b).
  - now exact (@idToHom U a b).
  - now exact (@idToHomToId U a b).
  - now exact (@homToIdToHom U a b).
Defined.

Module PathCompletion (T: PropositionalTruncation).
  Import T.
  Module C := GroupoidCompletion T.
  Import C C.W.
  Set Universe Polymorphism.

  Definition classifying@{g o h c +} (G: Groupoid@{g o h}): HGpd@{c} :=
    gobj (completion G).

  Definition completedPaths (G: Groupoid): UnivalentGroupoid :=
    pathGpd (classifying G).

  Definition pathCompletionUnit (G: Groupoid): Functor G (completedPaths G) :=
    compFunctor (completionUnit G) (groupoidToPaths (completion G)).

  Definition toPathsWeak (U: UnivalentGroupoid): IsWeakEquivalence (groupoidToPaths U).
  Proof.
    refine (@Build_IsWeakEquivalence U (pathGpd (gobj U)) (groupoidToPaths U)
      (groupoidToPathsFullyFaithful U) _).
    intro x. now exact (tr (x; eq_refl)).
  Defined.

  Definition pathCompletionUnitWeak (G: Groupoid): IsWeakEquivalence (pathCompletionUnit G) :=
    weakCompose (completionUnit G) (groupoidToPaths (completion G))
      (completionUnitWeak G) (toPathsWeak (completion G)).
End PathCompletion.
