Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Category HSetCat UnivalenceFacts FunctorUnivalence Full
  Yoneda WeakEquivalence.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

Definition Representable (C: Category) (P: Functor (Op C) HSetCat): Type :=
  {a: C.(CObj) &T
    Iso (functorCategory (Op C) HSetCat) (representable C a) P}.

(** Rezk completion as the essential image of the Yoneda embedding.
    Propositional truncation makes representability a proposition, so the full
    subcategory inherits univalence from the presheaf category. *)
Module CategoryCompletion (T: PropositionalTruncation).
  Import T.
  Module W := CategoryWeakEquivalences T.
  Import W W.TF.
  Set Universe Polymorphism.

  Definition MerelyRepresentable (C: Category) (P: Functor (Op C) HSetCat): Type :=
    merely (Representable C P).

  Definition completionCategory (C: Category): Category :=
    subtypeCategory (functorCategory (Op C) HSetCat) (MerelyRepresentable C).

  Definition completionUnivalence (C: Category):
    IsUnivalentCategory (completionCategory C) :=
    subtypeCategoryUnivalence _ (functorCategoryUnivalence hsetCategoryUnivalence)
      (MerelyRepresentable C) (fun P => merelyProp _).

  Definition completionUnit (C: Category): Functor C (completionCategory C).
  Proof.
    refine {| fobj a := (representable C a; tr (a; @idToIso _ _ _ eq_refl));
      fhom a b f := yonedaArrow f; fid := _; fcomp := _ |}.
    - now exact (yoneda C).(fid).
    - now exact (@fcomp _ _ (yoneda C)).
  Defined.

  Definition completionUnitFullyFaithful (C: Category):
    FullyFaithful (completionUnit C) := yonedaFullyFaithful C.

  Definition completionUnitEssentiallySurjective (C: Category):
    EssentiallySurjective (completionUnit C).
  Proof.
    intros [P p]. refine (trMap _ p).
    intros [a i]. refine (a; _).
    now exact (@liftFullIso _ _ (fun z: (completionCategory C).(CObj) => z.1)
      ((completionUnit C).(fobj) a) (P; p) i).
  Defined.

  Definition completionUnitWeak (C: Category): IsWeakEquivalence (completionUnit C) :=
    (completionUnitFullyFaithful C; completionUnitEssentiallySurjective C).
End CategoryCompletion.
