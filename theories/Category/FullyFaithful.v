(** Full faithfulness is equivalence on each hom-type, and is preserved
    by identities and composition. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation Equiv.
From Bonak.Category Require Import Category.
Set Primitive Projections.
Set Universe Polymorphism.

Definition FullyFaithful {C D: Category} (F: Functor C D): Type :=
  forall a b, IsEquiv (@fhom C D F a b).

Definition ffEquiv {C D: Category} (F: Functor C D) (h: FullyFaithful F)
  (a b: C.(CObj)): Equiv (C.(CHom) a b) (D.(CHom) (F.(fobj) a) (F.(fobj) b)) :=
  {| eqvFun := F.(fhom); eqvIsEquiv := h a b |}.

Definition fullyFaithfulId (C: Category): FullyFaithful (idFunctor C) :=
  fun a b => idEquiv.(eqvIsEquiv).

Definition fullyFaithfulComp {C D E: Category} (F: Functor C D) (G: Functor D E)
  (f: FullyFaithful F) (g: FullyFaithful G): FullyFaithful (compFunctor F G) :=
  fun a b => (compEquiv (ffEquiv F f a b)
    (ffEquiv G g (F.(fobj) a) (F.(fobj) b))).(eqvIsEquiv).
