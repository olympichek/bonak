(** Weak equivalences of categories are fully faithful functors for which
    every target object merely has an isomorphic source representative. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Export FullyFaithful.
From Bonak.Category Require Import Category.
Set Primitive Projections.
Set Universe Polymorphism.

Module CategoryWeakEquivalences (T: PropositionalTruncation).
  Import T.
  Module TF := TruncationFacts T.
  Import TF.
  Set Universe Polymorphism.

  Definition EssentiallySurjective {C D: Category} (F: Functor C D): Type :=
    forall y: D.(CObj), merely {x: C.(CObj) &T Iso D (F.(fobj) x) y}.

  Definition IsWeakEquivalence {C D: Category} (F: Functor C D): Type :=
    {h: FullyFaithful F &T EssentiallySurjective F}.

  Definition Build_IsWeakEquivalence (C D: Category) (F: Functor C D)
    (h: FullyFaithful F) (e: EssentiallySurjective F): IsWeakEquivalence F := (h; e).

  Definition weakFullyFaithful {C D: Category} (F: Functor C D)
    (w: IsWeakEquivalence F): FullyFaithful F := w.1.

  Definition weakEssentiallySurjective {C D: Category} (F: Functor C D)
    (w: IsWeakEquivalence F): EssentiallySurjective F := w.2.

  Definition weakIdentity (C: Category): IsWeakEquivalence (idFunctor C) :=
    (fullyFaithfulId C; fun x => tr (x; idToIso eq_refl)).

  Definition essentiallySurjectiveComp {C D E: Category}
    (F: Functor C D) (G: Functor D E)
    (f: EssentiallySurjective F) (g: EssentiallySurjective G):
    EssentiallySurjective (compFunctor F G).
  Proof.
    intro z. refine (trRec (merelyProp _) _ (g z)).
    intros [y v]. refine (trMap _ (f y)).
    intros [x u]. now exact (x; composeIso (functorIso G u) v).
  Defined.

  Definition weakCompose {C D E: Category} (F: Functor C D) (G: Functor D E)
    (f: IsWeakEquivalence F) (g: IsWeakEquivalence G):
    IsWeakEquivalence (compFunctor F G) :=
    (fullyFaithfulComp F G f.1 g.1; essentiallySurjectiveComp F G f.2 g.2).

End CategoryWeakEquivalences.
