(** Weak equivalences retain full faithfulness as equivalence of hom-types
    and essential surjectivity as mere existence of representatives. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Groupoid.
From Bonak.Category.Groupoid Require Import SetBased.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category Require Export FullyFaithful.
Set Primitive Projections.
Set Universe Polymorphism.

Module WeakEquivalences (T: PropositionalTruncation).
  Import T.
  Module TF := TruncationFacts T.
  Import TF.
  Set Universe Polymorphism.

  Definition EssentiallySurjective {G H: Groupoid} (F: Functor G H): Type :=
    forall y: H.(CObj), merely {x: G.(CObj) &T H.(CHom) (F.(fobj) x) y}.

  (** A transparent pair keeps the weak-equivalence type shared by separate
      applications of the same truncation interface. *)
  Definition IsWeakEquivalence {G H: Groupoid} (F: Functor G H): Type :=
    {h: FullyFaithful F &T EssentiallySurjective F}.

  Definition Build_IsWeakEquivalence (G H: Groupoid) (F: Functor G H)
    (h: FullyFaithful F) (e: EssentiallySurjective F): IsWeakEquivalence F := (h; e).

  Definition weakFullyFaithful {G H: Groupoid} (F: Functor G H)
    (w: IsWeakEquivalence F): FullyFaithful F := w.1.

  Definition weakEssentiallySurjective {G H: Groupoid} (F: Functor G H)
    (w: IsWeakEquivalence F): EssentiallySurjective F := w.2.

  Definition essentiallySurjectiveComp {G H K: Groupoid}
    (F: Functor G H) (E: Functor H K)
    (f: EssentiallySurjective F) (e: EssentiallySurjective E):
    EssentiallySurjective (compFunctor F E).
  Proof.
    intro z. refine (trRec (merelyProp _) _ (e z)).
    intros [y v]. refine (trRec (merelyProp _) _ (f y)).
    intros [x u]. now exact (tr (x; E.(fhom) u ⨟ v)).
  Defined.

  Definition weakCompose {G H K: Groupoid} (F: Functor G H) (E: Functor H K)
    (f: IsWeakEquivalence F) (e: IsWeakEquivalence E):
    IsWeakEquivalence (compFunctor F E) :=
    @Build_IsWeakEquivalence G K (compFunctor F E)
      (fullyFaithfulComp F E (weakFullyFaithful _ f) (weakFullyFaithful _ e))
      (essentiallySurjectiveComp F E
        (weakEssentiallySurjective _ f) (weakEssentiallySurjective _ e)).
End WeakEquivalences.

(** Set covers of 1-types and the covers induced by weak equivalences
    from groupoids with h-set objects to univalent groupoids. *)
Module GroupoidSetCovers (T: PropositionalTruncation).
  Import T.
  Module W := WeakEquivalences T.
  Include SetCovers T.

  Definition SetsCover1Types: Type := forall X: HGpd, merely (SetCover X).

  Definition weakEquivalenceCover {G: HSetGroupoid} (U: UnivalentGroupoid)
    (F: Functor G U) (w: W.IsWeakEquivalence F): SetCover U.(CObj).
  Proof.
    refine (hsetGroupoidObjects G; (F.(fobj); _)).
    intro y. refine (TF.trMap _ (W.weakEssentiallySurjective _ w y)).
    intros [x f]. now exact (x; homToId f).
  Defined.
End GroupoidSetCovers.
