(** H-set families classified by maps of their total spaces into an
    equivalent base. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Equiv Univalence.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** Changing the base of a map along an equivalence keeps its total space. *)
Definition hsetMapBaseChange {M N: HSet} (e: Equiv M N):
  Equiv {T: HSet &T T -> M} {T: HSet &T T -> N}.
Proof.
  refine (qinvEquiv (fun p => (p.1; fun x => e (p.2 x)))
    (fun p => (p.1; fun x => invEq e (p.2 x))) _ _);
    intros [T f]; apply f_equal; apply functional_extensionality_dep; intro x.
  - now apply retEq.
  - now apply secEq.
Defined.

(** A family over [M] is its total space, mapped to [N] through [e]. *)
Definition hsetFamilyMapEquivAlong {M N: HSet} (e: Equiv M N):
  Equiv (M -> HSet) {T: HSet &T T -> N} :=
  compEquiv (hsetFamilyMapEquiv M) (hsetMapBaseChange e).
