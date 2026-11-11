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
  Equiv {T: HSet &T T -> M} {T: HSet &T T -> N} :=
  sigTEquivSnd (fun T: HSet => @piEquiv T (fun _ => M) (fun _ => N) (fun _ => e)).

(** A family over [M] is its total space, mapped to [N] through [e]. *)
Definition hsetFamilyMapEquivAlong {M N: HSet} (e: Equiv M N):
  Equiv (M -> HSet) {T: HSet &T T -> N} :=
  compEquiv (hsetFamilyMapEquiv M) (hsetMapBaseChange e).
