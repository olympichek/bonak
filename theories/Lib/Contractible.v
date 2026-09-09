(** Contractible types and uniqueness of their contraction. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT Notation.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Universe Polymorphism.

(** Contractibility

    A contractible type is a mere proposition, hence an h-set (Lemma 3.3.4 of
    the HoTT book), and being contractible is itself a proposition (Lemma
    3.11.4). *)

Definition Contr (X: Type): Type := {c: X &T forall x, c = x}.

Lemma contrPathEq {X: Type} (c: X) (h: forall x, c = x) {x y: X} (p: x = y):
  p = eq_sym (h x) • h y.
Proof.
  destruct p. now destruct (h x).
Qed.

Lemma contrUIP {X: Type} (H: Contr X) {x y: X} (p q: x = y): p = q.
Proof.
  now exact (contrPathEq H.1 H.2 p • eq_sym (contrPathEq H.1 H.2 q)).
Qed.

Lemma contrProp {X: Type} (u v: Contr X): u = v.
Proof.
  refine (eq_existT_curried (u.2 v.1) _).
  apply functional_extensionality_dep; intro x. now apply (contrUIP u).
Qed.

