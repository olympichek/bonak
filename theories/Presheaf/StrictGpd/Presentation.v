(** Strict face presentations in groupoids with h-set objects. Exchange is
    pointwise equality of functors, on both objects and arrows. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Category.Groupoid Require Import SetBased.
From Bonak.Category Require Import FunctorPointwise.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Record νStrictGpdPresentation {arity: HSet} := {
  G0: nat -> HSetGroupoid;
  GFace n q (Hq: q <= n) (ε: arity): Functor (G0 n.+1) (G0 n);
  GFaceCoh n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity):
    GFace n.+1 r (Hr ↕ (↑ Hq)) ω ⨟ᶠ GFace n q Hq ε ≐
    GFace n.+1 q.+1 (⇑ Hq) ε ⨟ᶠ GFace n r (Hr ↕ Hq) ω;
}.
Arguments νStrictGpdPresentation arity : clear implicits.

Definition AugmentedSemiSimplicialStrictGpdPresentation := νStrictGpdPresentation hunit.
Definition SemiCubicalStrictGpdPresentation := νStrictGpdPresentation hbool.
