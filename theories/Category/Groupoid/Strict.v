Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation.
From Bonak.Category Require Export Groupoid FunctorAlgebra.
Set Primitive Projections.
Set Universe Polymorphism.
Set Printing Projections.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Strict groupoids: groupoids with an h-set of objects, independently of
    categorical univalence. *)
Record StrictGroupoid := {
  strictGroupoid:> Groupoid;
  groupoidStrictness: IsStrictCategory strictGroupoid;
}.

Definition strictGroupoidObjects (G: StrictGroupoid): HSet :=
  {| Dom := G.(CObj); UIP := G.(groupoidStrictness) |}.
Coercion strictGroupoidObjects: StrictGroupoid >-> HSet.

(** Pulling back a groupoid to any h-set of candidate representatives
    gives a groupoid with h-set objects. Coverage is a separate condition. *)
Definition presentationGroupoid (U: Groupoid) (S: HSet)
  (p: S -> U.(CObj)): StrictGroupoid.
Proof.
  refine {| strictGroupoid := {| groupoid :=
    {| CObj := S; CHom x y := U.(CHom) (p x) (p y);
       cid x := U.(cid) (p x);
       ccomp x y z f g := f ⨟ g;
       cidl x y f := U.(cidl) f;
       cidr x y f := U.(cidr) f;
       cassoc x y z w f g h := U.(cassoc) f g h |};
    groupoidInvertibility := _ |};
    groupoidStrictness := @UIP S |}.
  intros x y f. refine (@Build_IsInvertible _ x y f (ginv f) _ _).
  - now apply ginvR.
  - now apply ginvL.
Defined.

Definition presentationFunctor (U: Groupoid) (S: HSet)
  (p: S -> U.(CObj)): Functor (presentationGroupoid U S p) U :=
  {| fobj := p;
     fhom := fun x y f => f;
     fid := fun x => eq_refl;
     fcomp := fun x y z f g => eq_refl |}.

(** The terminal groupoid. *)
Unset Universe Minimization ToSet.

Definition unitGroupoid: StrictGroupoid.
Proof.
  refine {| strictGroupoid := {| groupoid :=
    {| CObj := unit; CHom _ _ := hunit; cid _ := tt;
       ccomp _ _ _ _ _ := tt;
       cidl _ _ f := hunit_ext tt f; cidr _ _ f := hunit_ext tt f;
       cassoc _ _ _ _ _ _ _ := eq_refl |} |}; groupoidStrictness := unit_UIP |}.
  intros a b f. now refine (@Build_IsInvertible _ a b f tt eq_refl eq_refl).
Defined.

Definition terminalFunctor (G: StrictGroupoid): Functor G unitGroupoid :=
  {| fobj := fun _ => tt;
     fhom := fun _ _ _ => tt;
     fid := fun _ => eq_refl;
     fcomp := fun _ _ _ _ _ => eq_refl |}.

(** The category of groupoids with h-set objects. *)

Definition strictGroupoidFunctorSet (G H: StrictGroupoid): HSet :=
  functorSet G H H.(groupoidStrictness).

Definition StrictGroupoidCat: Category.
Proof.
  refine {| CObj := StrictGroupoid; CHom := strictGroupoidFunctorSet;
    cid := idFunctor; ccomp G H K F L := F ⨟ᶠ L |}.
  - intros G H F. apply (functorEqPath H.(groupoidStrictness)).
    unshelve econstructor; now intros.
  - intros G H F. apply (functorEqPath H.(groupoidStrictness)).
    unshelve econstructor; now intros.
  - intros G H K L F R S. apply (functorEqPath L.(groupoidStrictness)).
    now apply feqAssoc.
Defined.
