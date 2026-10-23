Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation.
From Bonak.Category Require Export Groupoid FunctorAlgebra.
Set Primitive Projections.
Set Universe Polymorphism.
Set Printing Projections.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Groupoids with an h-set of objects, independently of categorical univalence. *)
Record HSetGroupoid := {
  hsetGroupoid:> Groupoid;
  hsetGroupoidUIP: forall (x y: hsetGroupoid.(CObj)) (p q: x = y), p = q;
}.

Definition hsetGroupoidObjects (G: HSetGroupoid): HSet :=
  {| Dom := G.(CObj); UIP := G.(hsetGroupoidUIP) |}.
Coercion hsetGroupoidObjects: HSetGroupoid >-> HSet.

(** Pulling back a groupoid to any h-set of candidate representatives
    gives a groupoid with h-set objects. Coverage is a separate condition. *)
Definition presentationGroupoid (U: Groupoid) (S: HSet)
  (p: S -> U.(CObj)): HSetGroupoid.
Proof.
  refine {| hsetGroupoid := {| gcat :=
    {| CObj := S; CHom x y := U.(CHom) (p x) (p y);
       cid x := U.(cid) (p x);
       ccomp x y z f g := f ⨟ g;
       cidl x y f := U.(cidl) f;
       cidr x y f := U.(cidr) f;
       cassoc x y z w f g h := U.(cassoc) f g h |};
    groupoidInvertibility := _ |};
    hsetGroupoidUIP := @UIP S |}.
  intros x y f. refine (@Build_IsInvertible _ x y f (ginv f) _ _).
  - now apply ginvR.
  - now apply ginvL.
Defined.

Definition presentationFunctor (U: Groupoid) (S: HSet)
  (p: S -> U.(CObj)): Functor (presentationGroupoid U S p) U :=
  Build_Functor (presentationGroupoid U S p) U p (fun x y f => f)
    (fun x => eq_refl) (fun x y z f g => eq_refl).

(** The terminal groupoid. *)
Unset Universe Minimization ToSet.

Definition unitGroupoid: HSetGroupoid.
Proof.
  refine {| hsetGroupoid := {| gcat :=
    {| CObj := unit; CHom _ _ := hunit; cid _ := tt;
       ccomp _ _ _ _ _ := tt;
       cidl _ _ f := hunit_ext tt f; cidr _ _ f := hunit_ext tt f;
       cassoc _ _ _ _ _ _ _ := eq_refl |} |}; hsetGroupoidUIP := unit_UIP |}.
  intros a b f. now refine (@Build_IsInvertible _ a b f tt eq_refl eq_refl).
Defined.

Definition terminalFunctor (G: HSetGroupoid): Functor G unitGroupoid :=
  Build_Functor G unitGroupoid (fun _ => tt) (fun _ _ _ => tt)
    (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl).

(** The category of groupoids with h-set objects. *)

Definition hsetFunctorSet (G H: HSetGroupoid): HSet :=
  functorSet G H H.(hsetGroupoidUIP).

Definition HSetGroupoidCat: Category.
Proof.
  refine {| CObj := HSetGroupoid; CHom := hsetFunctorSet;
    cid := idFunctor; ccomp G H K F L := F ⨟ᶠ L |}.
  - intros G H F. apply (functorEqPath H.(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
  - intros G H F. apply (functorEqPath H.(hsetGroupoidUIP)).
    unshelve econstructor; now intros.
  - intros G H K L F R S. apply (functorEqPath L.(hsetGroupoidUIP)).
    now apply feqAssoc.
Defined.
