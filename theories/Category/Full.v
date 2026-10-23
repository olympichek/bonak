Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Contractible.
From Bonak.Category Require Import Category UnivalenceFacts.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Full categories on a family of objects, and univalence of full subcategories
    cut out by a proposition. *)
Definition fullCategory (C: Category) {A: Type} (o: A -> C.(CObj)): Category :=
  {| CObj := A; CHom a b := C.(CHom) (o a) (o b);
     cid a := C.(cid) (o a); ccomp a b c f g := C.(ccomp) f g;
     cidl a b f := C.(cidl) f; cidr a b f := C.(cidr) f;
     cassoc a b c d f g h := C.(cassoc) f g h |}.

Definition fullIso {C: Category} {A: Type} (o: A -> C.(CObj)) {a b: A}
  (i: Iso (fullCategory C o) a b): Iso C (o a) (o b) :=
  @Build_Iso C _ _ i.(isoHom)
    (@Build_IsInvertible C _ _ _ (inverse i.(isoInvertible))
      (inverseR i.(isoInvertible)) (inverseL i.(isoInvertible))).

Definition liftFullIso {C: Category} {A: Type} (o: A -> C.(CObj)) {a b: A}
  (i: Iso C (o a) (o b)): Iso (fullCategory C o) a b :=
  @Build_Iso (fullCategory C o) _ _ i.(isoHom)
    (@Build_IsInvertible (fullCategory C o) _ _ _ (inverse i.(isoInvertible))
      (inverseR i.(isoInvertible)) (inverseL i.(isoInvertible))).

Definition subtypeCategory (C: Category) (P: C.(CObj) -> Type): Category :=
  fullCategory C (fun z: {x: C.(CObj) &T P x} => z.1).

Definition subtypeCategoryUnivalence (C: Category) (u: IsUnivalentCategory C)
  (P: C.(CObj) -> Type) (h: forall x, IsHProp (P x)):
  IsUnivalentCategory (subtypeCategory C P).
Proof.
  apply categoryUnivalenceFromTotal. intro a.
  pose (o := fun z: {x: C.(CObj) &T P x} => z.1).
  pose (Code := {z: {b: C.(CObj) &T Iso C a.1 b} &T P z.1}).
  pose (enc := fun z: {b: {x: C.(CObj) &T P x} &T
      Iso (subtypeCategory C P) a b} => ((z.1.1; fullIso o z.2); z.1.2): Code).
  pose (dec := fun z: Code => ((z.1.1; z.2); @liftFullIso C _ o a (z.1.1; z.2) z.1.2)).
  refine (retractContr enc dec _ _).
  - intros [b i]. refine (eq_existT_curried eq_refl _).
    apply isoEq. now reflexivity.
  - exists ((a.1; idToIso eq_refl); a.2). intros [z p].
    refine (eq_existT_curried ((categoryIsoTotal u a.1).2 z) _).
    now apply h.
Defined.
