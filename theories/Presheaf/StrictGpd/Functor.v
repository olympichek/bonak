(** Translations between strict groupoid face presentations and presheaves. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Category.Groupoid Require Export SetBased.
From Bonak.Presheaf Require Import νSemiShape CategoryAction.
From Bonak.Presheaf.StrictGpd Require Export Presentation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition pshStr {A: HSet} (P: νStrictGpdPresentation A):
  CategoryFaceStr A HSetGroupoidCat :=
  @Build_CategoryFaceStr A HSetGroupoidCat P.(G0) P.(GFace).

Definition pshCoh {A: HSet} (P: νStrictGpdPresentation A): CategoryCoh (pshStr P) :=
  P.(GFaceCoh).

Definition toFunctor {A: HSet} (P: νStrictGpdPresentation A):
  Functor (Op (νSemiShape A)) HSetGroupoidCat :=
  Build_Functor (Op (νSemiShape A)) HSetGroupoidCat P.(G0)
    (fun m n w => categoryApplyW m w (pshStr P))
    (fun n => categoryApplyWId (pshStr P))
    (fun p m n g f => eq_sym (categoryApplyWComp p m n g f (pshStr P) (pshCoh P))).

Definition ofFunctorCoh {A: HSet} (F: Functor (Op (νSemiShape A)) HSetGroupoidCat)
  n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A):
  F.(fhom) (a := S (S n)) (b := S n) (wgen (S n) r ω) ⨟ᶠ
    F.(fhom) (a := S n) (b := n) (wgen n q ε) =
  F.(fhom) (a := S (S n)) (b := S n) (wgen (S n) (S q) ε) ⨟ᶠ
    F.(fhom) (a := S n) (b := n) (wgen n r ω).
Proof.
  refine (eq_sym (F.(fcomp) (wgen (S n) r ω) (wgen n q ε)) • _).
  refine (f_equal (fun w => F.(fhom) (a := S (S n)) (b := n) w)
    (wgenExchange n q Hq r Hr ε ω) • _).
  now exact (F.(fcomp) (wgen (S n) (S q) ε) (wgen n r ω)).
Defined.

Definition ofFunctor {A: HSet} (F: Functor (Op (νSemiShape A)) HSetGroupoidCat):
  νStrictGpdPresentation A := {|
  G0 := F.(fobj);
  GFace n q Hq ε := F.(fhom) (a := S n) (b := n) (wgen n q ε);
  GFaceCoh := ofFunctorCoh F;
|}.
