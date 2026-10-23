(** The strict face presentation and presheaf translations are inverse. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp Funext.
From Bonak.Category Require Import CategoryEq.
From Bonak.Presheaf Require Import νSemiShape CategoryAction.
From Bonak.Presheaf.StrictGpd Require Export Functor.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Lemma presheafEqIntro {A: HSet} (P Q: νStrictGpdPresentation A)
  (e0: P.(G0) = Q.(G0))
  (e1: rew [fun G0: nat -> HSetGroupoid =>
    forall n q (Hq: q <= n) (ε: A), Functor (G0 (S n)) (G0 n)] e0 in
      P.(GFace) = Q.(GFace)):
  P = Q.
Proof.
  destruct P as [Po Pf Pc], Q as [Qo Qf Qc]; cbn in e0, e1.
  destruct e0; cbn in e1; destruct e1.
  apply (f_equal (fun C => {| G0 := Po; GFace := Pf; GFaceCoh := C |})).
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro r.
  apply spropFunext; intro Hr.
  apply functional_extensionality_dep; intro ε.
  apply functional_extensionality_dep; intro ω.
  now apply (functorEqProp (Po n).(hsetGroupoidUIP)).
Defined.

Lemma ofToFunctor {A: HSet} (P: νStrictGpdPresentation A):
  ofFunctor (toFunctor P) = P.
Proof.
  refine (presheafEqIntro (ofFunctor (toFunctor P)) P eq_refl _).
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro ε.
  now exact (categoryApplyWGen (pshStr P) n q Hq ε).
Defined.

Lemma toOfFunctor {A: HSet} (F: Functor (Op (νSemiShape A)) HSetGroupoidCat):
  toFunctor (ofFunctor F) = F.
Proof.
  refine (functorEq (toFunctor (ofFunctor F)) F eq_refl _).
  intros m n w.
  now exact (categoryApplyWFhom m n w F
    (fun k q Hq ε => F.(fhom) (a := S k) (b := k) (wgen k q ε))
    (fun k q Hq ε => eq_refl)).
Defined.
