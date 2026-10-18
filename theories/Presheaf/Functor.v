(** Translations between face presentations and set-valued functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Category Require Import Category HSetCat CategoryEq.
From Bonak.Presheaf Require Import SemiSimplicialShape WordAction.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Presheaf Require Export Presentation.

Set Primitive Projections.
Set Printing Projections.

Definition pshStr (P: SSSetPresentation): FaceStr := {|
  S0 n := P.(F0) n;
  SFace := P.(Face);
|}.

Section PresheafFunctor.

(** Interpreting faces along words *)

Definition toFunctor (P: SSSetPresentation): Functor (Op SemiSimplicialShape) HSetCat :=
  Build_Functor (Op SemiSimplicialShape) HSetCat (fun n => P.(F0) n)
    (fun a b w => applyW a w (pshStr P))
    (fun a => functional_extensionality_dep _ _
       (fun x => applyW_id (pshStr P) x))
    (fun a b c f g => functional_extensionality_dep _ _
       (fun x => eq_sym (applyWComp a b c f g (pshStr P) P.(FaceCoh) x))).

(** Restricting a functor to generating cofaces *)

Lemma ofFunctorCoh (F: Functor (Op SemiSimplicialShape) HSetCat)
  n q (Hq: q <= n) r (Hr: r <= q) (X: F.(fobj) (S (S n))):
  F.(fhom) (wgen n q) (F.(fhom) (wgen (S n) r) X)
  = F.(fhom) (wgen n r) (F.(fhom) (wgen (S n) (S q)) X).
Proof.
  refine (eq_sym (f_equal (fun h => h X)
    (F.(fcomp) (a := S (S n)) (b := S n) (c := n)
       (wgen (S n) r) (wgen n q))) • _).
  refine (f_equal (fun w => F.(fhom) (a := S (S n)) (b := n) w X)
    (wgenExchange n q Hq r Hr) • _).
  now exact (f_equal (fun h => h X)
    (F.(fcomp) (a := S (S n)) (b := S n) (c := n)
       (wgen (S n) (S q)) (wgen n r))).
Defined.

Definition ofFunctor (F: Functor (Op SemiSimplicialShape) HSetCat): SSSetPresentation :=
  Build_SSSetPresentation (fun n => F.(fobj) n)
    (fun n q Hq => F.(fhom) (a := S n) (b := n) (wgen n q))
    (ofFunctorCoh F).

End PresheafFunctor.
