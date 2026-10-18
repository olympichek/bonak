(** Both round trips between face presentations and set-valued functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Category Require Import Category HSetCat CategoryEq.
From Bonak.Presheaf Require Import SemiSimplicialShape WordAction.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import Funext.

From Bonak.Presheaf Require Export Functor.

Set Primitive Projections.
Set Printing Projections.

Section PresheafRoundtrip.

(** The round trip on records *)

Lemma ofToFunctor (P: SSSetPresentation): ofFunctor (toFunctor P) = P.
Proof.
  refine (presheafEqIntro (ofFunctor (toFunctor P)) P eq_refl _); simpl.
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro x.
  now exact (applyWgen (pshStr P) n q Hq x).
Qed.

(** The round trip on functors: a functor is determined by its action on the
    generating cofaces, because every word is a composite of them. *)

Lemma applyWfhom (m: nat): forall n (w: Word n m)
  (F: Functor (Op SemiSimplicialShape) HSetCat)
  (SF: forall k q (Hq: q <= k), F.(fobj) (S k) -> F.(fobj) k)
  (HSF: forall k q (Hq: q <= k) x,
     SF k q Hq x = F.(fhom) (a := S k) (b := k) (wgen k q) x)
  (x: F.(fobj) m),
  applyW m w (Build_FaceStr (fun k => F.(fobj) k) SF) x
  = F.(fhom) (a := m) (b := n) w x.
Proof.
  induction m as [|m IHm]; intros n w F SF HSF x.
  - destruct n as [|n]; [|now destruct w].
    destruct w. now exact (eq_sym (f_equal (fun h => h x) (F.(fid) 0))).
  - destruct w as [w|w].
    + refine (IHm n w F SF HSF (SF m m leR_refl x) • _).
      refine (f_equal (F.(fhom) (a := m) (b := n) w) (HSF m m leR_refl x) • _).
      refine (eq_sym (f_equal (fun h => h x)
        (F.(fcomp) (a := S m) (b := m) (c := n) (wgen m m) w)) • _).
      now exact (f_equal (fun v => F.(fhom) (a := S m) (b := n) v x)
        (wgenSkip w)).
    + destruct n as [|n]; [now destruct w|].
      now exact (IHm n w (SemiSimplicialShapeShift ⨟ᶠ F)
        (fun k q Hq => SF (S k) q (↑ Hq))
        (fun k q Hq x => HSF (S k) q (↑ Hq) x
           • f_equal (fun v => F.(fhom) (a := S (S k)) (b := S k) v x)
               (wgenLift Hq)) x).
Defined.

Lemma toOfFunctor (F: Functor (Op SemiSimplicialShape) HSetCat):
  toFunctor (ofFunctor F) = F.
Proof.
  refine (functorEq (toFunctor (ofFunctor F)) F eq_refl _); simpl; intros a b w.
  apply functional_extensionality_dep; intro x.
  now exact (applyWfhom a b w F
    (fun k q Hq => F.(fhom) (a := S k) (b := k) (wgen k q))
    (fun k q Hq x => eq_refl) x).
Qed.

End PresheafRoundtrip.
