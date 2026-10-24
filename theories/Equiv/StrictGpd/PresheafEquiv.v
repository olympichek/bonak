(** Isomorphisms of strict face presentations, compatible with every face. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation LeSProp Funext.
From Bonak.Category.Groupoid Require Import StructureIdentity.
From Bonak.Presheaf.StrictGpd Require Import Roundtrip.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Record PresheafIso {A: HSet} {P Q: νStrictGpdPresentation A} := {
  G0Iso n: HSetGroupoidIso (P.(G0) n) (Q.(G0) n);
  GFaceIso n q (Hq: q <= n) (ε: A):
    P.(GFace) n q Hq ε ⨟ᶠ hsetGroupoidIsoFunctor (G0Iso n) ≐
    hsetGroupoidIsoFunctor (G0Iso n.+1) ⨟ᶠ Q.(GFace) n q Hq ε;
}.
Arguments PresheafIso {A} P Q.

(** Isomorphism induction applies to a whole family of levels at once. *)
Local Definition levelIsoInd (G: nat -> HSetGroupoid)
  (P: forall H: nat -> HSetGroupoid,
    (forall n, HSetGroupoidIso (G n) (H n)) -> Type)
  (h: P G (fun n => idHSetGroupoidIso (G n)))
  (H: nat -> HSetGroupoid) (e: forall n, HSetGroupoidIso (G n) (H n)): P H e.
Proof.
  assert (paths: forall n,
    ((G n; idHSetGroupoidIso (G n)): {K: HSetGroupoid &T HSetGroupoidIso (G n) K}) =
    (H n; e n)).
  { intro n. now refine (hsetGroupoidIsoInd (G n)
      (fun K e => (G n; idHSetGroupoidIso (G n)) = (K; e)) eq_refl (H n) (e n)). }
  pose (p := functional_extensionality_dep_good _ _ paths).
  now exact (@eq_rect (forall n, {K: HSetGroupoid &T HSetGroupoidIso (G n) K})
    (fun n => (G n; idHSetGroupoidIso (G n)))
    (fun z => P (fun n => (z n).1) (fun n => (z n).2)) h
    (fun n => (H n; e n)) p).
Defined.

Lemma presheafIsoEq {A: HSet} {P Q: νStrictGpdPresentation A}
  (e: PresheafIso P Q): P = Q.
Proof.
  destruct Q as [Qo Qf Qc], e as [eo ef]. cbn in eo, ef.
  revert Qf Qc ef.
  refine (levelIsoInd P.(G0) (fun Qo eo => forall
    (Qf: forall n q (Hq: q <= n) (ε: A), Functor (Qo n.+1) (Qo n))
    (Qc: forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A),
      Qf n.+1 r (Hr ↕ (↑ Hq)) ω ⨟ᶠ Qf n q Hq ε =
      Qf n.+1 q.+1 (⇑ Hq) ε ⨟ᶠ Qf n r (Hr ↕ Hq) ω),
    (forall n q (Hq: q <= n) (ε: A),
      P.(GFace) n q Hq ε ⨟ᶠ hsetGroupoidIsoFunctor (eo n) ≐
      hsetGroupoidIsoFunctor (eo n.+1) ⨟ᶠ Qf n q Hq ε) ->
    P = {| G0 := Qo; GFace := Qf; GFaceCoh := Qc |}) _ Qo eo).
  intros Qf Qc ef.
  refine (presheafEqIntro P {| G0 := P.(G0); GFace := Qf; GFaceCoh := Qc |}
    eq_refl _).
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro ε.
  apply (functorEqPath (P.(G0) n).(hsetGroupoidUIP)).
  now exact (@Build_FunctorEq (P.(G0) n.+1) (P.(G0) n)
    (P.(GFace) n q Hq ε) (Qf n q Hq ε)
    (ef n q Hq ε).(objEq) (ef n q Hq ε).(homEq)).
Defined.
