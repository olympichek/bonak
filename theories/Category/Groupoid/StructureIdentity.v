(** Structure identity for groupoids with h-set objects and arrows. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Univalence RewLemmas Notation.
From Bonak.Category.Groupoid Require Export SetBased.
From Bonak.Category Require Export FunctorAlgebra.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record HSetGroupoidIso {G H: HSetGroupoid} := {
  sgisoObj: Equiv G H;
  sgisoHom: forall x y, Equiv (G.(CHom) x y) (H.(CHom) (sgisoObj x) (sgisoObj y));
  sgisoId: forall x, sgisoHom x x (cid x) = cid (sgisoObj x);
  sgisoComp: forall x y z (f: G.(CHom) x y) (g: G.(CHom) y z),
    sgisoHom x z (f ⨟ g) = sgisoHom x y f ⨟ sgisoHom y z g;
}.
Arguments HSetGroupoidIso G H : clear implicits.

Definition hsetGroupoidIsoFunctor {G H} (e: HSetGroupoidIso G H): Functor G H :=
  {| fobj := e.(sgisoObj); fhom := e.(sgisoHom);
     fid := e.(sgisoId); fcomp := e.(sgisoComp) |}.

Definition idHSetGroupoidIso (G: HSetGroupoid): HSetGroupoidIso G G :=
  @Build_HSetGroupoidIso G G idEquiv (fun _ _ => idEquiv)
    (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl).

Definition hsetGroupoidIsoInd (G: HSetGroupoid)
  (Q: forall H: HSetGroupoid, HSetGroupoidIso G H -> Type)
  (q: Q G (idHSetGroupoidIso G)) (H: HSetGroupoid) (e: HSetGroupoidIso G H): Q H e.
Proof.
  destruct G as [[[O M i c l r s] inv] u].
  destruct H as [[[O' M' i' c' l' r' s'] inv'] u'].
  destruct e as [eo eh ei ec]. cbn in eo, eh, ei, ec.
  revert M' i' c' l' r' s' inv' u' eh ei ec.
  pattern O', eo. apply equivInd.
  intros M' i' c' l' r' s' inv' u' eh ei ec.
  cbn in eh, ei, ec.
  revert i' c' l' r' s' inv' u' ei ec.
  pattern M', eh.
  match goal with |- ?P _ _ => refine (hsetFamilyEquivInd2 _ P _ _ _) end.
  intros i' c' l' r' s' inv' u' ei ec. cbn in ei, ec.
  assert (pi: i = i').
  { apply functional_extensionality_dep. now exact ei. }
  destruct pi.
  assert (pc: c = c').
  { repeat (apply functional_extensionality_dep; intro). now apply ec. }
  destruct pc.
  assert (pl: l = l').
  { repeat (apply functional_extensionality_dep; intro). now apply (M _ _).(UIP). }
  destruct pl.
  assert (pr: r = r').
  { repeat (apply functional_extensionality_dep; intro). now apply (M _ _).(UIP). }
  destruct pr.
  assert (ps: s = s').
  { repeat (apply functional_extensionality_dep; intro). now apply (M _ _).(UIP). }
  destruct ps.
  destruct (isGroupoidProp inv inv').
  assert (pu: u = u').
  { repeat (apply functional_extensionality_dep; intro).
    now apply (eq_hprop_UIP (u _ _)). }
  destruct pu.
  assert (pei: ei = (fun _ => eq_refl)).
  { repeat (apply functional_extensionality_dep; intro). now apply (M _ _).(UIP). }
  assert (pec: ec = (fun _ _ _ _ _ => eq_refl)).
  { repeat (apply functional_extensionality_dep; intro). now apply (M _ _).(UIP). }
  rewrite pei, pec. now exact q.
Defined.

(** Functors induced by equalities of groupoids. *)

Definition transportGroupoidFunctor {G H: HSetGroupoid} (e: G = H): Functor G H :=
  rew [fun K: HSetGroupoid => Functor G K] e in idFunctor G.

Lemma transportGroupoidFunctorComp {G H K: HSetGroupoid} (e: G = H) (p: H = K):
  transportGroupoidFunctor (e • p) =
  transportGroupoidFunctor e ⨟ᶠ transportGroupoidFunctor p.
Proof.
  destruct e, p.
  now exact (@transportCategoryFunctorComp G G G eq_refl eq_refl).
Defined.

Lemma transportGroupoidFunctorSymL {G H: HSetGroupoid} (e: G = H):
  transportGroupoidFunctor e ⨟ᶠ transportGroupoidFunctor (eq_sym e) = idFunctor G.
Proof.
  destruct e. now exact (@transportCategoryFunctorSymL G G eq_refl).
Defined.

Lemma transportGroupoidFunctorSymR {G H: HSetGroupoid} (e: G = H):
  transportGroupoidFunctor (eq_sym e) ⨟ᶠ transportGroupoidFunctor e = idFunctor H.
Proof.
  destruct e. now exact (@transportCategoryFunctorSymR G G eq_refl).
Defined.
