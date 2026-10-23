Set Warnings "-notation-overridden".
From Bonak.Category Require Export Category CategoryEq FunctorPointwise.
From Bonak.Lib Require Import HSet Notation.
From Stdlib.Logic Require Import FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Functor composition is associative and unital as equality of records.
    Hom-set UIP and functional extensionality identify the law proofs. *)
Lemma functorIdL {C D: Category} (F: Functor C D): compFunctor (idFunctor C) F = F.
Proof.
  now exact (functorEqOn (toFunctorOn (compFunctor (idFunctor C) F))
    (toFunctorOn F) (fun a b f => eq_refl)).
Qed.

Lemma functorIdR {C D: Category} (F: Functor C D): compFunctor F (idFunctor D) = F.
Proof.
  now exact (functorEqOn (toFunctorOn (compFunctor F (idFunctor D)))
    (toFunctorOn F) (fun a b f => eq_refl)).
Qed.

Lemma functorAssocEq {C D E K: Category} (F: Functor C D) (G: Functor D E)
  (H: Functor E K): compFunctor (compFunctor F G) H = compFunctor F (compFunctor G H).
Proof.
  now exact (functorEqOn (toFunctorOn (compFunctor (compFunctor F G) H))
    (toFunctorOn (compFunctor F (compFunctor G H))) (fun a b f => eq_refl)).
Qed.

(** Extensional equality of functors with h-set objects in the target. *)
Unset Universe Minimization ToSet.

Definition pathFunctorEq {C D: Category} {F L: Functor C D}
  (e: F = L): F ≐ L.
Proof. destruct e. now apply feqRefl. Defined.

Section Extensionality.
Context {C D: Category}.
Context (objectUIP: forall (x y: D.(CObj)) (p q: x = y), p = q).

Lemma functorEqPath {F L: Functor C D} (e: F ≐ L): F = L.
Proof.
  pose (p := functional_extensionality _ _ e.(objEq)).
  apply (functorEq F L p).
  assert (transportHom: forall (o o': C.(CObj) -> D.(CObj)) (q: o = o')
    x y (f: D.(CHom) (o x) (o y)),
    (rew [fun a => D.(CHom) (a x) (a y)] q in f) =
      castArrow (f_equal (fun a => a x) q) (f_equal (fun a => a y) q) f).
  { now intros o o' q; destruct q. }
  intros x y f. rewrite transportHom.
  rewrite (objectUIP _ _ (f_equal (fun a => a x) p) (e.(objEq) x)).
  rewrite (objectUIP _ _ (f_equal (fun a => a y) p) (e.(objEq) y)).
  now apply e.(homEq).
Defined.

Lemma functorEqProp {F L: Functor C D} (p q: F ≐ L): p = q.
Proof.
  destruct p as [po ph], q as [qo qh].
  assert (e: po = qo).
  { apply functional_extensionality_dep; intro x. now apply objectUIP. }
  destruct e.
  assert (e: ph = qh).
  { apply functional_extensionality_dep; intro x.
    apply functional_extensionality_dep; intro y.
    apply functional_extensionality_dep; intro f. now apply (D.(CHom) _ _).(UIP). }
  now destruct e.
Defined.
End Extensionality.

(** Functors induced by equalities of categories. *)
Import Logic.EqNotations.

Definition transportCategoryFunctor {C D: Category} (e: C = D): Functor C D :=
  rew [fun E: Category => Functor C E] e in idFunctor C.

Lemma transportCategoryFunctorComp {C D E: Category} (e: C = D) (p: D = E):
  transportCategoryFunctor (e • p) =
  transportCategoryFunctor e ⨟ᶠ transportCategoryFunctor p.
Proof. destruct e, p. now symmetry; apply functorIdL. Defined.

Lemma transportCategoryFunctorSymL {C D: Category} (e: C = D):
  transportCategoryFunctor e ⨟ᶠ transportCategoryFunctor (eq_sym e) = idFunctor C.
Proof. destruct e. now apply functorIdL. Defined.

Lemma transportCategoryFunctorSymR {C D: Category} (e: C = D):
  transportCategoryFunctor (eq_sym e) ⨟ᶠ transportCategoryFunctor e = idFunctor D.
Proof. destruct e. now apply functorIdL. Defined.
