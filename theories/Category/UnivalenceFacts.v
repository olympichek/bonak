(** Univalence of the category of h-sets, and the contractible total space
    characterization of univalent categories. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Univalence Contractible.
From Bonak.Category Require Import Category HSetCat.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

Definition setIsoEquiv {A B: HSet} (i: Iso HSetCat A B): Equiv A B :=
  qinvEquiv i.(isoHom) (inverse i.(isoInvertible))
    (fun x => f_equal (fun f => f x) (inverseR i.(isoInvertible)))
    (fun y => f_equal (fun f => f y) (inverseL i.(isoInvertible))).

Definition setIsoPath {A B: HSet} (i: Iso HSetCat A B): A = B :=
  hsetEq (setIsoEquiv i).

Lemma setIsoPathRet {A B: HSet} (p: A = B): setIsoPath (@idToIso HSetCat A B p) = p.
Proof.
  destruct p. unfold setIsoPath, hsetEq.
  change (hsetEqIntro A A (invEq (uaEquiv A A) (idToEquiv eq_refl)) = eq_refl).
  refine (f_equal (hsetEqIntro A A) (retEq (uaEquiv A A) eq_refl) • _).
  now exact (hsetEqIntroEta (eq_refl: A = A)).
Qed.

Local Lemma setIdToIsoPoint {A B: HSet} (p: A = B) (x: A):
  (@idToIso HSetCat A B p).(isoHom) x = rew [Dom] p in x.
Proof. now destruct p. Qed.

Lemma setIsoPathSec {A B: HSet} (i: Iso HSetCat A B): @idToIso HSetCat A B (setIsoPath i) = i.
Proof.
  apply (@isoEq HSetCat A B _ i).
  change ((fun x: A => (@idToIso HSetCat A B (setIsoPath i)).(isoHom) x)
    = (fun x: A => i.(isoHom) x)).
  apply functional_extensionality_dep; intro x.
  rewrite setIdToIsoPoint. now apply hsetEqRew.
Qed.

Definition hsetCategoryUnivalence: IsUnivalentCategory HSetCat :=
  fun A B => equivFibers (qinvEquiv (@idToIso HSetCat A B) (@setIsoPath A B)
    setIsoPathRet setIsoPathSec).

Definition categoryIsoTotal {C: Category} (u: IsUnivalentCategory C) (a: C.(CObj)):
  Contr {b: C.(CObj) &T Iso C a b}.
Proof.
  exists (a; idToIso eq_refl). intros [b i].
  pose (p := categoryIsoPath u i).
  assert (h: idToIso p = i) by now apply (secEq (idToIsoEquiv u a b)).
  refine (eq_existT_curried p _).
  transitivity (idToIso p).
  - now destruct p.
  - now exact h.
Defined.

Definition categoryUnivalenceFromTotal (C: Category)
  (h: forall a, Contr {b: C.(CObj) &T Iso C a b}): IsUnivalentCategory C.
Proof.
  intros a b i.
  pose (e := identitySystemEquiv a (Iso C a) (idToIso eq_refl) (h a) b).
  assert (q: e.(eqvFun) = @idToIso C a b).
  { apply functional_extensionality_dep; intro p. now destruct p. }
  rewrite <- q. now apply equivFibers.
Defined.
