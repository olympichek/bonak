Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Univalence.
From Bonak.Category Require Import Category.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** The category of h-sets and functions. Its hom-types are h-sets by
    [hpiT], which is where functional extensionality enters. *)

Definition HSetCat: Category := {|
  CObj := HSet;
  CHom A B := hpiT (fun _: A => B);
  cid A := fun x => x;
  ccomp A B C f g := fun x => g (f x);
  cidl A B f := eq_refl;
  cidr A B f := eq_refl;
  cassoc A B C D f g h := eq_refl;
|}.

(** Functor laws evaluated at an element of the source h-set. *)

Lemma fhomCompPt {C: Category} (F: Functor C HSetCat) {a b c}
  (f: C.(CHom) a b) (g: C.(CHom) b c) (x: F.(fobj) a):
  F.(fhom) g (F.(fhom) f x) = F.(fhom) (f ⨟ g) x.
Proof. exact (eq_sym (f_equal (fun h => h x) (F.(fcomp) f g))). Qed.

Lemma fhomIdPt {C: Category} (F: Functor C HSetCat) a (x: F.(fobj) a):
  F.(fhom) (C.(cid) a) x = x.
Proof. exact (f_equal (fun h => h x) (F.(fid) a)). Qed.

(** The category of h-sets is univalent: an isomorphism of h-sets is an
    equivalence of their carriers, which [hsetEq] turns into a path. *)

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
