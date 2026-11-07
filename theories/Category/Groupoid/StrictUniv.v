(** Strict univalent groupoids are discrete.

    In a univalent groupoid, the arrows between two objects are equivalent to
    the paths between them. When the objects also form an h-set, these paths
    are unique, so the groupoid is the discrete groupoid on an h-set. Strict
    univalent groupoids are therefore equivalent to h-sets, and equal to them
    by univalence. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation HGpd.
From Bonak.Lib Require Import Equiv Univalence.
From Bonak.Category Require Import Category Groupoid.
From Bonak.Category.Groupoid Require Import Path.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record StrictUnivGroupoid := {
  strictUnivGroupoid:> UnivGroupoid;
  univGroupoidStrictness: IsStrictCategory strictUnivGroupoid;
}.

Lemma strictUnivGroupoidEq (G H: StrictUnivGroupoid)
  (e: G.(strictUnivGroupoid) = H.(strictUnivGroupoid)): G = H.
Proof.
  destruct G as [G s], H as [H t]; cbn in e. destruct e.
  now destruct (isStrictCategoryProp s t).
Qed.

(** The arrows between two objects of a strict univalent groupoid form a
    proposition. *)

Lemma strictUnivHomProp (G: StrictUnivGroupoid) {a b: G.(CObj)}
  (f g: G.(CHom) a b): f = g.
Proof.
  now exact (eq_sym (idToHomToId (G := G) f)
    • (f_equal idToHom (G.(univGroupoidStrictness) a b
         (homToId f) (homToId g))
       • idToHomToId (G := G) g)).
Qed.

(** The discrete groupoid on an h-set, and the h-set of objects of a strict
    univalent groupoid *)

Definition discreteGroupoid (A: HSet): StrictUnivGroupoid := {|
  strictUnivGroupoid := pathGpd (hgpdOfHSet A);
  univGroupoidStrictness := @UIP A;
|}.

Definition strictUnivGroupoidObjects (G: StrictUnivGroupoid): HSet := {|
  Dom := G.(CObj);
  UIP := G.(univGroupoidStrictness);
|}.

Lemma discreteGroupoidObjects (A: HSet):
  strictUnivGroupoidObjects (discreteGroupoid A) = A.
Proof. now reflexivity. Qed.

(** The 1-type of objects of a strict univalent groupoid is its h-set of
    objects. *)

Lemma hgpdOfHSetObjects (G: StrictUnivGroupoid):
  hgpdOfHSet (strictUnivGroupoidObjects G) = gobj G.
Proof.
  refine (f_equal (fun u => {| GDom := G.(CObj); GUIP := u |}) _).
  apply functional_extensionality_dep; intro x.
  apply functional_extensionality_dep; intro y.
  apply functional_extensionality_dep; intro h.
  apply functional_extensionality_dep; intro g.
  apply functional_extensionality_dep; intro p.
  apply functional_extensionality_dep; intro q.
  now apply (eq_hprop_UIP (fun u v: h = g =>
    eq_hprop_UIP (G.(univGroupoidStrictness) x y) u v)).
Qed.

Lemma objectsDiscreteGroupoid (G: StrictUnivGroupoid):
  discreteGroupoid (strictUnivGroupoidObjects G) = G.
Proof.
  apply strictUnivGroupoidEq; cbn.
  rewrite hgpdOfHSetObjects. now apply piOneClassify.
Qed.

Definition hsetStrictUnivGroupoidEquiv: Equiv HSet StrictUnivGroupoid :=
  qinvEquiv discreteGroupoid strictUnivGroupoidObjects
    discreteGroupoidObjects objectsDiscreteGroupoid.

Definition hsetEqStrictUnivGroupoid: HSet = StrictUnivGroupoid :=
  ua hsetStrictUnivGroupoidEquiv.
