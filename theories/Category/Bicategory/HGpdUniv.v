(** The comparison between the bicategories of 1-types and of univalent
    groupoids.

    The coherent structure maps [piOne] and [classify] relate the bicategory
    [HGpdBicat] of 1-types and the bicategory [UnivGpdBicat] of univalent
    groupoids. Both are locally groupoidal, so each is a (2,1)-category. On
    objects, the two maps are the inverse equivalences [pathGpd] and [gobj].
    On 1-cells and 2-cells, the comparison is an equivalence at each pair of
    path groupoids: [piOneHomEquiv] and [piOneHom2Equiv]. The comparison is
    therefore an equality in every degree, and the two bicategories are
    equal ([hgpdBicatEqUnivGpdBicat]). *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation RewLemmas.
From Bonak Require Import HGpd.
From Bonak.Lib Require Import Equiv Univalence Funext.
From Bonak.Category Require Import Category CategoryEq Groupoid.
From Bonak.Category.Groupoid Require Import Path.
From Bonak.Category.Bicategory Require Import Bicategory BicategoryEq HGpdBicat
  Groupoids.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Set Keyed Unification.

(** The structure map from 1-types to groupoids *)

Local Lemma loopConcatRefl {X: Type} {x: X} (p q: x = x):
  p = eq_refl -> q = eq_refl -> p • q = eq_refl.
Proof. intros -> ->. reflexivity. Qed.

Local Lemma loopInverseRefl {X: Type} {x: X} (p: x = x):
  p = eq_refl -> eq_sym p = eq_refl.
Proof. intros ->. reflexivity. Qed.

Local Lemma loopMapRefl {X Y: Type} (f: X -> Y) {x: X} (p: x = x):
  p = eq_refl -> f_equal f p = eq_refl.
Proof. intros ->. reflexivity. Qed.

Local Ltac objectPathRefl :=
  first [ reflexivity
    | lazymatch goal with
      | |- f_equal _ (@pathFunctorComp ?A ?B ?C ?f ?g) = _ =>
        exact (@pathFunctorCompObj A B C f g)
      | |- f_equal _ (pathFunctorId ?A) = _ => exact (pathFunctorIdObj A)
      end
    | lazymatch goal with
      | |- ?p • ?q = _ => apply (loopConcatRefl p q); objectPathRefl
      | |- eq_sym ?p = _ => apply (loopInverseRefl p); objectPathRefl
      | |- f_equal ?F ?p = _ => apply (loopMapRefl F p); objectPathRefl
      end ].

Definition piOne: BicategoryStructureMap HGpdBicat UnivGpdBicat.
Proof.
  refine (Build_BicategoryStructureMap HGpdBicat UnivGpdBicat
    (fun A => pathGpd A) (fun A B f => pathFunctor f)
    (fun A => pathFunctorId A) (fun A B C f g => pathFunctorComp f g)
    (fun A B f g α => pathNat f g α) _ _ _ _ _ _ _).
  - intros A B f. apply natTransEq; intro x. now reflexivity.
  - intros A B f g h α β. apply natTransEq; intro x. now reflexivity.
  - intros A B C f g h α. apply natTransEq; intro x.
    now exact (eq_sym (ncompHom2RewOn (G := pathGpd A) (H := pathGpd C)
      (toFunctorOn (compFunctor (pathFunctor f) (pathFunctor g)))
      (toFunctorOn (pathFunctor (fun y: A => g (f y))))
      (toFunctorOn (compFunctor (pathFunctor f) (pathFunctor h)))
      (toFunctorOn (pathFunctor (fun y: A => h (f y))))
      (eq_sym (pathFunctorComp f g)) (eq_sym (pathFunctorComp f h))
      (pathFunctorCompObjSym f g) (pathFunctorCompObjSym f h)
      (whiskerLNat (pathFunctor f) (pathNat g h α)) x)).
  - intros A B C f g α h. apply natTransEq; intro x.
    now exact (eq_sym (ncompHom2RewOn (G := pathGpd A) (H := pathGpd C)
      (toFunctorOn (compFunctor (pathFunctor f) (pathFunctor h)))
      (toFunctorOn (pathFunctor (fun y: A => h (f y))))
      (toFunctorOn (compFunctor (pathFunctor g) (pathFunctor h)))
      (toFunctorOn (pathFunctor (fun y: A => h (g y))))
      (eq_sym (pathFunctorComp f h)) (eq_sym (pathFunctorComp g h))
      (pathFunctorCompObjSym f h) (pathFunctorCompObjSym g h)
      (whiskerRNat (pathNat f g α) (pathFunctor h)) x)).
  - intros A B f. apply natTransEq; intro x.
    rewrite ncompHom2Rew.
    assert (e: f_equal fobj
      (eq_sym (pathFunctorComp (fun x: A => x) f
        • f_equal (fun u => compFunctor u (pathFunctor f)) (pathFunctorId A))) = eq_refl).
    { rewrite <- eq_sym_map_distr, eq_trans_map_distr, fobjCompPathL. objectPathRefl. }
    cbn [comp1 bcomp id1 bid HGpdBicat UnivGpdBicat Hom].
    rewrite e. reflexivity.
  - intros A B f. apply natTransEq; intro x.
    rewrite ncompHom2Rew.
    assert (e: f_equal fobj
      (eq_sym (pathFunctorComp f (fun x: B => x)
        • f_equal (compFunctor (pathFunctor f)) (pathFunctorId B))) = eq_refl).
    { rewrite <- eq_sym_map_distr, eq_trans_map_distr, fobjCompPathR. objectPathRefl. }
    cbn [comp1 bcomp id1 bid HGpdBicat UnivGpdBicat Hom].
    rewrite e. reflexivity.
  - intros A B C D f g h. apply natTransEq; intro x.
    rewrite ncompHom2Rew.
    assert (e: f_equal fobj
      (eq_sym (pathFunctorComp (fun x => g (f x)) h
        • f_equal (fun u => compFunctor u (pathFunctor h)) (pathFunctorComp f g))) = eq_refl).
    { rewrite <- eq_sym_map_distr, eq_trans_map_distr, fobjCompPathL. objectPathRefl. }
    assert (e': f_equal fobj
      (eq_sym (pathFunctorComp f (fun x => h (g x))
        • f_equal (compFunctor (pathFunctor f)) (pathFunctorComp g h))) = eq_refl).
    { rewrite <- eq_sym_map_distr, eq_trans_map_distr, fobjCompPathR. objectPathRefl. }
    cbn [comp1 bcomp id1 bid HGpdBicat UnivGpdBicat Hom].
    rewrite e, e'. reflexivity.

Defined.

(** The structure map from groupoids to 1-types

    A functor acts on the identity types of objects through [homToId], which
    turns composition into concatenation and the action of a functor on
    arrows into [f_equal] of its object part. *)

Definition classify: BicategoryStructureMap UnivGpdBicat HGpdBicat.
Proof.
  refine (Build_BicategoryStructureMap UnivGpdBicat HGpdBicat
    (fun G => gobj G) (fun G H F => F.(fobj))
    (fun G => eq_refl) (fun G H K F F' => eq_refl)
    (fun G H F F' α x => homToId (α.(ncomp) x)) _ _ _ _ _ _ _).
  - intros G H F. apply functional_extensionality_dep; intro x.
    now apply homToIdId.
  - intros G H F F' F'' α β. apply functional_extensionality_dep; intro x.
    now apply homToIdComp.
  - intros G H K F F' F'' α. now reflexivity.
  - intros G H K F F' α F''.
    apply functional_extensionality_dep; intro x.
    now exact (homToIdFhom F'' (α.(ncomp) x)).
  - intros G H F. apply functional_extensionality_dep; intro x. apply homToIdId.
  - intros G H F. apply functional_extensionality_dep; intro x. apply homToIdId.
  - intros G H K L F F' F''. apply functional_extensionality_dep; intro x. apply homToIdId.

Defined.

Definition piOneHom2Equiv {A B: HGpd} (f g: A -> B):
  Equiv (@Hom2 HGpdBicat A B f g) (NatTrans (piOne.(f2hom) f) (piOne.(f2hom) g)).
Proof.
  unshelve refine (qinvEquiv (pathNat f g) (fun α => α.(ncomp)) _ _).
  - now intro α.
  - intro α. apply natTransEq; intro x. now reflexivity.
Defined.

(** The equality of the two bicategories

    [piOne] identifies [HGpdBicat] with [UnivGpdBicat] degreewise: on objects by
    [hgpdEqUnivGroupoid], on 1-cells by [piOneHomEquiv] and on 2-cells by
    [piOneHom2Equiv], each turned into an equality by univalence and matched
    with the corresponding map of [piOne] by the computation rules of
    univalence ([uaRew], [hsetEqRew]).

    Preservation of the unitors and associator is checked on the
    components of the corresponding natural transformations. *)

Definition hgpdBicatHomEq (A B: HGpd):
  (Hom HGpdBicat) A B = (Hom UnivGpdBicat) (piOne.(f2obj) A) (piOne.(f2obj) B) :=
  ua (piOneHomEquiv A B).

Definition hgpdBicatHom2Eq (A B: HGpd) (f g: (Hom HGpdBicat) A B):
  @Hom2 HGpdBicat A B f g
  = @Hom2 UnivGpdBicat (piOne.(f2obj) A) (piOne.(f2obj) B)
      (piOne.(f2hom) f) (piOne.(f2hom) g) :=
  hsetEq (h1 := @Hom2 HGpdBicat A B f g)
    (h2 := @Hom2 UnivGpdBicat (piOne.(f2obj) A) (piOne.(f2obj) B)
             (piOne.(f2hom) f) (piOne.(f2hom) g))
    (piOneHom2Equiv f g).

Unset Universe Minimization ToSet.

Lemma hgpdBicatEqUnivGpdBicat: HGpdBicat = UnivGpdBicat.
Proof.
  unshelve refine (bicategoryEq HGpdBicat UnivGpdBicat piOne hgpdEqUnivGroupoid _
    hgpdBicatHomEq _ hgpdBicatHom2Eq _).
  - apply functional_extensionality_dep; intro A.
    now exact (eq_sym (uaRew hgpdUnivGroupoidEquiv A)).
  - apply functional_extensionality_dep; intro A.
    apply functional_extensionality_dep; intro B.
    apply functional_extensionality_dep; intro f.
    now exact (eq_sym (uaRew (piOneHomEquiv A B) f)).
  - apply functional_extensionality_dep; intro A.
    apply functional_extensionality_dep; intro B.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    apply functional_extensionality_dep; intro α.
    now exact (eq_sym (hsetEqRew (h1 := @Hom2 HGpdBicat A B f g)
      (h2 := @Hom2 UnivGpdBicat (piOne.(f2obj) A) (piOne.(f2obj) B)
               (piOne.(f2hom) f) (piOne.(f2hom) g))
      (piOneHom2Equiv f g) α)).
Qed.
