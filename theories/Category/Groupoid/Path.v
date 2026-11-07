(** The path groupoid of a 1-type, and the equivalence between 1-types and
    univalent groupoids.

    A 1-type [A] gives the univalent groupoid [pathGpd A] of its points and
    paths, and a univalent groupoid [G] gives the 1-type [gobj G] of its
    objects. The two maps are inverse: [classifyPiOne] is an equality of
    [HGpd] records, and [piOneClassify] identifies the homs of a groupoid
    with the identity types of its objects, which is where univalence
    enters. A functor out of a path groupoid is determined by its object
    part, because it acts on paths by [f_equal] of that part
    ([piOneHomEquiv]). *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation RewLemmas.
From Bonak Require Import HGpd.
From Bonak.Lib Require Import Equiv Univalence Funext.
From Bonak.Category Require Import Category CategoryEq Groupoid.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Set Keyed Unification.

(** The fundamental groupoid of a 1-type

    Paths between points of a 1-type form an h-set, so they are the homs of a
    category, and [idToHom] is the identity on them: the univalence field is
    [univFromQinv] applied to the identity as quasi-inverse. *)

(** The identity types of a 1-type, as an [HSet], with the universe of the
    result left as a parameter. [hsetEq] identifies [HSet]s at one fixed
    universe, and the hom family of a path category has to be able to live
    there. *)

Definition pathHom@{i j} {A: HGpd@{i}} (x y: A): HSet@{j} := {|
  Dom := x = y;
  UIP := @GUIP A x y;
|}.

Definition pathCat@{i j} (A: HGpd@{i}): Category@{i j} :=
  catOf A (fun x y => pathHom@{i j} x y) (fun a => eq_refl)
    (fun a b c p q => p • q)
    (fun a b p => eq_trans_refl_l p)
    (fun a b p => eq_trans_refl_r p)
    (fun a b c d p q r => eqTransAssoc p q r).

Lemma idToHomPath {A: HGpd} {a b: A} (p: a = b):
  idToHom (C := pathCat A) p = p.
Proof.
  now destruct p.
Qed.

Definition pathGpd@{i j +} (A: HGpd@{i}): UnivGroupoid :=
  univGroupoidFromPaths (pathCat A)
    (univFromQinv (pathCat A) (fun a b p => p)
      (fun a b p => idToHomPath p) (fun a b p => idToHomPath p)).

(** The functor between path groupoids induced by a map of 1-types *)

Definition pathFunctor {A B: HGpd} (f: A -> B):
  Functor (pathCat A) (pathCat B) := {|
  fobj := f;
  fhom x y p := f_equal f p;
  fid x := eq_refl;
  fcomp x y z p q := eq_trans_map_distr f p q;
|}.

(** The identity and composition paths of [pathFunctor] act trivially on
    object maps. Transport along them leaves components of natural
    transformations unchanged. *)

Definition pathFunctorId (A: HGpd):
  pathFunctor (fun x: A => x) = idFunctor (pathCat A) :=
  functorEqOn (toFunctorOn (pathFunctor (fun x: A => x)))
    (toFunctorOn (idFunctor (pathCat A))) (fun a b p => f_equal_id p).

Lemma pathFunctorIdObj (A: HGpd): f_equal fobj (pathFunctorId A) = eq_refl.
Proof.
  now exact (functorEqOnObj (toFunctorOn (pathFunctor (fun x: A => x)))
    (toFunctorOn (idFunctor (pathCat A))) (fun a b p => f_equal_id p)).
Qed.

Definition pathFunctorComp {A B C: HGpd} (f: A -> B) (g: B -> C):
  pathFunctor (fun x => g (f x))
  = compFunctor (pathFunctor f) (pathFunctor g) :=
  functorEqOn (toFunctorOn (pathFunctor (fun x => g (f x))))
    (toFunctorOn (compFunctor (pathFunctor f) (pathFunctor g)))
    (fun a b p => eq_sym (f_equal_compose f g p)).

Lemma pathFunctorCompObj {A B C: HGpd} (f: A -> B) (g: B -> C):
  f_equal fobj (pathFunctorComp f g) = eq_refl.
Proof.
  now exact (functorEqOnObj (toFunctorOn (pathFunctor (fun x => g (f x))))
    (toFunctorOn (compFunctor (pathFunctor f) (pathFunctor g)))
    (fun a b p => eq_sym (f_equal_compose f g p))).
Qed.

Lemma pathFunctorCompObjSym {A B C: HGpd} (f: A -> B) (g: B -> C):
  f_equal fobj (eq_sym (pathFunctorComp f g)) = eq_refl.
Proof.
  now rewrite <- eq_sym_map_distr, (pathFunctorCompObj f g).
Qed.

Definition pathNat {A B: HGpd} (f g: A -> B) (α: forall x: A, f x = g x):
  NatTrans (pathFunctor f) (pathFunctor g) := {|
  ncomp := α;
  nnat x y p := homotopyNat f g α p;
|}.

(** The comparison on objects

    The two records have the same carrier, and the [GUIP] field is a
    proposition: any two of its proofs agree because the type they compare
    lives in an h-set. *)

Lemma classifyPiOne (A: HGpd): gobj (pathGpd A) = A.
Proof.
  destruct A as [Ad Au].
  apply (f_equal (fun u => {| GDom := Ad; GUIP := u |})).
  apply functional_extensionality_dep; intro x.
  apply functional_extensionality_dep; intro y.
  apply functional_extensionality_dep; intro h.
  apply functional_extensionality_dep; intro g.
  apply functional_extensionality_dep; intro p.
  apply functional_extensionality_dep; intro q.
  now apply (eq_hprop_UIP (fun u v: h = g => Au x y h g u v)).
Qed.

(** The homs of a groupoid are identified with the identity types of its
    objects by [hsetEq], which is where univalence is used. *)

Definition homFamilyEq (G: UnivGroupoid):
  G.(CHom) = (fun x y => pathHom (A := gobj G) x y) :=
  functional_extensionality_dep_good _ _ (fun x: G.(CObj) =>
    functional_extensionality_dep_good _ _ (fun y: G.(CObj) =>
      eq_sym (hsetEq (h1 := pathHom (A := gobj G) x y) (h2 := G.(CHom) x y)
        (idToHomEquiv G x y)))).

(** Evaluating [homFamilyEq] at a pair of objects: the two applications of
    functional extensionality are undone by the equation that characterises
    it on points. *)

Lemma homFamilyEqAt (G: UnivGroupoid) (a b: G.(CObj)):
  f_equal (fun K: G.(CObj) -> G.(CObj) -> HSet => K a b) (homFamilyEq G)
  = eq_sym (hsetEq (h1 := pathHom (A := gobj G) a b) (h2 := G.(CHom) a b)
      (idToHomEquiv G a b)).
Proof.
  now exact (funextGoodAt2 G.(CHom) (fun x y => pathHom (A := gobj G) x y)
    (fun x y => eq_sym (hsetEq (h1 := pathHom (A := gobj G) x y)
      (h2 := G.(CHom) x y)
      (idToHomEquiv G x y))) a b).
Qed.

Lemma homFamilyEqRew (G: UnivGroupoid) {a b: G.(CObj)} (v: G.(CHom) a b):
  rew [fun K: G.(CObj) -> G.(CObj) -> HSet => Dom (K a b)] (homFamilyEq G)
    in v = homToId v.
Proof.
  rewrite (rew_map Dom (fun K: G.(CObj) -> G.(CObj) -> HSet => K a b)).
  rewrite homFamilyEqAt. now apply hsetEqRewSym.
Qed.

Lemma piOneClassifyCat (G: UnivGroupoid): G.(groupoid) = pathCat (gobj G).
Proof.
  refine (catEqOf G.(groupoid) _ _ _ _ _ _ (homFamilyEq G) _ _).
  - intro a. rewrite homFamilyEqRew. now apply homToIdId.
  - intros a b d f g. rewrite 3 homFamilyEqRew. now apply homToIdComp.
Qed.

Lemma piOneClassify (G: UnivGroupoid): pathGpd (gobj G) = G.
Proof.
  now apply eq_sym, univGroupoidEqCat, piOneClassifyCat.
Qed.

(** Functors between path groupoids are determined by their object parts. *)

Lemma pathFunctorFhom {A B: HGpd} (F: Functor (pathCat A) (pathCat B))
  {x y: A} (p: x = y): F.(fhom) p = f_equal F.(fobj) p.
Proof.
  destruct p. now apply F.(fid).
Qed.

Lemma pathFunctorEta {A B: HGpd} (F: Functor (pathCat A) (pathCat B)):
  pathFunctor F.(fobj) = F.
Proof.
  now exact (functorEqOn (toFunctorOn (pathFunctor F.(fobj))) (toFunctorOn F)
    (fun x y p => eq_sym (pathFunctorFhom F p))).
Qed.

Definition piOneHomEquiv (A B: HGpd):
  Equiv (A -> B) (Functor (pathGpd A) (pathGpd B)) :=
  qinvEquiv pathFunctor (fun F => F.(fobj)) (fun f => eq_refl) pathFunctorEta.

(** The types of 1-types and of groupoids

    The two object maps are inverse, so the two types are equivalent and, by
    univalence, equal. *)

Definition hgpdUnivGroupoidEquiv: Equiv HGpd UnivGroupoid :=
  qinvEquiv pathGpd gobj classifyPiOne piOneClassify.

Definition hgpdEqUnivGroupoid: HGpd = UnivGroupoid := ua hgpdUnivGroupoidEquiv.
