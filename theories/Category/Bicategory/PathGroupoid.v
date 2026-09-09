(** The comparison between 1-types and univalent groupoids.

    A 1-type [A] gives the groupoid [pathGpd A] of its points and paths, and a
    groupoid [G] gives the 1-type [classGpd G] of its objects. The coherent
    structure maps [piOne] and [classify] relate the (2,1)-category [HGpd2Cat]
    of 1-types and the 2-category [UnivGpd2Cat] of univalent groupoids, and the
    two composites are the identity on objects: [classifyPiOne] is an equality
    of [HGpd] records, and [piOneClassify] identifies the homs of a groupoid
    with the identity types of its objects, which is where univalence enters.

    On 1-cells and 2-cells the comparison is an equivalence in each direction
    at a path groupoid: [piOneHomEquiv] and [piOneHom2Equiv]. A functor out of
    a path groupoid is determined by its object part, because it acts on paths
    by [f_equal] of that part. The comparison is therefore an equality in
    every degree, and the two 2-categories are equal ([hgpd2CatEqUnivGpd2Cat]). *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation RewLemmas.
From Bonak Require Import νGpd.HGpd.
From Bonak.Lib Require Import Equiv Univalence Funext.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Bicategory BicategoryEq.
From Bonak.Category Require Import Groupoid.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Bonak.Category.Bicategory Require Import HGpd2Cat.
From Bonak.Category.Bicategory Require Import UnivGpd2Cat.
From Bonak.Category Require Import CategoryEq.
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

Definition pathGpd@{i j +} (A: HGpd@{i}): UnivalentGroupoid :=
  univalentGroupoidFromPaths (pathCat A)
    (univFromQinv (pathCat A) (fun a b p => p)
      (fun a b p => idToHomPath p) (fun a b p => idToHomPath p)).

(** The 1-type of objects of a groupoid *)

Definition classGpd (G: UnivalentGroupoid): HGpd := gobj G.

(** The 2-functor from 1-types to groupoids *)

Definition pathFunctor {A B: HGpd} (f: A -> B):
  Functor (pathCat A) (pathCat B) :=
  Build_Functor (pathCat A) (pathCat B) f (fun x y p => f_equal f p)
    (fun x => eq_refl) (fun x y z p q => eq_trans_map_distr f p q).

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
  NatTrans (pathFunctor f) (pathFunctor g) :=
  Build_NatTrans _ _ (pathFunctor f) (pathFunctor g) α
    (fun x y p => homotopyNat f g α p).

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

Definition piOne: BicategoryStructureMap HGpd2Cat UnivGpd2Cat.
Proof.
  refine (Build_BicategoryStructureMap HGpd2Cat UnivGpd2Cat
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
    cbn [comp1 bcomp id1 bid HGpd2Cat UnivGpd2Cat Hom].
    rewrite e. reflexivity.
  - intros A B f. apply natTransEq; intro x.
    rewrite ncompHom2Rew.
    assert (e: f_equal fobj
      (eq_sym (pathFunctorComp f (fun x: B => x)
        • f_equal (compFunctor (pathFunctor f)) (pathFunctorId B))) = eq_refl).
    { rewrite <- eq_sym_map_distr, eq_trans_map_distr, fobjCompPathR. objectPathRefl. }
    cbn [comp1 bcomp id1 bid HGpd2Cat UnivGpd2Cat Hom].
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
    cbn [comp1 bcomp id1 bid HGpd2Cat UnivGpd2Cat Hom].
    rewrite e, e'. reflexivity.

Defined.

(** The structure map from groupoids to 1-types

    A functor acts on the identity types of objects through [homToId], which
    turns composition into concatenation and the action of a functor on
    arrows into [f_equal] of its object part. *)

Definition classify: BicategoryStructureMap UnivGpd2Cat HGpd2Cat.
Proof.
  refine (Build_BicategoryStructureMap UnivGpd2Cat HGpd2Cat
    (fun G => classGpd G) (fun G H F => F.(fobj))
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

(** The comparison on objects

    The two records have the same carrier, and the [GUIP] field is a
    proposition: any two of its proofs agree because the type they compare
    lives in an h-set. *)

Lemma classifyPiOne (A: HGpd): classGpd (pathGpd A) = A.
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

Definition homFamilyEq (G: UnivalentGroupoid):
  G.(CHom) = (fun x y => pathHom (A := gobj G) x y) :=
  functional_extensionality_dep_good _ _ (fun x: G.(CObj) =>
    functional_extensionality_dep_good _ _ (fun y: G.(CObj) =>
      eq_sym (hsetEq (h1 := pathHom (A := gobj G) x y) (h2 := G.(CHom) x y)
        (idToHomEquiv G x y)))).

(** Evaluating [homFamilyEq] at a pair of objects: the two applications of
    functional extensionality are undone by the equation that characterises
    it on points. *)

Lemma homFamilyEqAt (G: UnivalentGroupoid) (a b: G.(CObj)):
  f_equal (fun K: G.(CObj) -> G.(CObj) -> HSet => K a b) (homFamilyEq G)
  = eq_sym (hsetEq (h1 := pathHom (A := gobj G) a b) (h2 := G.(CHom) a b)
      (idToHomEquiv G a b)).
Proof.
  now exact (funextGoodAt2 G.(CHom) (fun x y => pathHom (A := gobj G) x y)
    (fun x y => eq_sym (hsetEq (h1 := pathHom (A := gobj G) x y)
      (h2 := G.(CHom) x y)
      (idToHomEquiv G x y))) a b).
Qed.

Lemma homFamilyEqRew (G: UnivalentGroupoid) {a b: G.(CObj)} (v: G.(CHom) a b):
  rew [fun K: G.(CObj) -> G.(CObj) -> HSet => Dom (K a b)] (homFamilyEq G)
    in v = homToId v.
Proof.
  rewrite (rew_map Dom (fun K: G.(CObj) -> G.(CObj) -> HSet => K a b)).
  rewrite homFamilyEqAt. now apply hsetEqRewSym.
Qed.

Lemma piOneClassifyCat (G: UnivalentGroupoid): G.(gcat) = pathCat (gobj G).
Proof.
  refine (catEqOf G.(gcat) _ _ _ _ _ _ (homFamilyEq G) _ _).
  - intro a. rewrite homFamilyEqRew. now apply homToIdId.
  - intros a b d f g. rewrite 3 homFamilyEqRew. now apply homToIdComp.
Qed.

Lemma piOneClassify (G: UnivalentGroupoid): pathGpd (classGpd G) = G.
Proof.
  now apply eq_sym, univalentGroupoidEqCat, piOneClassifyCat.
Qed.

(** The comparison on 1-cells and 2-cells *)

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

Definition piOneHom2Equiv {A B: HGpd} (f g: A -> B):
  Equiv (@Hom2 HGpd2Cat A B f g) (NatTrans (piOne.(f2hom) f) (piOne.(f2hom) g)).
Proof.
  unshelve refine (qinvEquiv (pathNat f g) (fun α => α.(ncomp)) _ _).
  - now intro α.
  - intro α. apply natTransEq; intro x. now reflexivity.
Defined.

(** The types of 1-types and of groupoids

    The two object maps are inverse, so the two types are equivalent and, by
    univalence, equal. *)

Definition hgpdUnivalentGroupoidEquiv: Equiv HGpd UnivalentGroupoid :=
  qinvEquiv pathGpd classGpd classifyPiOne piOneClassify.

Definition hgpdEqUnivalentGroupoid: HGpd = UnivalentGroupoid := ua hgpdUnivalentGroupoidEquiv.

(** The equality of the two 2-categories

    [piOne] identifies [HGpd2Cat] with [UnivGpd2Cat] degreewise: on objects by
    [hgpdEqUnivalentGroupoid], on 1-cells by [piOneHomEquiv] and on 2-cells by
    [piOneHom2Equiv], each turned into an equality by univalence and matched
    with the corresponding map of [piOne] by the computation rules of
    univalence ([uaRew], [hsetEqRew]).

    Preservation of the unitors and associator is checked on the
    components of the corresponding natural transformations. *)

Definition hgpd2CatHomEq (A B: HGpd):
  (Hom HGpd2Cat) A B = (Hom UnivGpd2Cat) (piOne.(f2obj) A) (piOne.(f2obj) B) :=
  ua (piOneHomEquiv A B).

Definition hgpd2CatHom2Eq (A B: HGpd) (f g: (Hom HGpd2Cat) A B):
  @Hom2 HGpd2Cat A B f g
  = @Hom2 UnivGpd2Cat (piOne.(f2obj) A) (piOne.(f2obj) B)
      (piOne.(f2hom) f) (piOne.(f2hom) g) :=
  hsetEq (h1 := @Hom2 HGpd2Cat A B f g)
    (h2 := @Hom2 UnivGpd2Cat (piOne.(f2obj) A) (piOne.(f2obj) B)
             (piOne.(f2hom) f) (piOne.(f2hom) g))
    (piOneHom2Equiv f g).

Lemma hgpd2CatEqUnivGpd2Cat: HGpd2Cat = UnivGpd2Cat.
Proof.
  unshelve refine (bicategoryEq HGpd2Cat UnivGpd2Cat piOne hgpdEqUnivalentGroupoid _
    hgpd2CatHomEq _ hgpd2CatHom2Eq _).
  - apply functional_extensionality_dep; intro A.
    now exact (eq_sym (uaRew hgpdUnivalentGroupoidEquiv A)).
  - apply functional_extensionality_dep; intro A.
    apply functional_extensionality_dep; intro B.
    apply functional_extensionality_dep; intro f.
    now exact (eq_sym (uaRew (piOneHomEquiv A B) f)).
  - apply functional_extensionality_dep; intro A.
    apply functional_extensionality_dep; intro B.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    apply functional_extensionality_dep; intro α.
    now exact (eq_sym (hsetEqRew (h1 := @Hom2 HGpd2Cat A B f g)
      (h2 := @Hom2 UnivGpd2Cat (piOne.(f2obj) A) (piOne.(f2obj) B)
               (piOne.(f2hom) f) (piOne.(f2hom) g))
      (piOneHom2Equiv f g) α)).
Qed.
