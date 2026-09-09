(** Groupoids separate invertibility of arrows from categorical univalence.
    For univalent groupoids, the canonical map from object paths to arrows
    is an equivalence, and the object type is a 1-type. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation.
From Bonak Require Import νGpd.HGpd.
From Bonak.Lib Require Import Equiv Contractible.
From Bonak.Category Require Export Category.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Set Keyed Unification.

(** Univalent groupoids *)

Definition IsGroupoid (C: Category): Type :=
  forall a b (f: C.(CHom) a b), IsInvertible f.

Lemma isGroupoidProp {C} (u v: IsGroupoid C): u = v.
Proof.
  repeat (apply functional_extensionality_dep; intro). apply isInvertibleProp.
Qed.

Record Groupoid := {
  gcat:> Category;
  groupoidInvertibility: IsGroupoid gcat;
}.

Record UnivalentGroupoid := {
  underlyingGroupoid:> Groupoid;
  groupoidUnivalence: IsUnivalentCategory underlyingGroupoid;
}.

Definition guniv (G: UnivalentGroupoid) (a b: G.(CObj))
  (f: G.(CHom) a b): Contr {p: a = b &T idToHom p = f}.
Proof.
  pose (e := idToIsoEquiv G.(groupoidUnivalence) a b).
  pose (i := {| isoHom := f; isoInvertible := G.(groupoidInvertibility) a b f |}).
  exists (invEq e i; eq_sym (idToIsoHom (invEq e i)) • f_equal isoHom (secEq e i)).
  intros [p h]. unshelve refine (eq_existT_curried _ _).
  - refine (f_equal (invEq e) _ • retEq e p).
    apply isoEq. cbn. now rewrite idToIsoHom.
  - apply (G.(CHom) a b).
Defined.

(** The two round trips of [idToHom]. The retraction is the first component
    of the contraction applied to the fibre element [(p; eq_refl)]. *)

Definition homToId {G: UnivalentGroupoid} {a b: G.(CObj)} (f: G.(CHom) a b): a = b :=
  ((guniv G) a b f).1.1.

Definition idToHomToId {G: UnivalentGroupoid} {a b: G.(CObj)} (f: G.(CHom) a b):
  idToHom (homToId f) = f := ((guniv G) a b f).1.2.

Lemma homToIdToHom {G: UnivalentGroupoid} {a b: G.(CObj)} (p: a = b):
  homToId (idToHom p) = p.
Proof.
  now exact (f_equal (fun z => z.1)
    (((guniv G) a b (idToHom p)).2 (p; eq_refl))).
Qed.

Definition idToHomEquiv (G: UnivalentGroupoid) (a b: G.(CObj)):
  Equiv (a = b) (G.(CHom) a b) :=
  qinvEquiv idToHom homToId homToIdToHom idToHomToId.

Lemma idToHomInj {G: UnivalentGroupoid} {a b: G.(CObj)} (p q: a = b)
  (e: idToHom p = idToHom q): p = q.
Proof.
  now exact (eq_sym (homToIdToHom p) • (f_equal homToId e • homToIdToHom q)).
Qed.

Lemma homToIdId {G: UnivalentGroupoid} (a: G.(CObj)): homToId (G.(cid) a) = eq_refl.
Proof.
  now exact (homToIdToHom (eq_refl: a = a)).
Qed.

Lemma homToIdComp {G: UnivalentGroupoid} {a b c: G.(CObj)} (u: G.(CHom) a b)
  (v: G.(CHom) b c): homToId (u ⨟ v) = homToId u • homToId v.
Proof.
  apply idToHomInj.
  now rewrite <- idToHomTrans, 3 idToHomToId.
Qed.

Lemma homToIdFhom {G H: UnivalentGroupoid} (F: Functor G.(gcat) H.(gcat))
  {a b: G.(CObj)} (u: G.(CHom) a b):
  homToId (F.(fhom) u) = f_equal F.(fobj) (homToId u).
Proof.
  apply idToHomInj.
  now rewrite <- fhomIdToHom, 2 idToHomToId.
Qed.

(** A quasi-inverse of [idToHom] suffices to build the univalence field: the
    fibre element is unique in its first component by injectivity of
    [idToHom], and in its second by [UIP] of the hom-h-set. *)

Lemma univFromQinv (C: Category) (h: forall a b, C.(CHom) a b -> a = b)
  (Hs: forall a b (f: C.(CHom) a b), idToHom (h a b f) = f)
  (Hr: forall a b (p: a = b), h a b (idToHom p) = p)
  (a b: C.(CObj)) (f: C.(CHom) a b): Contr {p: a = b &T idToHom p = f}.
Proof.
  exists (h a b f; Hs a b f); intro x.
  refine (eq_existT_curried (f_equal (h a b) (eq_sym x.2) • Hr a b x.1) _).
  now apply (C.(CHom) a b).
Qed.

(** The objects of a univalent groupoid form a 1-type: their identity types retract
    onto the hom-h-sets. *)

Definition gobj (G: UnivalentGroupoid): HGpd := {|
  GDom := G.(CObj);
  GUIP x y := retract_UIP (@idToHom G x y) (@homToId G x y) homToIdToHom;
|}.

(** Inversion in groupoids. *)

Definition ginv {G: Groupoid} {a b: G.(CObj)} (f: G.(CHom) a b):
  G.(CHom) b a := inverse (G.(groupoidInvertibility) a b f).

Lemma ginvR {G: Groupoid} {a b: G.(CObj)} (f: G.(CHom) a b):
  f ⨟ ginv f = G.(cid) a.
Proof.
  exact (inverseR (G.(groupoidInvertibility) a b f)).
Qed.

Lemma ginvL {G: Groupoid} {a b: G.(CObj)} (f: G.(CHom) a b):
  ginv f ⨟ f = G.(cid) b.
Proof.
  exact (inverseL (G.(groupoidInvertibility) a b f)).
Qed.

(** Conjugating a commuting square by the inverses of its vertical sides *)

Lemma ginvCancel {G: Groupoid} {a b c d: G.(CObj)} (u: G.(CHom) a b)
  (v: G.(CHom) c d) (m: G.(CHom) a c) (n: G.(CHom) b d)
  (E: u ⨟ n = m ⨟ v): ginv m ⨟ u = v ⨟ ginv n.
Proof.
  rewrite <- (G.(cidr) u), <- (ginvR n), <- (G.(cassoc) u n (ginv n)), E.
  rewrite (G.(cassoc) m v (ginv n)), <- (G.(cassoc) (ginv m) m (v ⨟ ginv n)).
  rewrite (ginvL m). now apply G.(cidl).
Qed.

(** A natural transformation between functors into a groupoid is invertible:
    its components are, and naturality is preserved by conjugation. *)

Definition natInv {C: Category} {H: Groupoid} {F F': Functor C H} (α: NatTrans F F'):
  NatTrans F' F := {|
  ncomp a := ginv (α.(ncomp) a);
  nnat a b f := eq_sym (ginvCancel (F.(fhom) f) (F'.(fhom) f)
    (α.(ncomp) a) (α.(ncomp) b) (α.(nnat) f));
|}.

Definition natInvertible {C: Category} {H: Groupoid} {F F': Functor C H}
  (α: NatTrans F F'): @IsInvertible (functorCategory C H) F F' α.
Proof.
  refine (@Build_IsInvertible (functorCategory C H) F F' α (natInv α) _ _).
  - apply natTransEq; intro x. apply ginvR.
  - apply natTransEq; intro x. apply ginvL.
Defined.

(** Invertibility and univalence are properties, so univalent groupoids
    with equal underlying categories are equal. *)

Lemma univalentGroupoidEqCat (G H: UnivalentGroupoid)
  (e: G.(gcat) = H.(gcat)): G = H.
Proof.
  destruct G as [[Gc Gi] Gu], H as [[Hc Hi] Hu]; cbn in e. destruct e.
  destruct (isGroupoidProp Gi Hi).
  now destruct (isUnivalentCategoryProp Gu Hu).
Qed.

Definition univalentGroupoidFromPaths (C: Category)
  (u: forall a b (f: C.(CHom) a b), Contr {p: a = b &T idToHom p = f}):
  UnivalentGroupoid.
Proof.
  assert (gi: IsGroupoid C).
  { intros a b f. destruct (u a b f).1 as [p e]. destruct e, p.
    exact {| inverse := cid a; inverseR := C.(cidl) _; inverseL := C.(cidl) _ |}. }
  refine {| underlyingGroupoid := {| gcat := C; groupoidInvertibility := gi |};
            groupoidUnivalence := _ |}.
  intros a b i. destruct (u a b i.(isoHom)).1 as [p e].
  exists (p; isoEq (idToIso p) i (idToIsoHom p • e)).
  intros [q h]. unshelve refine (eq_existT_curried _ _).
  - exact (f_equal (fun z => z.1)
      (eq_sym ((u a b i.(isoHom)).2 (p; e))
       • (u a b i.(isoHom)).2
          (q; eq_sym (idToIsoHom q) • f_equal isoHom h))).
  - apply (isoSet C a b).
Defined.

Lemma univalentGroupoidFromPathsRet (G: UnivalentGroupoid):
  univalentGroupoidFromPaths G (guniv G) = G.
Proof. apply univalentGroupoidEqCat. reflexivity. Qed.

Lemma univalentGroupoidFromPathsSec (C: Category)
  (u: forall a b (f: C.(CHom) a b), Contr {p: a = b &T idToHom p = f}):
  guniv (univalentGroupoidFromPaths C u) = u.
Proof.
  repeat (apply functional_extensionality_dep; intro). apply contrProp.
Qed.
