Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Export Bicategory.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** Functions between 1-types and homotopies form a groupoid. *)
Definition hgpdHomCategory (X Y: HGpd): Category.
Proof.
  refine {| CObj := X -> Y;
    CHom f g := hpiT (fun x: X => hpaths (f x) (g x));
    cid f := fun x => eq_refl;
    ccomp f g h α β := fun x => α x • β x |}.
  - intros f g α. apply functional_extensionality_dep; intro x. apply eq_trans_refl_l.
  - intros; reflexivity.
  - intros f g h i α β γ. apply functional_extensionality_dep; intro x. apply eqTransAssoc.
Defined.

(** The bicategory of 1-types, functions, and homotopies. *)
Definition HGpd2Cat: Bicategory.
Proof.
  unshelve refine {|
    BObj := HGpd;
    BHom := hgpdHomCategory;
    bid a := fun x => x;
    bcomp a b c f g := fun x => g (f x);
    bwhiskerL a b c f g h α := fun x => α (f x);
    bwhiskerR a b c f g α h := fun x => f_equal h (α x);
    bunitL a b f := idToIso eq_refl;
    bunitR a b f := idToIso eq_refl;
    bassoc a b c d f g h := idToIso eq_refl;
  |}; intros; apply functional_extensionality_dep; intro x; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply eq_trans_map_distr.
  - destruct (α x). cbn. apply eq_trans_refl_l.
  - apply eq_sym, eq_trans_refl_l.
  - rewrite f_equal_id. apply eq_sym, eq_trans_refl_l.
  - apply eq_sym, eq_trans_refl_l.
  - rewrite f_equal_compose. apply eq_sym, eq_trans_refl_l.
  - apply eq_sym, eq_trans_refl_l.
  - reflexivity.
  - reflexivity.
Defined.

Definition hgpdLocallyGroupoid: IsLocallyGroupoid HGpd2Cat.
Proof.
  intros X Y f g α.
  refine (@Build_IsInvertible (hgpdHomCategory X Y) f g α (fun x => eq_sym (α x)) _ _);
    apply functional_extensionality_dep; intro x; cbn; destruct (α x); reflexivity.
Defined.

(** Function composition has reflexivity witnesses for its three laws. *)
Definition hgpdUnitL {X Y: HGpd} (f: X -> Y):
  (fun x => f x) = f := eq_refl.
Definition hgpdUnitR {X Y: HGpd} (f: X -> Y):
  (fun x => f x) = f := eq_refl.
Definition hgpdAssoc {X Y Z W: HGpd} (f: X -> Y) (g: Y -> Z) (h: Z -> W):
  (fun x => h (g (f x))) = (fun x => h (g (f x))) := eq_refl.

(** Evaluating transport of a 2-cell of [HGpd2Cat] at a point. *)

Lemma hom2RewPt {X Y: HGpd} {f f' g g': X -> Y} (p: f = f') (q: g = g')
  (α: forall x: X, f x = g x) (x: X):
  @hom2Rew HGpd2Cat X Y f f' g g' p q α x
  = eq_sym (f_equal (fun h => h x) p) • (α x • f_equal (fun h => h x) q).
Proof. destruct p, q; simpl. now destruct (α x). Defined.

(** Pointwise computation of transport, identities and whiskering in [HGpd2Cat]. *)

Lemma rewC2Pt {a d: HGpd} {U V V': (@Hom HGpd2Cat) a d} (q: V = V')
  (β: (Hom2 (B := HGpd2Cat)) U V) (X: a):
  (rew [fun v: (@Hom HGpd2Cat) a d => (Hom2 (B := HGpd2Cat)) U v] q in β) X
  = β X • f_equal (fun w: (@Hom HGpd2Cat) a d => w X) q.
Proof. now destruct q. Defined.

Lemma hgpd2CatI2Pt {X Y: HGpd} (g: X -> Y) (x: X):
  @id2 HGpd2Cat X Y g x = eq_refl.
Proof. now reflexivity. Defined.

Lemma psfUnitLAlgebra {X Y: HGpd} (g: (@Hom HGpd2Cat) X Y)
  {u: (@Hom HGpd2Cat) X X} {c: (@Hom HGpd2Cat) X Y}
  (P: u = (id1 (B := HGpd2Cat)) X) (K: (comp1 (B := HGpd2Cat)) ((id1 (B := HGpd2Cat)) X) g = c) (x: X):
  f_equal (fun h: X -> Y => h x)
    (f_equal (fun v: (@Hom HGpd2Cat) X X => (comp1 (B := HGpd2Cat)) v g) P • K)
  = f_equal g (f_equal (fun h: X -> X => h x) P)
    • f_equal (fun h: X -> Y => h x) K.
Proof. destruct K, P. now reflexivity. Defined.

Lemma psfUnitRAlgebra {X Y: HGpd} (g: (@Hom HGpd2Cat) X Y)
  {u: (@Hom HGpd2Cat) Y Y} {c: (@Hom HGpd2Cat) X Y}
  (P: u = (id1 (B := HGpd2Cat)) Y) (K: (comp1 (B := HGpd2Cat)) g ((id1 (B := HGpd2Cat)) Y) = c) (x: X):
  f_equal (fun h: X -> Y => h x) (f_equal (@comp1 HGpd2Cat X Y Y g) P • K)
  = f_equal (fun h: Y -> Y => h (g x)) P
    • f_equal (fun h: X -> Y => h x) K.
Proof. destruct K, P. now reflexivity. Defined.
