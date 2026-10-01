Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Export Bicategory.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** Functions between 1-types and homotopies form a groupoid. *)
Definition hgpdHomCategory (X Y: HGpd): Category := {|
  CObj := X -> Y;
  CHom f g := hpiT (fun x: X => hpaths (f x) (g x));
  cid f := fun x => eq_refl;
  ccomp f g h α β := fun x => α x • β x;
  cidl f g α := functional_extensionality_dep _ _
    (fun x => eq_trans_refl_l (α x));
  cidr f g α := eq_refl;
  cassoc f g h i α β γ := functional_extensionality_dep _ _
    (fun x => eqTransAssoc (α x) (β x) (γ x));
|}.

Local Lemma homotopyInterchange {X Y: Type} {f g: X -> Y}
  (α: forall x, f x = g x) {x y: X} (p: x = y):
  f_equal f p • α y = α x • f_equal g p.
Proof. destruct p. cbn. now apply eq_trans_refl_l. Defined.

Local Lemma homotopyUnitRNat {X: Type} {x y: X} (p: x = y):
  f_equal (fun z => z) p = eq_refl • p.
Proof. rewrite f_equal_id. now apply eq_sym, eq_trans_refl_l. Defined.

Local Lemma homotopyAssocNatR {X Y Z: Type} (f: X -> Y) (g: Y -> Z)
  {x y: X} (p: x = y):
  f_equal g (f_equal f p) = eq_refl • f_equal (fun z => g (f z)) p.
Proof. rewrite f_equal_compose. now apply eq_sym, eq_trans_refl_l. Defined.

(** The bicategory of 1-types, functions, and homotopies. Its coherence
    laws follow pointwise from path composition and congruence. *)
Definition HGpd2Cat: Bicategory := {|
  BObj := HGpd;
  BHom := hgpdHomCategory;
  bid a := fun x => x;
  bcomp a b c f g := fun x => g (f x);
  bwhiskerL a b c f g h α := fun x => α (f x);
  bwhiskerR a b c f g α h := fun x => f_equal h (α x);
  bunitL a b f := idToIso eq_refl;
  bunitR a b f := idToIso eq_refl;
  bassoc a b c d f g h := idToIso eq_refl;
  bwhiskerLId a b c f g := functional_extensionality_dep _ _ (fun x => eq_refl);
  bwhiskerRId a b c f g := functional_extensionality_dep _ _ (fun x => eq_refl);
  bwhiskerLComp a b c f g h i α β :=
    functional_extensionality_dep _ _ (fun x => eq_refl);
  bwhiskerRComp a b c f g h α β i := functional_extensionality_dep _ _
    (fun x => @eq_trans_map_distr _ _ _ _ _ i (α x) (β x));
  binterchange a b c f g h i α β := functional_extensionality_dep _ _
    (fun x => homotopyInterchange β (α x));
  bunitLNat a b f g α := functional_extensionality_dep _ _
    (fun x => eq_sym (eq_trans_refl_l (α x)));
  bunitRNat a b f g α := functional_extensionality_dep _ _
    (fun x => homotopyUnitRNat (α x));
  bassocNatL a b c d f g h i α := functional_extensionality_dep _ _
    (fun x => eq_sym (eq_trans_refl_l (α (g (f x)))));
  bassocNatR a b c d f g α h i := functional_extensionality_dep _ _
    (fun x => homotopyAssocNatR h i (α x));
  bassocNatM a b c d f g h α i := functional_extensionality_dep _ _
    (fun x => eq_sym (eq_trans_refl_l (f_equal i (α (f x)))));
  btriangle a b c f g := functional_extensionality_dep _ _ (fun x => eq_refl);
  bpentagon a b c d e f g h i := functional_extensionality_dep _ _ (fun x => eq_refl);
|}.

Local Lemma homotopyInverseR {X: Type} {x y: X} (p: x = y):
  p • eq_sym p = eq_refl.
Proof. now destruct p. Defined.

Local Lemma homotopyInverseL {X: Type} {x y: X} (p: x = y):
  eq_sym p • p = eq_refl.
Proof. now destruct p. Defined.

Definition hgpdLocallyGroupoid: IsLocallyGroupoid HGpd2Cat :=
  fun X Y f g α =>
    @Build_IsInvertible (hgpdHomCategory X Y) f g α (fun x => eq_sym (α x))
      (functional_extensionality_dep _ _ (fun x => homotopyInverseR (α x)))
      (functional_extensionality_dep _ _ (fun x => homotopyInverseL (α x))).

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
