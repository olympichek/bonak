(** A category as a bicategory whose 2-cells are equalities of arrows.
    Since the hom-types are h-sets, parallel 2-cells agree. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.Category.Bicategory Require Export Bicategory.
Set Primitive Projections.
Set Printing Projections.

Polymorphic Definition discreteHomCategory@{u v} (X: HSet@{u}): Category@{u v} := {|
  CObj := X;
  CHom f g := {| Dom := f = g;
    UIP p q α β := eq_hprop_UIP (fun p q => @UIP X f g p q) α β |};
  cid f := eq_refl;
  ccomp f g h α β := α • β;
  cidl f g α := eq_trans_refl_l α;
  cidr f g α := eq_refl;
  cassoc f g h i α β γ := eqTransAssoc α β γ;
|}.

(** Equality 2-cells are inverted by path reversal. *)
Polymorphic Definition discreteHomInvertible@{u v} {X: HSet@{u}} {f g: X} (α: f = g):
  @IsInvertible (discreteHomCategory@{u v} X) f g α :=
  @Build_IsInvertible (discreteHomCategory X) f g α (eq_sym α)
    (eq_trans_sym_inv_r α) (eq_trans_sym_inv_l α).

Polymorphic Definition discreteHomIso@{u v} {X: HSet@{u}} {f g: X} (α: f = g):
  Iso (discreteHomCategory@{u v} X) f g :=
  Build_Iso (discreteHomCategory X) f g α (discreteHomInvertible α).

Local Lemma discreteInterchange {C: Category} {a b c}
  {f g: C.(CHom) a b} {h i: C.(CHom) b c} (α: f = g) (β: h = i):
  f_equal (fun u => u ⨟ h) α • f_equal (ccomp g) β
  = f_equal (ccomp f) β • f_equal (fun u => u ⨟ i) α.
Proof. now destruct α, β. Defined.

Local Lemma discreteUnitLNat {C: Category} {a b}
  {f g: C.(CHom) a b} (α: f = g):
  f_equal (ccomp (cid a)) α • C.(cidl) g = C.(cidl) f • α.
Proof. destruct α. now apply eq_trans_refl_l. Defined.

Local Lemma discreteUnitRNat {C: Category} {a b}
  {f g: C.(CHom) a b} (α: f = g):
  f_equal (fun u => u ⨟ cid b) α • C.(cidr) g = C.(cidr) f • α.
Proof. destruct α. now apply eq_trans_refl_l. Defined.

Local Lemma discreteAssocNatL {C: Category} {a b c d}
  (f: C.(CHom) a b) (g: C.(CHom) b c) {h i: C.(CHom) c d} (α: h = i):
  f_equal (ccomp (f ⨟ g)) α • C.(cassoc) f g i
  = C.(cassoc) f g h • f_equal (ccomp f) (f_equal (ccomp g) α).
Proof. destruct α. now apply eq_trans_refl_l. Defined.

Local Lemma discreteAssocNatR {C: Category} {a b c d}
  {f g: C.(CHom) a b} (α: f = g) (h: C.(CHom) b c) (i: C.(CHom) c d):
  f_equal (fun u => u ⨟ i) (f_equal (fun u => u ⨟ h) α) • C.(cassoc) g h i
  = C.(cassoc) f h i • f_equal (fun u => u ⨟ (h ⨟ i)) α.
Proof. destruct α. now apply eq_trans_refl_l. Defined.

Local Lemma discreteAssocNatM {C: Category} {a b c d}
  (f: C.(CHom) a b) {g h: C.(CHom) b c} (α: g = h) (i: C.(CHom) c d):
  f_equal (fun u => u ⨟ i) (f_equal (ccomp f) α) • C.(cassoc) f h i
  = C.(cassoc) f g i • f_equal (ccomp f) (f_equal (fun u => u ⨟ i) α).
Proof. destruct α. now apply eq_trans_refl_l. Defined.

(** The category laws supply the unitors and associator. Naturality follows
    by path induction; UIP supplies the triangle and pentagon relating
    the independently specified category laws. *)
Definition locallyDiscrete (C: Category): Bicategory := {|
  BObj := C.(CObj);
  BHom a b := discreteHomCategory (C.(CHom) a b);
  bid := C.(cid);
  bcomp a b c := @ccomp C a b c;
  bwhiskerL a b c f g h α := f_equal (C.(ccomp) f) α;
  bwhiskerR a b c f g α h := f_equal (fun u => C.(ccomp) u h) α;
  bunitL a b f := discreteHomIso (C.(cidl) f);
  bunitR a b f := discreteHomIso (C.(cidr) f);
  bassoc a b c d f g h := discreteHomIso (C.(cassoc) f g h);
  bwhiskerLId a b c f g := eq_refl;
  bwhiskerRId a b c f g := eq_refl;
  bwhiskerLComp a b c f g h i α β := eq_trans_map_distr (ccomp f) α β;
  bwhiskerRComp a b c f g h α β i :=
    eq_trans_map_distr (fun u => u ⨟ i) α β;
  binterchange a b c f g h i α β := discreteInterchange α β;
  bunitLNat a b f g α := discreteUnitLNat α;
  bunitRNat a b f g α := discreteUnitRNat α;
  bassocNatL a b c d f g h i α := discreteAssocNatL f g α;
  bassocNatR a b c d f g α h i := discreteAssocNatR α h i;
  bassocNatM a b c d f g h α i := discreteAssocNatM f α i;
  btriangle a b c f g := @UIP (C.(CHom) a c) _ _ _ _;
  bpentagon a b c d e f g h i := @UIP (C.(CHom) a e) _ _ _ _;
|}.

Definition locallyDiscreteGroupoid (C: Category): IsLocallyGroupoid (locallyDiscrete C) :=
  fun a b f g α => discreteHomInvertible α.
