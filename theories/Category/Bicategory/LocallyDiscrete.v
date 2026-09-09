(** A category as a bicategory whose 2-cells are equalities of arrows.
    Since the hom-types are h-sets, parallel 2-cells agree. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation.
From Bonak.Category.Bicategory Require Export Bicategory.
Set Primitive Projections.
Set Printing Projections.

Definition discreteHomCategory (X: HSet): Category.
Proof.
  refine {| CObj := X;
    CHom f g := {| Dom := f = g;
      UIP p q α β := eq_hprop_UIP (fun p q => @UIP X f g p q) α β |};
    cid f := eq_refl;
    ccomp f g h α β := α • β |}; intros; apply X.
Defined.

Definition locallyDiscrete (C: Category): Bicategory.
Proof.
  unshelve refine {|
    BObj := C.(CObj);
    BHom a b := discreteHomCategory (C.(CHom) a b);
    bid := C.(cid);
    bcomp a b c := @ccomp C a b c;
    bwhiskerL a b c f g h α := f_equal (C.(ccomp) f) α;
    bwhiskerR a b c f g α h := f_equal (fun u => C.(ccomp) u h) α;
    bunitL a b f := Build_Iso (discreteHomCategory (C.(CHom) a b)) _ _ (C.(cidl) f) _;
    bunitR a b f := Build_Iso (discreteHomCategory (C.(CHom) a b)) _ _ (C.(cidr) f) _;
    bassoc a b c d f g h := Build_Iso (discreteHomCategory (C.(CHom) a d)) _ _ (C.(cassoc) f g h) _;
  |}.
  - intros. refine (@Build_IsInvertible (discreteHomCategory _) _ _ (C.(cidl) f) (eq_sym (C.(cidl) f)) _ _); apply (C.(CHom)).
  - intros. refine (@Build_IsInvertible (discreteHomCategory _) _ _ (C.(cidr) f) (eq_sym (C.(cidr) f)) _ _); apply (C.(CHom)).
  - intros. refine (@Build_IsInvertible (discreteHomCategory _) _ _ (C.(cassoc) f g h) (eq_sym (C.(cassoc) f g h)) _ _); apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).
  - intros; apply (C.(CHom)).

Defined.

Definition locallyDiscreteGroupoid (C: Category): IsLocallyGroupoid (locallyDiscrete C).
Proof.
  intros a b f g α. refine (@Build_IsInvertible (discreteHomCategory _) _ _ α (eq_sym α) _ _); apply (C.(CHom)).
Defined.
