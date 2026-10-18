(** 2-truncated types, with unit and dependent-sum constructors. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet SSGpd.HGpd.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** An [H2Gpd] has identity types that are [HGpd]s. *)

Record H2Gpd := {
  G2Dom:> Type;
  G2UIP {x y: G2Dom} {h g: x = y} {p q: h = g} {α β: p = q}: α = β;
}.

Definition g2paths {A: H2Gpd} (x y: A): HGpd := {|
  GDom := x = y;
  GUIP := @G2UIP A x y;
|}.

Lemma gpd_G2UIP {X: HGpd} {x y: X} {h g: x = y} {p q: h = g} (α β: p = q):
  α = β.
Proof.
  now apply (eq_hprop_UIP (@GUIP X x y h g)).
Defined.

Lemma unit_G2UIP (x y: unit) (h g: x = y) (p q: h = g) (α β: p = q): α = β.
Proof.
  now apply (eq_hprop_UIP (unit_GUIP x y h g)).
Defined.

Definition g2unit@{m}: H2Gpd@{m} := {|
  G2Dom := unit;
  G2UIP := unit_G2UIP;
|}.

(** A retract of a 1-truncated type is 1-truncated: [retract_UIP] applied
    to the path spaces, with [retract_eq] as the retraction identity. *)

Lemma retract_GUIP {A: Type} {B: HGpd} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) (x y: A) (h k: x = y) (p q: h = k): p = q.
Proof.
  eapply (retract_UIP (B := hpaths (f x) (f y))
    (fun r: x = y => f_equal f r)
    (fun r => eq_trans (eq_sym (H x)) (eq_trans (f_equal g r) (H y)))).
  intro r. symmetry. now apply retract_eq.
Defined.

(** [sigT] seen as a type constructor on [H2Gpd] *)

Definition sigT_path_gcode {A: H2Gpd} {B: A -> H2Gpd} (x y: {a: A &T B a}):
  HGpd :=
  gsigT (A := g2paths x.1 y.1)
    (fun p => g2paths (rew [B] p in x.2) y.2).

Definition sigT_path_gencode {A: H2Gpd} {B: A -> H2Gpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_gcode x y :=
  (projT1_eq p; projT2_eq p).

Definition sigT_path_gdecode {A: H2Gpd} {B: A -> H2Gpd} {x y: {a: A &T B a}}
  (p: sigT_path_gcode x y): x = y :=
  (= p.1; p.2).

Lemma sigT_path_gdecode_gencode {A: H2Gpd} {B: A -> H2Gpd}
  {x y: {a: A &T B a}} (p: x = y):
  sigT_path_gdecode (sigT_path_gencode p) = p.
Proof.
  symmetry. now apply sigT_decompose_eq.
Defined.

Lemma sigT_G2UIP {A: H2Gpd} {B: A -> H2Gpd} (x y: {a: A &T B a})
  (h g: x = y) (p q: h = g) (α β: p = q): α = β.
Proof.
  eapply retract_GUIP with
    (f := @sigT_path_gencode A B x y)
    (g := @sigT_path_gdecode A B x y).
  now exact sigT_path_gdecode_gencode.
Defined.

Definition g2sigT {A: H2Gpd} (B: A -> H2Gpd): H2Gpd := {|
  G2Dom := {a: A &T B a};
  G2UIP := sigT_G2UIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (g2sigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (g2sigT (A := A) (fun x => P%type)): type_scope.
