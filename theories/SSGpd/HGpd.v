(** 1-truncated types, with unit and dependent-sum constructors. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** An [HGpd] has identity types that are [HSet]s. *)

Record HGpd := {
  GDom:> Type;
  GUIP {x y: GDom} {h g: x = y} {p q: h = g}: p = q;
}.

Definition hpaths {A: HGpd} (x y: A): HSet := {|
  Dom := x = y;
  UIP := @GUIP A x y;
|}.

Definition trans_sym_eq (A: Type) {x y: A} (u: x = y) :=
  @HSet.trans_sym_eq A x y u.

Definition nu_left_inv_on (A: Type) (x: A)
  (eq_dec: forall y: A, x = y \/ x <> y) {y: A} (u: x = y) :=
  @HSet.nu_left_inv_on A x eq_dec y u.

Definition eq_proofs_unicity_on := @HSet.eq_proofs_unicity_on.

Definition UIP_dec := @HSet.UIP_dec.

Lemma unit_GUIP (x y: unit) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply unit_UIP.
Defined.


Definition gunit@{m}: HGpd@{m} := {|
  GDom := unit;
  GUIP := unit_GUIP;
|}.


(** [sigT] seen as a type constructor on [HGpd] *)

Definition sigT_path_code {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a}):
  HSet :=
  hsigT (A := hpaths x.1 y.1)
    (fun p => hpaths (rew [B] p in x.2) y.2).

Definition sigT_path_encode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_code x y :=
  (projT1_eq p; projT2_eq p).

Definition sigT_path_decode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: sigT_path_code x y): x = y :=
  (= p.1; p.2).

Lemma sigT_path_decode_encode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_decode (sigT_path_encode p) = p.
Proof.
  symmetry. apply sigT_decompose_eq.
Defined.

Lemma sigT_GUIP {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a})
  (h g: x = y) (p q: h = g): p = q.
Proof.
  eapply retract_UIP with
    (f := @sigT_path_encode A B x y)
    (g := @sigT_path_decode A B x y).
  exact sigT_path_decode_encode.
Defined.

Definition gsigT {A: HGpd} (B: A -> HGpd): HGpd := {|
  GDom := {a: A &T B a};
  GUIP := sigT_GUIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (gsigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (gsigT (A := A) (fun x => P%type)): type_scope.
