(** This file defines HGpd and provides unit, sigT and forall on HGpd. *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Eqdep_dec.

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** [HGpd] is the next truncation level: its identity types are [HSet]s. *)

Record HGpd := {
  GDom:> Type;
  GUIP {x y: GDom} {h g: x = y} {p q: h = g}: p = q;
}.

Definition hpaths {A: HGpd} (x y: A): HSet := {|
  Dom := x = y;
  UIP := @GUIP A x y;
|}.

Lemma retract_eq {A B: Type} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) {x y: A} (p: x = y):
  p = eq_trans (eq_sym (H x)) (eq_trans (f_equal g (f_equal f p)) (H y)).
Proof.
  destruct p; simpl. destruct (H x). reflexivity.
Qed.

Lemma retract_UIP {A: Type} {B: HSet} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) (x y: A) (p q: x = y): p = q.
Proof.
  rewrite (retract_eq f g H p).
  rewrite (retract_eq f g H q).
  now rewrite (@UIP B (f x) (f y) (f_equal f p) (f_equal f q)).
Qed.

Lemma unit_GUIP (x y: unit) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply unit_UIP.
Qed.

Lemma bool_GUIP (x y: bool) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply bool_UIP.
Qed.

Definition gunit@{m}: HGpd@{m} := {|
  GDom := unit;
  GUIP := unit_GUIP;
|}.

Definition gbool@{m}: HGpd@{m} := {|
  GDom := bool;
  GUIP := bool_GUIP;
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
Qed.

Lemma sigT_GUIP {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a})
  (h g: x = y) (p q: h = g): p = q.
Proof.
  eapply retract_UIP with
    (f := @sigT_path_encode A B x y)
    (g := @sigT_path_decode A B x y).
  exact sigT_path_decode_encode.
Qed.

Definition gsigT {A: HGpd} (B: A -> HGpd): HGpd := {|
  GDom := {a: A &T B a};
  GUIP := sigT_GUIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (gsigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (gsigT (A := A) (fun x => P%type)): type_scope.

(** [forall] defined over an [HGpd] codomain *)

Lemma gpiT_decompose {A: Type} (B: A -> HGpd)
  (f g: forall a: A, B a) (p: f = g):
  functional_extensionality_dep_good _ _
    (fun x => f_equal (fun H => H x) p) = p.
Proof.
  destruct p; now apply functional_extensionality_dep_good_refl.
Qed.

Definition piT_path_code {A: Type} (B: A -> HGpd)
  (f g: forall a: A, B a): HSet :=
  hpiT (fun a => hpaths (f a) (g a)).

Definition piT_path_encode {A: Type} {B: A -> HGpd}
  {f g: forall a: A, B a} (p: f = g): piT_path_code B f g :=
  fun a => f_equal (fun H => H a) p.

Definition piT_path_decode {A: Type} {B: A -> HGpd}
  {f g: forall a: A, B a} (p: piT_path_code B f g): f = g :=
  functional_extensionality_dep_good _ _ p.

Definition gpiT_GUIP {A: Type} (B: A -> HGpd) (f g: forall a: A, B a)
  (h i: f = g) (p q: h = i): p = q.
Proof.
  eapply retract_UIP with
    (f := @piT_path_encode A B f g)
    (g := @piT_path_decode A B f g).
  exact (gpiT_decompose B f g).
Qed.

Definition gpiT {A: Type} (B: A -> HGpd): HGpd.
Proof.
  exists (forall a: A, B a). now apply gpiT_GUIP.
Defined.

Notation "'gforall' x .. y , P" :=
  (gpiT (fun x => .. (gpiT (fun y => P%type)) ..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' 'gforall'  x  ..  y ']' ,  '/' P ']'"): type_scope.
