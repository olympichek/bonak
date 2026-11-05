(** This file defines HGpd and provides unit and sigT on HGpd. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet.
From Bonak.Lib Require Import Notation RewLemmas Equiv Univalence.
From Stdlib Require Import Logic.FunctionalExtensionality.

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

(** A transparent copy of Stdlib's [Eqdep_dec.UIP_dec] (Hedberg's
    theorem): the stdlib proof chain is [Qed]-opaque, which would leave
    normal forms of groupoid-level coherences stuck on it. *)

Section EqdepDec.

Variable A: Type.

Let comp {x y y': A} (eq1: x = y) (eq2: x = y'): y = y' :=
  eq_ind _ (fun a => a = y') eq2 _ eq1.

Remark trans_sym_eq {x y: A} (u: x = y): comp u u = eq_refl y.
Proof.
  case u; trivial.
Defined.

Variable x: A.
Variable eq_dec: forall y: A, x = y \/ x <> y.

Let nu {y: A} (u: x = y): x = y :=
  match eq_dec y with
  | or_introl eqxy => eqxy
  | or_intror neqxy => False_ind _ (neqxy u)
  end.

#[local]
Lemma nu_constant {y: A} (u v: x = y): nu u = nu v.
Proof.
  unfold nu.
  destruct (eq_dec y) as [Heq|Hneq].
  - reflexivity.
  - case Hneq; trivial.
Defined.

Let nu_inv {y: A} (v: x = y): x = y := comp (nu (eq_refl x)) v.

Remark nu_left_inv_on {y: A} (u: x = y): nu_inv (nu u) = u.
Proof.
  case u; unfold nu_inv.
  apply trans_sym_eq.
Defined.

Theorem eq_proofs_unicity_on (y: A) (p1 p2: x = y): p1 = p2.
Proof.
  elim (nu_left_inv_on p1).
  elim (nu_left_inv_on p2).
  elim (nu_constant p1 p2).
  reflexivity.
Defined.

End EqdepDec.

Theorem UIP_dec (A: Type) (eq_dec: forall x y: A, {x = y} + {x <> y})
  (x y: A) (p1 p2: x = y): p1 = p2.
Proof.
  apply eq_proofs_unicity_on.
  intros y'; destruct (eq_dec x y'); [now left | now right].
Defined.

Lemma unit_GUIP (x y: unit) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply unit_UIP.
Defined.


Definition gunit@{m}: HGpd@{m} := {|
  GDom := unit;
  GUIP := unit_GUIP;
|}.

(** Every [HSet] is canonically an [HGpd]. *)

Definition hgpdOfHSet (A: HSet): HGpd := {|
  GDom := A;
  GUIP := fun x y h g p q =>
    eq_hprop_UIP (fun p q => A.(UIP)) p q;
|}.

(** The path space of an [HGpd], regarded one truncation level up. *)

Definition gpaths {A: HGpd} (x y: A): HGpd :=
  hgpdOfHSet (hpaths x y).


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

(** Equality of [HGpd]s from equivalence of their carriers.

    As for [HSet], univalence supplies the path between the carrier types.
    The remaining [GUIP] fields are propositions pointwise: either field
    identifies any two inhabitants of an equality between paths.  Functional
    extensionality therefore identifies the transported fields. *)

Monomorphic Definition hgpdEqIntro (g1 g2: HGpd) (p: g1.(GDom) = g2.(GDom)): g1 = g2.
Proof.
  destruct g1 as [d1 u1], g2 as [d2 u2]; cbn in p; destruct p.
  apply (f_equal (fun u => {| GDom := d1; GUIP := u |})).
  apply functional_extensionality_dep_good; intro x.
  apply functional_extensionality_dep_good; intro y.
  apply functional_extensionality_dep_good; intro h.
  apply functional_extensionality_dep_good; intro g.
  apply functional_extensionality_dep_good; intro a.
  apply functional_extensionality_dep_good; intro b.
  now apply (eq_hprop_UIP (@u1 x y h g)).
Defined.

Monomorphic Definition hgpdEq {g1 g2: HGpd} (e: Equiv g1 g2): g1 = g2 :=
  hgpdEqIntro g1 g2 (ua e).

Monomorphic Lemma hgpdEqIntroRew (g1 g2: HGpd) (p: g1.(GDom) = g2.(GDom)) (x: g1):
  rew [GDom] (hgpdEqIntro g1 g2 p) in x =
  rew [fun T: Type => T] p in x.
Proof.
  destruct g1 as [d1 u1], g2 as [d2 u2]; cbn in p; destruct p; cbn.
  rewrite <- (rew_map GDom (fun u => {| GDom := d1; GUIP := u |})).
  now apply rew_const.
Qed.

Monomorphic Lemma hgpdEqRew {g1 g2: HGpd} (e: Equiv g1 g2) (x: g1):
  rew [GDom] (hgpdEq e) in x = e x.
Proof.
  unfold hgpdEq. rewrite hgpdEqIntroRew. now apply uaRew.
Qed.

Monomorphic Lemma hgpdEqRewSym {g1 g2: HGpd} (e: Equiv g1 g2) (x: g2):
  rew [GDom] (eq_sym (hgpdEq e)) in x = invEq e x.
Proof.
  apply (eqvInj e).
  now exact (eq_sym (hgpdEqRew e _)
    • (rew_sym_cancel_r (P := GDom) (hgpdEq e) x • eq_sym (secEq e x))).
Qed.

(** Univalence as induction on equivalences of 1-types and their families. *)

Definition hgpdEquivInd (A: HGpd)
  (P: forall B: HGpd, Equiv A B -> Type) (h: P A idEquiv)
  (B: HGpd) (e: Equiv A B): P B e.
Proof.
  destruct A as [A u], B as [B v]. cbn in e.
  revert v. refine (equivInd
    (fun B e => forall v, P {| GDom := B; GUIP := v |} e) _ e).
  intro v.
  assert (q: u = v).
  { repeat (apply functional_extensionality_dep; intro).
    now apply (eq_hprop_UIP (u _ _ _ _)). }
  destruct q. now exact h.
Defined.

Definition hgpdEquivContr (A B: HGpd) (e: Equiv A B):
  existT (fun C: HGpd => Equiv A C) A idEquiv = (B; e) :=
  hgpdEquivInd A (fun B e =>
    existT (fun C: HGpd => Equiv A C) A idEquiv = (B; e)) eq_refl B e.

Definition hgpdFamilyEquivInd {I: Type} (H: I -> HGpd)
  (P: forall K: I -> HGpd, (forall i, Equiv (H i) (K i)) -> Type)
  (h: P H (fun _ => idEquiv)) (K: I -> HGpd)
  (e: forall i, Equiv (H i) (K i)): P K e.
Proof.
  assert (q: (fun i => existT (fun C: HGpd => Equiv (H i) C) (H i) idEquiv)
    = (fun i => (K i; e i))).
  { apply functional_extensionality_dep. intro i. now apply hgpdEquivContr. }
  pose (r := f_equal (fun z: forall i, {C: HGpd &T Equiv (H i) C} =>
    existT (fun L: I -> HGpd => forall i, Equiv (H i) (L i))
      (fun i => (z i).1) (fun i => (z i).2)) q).
  now exact (@eq_rect {L: I -> HGpd &T forall i, Equiv (H i) (L i)}
    (H; fun _ => idEquiv) (fun z => P z.1 z.2) h (K; e) r).
Defined.
