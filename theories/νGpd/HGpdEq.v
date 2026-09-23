(** Equality of groupoids induced by equivalences of their carriers. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import Notation HSet RewLemmas Univalence νGpd.HGpd.
From Bonak.Lib Require Import Equiv.
Import Logic.EqNotations.

(** Equality of [HGpd]s from equivalence of their carriers.

    As for [HSet], univalence supplies the path between the carrier types.
    The remaining [GUIP] fields are propositions pointwise: either field
    identifies any two inhabitants of an equality between paths.  Functional
    extensionality therefore identifies the transported fields. *)

Definition hgpdEqIntro (g1 g2: HGpd) (p: g1.(GDom) = g2.(GDom)): g1 = g2.
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

Definition hgpdEq {g1 g2: HGpd} (e: Equiv g1 g2): g1 = g2 :=
  hgpdEqIntro g1 g2 (ua e).

Lemma hgpdEqIntroRew (g1 g2: HGpd) (p: g1.(GDom) = g2.(GDom)) (x: g1):
  rew [GDom] (hgpdEqIntro g1 g2 p) in x =
  rew [fun T: Type => T] p in x.
Proof.
  destruct g1 as [d1 u1], g2 as [d2 u2]; cbn in p; destruct p; cbn.
  rewrite <- (rew_map GDom (fun u => {| GDom := d1; GUIP := u |})).
  now apply rew_const.
Qed.

Lemma hgpdEqRew {g1 g2: HGpd} (e: Equiv g1 g2) (x: g1):
  rew [GDom] (hgpdEq e) in x = e x.
Proof.
  unfold hgpdEq. rewrite hgpdEqIntroRew. now apply uaRew.
Qed.

Lemma hgpdEqRewSym {g1 g2: HGpd} (e: Equiv g1 g2) (x: g2):
  rew [GDom] (eq_sym (hgpdEq e)) in x = invEq e x.
Proof.
  apply (eqvInj e).
  now exact (eq_sym (hgpdEqRew e _)
    • (rew_sym_cancel_r (P := GDom) (hgpdEq e) x • eq_sym (secEq e x))).
Qed.
