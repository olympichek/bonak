(** The equality theory of presheaves: the levelwise equivalence
    [PresheafEquiv], and its upgrade to an equality [presheafEquivEq].

    Two presheaves are the same when their cells correspond level by level,
    compatibly with the face maps. Univalence and functional extensionality are
    enough to turn such a correspondence into an equality. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import RewLemmas HSet LeSProp Notation
  Funext Univalence Presheaf.Presentation.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafEquiv.

(** Equivalence of presheaves *)
Record PresheafEquiv (psh psh': SSSetPresentation) := {
  F0Equiv n: Equiv (psh.(F0) n) (psh'.(F0) n);
  FaceEquiv n q (Hq: q <= n) (X: psh.(F0) n.+1):
    F0Equiv n (psh.(Face) n q Hq X) =
    psh'.(Face) n q Hq (F0Equiv n.+1 X)
}.

(** Helper transport lemmas *)

Lemma rew_face_app {F01 F02: nat -> HSet} (e: F01 = F02)
  (h: forall n q (Hq: q <= n), F01 n.+1 -> F01 n)
  n q (Hq: q <= n) (Y: F02 n.+1):
  (rew [fun F0: nat -> HSet =>
     forall n q (Hq: q <= n), F0 n.+1 -> F0 n] e in h)
    n q Hq Y =
  rew [fun F0: nat -> HSet => (F0 n).(Dom)] e in
    (h n q Hq (rew [fun F0: nat -> HSet => (F0 n.+1).(Dom)] (eq_sym e) in Y)).
Proof.
  now destruct e.
Qed.

Lemma funExtBetaHSet {F01 F02: nat -> HSet} (H: forall n, F01 n = F02 n)
  (m: nat):
  f_equal (fun h: nat -> HSet => h m)
    (functional_extensionality_dep_good F01 F02 H) = H m.
Proof.
  now exact (f_equal__functional_extensionality_dep_good H m).
Qed.

(** The transport is pushed inward until it becomes the equivalence. The
    [F0] path is [funext] of the levelwise HSet equalities ([hsetEq]);
    applying a transported face map computes through the function type
    ([rew_face_app]); the [F0] path then projects pointwise ([rew_map] +
    [funExtBetaHSet]); and transport along [hsetEq] is the equivalence
    ([hsetEqRew]). *)

Lemma presheafFaceEquivEq {psh1 psh2: SSSetPresentation} (E: PresheafEquiv psh1 psh2):
  rew [fun F0: nat -> HSet =>
    forall n q (Hq: q <= n), F0 n.+1 -> F0 n]
    (functional_extensionality_dep_good _ _
      (fun n => hsetEq (F0Equiv _ _ E n))) in psh1.(Face) = psh2.(Face).
Proof.
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep_good; intro Y.
  rewrite rew_face_app.
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun F0: nat -> HSet => F0 n)).
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun F0: nat -> HSet => F0 n.+1)).
  rewrite <- eq_sym_f_equal.
  rewrite 2 funExtBetaHSet.
  cbv beta.
  rewrite hsetEqRew, hsetEqRewSym.
  refine (FaceEquiv _ _ E n q Hq (invEq (F0Equiv _ _ E n.+1) Y) • _).
  now exact (f_equal (psh2.(Face) n q Hq) (secEq (F0Equiv _ _ E n.+1) Y)).
Qed.

Lemma presheafEquivEq {psh1 psh2: SSSetPresentation} (E: PresheafEquiv psh1 psh2):
  psh1 = psh2.
Proof.
  now exact (presheafEqIntro psh1 psh2 _ (presheafFaceEquivEq E)).
Qed.

End PresheafEquiv.
