(** The fibred presentation of augmented semi-simplicial sets has one
    set of cells per dimension and face maps satisfying the exchange law.
    Level [n] consists of cells with [n] vertices; level [0] is the
    augmentation. Each level maps to its faces by the face maps. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation LeSProp.

From Bonak.Lib Require Import Funext.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.

Set Primitive Projections.
Set Printing Projections.

(** [Face n q Hq] removes position [q]. In [FaceCoh], deleting
    [r] first shifts the higher position [q.+1] to [q]; deleting [q.+1]
    first leaves [r] unchanged. *)

Record SSSetPresentation := {
  F0: nat -> HSet;
  Face n q (Hq: q <= n): F0 n.+1 -> F0 n;
  FaceCoh n q (Hq: q <= n) r (Hr: r <= q) (X: F0 n.+2):
    Face n q Hq (Face n.+1 r (Hr ↕ (↑ Hq)) X) =
    Face n r (Hr ↕ Hq) (Face n.+1 q.+1 (⇑ Hq) X)
}.

Definition AugmentedSemiSimplicialPresentation := SSSetPresentation.

(** The levels and faces determine a presentation: the exchange law is an
    equality in an [HSet], so its proofs agree. *)

Lemma presheafEqIntro (psh1 psh2: SSSetPresentation)
  (e0: psh1.(F0) = psh2.(F0))
  (e1: rew [fun F0: nat -> HSet =>
         forall n q (Hq: q <= n), F0 n.+1 -> F0 n] e0 in
       psh1.(Face) = psh2.(Face)):
  psh1 = psh2.
Proof.
  destruct psh1 as [F01 Face1 Coh1], psh2 as [F02 Face2 Coh2];
    cbn in e0, e1.
  destruct e0; cbn in e1; destruct e1.
  apply (f_equal (fun C => {| F0 := F01; Face := Face1; FaceCoh := C |})).
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep_good; intro r.
  apply spropFunext; intro Hr.
  apply functional_extensionality_dep_good; intro Y.
  now apply (F01 n).(UIP).
Qed.
