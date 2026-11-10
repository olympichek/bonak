(** Concatenation of face words and extension by retained coordinates. *)

Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From Stdlib Require Import Arith.PeanoNat.
From Bonak.Lib Require Import HSet Notation LeSProp NatLemmas.
From Bonak.Presheaf Require Import νSemiShape.

Module WordTensor.

(** The first word describes the top coordinates of the concatenation. *)
Fixpoint tensor {A: HSet} (l: nat) {struct l}:
  forall k r s, Word A k l -> Word A r s -> Word A (k + r) (l + s).
Proof.
  destruct l as [|l].
  - intros [|k] r s u v; [now exact v|now destruct u].
  - intros k r s u v. destruct u as [[a u]|u].
    + now exact (wskip a (tensor A l k r s u v)).
    + destruct k as [|k]; [now destruct u|].
      now exact (wkeep (tensor A l k r s u v)).
Defined.

Arguments tensor {A l k r s} u v.

Lemma tensorId {A: HSet} (k r: nat):
  tensor (wid (A := A) k) (wid r) = wid (k + r).
Proof.
  induction k as [|k IH]; [now reflexivity|].
  now exact (f_equal wkeep IH).
Defined.

Lemma tensorComp {A: HSet} {k l m r s t}
  (u: Word A k l) (u': Word A l m)
  (v: Word A r s) (v': Word A s t):
  wcomp (tensor u' v') (tensor u v) = tensor (wcomp u' u) (wcomp v' v).
Proof.
  revert k l u u'; induction m as [|m IH]; intros k l u u'.
  - destruct l as [|l]; [|now destruct u'].
    destruct k as [|k]; [now destruct u, u'|now destruct u].
  - destruct u' as [[a u']|u'].
    + now exact (f_equal (wskip a) (IH k l u u')).
    + destruct l as [|l]; [now destruct u'|].
      destruct u as [[a u]|u].
      * now exact (f_equal (wskip a) (IH k l u u')).
      * destruct k as [|k]; [now destruct u|].
        now exact (f_equal wkeep (IH k l u u')).
Defined.

Lemma tensorFactor {A: HSet} {k l r s: nat}
  (u: Word A k l) (v: Word A r s):
  tensor u v = wcomp (tensor (wid l) v) (tensor u (wid r)).
Proof. now rewrite tensorComp, wcompIdl, wcompIdr. Defined.

(** Reindexing is used once at the interface to give the public rank order. *)
Definition wordCast {A: HSet} {i j k l: nat}
  (p: i = k) (q: j = l) (f: Word A i j): Word A k l :=
  match p, q with eq_refl, eq_refl => f end.

Lemma wordCastId {A: HSet} {i j: nat} (p: i = j):
  wordCast (A := A) p p (wid i) = wid j.
Proof. now destruct p. Defined.

Lemma wordCastComp {A: HSet} {i j k i' j' k': nat}
  (p: i = i') (q: j = j') (r: k = k')
  (f: Word A i j) (g: Word A j k):
  wcomp (wordCast q r g) (wordCast p q f) = wordCast p r (wcomp g f).
Proof. now destruct p, q, r. Defined.

Local Lemma wordCastTrans {A: HSet} {i j k l m n: nat}
  (p: i = k) (q: j = l) (r: k = m) (s: l = n) (f: Word A i j):
  wordCast r s (wordCast p q f) = wordCast (eq_trans p r) (eq_trans q s) f.
Proof. now destruct p, q, r, s. Defined.

Definition paddedWord {A: HSet} (k: nat) {r s: nat} (f: Word A r s):
  Word A (r + k) (s + k) :=
  wordCast (Nat.add_comm k r) (Nat.add_comm k s) (tensor (wid k) f).

Definition residualWord {A: HSet} (r: nat) {k l: nat} (u: Word A k l):
  Word A (r + k) (r + l) :=
  wordCast (Nat.add_comm k r) (Nat.add_comm l r) (tensor u (wid r)).

Lemma paddedId {A: HSet} (k r: nat):
  paddedWord k (wid (A := A) r) = wid (r + k).
Proof. unfold paddedWord. rewrite tensorId. now apply wordCastId. Defined.

Lemma paddedComp {A: HSet} (k: nat) {r s t: nat}
  (f: Word A r s) (g: Word A s t):
  wcomp (paddedWord k g) (paddedWord k f) = paddedWord k (wcomp g f).
Proof.
  unfold paddedWord. rewrite wordCastComp, tensorComp, wcompIdl.
  now reflexivity.
Defined.

Lemma residualId {A: HSet} (r k: nat):
  residualWord r (wid (A := A) k) = wid (r + k).
Proof. unfold residualWord. rewrite tensorId. now apply wordCastId. Defined.

Lemma residualComp {A: HSet} (r: nat) {k l m: nat}
  (u: Word A k l) (v: Word A l m):
  wcomp (residualWord r v) (residualWord r u) = residualWord r (wcomp v u).
Proof.
  unfold residualWord. rewrite wordCastComp, tensorComp, wcompIdl.
  now reflexivity.
Defined.

Lemma paddedResidual {A: HSet} {r s k l: nat}
  (f: Word A r s) (u: Word A k l):
  wcomp (paddedWord l f) (residualWord r u) =
  wcomp (residualWord s u) (paddedWord k f).
Proof.
  unfold paddedWord, residualWord.
  rewrite 2 wordCastComp, 2 tensorComp.
  rewrite 2 wcompIdl, 2 wcompIdr. now reflexivity.
Defined.

Lemma tensorGen {A: HSet} (k q: nat) (Hq: q <= k) (r: nat) (a: A):
  tensor (wgen k q a) (wid r) = wgen (k + r) (q + r) a.
Proof.
  revert q Hq; induction k as [|k IH]; intros q Hq.
  - pose proof (leR0Eq Hq) as e; subst q.
    cbn [wgen tensor]. now rewrite wgenTop.
  - destruct (Nat.eqb q (S k)) eqn:e.
    + pose proof (natEqbEq q (S k) e) as h; subst q.
      rewrite 2 wgenTop. change (wskip a (tensor (wid (S k)) (wid r)) = wskip a (wid (S k + r))).
      now rewrite tensorId.
    + pose proof (leRDown q k Hq e) as h.
      rewrite (wgenLift h a).
      change (wkeep (tensor (wgen k q a) (wid r)) = wgen (S (k + r)) (q + r) a).
      rewrite (wgenLift (leR_add_mono_r h r) a).
      now exact (f_equal wkeep (IH q h)).
Defined.

Local Lemma wordCastGen {A: HSet} {n m: nat}
  (p: n = m) (q: S n = S m) (j: nat) (a: A):
  wordCast p q (wgen n j a) = wgen m j a.
Proof.
  replace q with (f_equal S p) by now apply natUIP.
  now destruct p.
Defined.

Lemma residualGen {A: HSet} (r k q: nat) (Hq: q <= k) (a: A):
  wordCast eq_refl (Nat.add_succ_r r k) (residualWord r (wgen k q a)) =
  wgen (r + k) (r + q) a.
Proof.
  unfold residualWord. rewrite wordCastTrans, (tensorGen k q Hq r a).
  etransitivity; [apply wordCastGen|]. now rewrite (Nat.add_comm q r).
Defined.

End WordTensor.
