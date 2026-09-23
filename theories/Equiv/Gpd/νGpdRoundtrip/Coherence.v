(** Prefix coherence and generated B-side exchange for the backward round trip. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Exchange.
From Bonak.Lib Require Import Equiv.
From Bonak.Equiv.Gpd Require Import PathAlgebra.
From Bonak Require Import Limit.
Import Logic.EqNotations.

Set Primitive Projections.
From Bonak Require Import νGpd.Pasting.

Set Keyed Unification.

Module CoherenceOn (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base)
  (CanonicalBase: Bonak.Equiv.Gpd.νGpdRoundtrip.Canonical.CanonicalSig A Base Translations)
  (ExchangeBase: Bonak.Equiv.Gpd.νGpdRoundtrip.Exchange.ExchangeSig A Base Translations CanonicalBase).
Import A.

Module Export Exchange := ExchangeBase.

Section Tail.
Context {m} {Xpre: (νGpdAt m).(prefix)} (S0: νGpdFrom m Xpre)
  {pa ka} {dcA: DepsCohs3 pa ka}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dcA).

(** This is faceDeep3Compose, packaged in the vocabulary of gFaceC. *)
Lemma gFaceComposeZero
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB):
  forall (q: nat) (Hq: q <= ka) (Hdim: cohs3ChainLen b + q <= kb)
    (epsilon: arity) (z: gF0 S0 1),
  gFaceC S0 (cohs3ChainCompose a b) 0 (cohs3ChainLen b + q) Hdim epsilon z
  = gFaceC S0 a 0 q Hq epsilon z.
Proof.
  induction b as [|pb kb dcB b IH]; intros q Hq Hdim epsilon z.
  - now reflexivity.
  - now exact (IH q Hq (⇓ Hdim) epsilon z).
Defined.

(** Both sides use the tail [b]: [chainUp1 (Cons c)] reduces to
    [Cons (chainUp1 c)]. *)
Lemma gFaceComposeOne
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB):
  forall (q: nat) (Hq: q <= ka.+1) (Hdim: cohs3ChainLen b + q <= kb.+1)
    (epsilon: arity) (z: gF0 S0 2),
  gFaceC S0 (cohs3ChainCompose a b) 1 (cohs3ChainLen b + q) Hdim epsilon z
  = gFaceC S0 a 1 q Hq epsilon z.
Proof.
  induction b as [|pb kb dcB b IH]; intros q Hq Hdim epsilon z.
  - now reflexivity.
  - now exact (IH q Hq (⇓ Hdim) epsilon z).
Defined.

(** Keep (len+q).+1 syntactically intact, matching the upper epsilon face
    in gFaceCohC. This avoids an extra plus_n_Sm whisker inside the square. *)
Lemma gFaceComposeOneSucc
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB):
  forall (q: nat) (Hq: q.+1 <= ka.+1)
    (Hdim: (cohs3ChainLen b + q).+1 <= kb.+1)
    (epsilon: arity) (z: gF0 S0 2),
  gFaceC S0 (cohs3ChainCompose a b) 1 (cohs3ChainLen b + q).+1 Hdim epsilon z
  = gFaceC S0 a 1 q.+1 Hq epsilon z.
Proof.
  induction b as [|pb kb dcB b IH]; intros q Hq Hdim epsilon z.
  - now reflexivity.
  - now exact (IH q Hq (⇓ Hdim) epsilon z).
Defined.

(** Coherence of the two vertex paths over the same tail at both
    levels. The statement allows arbitrary [Q] and [R]; the layer clause
    uses [R = 0]. *)
Lemma gFaceComposeCoh
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB):
  forall (Q: nat) (HQ: Q <= ka) (R: nat) (HR: R <= Q)
    (HQfull: cohs3ChainLen b + Q <= kb)
    (HRfull: cohs3ChainLen b + R <= cohs3ChainLen b + Q)
    (epsilon omega: arity) (z: gF0 S0 2),
  gFaceCohC S0 (cohs3ChainCompose a b) 0
    (cohs3ChainLen b + Q) HQfull (cohs3ChainLen b + R) HRfull epsilon omega z
  • (gFaceComposeZero b R (HR ↕ HQ) (HRfull ↕ HQfull) omega
       (gFaceC S0 (cohs3ChainCompose a b) 1
         (cohs3ChainLen b + Q).+1 (⇑ HQfull) epsilon z)
     • f_equal (gFaceC S0 a 0 R (HR ↕ HQ) omega)
         (gFaceComposeOneSucc b Q (⇑ HQ) (⇑ HQfull) epsilon z))
  = (gFaceComposeZero b Q HQ HQfull epsilon
       (gFaceC S0 (cohs3ChainCompose a b) 1
         (cohs3ChainLen b + R) (HRfull ↕ ↑ HQfull) omega z)
     • f_equal (gFaceC S0 a 0 Q HQ epsilon)
         (gFaceComposeOne b R (HR ↕ ↑ HQ)
           (HRfull ↕ ↑ HQfull) omega z))
    • gFaceCohC S0 a 0 Q HQ R HR epsilon omega z.
Proof.
  induction b as [|pb kb dcB b IH];
    intros Q HQ R HR HQfull HRfull epsilon omega z.
  - cbn [cohs3ChainCompose cohs3ChainLen gFaceComposeZero
      gFaceComposeOne gFaceComposeOneSucc f_equal].
    now rewrite 2 eq_trans_refl_l, eq_trans_refl_r.
  - cbn [cohs3ChainCompose cohs3ChainLen gFaceCohC].
    rewrite (faceAtCohUpShift (νExt3At S0) (cohs3ChainCompose a b)
      (cohs3ChainLen b + Q) (⇓ HQfull)
      (cohs3ChainLen b + R) (⇓ HRfull) epsilon omega
      (deepCell (cohs3ChainDepsCohs2
        (chainUp1 (νExt3At S0) (DepsCohs3ChainCons (cohs3ChainCompose a b)))) z)).
    now exact (IH Q HQ R HR (⇓ HQfull) (⇓ HRfull) epsilon omega z).
Defined.

(** The face-to-[νFace] comparison respects the tail shift, including
    its chain-package corrections. *)
Lemma faceAsNuCompose
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q <= ka) (Hdim: cohs3ChainLen b + q <= kb)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain (νDepsCohsAt S0) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 a)
    = (cohsChainLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2 (cohs3ChainCompose a b))
    = (cohsChainLen c + (cohs3ChainLen b + q))%nat)
  (epsilon: arity) (z: gF0 S0 1):
  faceDeepAsνFace (cohs3ChainDepsCohs2 (cohs3ChainCompose a b))
    (cohs3ChainLen b + q) Hdim c Hfull epsilon z.1 z.2
  = gFaceComposeZero b q Hq Hdim epsilon z
    • faceDeepAsνFace (cohs3ChainDepsCohs2 a) q Hq c Hhead epsilon z.1 z.2.
Proof.
  revert Hdim Hfull.
  induction b as [|pb kb dcB b IH]; intros Hdim Hfull.
  - cbn [cohs3ChainCompose cohs3ChainLen gFaceComposeZero].
    rewrite (natUIP Hfull Hhead).
    symmetry. apply eq_trans_refl_l.
  - cbn [cohs3ChainCompose cohs3ChainLen cohs3ChainDepsCohs2
      faceDeepAsνFace gFaceComposeZero].
    now exact (IH (⇓ Hdim) _).
Defined.

Lemma faceAsNuComposeOne
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q <= ka.+1) (Hdim: cohs3ChainLen b + q <= kb.+1)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain (νDepsCohsAt (next S0)) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (cohsChainLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    = (cohsChainLen c + (cohs3ChainLen b + q))%nat)
  (epsilon: arity) (z: gF0 S0 2):
  faceDeepAsνFace (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    (cohs3ChainLen b + q) Hdim c Hfull epsilon z.1 z.2
  = gFaceComposeOne b q Hq Hdim epsilon z
    • faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
        q Hq c Hhead epsilon z.1 z.2.
Proof.
  revert Hdim Hfull.
  induction b as [|pb kb dcB b IH]; intros Hdim Hfull.
  - cbn [cohs3ChainCompose cohs3ChainLen gFaceComposeOne].
    rewrite (natUIP Hfull Hhead).
    symmetry. apply eq_trans_refl_l.
  - cbn [cohs3ChainCompose cohs3ChainLen chainUp1 cohs3ChainUp
      cohs3ChainDepsCohs2 faceDeepAsνFace gFaceComposeOne].
    now exact (IH (⇓ Hdim) _).
Defined.

(** Successor form at the ε-vertex of [gFaceCohC]. *)
Lemma faceAsNuComposeOneSucc
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q.+1 <= ka.+1)
  (Hdim: (cohs3ChainLen b + q).+1 <= kb.+1)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain (νDepsCohsAt (next S0)) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (cohsChainLen c + q.+1)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    = (cohsChainLen c + (cohs3ChainLen b + q).+1)%nat)
  (epsilon: arity) (z: gF0 S0 2):
  faceDeepAsνFace (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    (cohs3ChainLen b + q).+1 Hdim c Hfull epsilon z.1 z.2
  = gFaceComposeOneSucc b q Hq Hdim epsilon z
    • faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
        q.+1 Hq c Hhead epsilon z.1 z.2.
Proof.
  revert Hdim Hfull.
  induction b as [|pb kb dcB b IH]; intros Hdim Hfull.
  - cbn [cohs3ChainCompose cohs3ChainLen gFaceComposeOneSucc].
    rewrite (natUIP Hfull Hhead).
    symmetry. apply eq_trans_refl_l.
  - cbn [cohs3ChainCompose cohs3ChainLen chainUp1 cohs3ChainUp
      cohs3ChainDepsCohs2 faceDeepAsνFace gFaceComposeOneSucc].
    now exact (IH (⇓ Hdim) _).
Defined.

Lemma tailComparisonCancel {T: Type} {x y z: T} (d: x = y) (beta: y = z):
  (d • beta) • eq_sym beta = d.
Proof.
  now exact (eqTransCancelR beta d).
Defined.

(** Identify the upper paths of [descFaceAtPrefixCommonFace] with
    [D1] and [D1S], retaining the chosen tail. *)
Lemma faceCommonOne
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q <= ka.+1) (Hdim: cohs3ChainLen b + q <= kb.+1)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain (νDepsCohsAt (next S0)) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (cohsChainLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    = (cohsChainLen c + (cohs3ChainLen b + q))%nat)
  (epsilon: arity) (z: gF0 S0 2):
  faceDeepAsνFace (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    (cohs3ChainLen b + q) Hdim c Hfull epsilon z.1 z.2
  • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
      q Hq c Hhead epsilon z.1 z.2)
  = gFaceComposeOne b q Hq Hdim epsilon z.
Proof.
  rewrite (faceAsNuComposeOne b q Hq Hdim c Hhead Hfull epsilon z).
  now apply tailComparisonCancel.
Defined.

Lemma faceCommonOneSucc
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q.+1 <= ka.+1)
  (Hdim: (cohs3ChainLen b + q).+1 <= kb.+1)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain (νDepsCohsAt (next S0)) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (cohsChainLen c + q.+1)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    = (cohsChainLen c + (cohs3ChainLen b + q).+1)%nat)
  (epsilon: arity) (z: gF0 S0 2):
  faceDeepAsνFace (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At S0) (cohs3ChainCompose a b)))
    (cohs3ChainLen b + q).+1 Hdim c Hfull epsilon z.1 z.2
  • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
      q.+1 Hq c Hhead epsilon z.1 z.2)
  = gFaceComposeOneSucc b q Hq Hdim epsilon z.
Proof.
  rewrite (faceAsNuComposeOneSucc b q Hq Hdim c Hhead Hfull epsilon z).
  now apply tailComparisonCancel.
Defined.

End Tail.
Lemma prefixAddAssoc (i j k: nat): ((i + j) + k)%nat = (i + (j + k))%nat.
Proof. induction i; cbn; [now reflexivity | now rewrite IHi]. Defined.

Lemma prefixAddComm (i j: nat): (i + j)%nat = (j + i)%nat.
Proof.
  induction i; cbn.
  - now exact (plus_n_O j).
  - now exact (f_equal S IHi • plus_n_Sm j i).
Defined.

(** The cut retains its intermediate [DepsCohs] and chain. At a
    positive index it returns the parent package unchanged. *)
Fixpoint prefixCut {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3) {struct a}:
  forall (q: nat), q <= k -> DCPack (νDepsCohsAt S0).
Proof.
  destruct a as [|p k dc3 a]; intros q Hq.
  - now exact (dcPackOf DepsCohsChainNil).
  - destruct q as [|q].
    + now exact (dcPackOf (cohs2ChainDepsCohs
        (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)))).
    + now exact (@prefixCut M XpB0 S0 p.+1 k dc3 a q (⇓ Hq)).
Defined.

Lemma prefixCutLength {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3):
  forall (q: nat) (Hq: q <= k),
  cohs3ChainLen a = (dcPackLen (prefixCut a q Hq) + q)%nat.
Proof.
  induction a as [|p k dc3 a IH]; intros q Hq.
  - destruct q as [|q].
    + now reflexivity.
    + destruct (leR_O_contra Hq).
  - destruct q as [|q].
    + now exact (eq_sym (cohs3ChainDepsCohs2Len (DepsCohs3ChainCons a))
        • localZeroLength (DepsCohs3ChainCons a)).
    + now exact (f_equal S (IH q (⇓ Hq))
        • plus_n_Sm (dcPackLen (prefixCut a q (⇓ Hq))) q).
Defined.

Definition prefixCutTwoLength {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3) (q: nat) (Hq: q <= k):
  cohs2ChainLen (cohs3ChainDepsCohs2 a)
  = (cohsChainLen (prefixCut a q Hq).2.2.2 + q)%nat :=
  cohs3ChainDepsCohs2Len a • prefixCutLength a q Hq.

Lemma gFaceAsNuLengthIrr {M} {XpB0: (νGpdAt M).(prefix)}
  (S0: νGpdFrom M XpB0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (dim: nat) (Hdim: dim <= k) {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain (νDepsCohsAt S0) dcC)
  (H H': cohs3ChainLen a = (cohsChainLen c + dim)%nat)
  (epsilon: arity) (z: gF0 S0 1):
  gFaceCAsνFace S0 a dim Hdim c H epsilon z
  = gFaceCAsνFace S0 a dim Hdim c H' epsilon z.
Proof. rewrite (natUIP H H'). now reflexivity. Defined.

Lemma faceAsNuComposeCut {P K} {dcTop: DepsCohs3 P K}
  {pa ka} {dcA: DepsCohs3 pa ka} (a: DepsCohs3Chain dcTop dcA)
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q <= ka) (Hdim: cohs3ChainLen b + q <= kb)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain dcTop.(_depsCohs2).(_depsCohs) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 a) = (cohsChainLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2 (cohs3ChainCompose a b))
    = (cohsChainLen c + (cohs3ChainLen b + q))%nat)
  (epsilon: arity) d v:
  faceDeepAsνFace (cohs3ChainDepsCohs2 (cohs3ChainCompose a b))
    (cohs3ChainLen b + q) Hdim c Hfull epsilon d v
  = faceDeep3Compose a b q Hq Hdim epsilon d v
    • faceDeepAsνFace (cohs3ChainDepsCohs2 a) q Hq c Hhead epsilon d v.
Proof.
  revert Hdim Hfull.
  induction b as [|pb kb dcB b IH]; intros Hdim Hfull.
  - cbn [cohs3ChainCompose cohs3ChainLen faceDeep3Compose].
    rewrite (natUIP Hfull Hhead).
    symmetry. apply eq_trans_refl_l.
  - cbn [cohs3ChainCompose cohs3ChainLen cohs3ChainDepsCohs2
      faceDeepAsνFace faceDeep3Compose].
    now exact (IH (⇓ Hdim) _).
Defined.

(** Name the one-step recursive equality before applying congruence.  In
    particular, do not ask unification to choose between the parent chain
    (at p.+1) and its child (at p) merely from their convertible face cells. *)
Lemma faceAsNuSuccCut {P K} {dcTop: DepsCohs3 P K}
  {p k} {dcA: DepsCohs3 p.+1 k} (a: DepsCohs3Chain dcTop dcA)
  (q: nat) (Hq: q.+1 <= k.+1)
  {pc kc} {dcC: DepsCohs pc kc}
  (c: DepsCohsChain dcTop.(_depsCohs2).(_depsCohs) dcC)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 a) = (cohsChainLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))
    = (cohsChainLen c + q.+1)%nat)
  (epsilon: arity) d v:
  faceDeepAsνFace (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))
    q.+1 Hq c Hfull epsilon d v
  = faceDeepAsνFace (cohs3ChainDepsCohs2 a) q (⇓ Hq) c Hhead epsilon d v.
Proof.
  pose proof (faceAsNuComposeCut a (DepsCohs3ChainCons DepsCohs3ChainNil)
    q (⇓ Hq) Hq c Hhead Hfull epsilon d v) as H.
  cbn [faceDeep3Compose] in H.
  rewrite eq_trans_refl_l in H.
  now exact H.
Defined.

#[local] Arguments Desc {X n Xpre}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments descFaceAtPrefix {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descFaceAtPrefixZero {X M XpB0 S0} HD {p k dc3}.

Section CommonFace.
Variable X: νGpds.

Definition prefixCutFullLength {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (q: nat) (Hq: q <= k) (dim: nat) (Hd: dim = (q + p)%nat)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat):
  cohs3ChainLen (descChain HD).2
  = (cohsChainLen (prefixCut a q Hq).2.2.2 + dim)%nat :=
  Hlen
  • f_equal (fun n => (n + p)%nat)
      (cohs2ChainDepsCohsLen (cohs3ChainDepsCohs2 a)
        • cohs3ChainDepsCohs2Len a • prefixCutLength a q Hq)
  • prefixAddAssoc (dcPackLen (prefixCut a q Hq)) q p
  • f_equal (fun n => (dcPackLen (prefixCut a q Hq) + n)%nat) (eq_sym Hd).

Lemma descFaceAtPrefixZeroCommon {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen Hfull: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 a)
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + 0)%nat)
  (Hq: 0 <= k) (Hdim: p <= M) (epsilon: arity) (z: νTotal (next S0)):
  descFaceAtPrefixZero HD a Hlen Hq Hdim epsilon z
  = gFaceCAsνFace S0 (descChain HD).2 p Hdim
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hfull epsilon z
    • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 a) 0 Hq
        (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hhead epsilon z.1 z.2).
Proof.
  unfold descFaceAtPrefixZero.
  rewrite (natUIP Hlen Hfull), (natUIP (localZeroLength a) Hhead).
  now reflexivity.
Defined.

(** The common-face identity returns the cut package; both
    comparisons with [νFace] use that package as their endpoint. *)
Lemma descFaceAtPrefixCommonFace {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3):
  forall (q: nat) (Hq: q <= k) (dim: nat) (Hdim: dim <= M)
    (Hd: dim = (q + p)%nat)
    (Hlen: cohs3ChainLen (descChain HD).2
      = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (epsilon: arity) (z: νTotal (next S0)),
  descFaceAtPrefix HD a q Hq dim Hdim Hd Hlen epsilon z
  = gFaceCAsνFace S0 (descChain HD).2 dim Hdim (prefixCut a q Hq).2.2.2
      (prefixCutFullLength HD a q Hq dim Hd Hlen) epsilon z
    • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 a) q Hq
        (prefixCut a q Hq).2.2.2 (prefixCutTwoLength a q Hq) epsilon z.1 z.2).
Proof.
  induction a as [|p k dc3 a IH]; intros q Hq dim Hdim Hd Hlen epsilon z.
  - destruct q as [|q].
    + subst dim.
      now exact (descFaceAtPrefixZeroCommon HD DepsCohs3ChainNil Hlen
        (prefixCutFullLength HD DepsCohs3ChainNil 0 Hq _ eq_refl Hlen)
        (prefixCutTwoLength DepsCohs3ChainNil 0 Hq) Hq Hdim epsilon z).
    + destruct (leR_O_contra Hq).
  - destruct q as [|q].
    + subst dim.
      now exact (descFaceAtPrefixZeroCommon HD (DepsCohs3ChainCons a) Hlen
        (prefixCutFullLength HD (DepsCohs3ChainCons a) 0 Hq _ eq_refl Hlen)
        (prefixCutTwoLength (DepsCohs3ChainCons a) 0 Hq) Hq Hdim epsilon z).
    + cbn [descFaceAtPrefix prefixCut].
      rewrite (IH q (⇓ Hq) dim Hdim (Hd • plus_n_Sm q p)
        (Hlen • plus_n_Sm (cohsChainLen
          (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p) epsilon z).
      apply f_equal2.
      * apply gFaceAsNuLengthIrr.
      * apply f_equal.
        now exact (eq_sym (faceAsNuSuccCut a q Hq (prefixCut a q (⇓ Hq)).2.2.2
          (prefixCutTwoLength a q (⇓ Hq))
          (prefixCutTwoLength (DepsCohs3ChainCons a) q.+1 Hq)
          epsilon z.1 z.2)).
Defined.

Definition prefixFullLength3 {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat):
  cohs3ChainLen (descChain HD).2 = (cohs3ChainLen a + p)%nat :=
  Hlen • f_equal (fun n => (n + p)%nat)
    (cohs2ChainDepsCohsLen (cohs3ChainDepsCohs2 a) • cohs3ChainDepsCohs2Len a).

End CommonFace.
#[local] Arguments Desc {X n Xpre}.
#[local] Arguments DescS {X n Xpre S0}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments descCell {X m XpB SB}.
#[local] Arguments descCellFace {X n XpB SB}.
#[local] Arguments descQcells {X M XpB0 S0 HD p k dcB}.
#[local] Arguments frtChainUp {M XpB0 S0 p k dc3M}.
#[local] Arguments frtPairRead {M XpB0 S0 p k dcB}.
#[local] Arguments frtPairReadDeepCell {M XpB0 S0 p k dc3}.
#[local] Arguments descCellPairRestrAt {X n XpB0 S0} HD {pB kB dcB}.
#[local] Arguments descCellPairRestrCanonical {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descCellPairRestrCanonicalZeroRead {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descCellPairRestrCanonicalCons {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descCellPairRestrCanonicalFrame {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descCellPairRestrCanonicalAsFace {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonNormal {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descFaceAtPrefix {X M XpB0 S0} HD {p k dc3}.

Lemma readComparisonCancel
  {Y B: Type} (f g: Y -> B) (eta: forall y, g y = f y)
  {y z: Y} (alpha: y = z) {v: B} (h: f z = v):
  eq_sym (eta y) • (f_equal g alpha • (eta z • h))
  = f_equal f alpha • h.
Proof.
  rewrite (eq_trans_assoc (f_equal g alpha) (eta z) h),
    (eq_trans_natural g f eta alpha), <- eq_trans_assoc.
  now apply eq_trans_sym_cancel_l.
Defined.

Section ReadRebuild.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}.

(** Both section paths recurse through the same chain by the action
    of [unassoc]. [frtPairReadDeepCell] identifies their two readers. *)
Lemma readRebuildUpSection
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3):
  forall Y: CellHere dc3,
  localReadRebuild (chainUp1 (νExt3At S0) a) Y
  = frtPairReadDeepCell a
      (faceRebuild (chainUp1 (νExt3At S0) a) Y)
    • deepCellRebuildUp (νExt3At S0) a Y.
Proof.
  induction a as [|p k dc3 a IH]; intro Y.
  - now reflexivity.
  - pose (Ya := ((Y.1; Y.2.1); Y.2.2): CellHere dc3).
    change
      (f_equal unassoc (localReadRebuild (chainUp1 (νExt3At S0) a) Ya)
       = f_equal unassoc
           (frtPairReadDeepCell a
             (faceRebuild (chainUp1 (νExt3At S0) a) Ya))
         • f_equal unassoc (deepCellRebuildUp (νExt3At S0) a Ya)).
    rewrite <- eq_trans_map_distr.
    now exact (f_equal (fun h => f_equal unassoc h) (IH Ya)).
Defined.

Lemma readFaceUpSection
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (j: nat) (Hj: j <= k.+1) (epsilon: arity) (w: CellBelow dc3):
  localFaceComparison (chainUp1 (νExt3At S0) a) j Hj epsilon w
  = frtPairReadDeepCell a
      (faceAt (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
        j Hj epsilon w.1 w.2)
    • deepCellFaceAtUp (νExt3At S0) a j Hj epsilon w.1 w.2.
Proof.
  now exact (readRebuildUpSection a
    (restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs)
      j Hj epsilon w.1 w.2)).
Defined.

(** Cancel the inverse read/deep correction introduced by
    [descPairFaceComparisonTotalNormal] at the lower stage. [Alpha] may
    be any path to the upper face. *)
Lemma readFaceUpPrefix
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (j: nat) (Hj: j <= k.+1) (epsilon: arity) (w: CellBelow dc3)
  {y: νTotal (next S0)}
  (alpha: y =
    faceAt (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
      j Hj epsilon w.1 w.2):
  eq_sym (frtPairReadDeepCell a y)
    • (f_equal (localPairRead (chainUp1 (νExt3At S0) a)) alpha
       • localFaceComparison (chainUp1 (νExt3At S0) a) j Hj epsilon w)
  = f_equal (deepCell (cohs3ChainDepsCohs2 a)) alpha
      • deepCellFaceAtUp (νExt3At S0) a j Hj epsilon w.1 w.2.
Proof.
  rewrite readFaceUpSection.
  now apply readComparisonCancel.
Defined.

End ReadRebuild.

Section Descent.
Variable X: νGpds.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).

Let aUp := cohs3ChainUp (νExt3At S0) a.
Let b := chainUp1 (νExt3At S0) a.
Let cb' := frtChainUp a.

(** Read the upper ε-frame path as the ω-restriction of a canonical
    upper total path, using the tail of [localFaceComparisonCoh] at local
    index [q.+1]. [CanonicalFrame] supplies the [descQcells] comparison. *)
Lemma descQcellsOmegaAsUpperCanonical
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
    = (cohsChainLen cb' + p.+1)%nat)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (epsilon omega: arity) (t: (g X).(G0) M.+2):
  f_equal (frtPairRestrAt dc3.(_depsCohs2).(_depsCohs) omega)
    (descQcells cb' Hlen' q Hq Hqp epsilon t)
  = f_equal (localRestriction dc3 0 leR_O omega)
      (descCellPairRestrCanonical (DescS HD) b q.+1 (⇑ Hq)
        (q + p.+1) Hqp (eq_sym (plus_n_Sm q p))
        (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cb') p)) epsilon t).
Proof.
  unfold b, chainUp1.
  rewrite (descCellPairRestrCanonicalCons (DescS HD) aUp q (⇑ Hq)
    (q + p.+1) Hqp (eq_sym (plus_n_Sm q p))
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cb') p)) epsilon t).
  rewrite (natUIP (eq_sym (plus_n_Sm q p) • plus_n_Sm q p) eq_refl).
  rewrite (natUIP
    ((Hlen' • eq_sym (plus_n_Sm (cohsChainLen cb') p))
      • plus_n_Sm (cohsChainLen cb') p) Hlen').
  rewrite <- (descCellPairRestrCanonicalFrame (DescS HD) aUp
    Hlen' q Hq Hqp epsilon t).
  unfold projT1_eq.
  lazymatch goal with
  | |- @f_equal _ _ ?gg _ _ (@f_equal _ _ ?ff _ _ ?ee) = _ =>
    rewrite (@f_equal_comp2 _ _ _ ff gg _ _ ee)
  end.
  lazymatch goal with
  | |- _ = @f_equal _ _ ?gg _ _ (@f_equal _ _ ?ff _ _ ?ee) =>
    rewrite (@f_equal_comp2 _ _ _ ff gg _ _ ee)
  end.
  now reflexivity.
Defined.

(** Normalize the two upper canonical paths at indices [q.+1] and [0].
    The inverse [frtPairReadDeepCell] cancels, leaving the descent/prefix
    composite read by [deepCell], followed by the upper section. *)
Lemma descUpperCanonicalDeepNormal
  (HlenB: cohs3ChainLen (descChain (DescS HD)).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 b)) + p)%nat)
  (j: nat) (Hj: j <= k.+1) (dim: nat) (Hdim: dim <= M.+1)
  (Hd: dim = (j + p)%nat)
  (epsilon: arity) (t: (g X).(G0) M.+2):
  let T := descCell (DescS (DescS HD)) t in
  let w := deepCell (cohs3ChainDepsCohs2 b) T in
  eq_sym (frtPairReadDeepCell a
    (descCell (DescS HD) ((g X).(GFace) M.+1 dim Hdim epsilon t)))
    • descCellPairRestrCanonical (DescS HD) b j Hj dim Hdim Hd HlenB epsilon t
  = f_equal (deepCell (cohs3ChainDepsCohs2 a))
      (descCellFace (DescS HD) dim Hdim Hdim epsilon t
       • descFaceAtPrefix (DescS HD) b j Hj dim Hdim Hd HlenB epsilon T)
    • deepCellFaceAtUp (νExt3At S0) a j Hj epsilon w.1 w.2.
Proof.
  intros T w.
  rewrite descCellPairRestrCanonicalAsFace.
  rewrite descPairFaceComparisonNormal.
  pose proof (readFaceUpPrefix a j Hj epsilon w
    (descCellFace (DescS HD) dim Hdim Hdim epsilon t
      • descFaceAtPrefix (DescS HD) b j Hj dim Hdim Hd HlenB epsilon T)) as H.
  rewrite (eq_trans_map_distr (localPairRead b)
    (descCellFace (DescS HD) dim Hdim Hdim epsilon t)
    (descFaceAtPrefix (DescS HD) b j Hj dim Hdim Hd HlenB epsilon T)) in H.
  rewrite <- (eq_trans_assoc
    (f_equal (localPairRead b)
      (descCellFace (DescS HD) dim Hdim Hdim epsilon t))
    (f_equal (localPairRead b)
      (descFaceAtPrefix (DescS HD) b j Hj dim Hdim Hd HlenB epsilon T))
    (localFaceComparison b j Hj epsilon w)) in H.
  now exact H.
Defined.

End Descent.

Section ZeroCons.
Variable X: νGpds.

(** The chosen zero path reencodes the pair law. Its generated
    restriction-painting correction computes to reflexivity. *)
Lemma descPairLawZeroConsCanonical
  {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p.+1 k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs
        (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a))) + p)%nat)
  (Hp: p <= M) (omega: arity) (t: (g X).(G0) M.+1):
  descCellPairRestrAt HD
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)))
    p Hp Hlen omega t
  = descCellPairRestrCanonical HD (DepsCohs3ChainCons a)
      0 leR_O p Hp eq_refl Hlen omega t.
Proof.
  rewrite descCellPairRestrCanonicalZeroRead.
  pose (law := descCellPairRestrAt HD
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)))
    p Hp Hlen omega t).
  change (law = (=projT1_eq law; projT2_eq law • eq_refl)).
  now exact (eq_sym (f_equal (fun h => (=projT1_eq law; h))
    (eq_trans_refl_r (projT2_eq law)) • totalPathReencode law)).
Defined.

End ZeroCons.

#[local] Arguments FrtDeps {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtDepsCohs {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtFramesNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPaintingsNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frDepsA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frBound {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frTr {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtTrBaseOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshCohsOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtDepsCohsGen {X M XpB0 S0 HD p k dc2}.
#[local] Arguments frtPairLawPrev {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments proj1FrtDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtDepsOf {X M XpB0 S0 HD p k dcB cB}.

Section GeneratedOmega.
Variable X: νGpds.
Context {M: nat} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0)
  {p k: nat} {dc3M: DepsCohs3 p k}
  (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
  (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
    (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA
    (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX rpA
    (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp cohsA
    (mkDepsCohs dc3M.(_depsCohs2)).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
    = (cohsChainLen (frtChainUp aH) + p.+1)%nat)
  (frames: FrtFramesNextType
    (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
      cohsA trCohs pshCohs) (frtChainUp aH))
  (paintings: FrtPaintingsNextType
    (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
      cohsA trCohs pshCohs) (frtChainUp aH) frames).

Let FC := mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp
  pshRp cohsA trCohs pshCohs.
Let b := chainUp1 (νExt3At S0) aH.
Let Hp := ⇓ (proj1FrtDeps
  (mkFrtDepsOf FC (frtChainUp aH) frames paintings)).(_frBound).
Let HlenB := Hlen' • eq_sym (plus_n_Sm (cohsChainLen (frtChainUp aH)) p).

(** Specialize [frtPairLawPrev] to the generated [FC] of the B-side
    square. *)
Lemma frtPairLawPrevCanonical
  (omega: arity) (t: (g X).(G0) M.+2):
  frtPairLawPrev FC (frtChainUp aH) Hlen' frames paintings omega t
  = descCellPairRestrCanonical (DescS HD) b
      0 leR_O p Hp eq_refl HlenB omega t.
Proof.
  unfold frtPairLawPrev.
  now exact (descPairLawZeroConsCanonical X (DescS HD)
    (cohs3ChainUp (νExt3At S0) aH) HlenB Hp omega t).
Defined.

End GeneratedOmega.

Definition prefixQuotientZero {m} {Xpre: (νGpdAt m).(prefix)}
  (S0: νGpdFrom m Xpre)
  {pa ka} {dcA: DepsCohs3 pa ka} (a: DepsCohs3Chain (νDepsCohs3At S0) dcA)
  {pb kb} {dcB: DepsCohs3 pb kb} (full: DepsCohs3Chain (νDepsCohs3At S0) dcB)
  (q: nat) (Hq: q <= ka) (dim: nat) (Hdim: dim <= kb)
  (c: DCPack (νDepsCohsAt S0))
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 a) = (dcPackLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2 full) = (dcPackLen c + dim)%nat)
  (epsilon: arity) (z: gF0 S0 1):
  gFaceC S0 full 0 dim Hdim epsilon z = gFaceC S0 a 0 q Hq epsilon z :=
  faceDeepAsνFace (cohs3ChainDepsCohs2 full) dim Hdim c.2.2.2 Hfull epsilon z.1 z.2
  • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 a) q Hq c.2.2.2 Hhead epsilon z.1 z.2).

Definition prefixQuotientOne {m} {Xpre: (νGpdAt m).(prefix)}
  (S0: νGpdFrom m Xpre)
  {pa ka} {dcA: DepsCohs3 pa ka} (a: DepsCohs3Chain (νDepsCohs3At S0) dcA)
  {pb kb} {dcB: DepsCohs3 pb kb} (full: DepsCohs3Chain (νDepsCohs3At S0) dcB)
  (q: nat) (Hq: q <= ka.+1) (dim: nat) (Hdim: dim <= kb.+1)
  (c: DCPack (νDepsCohsAt (next S0)))
  (Hhead: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (dcPackLen c + q)%nat)
  (Hfull: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) full))
    = (dcPackLen c + dim)%nat)
  (epsilon: arity) (z: gF0 S0 2):
  gFaceC S0 full 1 dim Hdim epsilon z = gFaceC S0 a 1 q Hq epsilon z :=
  faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) full))
    dim Hdim c.2.2.2 Hfull epsilon z.1 z.2
  • eq_sym (faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
      q Hq c.2.2.2 Hhead epsilon z.1 z.2).

(** Full-chain coherence with independent global dimensions. Their
    arithmetic identifications are eliminated together over the same
    tail; the four cut packages and eight length witnesses are parameters. *)
Lemma prefixQuotientCoh {m} {Xpre: (νGpdAt m).(prefix)}
  (S0: νGpdFrom m Xpre)
  {pa ka} {dcA: DepsCohs3 pa ka} (a: DepsCohs3Chain (νDepsCohs3At S0) dcA)
  {pb kb} {dcB: DepsCohs3 pb kb} (full: DepsCohs3Chain (νDepsCohs3At S0) dcB)
  (n: nat) (Hfactor: cohs3ChainLen full = (cohs3ChainLen a + n)%nat)
  (Q: nat) (HQ: Q <= ka) (R: nat) (HR: R <= Q)
  (dimQ dimR: nat) (HdimQ: dimQ <= kb) (HdimR: dimR <= dimQ)
  (eQ: dimQ = (n + Q)%nat) (eR: dimR = (n + R)%nat)
  (cQ cR: DCPack (νDepsCohsAt S0))
  (cQU cRU: DCPack (νDepsCohsAt (next S0)))
  (HheadQ: cohs2ChainLen (cohs3ChainDepsCohs2 a) = (dcPackLen cQ + Q)%nat)
  (HheadR: cohs2ChainLen (cohs3ChainDepsCohs2 a) = (dcPackLen cR + R)%nat)
  (HheadQU: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (dcPackLen cQU + Q.+1)%nat)
  (HheadRU: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))
    = (dcPackLen cRU + R)%nat)
  (HfullQ: cohs2ChainLen (cohs3ChainDepsCohs2 full) = (dcPackLen cQ + dimQ)%nat)
  (HfullR: cohs2ChainLen (cohs3ChainDepsCohs2 full) = (dcPackLen cR + dimR)%nat)
  (HfullQU: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) full))
    = (dcPackLen cQU + dimQ.+1)%nat)
  (HfullRU: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) full))
    = (dcPackLen cRU + dimR)%nat)
  (epsilon omega: arity) (z: gF0 S0 2):
  gFaceCohC S0 full 0 dimQ HdimQ dimR HdimR epsilon omega z
  • (prefixQuotientZero S0 a full R (HR ↕ HQ) dimR (HdimR ↕ HdimQ)
       cR HheadR HfullR omega (gFaceC S0 full 1 dimQ.+1 (⇑ HdimQ) epsilon z)
     • f_equal (gFaceC S0 a 0 R (HR ↕ HQ) omega)
         (prefixQuotientOne S0 a full Q.+1 (⇑ HQ) dimQ.+1 (⇑ HdimQ)
           cQU HheadQU HfullQU epsilon z))
  = (prefixQuotientZero S0 a full Q HQ dimQ HdimQ
       cQ HheadQ HfullQ epsilon (gFaceC S0 full 1 dimR (HdimR ↕ ↑ HdimQ) omega z)
     • f_equal (gFaceC S0 a 0 Q HQ epsilon)
         (prefixQuotientOne S0 a full R (HR ↕ ↑ HQ) dimR (HdimR ↕ ↑ HdimQ)
           cRU HheadRU HfullRU omega z))
    • gFaceCohC S0 a 0 Q HQ R HR epsilon omega z.
Proof.
  destruct (chain3Factor a full n Hfactor) as (tail & Heq & Hn).
  destruct Heq.
  destruct Hn.
  subst dimQ dimR.
  unfold prefixQuotientZero, prefixQuotientOne.
  rewrite (faceAsNuCompose S0 a tail R (HR ↕ HQ) (HdimR ↕ HdimQ)
    cR.2.2.2 HheadR HfullR omega).
  rewrite (faceAsNuCompose S0 a tail Q HQ HdimQ
    cQ.2.2.2 HheadQ HfullQ epsilon).
  rewrite 2 tailComparisonCancel.
  rewrite (faceCommonOneSucc S0 a tail Q (⇑ HQ) (⇑ HdimQ)
    cQU.2.2.2 HheadQU HfullQU epsilon z).
  rewrite (faceCommonOne S0 a tail R (HR ↕ ↑ HQ) (HdimR ↕ ↑ HdimQ)
    cRU.2.2.2 HheadRU HfullRU omega z).
  now exact (gFaceComposeCoh S0 a tail Q HQ R HR HdimQ HdimR epsilon omega z).
Defined.

#[local] Arguments Desc {X n Xpre}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments descFaceAtPrefix {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descFaceAtPrefixCommonFace {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments prefixCutFullLength {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments prefixFullLength3 {X M XpB0 S0} HD {p k dc3}.

(** The prefix square for [canonicalSquareOfPrefix], with all four
    edges expressed as [descFaceAtPrefix] paths. The upper ε-face retains
    the successor index [(q+p).+1]. *)
Lemma descFaceAtPrefixCoh {X: νGpds}
  {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
  (HlenB: cohs3ChainLen (descChain (DescS HD)).2
    = (cohsChainLen (cohs2ChainDepsCohs
        (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a))) + p)%nat)
  (q: nat) (Hq: q <= k) (Hdim: q + p <= M)
  (epsilon omega: arity) (T: νTotal (next (next S0))):
  let Hp := leR_add_l q ↕ Hdim in
  gFaceCohC S0 (descChain HD).2 0 (q+p) Hdim p (leR_add_l q) epsilon omega T
  • (descFaceAtPrefix HD a 0 leR_O p Hp eq_refl Hlen omega
       (gFaceC S0 (descChain HD).2 1 (q+p).+1 (⇑ Hdim) epsilon T)
     • f_equal (gFaceC S0 a 0 0 leR_O omega)
         (descFaceAtPrefix (DescS HD) (chainUp1 (νExt3At S0) a)
           q.+1 (⇑ Hq) (q+p).+1 (⇑ Hdim) eq_refl HlenB epsilon T))
  = (descFaceAtPrefix HD a q Hq (q+p) Hdim eq_refl Hlen epsilon
       (gFaceC S0 (descChain HD).2 1 p (↑ Hp) omega T)
     • f_equal (gFaceC S0 a 0 q Hq epsilon)
         (descFaceAtPrefix (DescS HD) (chainUp1 (νExt3At S0) a)
           0 leR_O p (↑ Hp) eq_refl HlenB omega T))
    • faceAtCohUp (νExt3At S0) a q Hq 0 leR_O epsilon omega
        (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a)) T).1
        (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) a)) T).2.
Proof.
  intro Hp.
  rewrite 4 descFaceAtPrefixCommonFace.
  unfold gFaceCAsνFace.
  now exact (prefixQuotientCoh S0 a (descChain HD).2 p (prefixFullLength3 HD a Hlen)
    q Hq 0 leR_O (q+p) p Hdim (leR_add_l q)
    (prefixAddComm q p) (plus_n_O p)
    (prefixCut a q Hq) (prefixCut a 0 leR_O)
    (prefixCut (S0 := next S0) (chainUp1 (νExt3At S0) a) q.+1 (⇑ Hq))
    (prefixCut (S0 := next S0) (chainUp1 (νExt3At S0) a) 0 leR_O)
    (prefixCutTwoLength a q Hq) (prefixCutTwoLength a 0 leR_O)
    (prefixCutTwoLength (S0 := next S0) (chainUp1 (νExt3At S0) a) q.+1 (⇑ Hq))
    (prefixCutTwoLength (S0 := next S0) (chainUp1 (νExt3At S0) a) 0 leR_O)
    (cohs3ChainDepsCohs2Len (descChain HD).2
      • prefixCutFullLength HD a q Hq (q+p) eq_refl Hlen)
    (cohs3ChainDepsCohs2Len (descChain HD).2
      • prefixCutFullLength HD a 0 leR_O p eq_refl Hlen)
    (cohs3ChainDepsCohs2Len (descChain (DescS HD)).2
      • prefixCutFullLength (DescS HD) (chainUp1 (νExt3At S0) a)
          q.+1 (⇑ Hq) (q+p).+1 eq_refl HlenB)
    (cohs3ChainDepsCohs2Len (descChain (DescS HD)).2
      • prefixCutFullLength (DescS HD) (chainUp1 (νExt3At S0) a)
          0 leR_O p eq_refl HlenB)
    epsilon omega T).
Defined.

#[local] Arguments Desc {X n Xpre}.
#[local] Arguments DescS {X n Xpre S0}.
#[local] Arguments FgLevel {X}.
#[local] Arguments FrtDeps {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtDepsCohs {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtFramesNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtFramesPrevType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtFramesType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPaintingsNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPtChain {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments FrtPtStep {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtRestrLayerStep {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtSplitDataAt {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments FrtSplitStep {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtStepDataAt {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments _fcF {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcPshRp {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcTX {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcTrRp {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frFrames {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frPaintings {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frDepsA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frPshRestrs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frTrRestrs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments fgFrpNextOf {X}.
#[local] Arguments fgFrtNextOf {X}.
#[local] Arguments fgPrefixNext {X}.
#[local] Arguments fgQNext {X}.
#[local] Arguments fgTowerAt {X}.
#[local] Arguments frTr {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtDcB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtTopNext {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtTrCohs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtFrameStep {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtLayerType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtPaintingStepDown {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments proj1FrtDepsCohs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments pshRc {X}.
#[local] Arguments pshRp {X}.
#[local] Arguments pshTw {X}.
#[local] Arguments towerFrtDepsCohs {X}.
#[local] Arguments towerFrtDepsCohsOf {X}.
#[local] Arguments FrtPairLawAt {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtRestr0At {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtRestrLayerStepAt {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcCohsA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcPX {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcPshCohs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcRpA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcXA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshCohs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshCohsOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtTrBase {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtDepsOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtResidueOfRestr {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments proj1FrtDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descQcells {X M XpB0 S0 HD p k dcB}.
#[local] Arguments frtCellPair {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments descTop {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments frtPairLawPrev {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPairLawAlignU {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments descCellPairRestrTotal {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments frtPairRestrPaintingAtQ {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPairSqExchangeQ {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtDepsCohsGen {X M XpB0 S0 HD p k dc2}.
#[local] Arguments frtChainUp {M XpB0 S0 p k dc3M}.
#[local] Arguments _frBound {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtCanonicalSquare {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments frtTopAlignU {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments frtTopAlignUCons {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments _fcXB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcRpB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcTrCohs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments fgDeps {X}.
#[local] Arguments fgFrtOf {X}.
#[local] Arguments fgFrpOf {X}.
#[local] Arguments descAt {X}.
#[local] Arguments descChainLen {X n Xpre S0}.
#[local] Arguments fgSplitOf {X}.
#[local] Arguments fgPtChain {X}.
#[local] Arguments fgRpStep {X}.
#[local] Arguments lvP {X m}.
#[local] Arguments lvFrt {X m}.
#[local] Arguments lvFrp {X m}.
#[local] Arguments lvQ {X m}.
#[local] Arguments lvW {X m}.
#[local] Arguments fgRpChainOfChains {X}.
#[local] Arguments rpBChainOf {X}.
#[local] Arguments frtCanonicalSquareOf {X} SP M {XpB0 S0} HD p {k dcB}.
#[local] Arguments fgRpStepCanonical {X}.
#[local] Arguments descCell {X m XpB SB}.
#[local] Arguments descCellPairRestrAt {X n XpB0 S0} HD {pB kB dcB}.
#[local] Arguments descCellPairRestrAtAsFace {X n XpB0 S0} HD {pB kB dcB}.
#[local] Arguments frtTrBaseOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frFrameEqvs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frPaintingEqvs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descCellFace {X n XpB SB}.
#[local] Arguments _frPshFrames {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frPshPaintings {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descCellPairRestrTotalCons {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descCellPairRestrTotalIrr {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descCellPairRestrTotalZero {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments mkFrtPaintingTypes {X} M {p k framesA framesB eqvs pshFrames cells} frt {paintingsA paintingsB}.
#[local] Arguments mkCellValues {X} M {p k}.
#[local] Arguments mkCellValuesOf {X} M {P K depsTop extTop p k deps ext}.
#[local] Arguments descCells {X m XpB SB}.
#[local] Arguments descPairFaceComparisonZero {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparison {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonZeroRead {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonCons {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments descPairFaceComparisonTotal {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments frtPairReadDeepCell {M XpB0 S0 p k dc3}.
#[local] Arguments _fcCohsB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descCellFaceSq {X n Xpre S0}.
#[local] Arguments descCellPairRestrCanonicalIrr {X M XpB0 S0} HD {p k dc3}.
Section FinalB.
Variable X: νGpds.
Context {M: nat} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0)
  {p k: nat} {dc3M: DepsCohs3 p k}
  (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
  (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
    (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA
    (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX rpA
    (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp cohsA
    (mkDepsCohs dc3M.(_depsCohs2)).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA))
  (Hlen: cohs3ChainLen (descChain HD).2
    = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) + p)%nat)
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
    = (cohsChainLen (frtChainUp aH) + p.+1)%nat)
  (frames: FrtFramesNextType
    (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
      cohsA trCohs pshCohs) (frtChainUp aH))
  (paintings: FrtPaintingsNextType
    (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
      cohsA trCohs pshCohs) (frtChainUp aH) frames).

Let FC := mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp
  pshRp cohsA trCohs pshCohs.
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH).
Let HP := frtPairLawAlignU HD aH Hlen F.

(** Generalize [frtPairSqLadderU] to every [q], using the B-side data.
    The [Frt] parameters package its endpoints. *)
Let bUp := chainUp1 (νExt3At S0) aH.
Let HlenB := Hlen' • eq_sym (plus_n_Sm (cohsChainLen (frtChainUp aH)) p).

Lemma frtPairSqExchangeQStored
  (q: nat) (Hq: q <= k) (epsilon omega: arity) (w: CellBelow dc3M):
  frtPairSqExchangeQ FC q Hq epsilon omega (w.1; w.2.1)
  = eq_sym (restrCellCoh dc3M q Hq 0 leR_O epsilon omega w.1 w.2).
Proof.
  rewrite (restrCellCohRZero dc3M q Hq leR_O epsilon omega w).
  unfold frtPairSqExchangeQ.
  lazymatch goal with
  | |- @eq_existT_curried _ _ _ _ _ _ _
      (@rewSwapSym ?DD ?PP ?xx ?yy ?cc ?uu ?vv ?ee) = _ =>
    now exact (eq_sym (@symExistTSwap DD PP yy xx cc vv uu ee))
  end.
Defined.

(** The concrete top frame in the B-side exchange theorem is the first
    two components of w. The upper chain bUp is a known Cons, so the
    identification follows by conversion. *)
Lemma frtPairSqExchangeQStoredAt
  (q: nat) (Hq: q <= k) (epsilon omega: arity)
  (t: (g X).(G0) M.+2):
  let T := descCell (DescS (DescS HD)) t in
  let w := deepCell (cohs3ChainDepsCohs2 bUp) T in
  frtPairSqExchangeQ FC q Hq epsilon omega
    (descTop (DescS HD) (frtChainUp aH) t).1
  = eq_sym (restrCellCoh dc3M q Hq 0 leR_O epsilon omega w.1 w.2).
Proof.
  intros T w.
  now exact (frtPairSqExchangeQStored q Hq epsilon omega w).
Defined.

Section RawIndexSquare.
Context (q: nat) (Hq: q <= k) (Hdim: q + p <= M)
  (epsilon omega: arity) (t: (g X).(G0) M.+2).

Let Hp := leR_add_l q ↕ Hdim.
Let T := descCell (DescS (DescS HD)) t.
Let w := deepCell (cohs3ChainDepsCohs2 bUp) T.
Let u := (g X).(GFace) M.+1 p (↑ Hp) omega t.
Let v := (g X).(GFace) M.+1 (q + p).+1 (⇑ Hdim) epsilon t.
Let y_o := gFaceC (next S0) (descChain (DescS HD)).2 0 p (↑ Hp) omega T.
Let y_e := gFaceC (next S0) (descChain (DescS HD)).2 0
  (q + p).+1 (⇑ Hdim) epsilon T.
Let C := localPairRead aH.
Let D := deepCell (cohs3ChainDepsCohs2 aH).
Let P := localPairRead bUp.
Let n_o := fun z: CellHere dc3M =>
  faceAt (cohs3ChainDepsCohs2 aH) 0 leR_O omega z.1 z.2.
Let n_e := fun z: CellHere dc3M =>
  faceAt (cohs3ChainDepsCohs2 aH) q Hq epsilon z.1 z.2.
Let r_o := localRestriction dc3M 0 leR_O omega.
Let r_e := localRestriction dc3M q Hq epsilon.
Let alpha_o := descFaceAtPrefix HD aH 0 leR_O p Hp eq_refl Hlen omega.
Let alpha_e := descFaceAtPrefix HD aH q Hq (q + p) Hdim eq_refl Hlen epsilon.
Let upper_e := descFaceAtPrefix (DescS HD) bUp q.+1 (⇑ Hq)
  (q + p).+1 (⇑ Hdim) eq_refl HlenB epsilon T.
Let upper_o := descFaceAtPrefix (DescS HD) bUp 0 leR_O
  p (↑ Hp) eq_refl HlenB omega T.
Let G := gFaceCohC S0 (descChain HD).2 0 (q + p) Hdim
  p (leR_add_l q) epsilon omega T.
Let Glocal := faceAtCohUp (νExt3At S0) aH q Hq 0 leR_O
  epsilon omega w.1 w.2.

(** The prefix coherence interface supplied by descFaceAtPrefixCoh,
    using the raw successor index throughout. *)
Definition ActualPrefixSquareForB: Type :=
  G • (alpha_o y_e • f_equal (fun y => n_o (D y)) upper_e)
  = (alpha_e y_o • f_equal (fun y => n_e (D y)) upper_o) • Glocal.

Lemma canonicalBExchangeOfPrefix (PC: ActualPrefixSquareForB):
  f_equal (frtCellPair HD cb)
    ((g X).(GFaceCoh) M (q + p) Hdim p (leR_add_l q) epsilon omega t)
  • (descCellPairRestrTotal HD aH 0 leR_O p Hp eq_refl Hlen omega v
     • (f_equal r_o
          (descCellPairRestrCanonical (DescS HD) bUp q.+1 (⇑ Hq)
            (q + p).+1 (⇑ Hdim) eq_refl HlenB epsilon t)
        • eq_sym (restrCellCoh dc3M q Hq 0 leR_O epsilon omega w.1 w.2)))
  = descCellPairRestrTotal HD aH q Hq (q + p) Hdim eq_refl Hlen epsilon u
    • f_equal r_e
        (descCellPairRestrCanonical (DescS HD) bUp 0 leR_O
          p (↑ Hp) eq_refl HlenB omega t).
Proof.
  pose proof (@canonicalSquareOfPrefix
    ((g X).(G0) M) (νTotal S0) (νTotal (next S0))
    (CellHere dc3M) (CellRestr dc3M)
    (descCell HD) C D P (frtPairReadDeepCell aH)
    (gFaceC S0 (descChain HD).2 0 p Hp omega)
    (gFaceC S0 (descChain HD).2 0 (q + p) Hdim epsilon)
    n_o n_e r_o r_e
    (localFaceComparison aH 0 leR_O omega)
    (localFaceComparison aH q Hq epsilon)
    alpha_o alpha_e _ _
    ((g X).(GFaceCoh) M (q + p) Hdim p (leR_add_l q) epsilon omega t)
    (descCell (DescS HD) v) y_e (descCell (DescS HD) u) y_o
    (descCellFace (DescS HD) (q + p).+1 (⇑ Hdim) (⇑ Hdim) epsilon t)
    (descCellFace (DescS HD) p (↑ Hp) (↑ Hp) omega t)
    (descCellFace HD p Hp Hp omega v)
    (descCellFace HD (q + p) Hdim Hdim epsilon u)
    G (descCellFaceSq HD (q + p) Hdim p (leR_add_l q) epsilon omega t)
    _ _ upper_e upper_o Glocal PC _ _
    (deepCellFaceAtUp (νExt3At S0) aH q.+1 (⇑ Hq) epsilon w.1 w.2)
    (deepCellFaceAtUp (νExt3At S0) aH 0 leR_O omega w.1 w.2)
    (restrCellCoh dc3M q Hq 0 leR_O epsilon omega w.1 w.2)
    (localFaceComparisonCoh (νExt3At S0) aH q Hq 0 leR_O
      epsilon omega w)
    (descCellPairRestrCanonical (DescS HD) bUp q.+1 (⇑ Hq)
      (q + p).+1 (⇑ Hdim) eq_refl HlenB epsilon t)
    (descCellPairRestrCanonical (DescS HD) bUp 0 leR_O
      p (↑ Hp) eq_refl HlenB omega t)
    (@descUpperCanonicalDeepNormal X M XpB0 S0 HD p k dc3M aH
      HlenB q.+1 (⇑ Hq) (q + p).+1 (⇑ Hdim) eq_refl epsilon t)
    (@descUpperCanonicalDeepNormal X M XpB0 S0 HD p k dc3M aH
      HlenB 0 leR_O p (↑ Hp) eq_refl omega t)) as H.
  rewrite 2 descCellPairRestrTotalAsFace.
  rewrite 2 descPairFaceComparisonTotalNormal.
  rewrite f_equal_compose in H.
  now exact H.
Defined.

End RawIndexSquare.

(** Generated B-side exchange with the explicit upper dimension correction.
    Prefix coherence is supplied by descFaceAtPrefixCoh. *)
Lemma frtPairSqTotalLadder
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (epsilon omega: arity) (t: (g X).(G0) M.+2):
  f_equal (frtCellPair HD cb)
    ((g X).(GFaceCoh) M (q + p) (⇓ leR_add_shift Hqp)
      p (leR_add_l q) epsilon omega t
     • f_equal ((g X).(GFace) M p
          (leR_add_l q ↕ (⇓ leR_add_shift Hqp)) omega)
         (pshFaceDimIrr (g X) (plus_n_Sm q p)
           (Hq := ⇑ (⇓ leR_add_shift Hqp)) (Hq' := Hqp) epsilon t))
  • (HP omega ((g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t)
     • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) omega)
          (descQcells (frtChainUp aH) Hlen' q Hq Hqp epsilon t)
        • frtPairSqExchangeQ FC q Hq epsilon omega
            (descTop (DescS HD) (frtChainUp aH) t).1))
  = descCellPairRestrTotal HD aH q Hq (q + p) (⇓ leR_add_shift Hqp)
      eq_refl Hlen epsilon
      ((g X).(GFace) M.+1 p
        (leR_add_l q ↕ ↑ (⇓ leR_add_shift Hqp)) omega t)
    • f_equal (frtPairRestrPaintingAtQ FC q Hq epsilon)
        (frtPairLawPrev FC (frtChainUp aH) Hlen' frames paintings omega t).
Proof.
  pose (Hdim := ⇓ leR_add_shift Hqp).
  pose (Hp := leR_add_l q ↕ Hdim).
  pose (T := descCell (DescS (DescS HD)) t).
  pose proof (descFaceAtPrefixCoh (X := X) HD aH Hlen HlenB
    q Hq Hdim epsilon omega T) as PC.
  pose (w := deepCell (cohs3ChainDepsCohs2 bUp) T).
  pose (e := plus_n_Sm q p).
  pose (v0 := (g X).(GFace) M.+1 (q + p).+1 (⇑ Hdim) epsilon t).
  pose (v1 := (g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t).
  pose (delta := pshFaceDimIrr (g X) e
    (Hq := ⇑ Hdim) (Hq' := Hqp) epsilon t).
  pose (K0 := descCellPairRestrCanonical (DescS HD) bUp q.+1 (⇑ Hq)
    (q + p).+1 (⇑ Hdim) eq_refl HlenB epsilon t).
  pose (K1 := descCellPairRestrCanonical (DescS HD) bUp q.+1 (⇑ Hq)
    (q + p.+1) Hqp (eq_sym e) HlenB epsilon t).

  unfold HP, frtPairLawAlignU.
  rewrite <- (descCellPairRestrTotalZero HD aH Hlen leR_O Hp omega v1).
  rewrite (@descQcellsOmegaAsUpperCanonical X M XpB0 S0 HD p k dc3M aH
    Hlen' q Hq Hqp epsilon omega t).
  rewrite frtPairLawPrevCanonical.
  rewrite (frtPairSqExchangeQStoredAt q Hq epsilon omega t).

  pose proof (@canonicalUpperReindex
    ((g X).(G0) M.+1) ((g X).(G0) M) (CellHere dc3M) (CellRestr dc3M)
    ((g X).(GFace) M p Hp omega) (frtCellPair HD cb)
    (frtCellPair (DescS HD) (DepsCohsChainCons (frtChainUp aH)))
    (localRestriction dc3M 0 leR_O omega)
    (fun z => descCellPairRestrTotal HD aH 0 leR_O p Hp eq_refl Hlen omega z)
    v0 v1 delta _ K0 K1
    (descCellPairRestrCanonicalIrr (DescS HD) bUp q.+1 (⇑ Hq)
      (q + p).+1 (q + p.+1) e (⇑ Hdim) Hqp
      eq_refl (eq_sym e) HlenB HlenB epsilon t)
    _ ((g X).(GFaceCoh) M (q + p) Hdim p (leR_add_l q) epsilon omega t)
    _ (eq_sym (restrCellCoh dc3M q Hq 0 leR_O epsilon omega w.1 w.2))) as R.
  rewrite R.
  now exact (canonicalBExchangeOfPrefix q Hq Hdim epsilon omega t PC).
Defined.

End FinalB.
End CoherenceOn.
