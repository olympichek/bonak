(** The indexed round trip for strict groupoid presentations. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category Require Import FunctorAlgebra.
From Bonak.Category.Groupoid Require Import StructureIdentity GraphFiberRoundtrip FamilyIdentity.
From Bonak.Presheaf.StrictGpd Require Import Presentation.
From Bonak.Equiv.StrictGpd Require Import νStrictGpdEquiv
  Constructions.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νStrictGpdRoundtripOn (A: LayerSig) (S: νStrictGpdSig A)
  (Base: ConstructionsSig A S).
Import A.
Module Export Core := S.
Module Export Faces := Base.Faces.
Module Export Reconstruction := Base.Reconstruction.
Module Export Extraction := Base.Extraction.
Module Export Indexed := νStrictGpdEquivOn A S.

Lemma pshChainLift (psh: νStrictGpdPresentation arity) {M P K} (PCTop: PshDepsCohs psh M P K)
  {p k} {dc: DepsCohs p k}
  (c0: DepsCohsChain (pshDepsCohs psh PCTop) dc):
  {PC: PshDepsCohs psh M p k &T {C: PshCohsChain psh PCTop PC &T
    ((dc; c0): {dc0: DepsCohs p k &T
       DepsCohsChain (pshDepsCohs psh PCTop) dc0}) =
    (pshDepsCohs psh PC; pshCohsChainCohs psh C)}}.
Proof.
  induction c0 as [|p k dc' c0' IH].
  - now exact (PCTop; (PshCohsChainNil; eq_refl)).
  - destruct IH as (PC', (C', e')).
    refine (proj1PshDepsCohs psh PC'; (PshCohsChainCons C'; _)).
    now exact (f_equal (fun s: {dc0: DepsCohs p.+1 k &T
        DepsCohsChain (pshDepsCohs psh PCTop) dc0} =>
      ((proj1DepsCohs s.1; DepsCohsChainCons s.2):
        {dc0: DepsCohs p k.+1 &T
          DepsCohsChain (pshDepsCohs psh PCTop) dc0})) e').
Defined.

(** Normal forms of chain packages

    The indexed round trip compares the chains synthesized by [g] with
    arbitrary chains from the same top stage. Both arise by iterating
    [dcStep] on the nil package; their lengths determine the comparison. *)

Lemma chain2DownIter {P K} (T2: DepsCohs2 P K) (j: nat):
  dc2PackDeps (chain2Down T2 j) =
  Nat.iter j dcStep (P; (K; (T2.(_depsCohs); DepsCohsChainNil))).
Proof.
  induction j; cbn [chain2Down Nat.iter nat_rect].
  - now reflexivity.
  - now rewrite dc2PackDepsStep, IHj.
Defined.

Lemma chainPackNF {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  ((p; (k; (dc; c))): DCPack dcTop) =
  Nat.iter (cohsChainLen c) dcStep (P; (K; (dcTop; DepsCohsChainNil))).
Proof.
  induction c as [|p k dc c IH].
  - now reflexivity.
  - now exact (f_equal dcStep IH).
Defined.

Lemma νFaceRewPrefix {n} {XpA XpB: (νStrictGpdAt n.+1).(prefix)} (e: XpA = XpB)
  {p k} {dc: DepsCohs p k} (cB: DepsCohsChain (prefixDepsCohs XpB) dc)
  (ε: arity):
  transportGroupoidFunctor (f_equal νFrame e) ⨟ᶠ νFace cB ε =
  νFace (rew <- [fun Xp => DepsCohsChain (prefixDepsCohs Xp) dc] e in cB) ε
    ⨟ᶠ transportGroupoidFunctor (f_equal νTotalGpd e).
Proof.
  destruct e. cbn [transportGroupoidFunctor].
  now rewrite functorIdL, functorIdR.
Defined.

Lemma νFaceRewPrefixNil {n} {XpA XpB: (νStrictGpdAt n.+1).(prefix)} (e: XpA = XpB)
  (ε: arity):
  transportGroupoidFunctor (f_equal νFrame e) ⨟ᶠ
    νFace (dcTop := prefixDepsCohs XpB) DepsCohsChainNil ε =
  νFace (dcTop := prefixDepsCohs XpA) DepsCohsChainNil ε ⨟ᶠ
    transportGroupoidFunctor (f_equal νTotalGpd e).
Proof.
  destruct e. cbn [transportGroupoidFunctor].
  now rewrite functorIdL, functorIdR.
Defined.

(** A commuting frame square identifies the reconstructed strict fiber
    with the original displayed groupoid. *)
Definition fillerIsoOfPrefix {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  {E: νFillerType XB} {C: StrictGroupoid} (HF: C = total E)
  (p: Functor C (νFrame XA))
  (h: p ⨟ᶠ transportGroupoidFunctor (f_equal νFrame e) =
    transportGroupoidFunctor HF ⨟ᶠ proj E):
  νFillerEqvType e (graphFiber p) E.
Proof.
  destruct e. cbn [f_equal transportGroupoidFunctor] in h.
  rewrite functorIdR in h.
  refine (graphFiberIsoOf eq_refl HF p _).
  now rewrite functorIdR, h.
Defined.

Lemma totalExtendCong {n} {X: (νStrictGpdAt n).(prefix)}
  {E P: νFillerType X} (q: E = P):
  f_equal νTotalGpd (extendCong (T := νStrictGpdTel) eq_refl q) = f_equal total q.
Proof. now destruct q. Defined.

(** The corresponding equality of totals sends the canonical graph
    section to the original cell, on objects and arrows. *)
Lemma fillerIsoOfPrefixWhole {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  {E: νFillerType XB} {C: StrictGroupoid} (HF: C = total E)
  (p: Functor C (νFrame XA))
  (h: p ⨟ᶠ transportGroupoidFunctor (f_equal νFrame e) =
    transportGroupoidFunctor HF ⨟ᶠ proj E):
  graphUnit p ⨟ᶠ transportGroupoidFunctor
    (f_equal νTotalGpd (extendCong (T := νStrictGpdTel) e
      (νFillerEq e (fillerIsoOfPrefix e HF p h)))) = transportGroupoidFunctor HF.
Proof.
  destruct e. rewrite totalExtendCong, totalFamilyPath.
  now apply graphFiberIsoOfWhole.
Defined.

Lemma fgFaceB {m} {Xpre: (νStrictGpdAt m.+1).(prefix)} (SB: νStrictGpdFrom m.+1 Xpre)
  {p k} {dc: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt SB) dc)
  (Hp: p <= m.+1) (ε: arity):
  gFace SB 0 p Hp ε = proj (this (next SB)) ⨟ᶠ νFace cB ε.
Proof.
  change (νFaceFuel SB (m.+1 - p) ε = proj (this (next SB)) ⨟ᶠ νFace cB ε).
  unfold νFaceFuel.
  rewrite (f_equal (fun z => z - p) (eq_sym (cohsChainStage cB))
    • addSubCancelL p (cohsChainLen cB)).
  now exact (f_equal
    (fun s: DCPack (νDepsCohsAt SB) => proj (this (next SB)) ⨟ᶠ νFace s.2.2.2 ε)
    (chain2DownIter (νDepsCohs2At SB) (cohsChainLen cB)
      • eq_sym (chainPackNF cB))).
Defined.

Lemma gFaceLevelEq {m0} {Xpre0: (νStrictGpdAt m0).(prefix)} (X0: νStrictGpdFrom m0 Xpre0)
  {n1 n2: nat} (e: n1 = n2) (dim: nat)
  (H1: dim <= n1 + m0) (H2: dim <= n2 + m0) (ε: arity):
  transportGroupoidFunctor (f_equal (fun l => gF0 X0 l.+1) e) ⨟ᶠ gFace X0 n2 dim H2 ε =
  gFace X0 n1 dim H1 ε ⨟ᶠ transportGroupoidFunctor (f_equal (gF0 X0) e).
Proof. destruct e. now rewrite functorIdL, functorIdR. Defined.

Section FG.
Variable X: νStrictGpds.

Inductive Desc: forall {n} {Xpre: (νStrictGpdAt n).(prefix)}, νStrictGpdFrom n Xpre -> Type :=
| DescZ: Desc X
| DescS {n} {Xpre: (νStrictGpdAt n).(prefix)} {S0: νStrictGpdFrom n Xpre}:
    Desc S0 -> Desc (next S0).

Fixpoint descF0 {n} {Xpre: (νStrictGpdAt n).(prefix)} {S0: νStrictGpdFrom n Xpre}
  (D: Desc S0) (k: nat) {struct D}: gF0 X (k + n) = gF0 S0 k :=
  match D in @Desc n0 _ S1 return gF0 X (k + n0) = gF0 S1 k with
  | DescZ => f_equal (gF0 X) (eq_sym (plus_n_O k))
  | @DescS n1 _ S1 D' =>
      f_equal (gF0 X) (eq_sym (plus_n_Sm k n1)) • descF0 D' k.+1
  end.

Definition descTotal {n} {Xpre: (νStrictGpdAt n).(prefix)} {S0: νStrictGpdFrom n Xpre}
  (D: Desc S0): gF0 X n = νTotal S0 := descF0 D 0.

Lemma descFaceInv {n} {Xpre: (νStrictGpdAt n).(prefix)} {S0: νStrictGpdFrom n Xpre}
  (D: Desc S0) (k dim: nat) (HdX: dim <= k + n) (HdS: dim <= k + n) (ε: arity):
  transportGroupoidFunctor (eq_sym (descF0 D k.+1)) ⨟ᶠ (g X).(GFace) (k + n) dim HdX ε =
  gFace S0 k dim HdS ε ⨟ᶠ transportGroupoidFunctor (eq_sym (descF0 D k)).
Proof.
  revert k dim HdX HdS ε; induction D; intros k dim HdX HdS ε.
  - cbn [descF0].
    rewrite 2 eq_sym_f_equal.
    rewrite (natUIP (eq_sym (eq_sym (plus_n_O k))) (plus_n_O k)).
    rewrite (natUIP (eq_sym (eq_sym (plus_n_O k.+1))) (f_equal S (plus_n_O k))).
    rewrite (f_equal_compose S (gF0 X) (plus_n_O k)).
    now exact (gFaceLevelEq X (plus_n_O k) dim HdS
      (leR_eq_r (plus_n_O (k + 0)) HdX) ε).
  - cbn [descF0].
    rewrite 2 eq_trans_sym_distr, 2 eq_sym_f_equal.
    rewrite (natUIP (eq_sym (eq_sym (plus_n_Sm k n))) (plus_n_Sm k n)).
    rewrite (natUIP (eq_sym (eq_sym (plus_n_Sm k.+1 n))) (f_equal S (plus_n_Sm k n))).
    rewrite (f_equal_compose S (gF0 X) (plus_n_Sm k n)), 2 transportGroupoidFunctorComp.
    rewrite functorAssocEq.
    rewrite (gFaceLevelEq X (plus_n_Sm k n) dim
      (leR_eq_r (eq_sym (plus_n_Sm k n) • plus_n_O (k + n).+1) HdS)
      (leR_eq_r (plus_n_O (k + n.+1)) HdX) ε).
    rewrite <- functorAssocEq.
    rewrite (IHD k.+1 dim (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS)
      (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS) ε).
    now rewrite functorAssocEq.
Defined.

Lemma descFace {n} {Xpre: (νStrictGpdAt n).(prefix)} {S0: νStrictGpdFrom n Xpre}
  (D: Desc S0) (k dim: nat) (HdX: dim <= k + n) (HdS: dim <= k + n) (ε: arity):
  (g X).(GFace) (k + n) dim HdX ε ⨟ᶠ transportGroupoidFunctor (descF0 D k) =
  transportGroupoidFunctor (descF0 D k.+1) ⨟ᶠ gFace S0 k dim HdS ε.
Proof.
  pose proof (f_equal (fun F => transportGroupoidFunctor (descF0 D k.+1) ⨟ᶠ F ⨟ᶠ
      transportGroupoidFunctor (descF0 D k)) (descFaceInv D k dim HdX HdS ε)) as e.
  cbn beta in e.
  rewrite <- (functorAssocEq
    (transportGroupoidFunctor (descF0 D k.+1))
    (transportGroupoidFunctor (eq_sym (descF0 D k.+1))) _) in e.
  rewrite transportGroupoidFunctorSymL, functorIdL in e.
  rewrite (functorAssocEq
    (transportGroupoidFunctor (descF0 D k.+1)) _ _) in e.
  rewrite (functorAssocEq (gFace S0 k dim HdS ε) _ _),
    transportGroupoidFunctorSymR, functorIdR in e.
  now exact e.
Defined.

Lemma descTotalS {n} {Xpre: (νStrictGpdAt n).(prefix)} {S0: νStrictGpdFrom n Xpre}
  (HD: Desc S0): descTotal (DescS HD) = descF0 HD 1.
Proof.
  unfold descTotal; cbn [descF0].
  rewrite (natUIP (eq_sym (plus_n_Sm 0 n)) eq_refl).
  now apply eq_trans_refl_l.
Defined.

(** The frame square carried at each level. Its extension follows by
    comparing every face and using the total-space computation above. *)
Definition FrtInv {m} {XpA XpB: (νStrictGpdAt m.+1).(prefix)} (e: XpA = XpB)
  (T: PshTower (g X) m XpA) (SB: νStrictGpdFrom m.+1 XpB) (HD: Desc SB): Type :=
  mkPshFrame (g X) (towerPshDeps (g X) T) ⨟ᶠ
    transportGroupoidFunctor (f_equal νFrame e) =
  transportGroupoidFunctor (descTotal HD) ⨟ᶠ proj (this SB).

Definition fgThis {m} {XpA XpB: (νStrictGpdAt m.+1).(prefix)} (e: XpA = XpB)
  (T: PshTower (g X) m XpA) (SB: νStrictGpdFrom m.+1 XpB) (HD: Desc SB)
  (FRT: FrtInv e T SB HD):
  νFillerEqvType e (mkPshFiller (g X) (towerPshDeps (g X) T)) (this SB) :=
  fillerIsoOfPrefix e (descTotal HD)
    (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT.

(** The prefix path one level up: the given prefix path extended by the
    filler path of [fgThis]. *)

Definition fgPathStep {m} {XpA XpB: (νStrictGpdAt m.+1).(prefix)}
  (e: XpA = XpB)
  (T: PshTower (g X) m XpA) (SB: νStrictGpdFrom m.+1 XpB) (HD: Desc SB)
  (FRT: FrtInv e T SB HD):
  ((XpA; mkPshFiller (g X) (towerPshDeps (g X) T)):
    (νStrictGpdAt m.+2).(prefix)) = (XpB; this SB) :=
  extendCong (T := νStrictGpdTel) e (νFillerEq e (fgThis e T SB HD FRT)).

Lemma fgFrameStep {m} {XpA XpB: (νStrictGpdAt m.+1).(prefix)}
  (e0: XpA = XpB)
  (T: PshTower (g X) m XpA) (rpPsh: PshTowerRestrPaintings (g X) T)
  (SB: νStrictGpdFrom m.+1 XpB) (HD: Desc SB) (FRT: FrtInv e0 T SB HD):
  FrtInv (fgPathStep e0 T SB HD FRT)
    (towerStep (g X) T rpPsh) (next SB) (DescS HD).
Proof.
  unfold FrtInv.
  apply (functorEqPath (νFrame ((XpB; this SB): (νStrictGpdAt m.+2).(prefix))).(groupoidStrictness)).
  apply (νFaceEq (dcTop := prefixDepsCohs
    ((XpB; this SB): (νStrictGpdAt m.+2).(prefix)))).
  intros p k dc cB ε. apply pathFunctorEq.
  set (e := fgPathStep e0 T SB HD FRT).
  set (cA := rew <- [fun Xp => DepsCohsChain (prefixDepsCohs Xp) dc] e in cB).
  pose (Hp := leR_eq_r (cohsChainStage cB) (leR_add_r p (cohsChainLen cB))).
  assert (hface:
    mkPshFrame (g X) (towerPshDeps (g X) (towerStep (g X) T rpPsh)) ⨟ᶠ
      νFace cA ε =
    (g X).(GFace) m.+1 p Hp ε ⨟ᶠ
      graphUnit (mkPshFrame (g X) (towerPshDeps (g X) T))).
  { destruct (pshChainLift (g X) (towerPshDepsCohs (g X) T rpPsh) cA)
      as (PC, (Cpsh, ePsh)).
    refine (f_equal (fun s: {dc0: DepsCohs p k &T
        DepsCohsChain (pshDepsCohs (g X) (towerPshDepsCohs (g X) T rpPsh)) dc0}
      => mkPshFrame (g X) (towerPshDeps (g X) (towerStep (g X) T rpPsh))
        ⨟ᶠ νFace s.2 ε) ePsh • _).
    now apply (functorEqPath (total (mkPshFiller (g X)
      (towerPshDeps (g X) T))).(groupoidStrictness)), (pshνFace (g X) Cpsh Hp ε). }
  rewrite functorAssocEq, (νFaceRewPrefix e cB ε).
  fold cA.
  rewrite <- functorAssocEq, hface, functorAssocEq.
  rewrite (fillerIsoOfPrefixWhole e0 (descTotal HD)
    (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT).
  rewrite functorAssocEq, <- (fgFaceB SB cB Hp ε), descTotalS.
  now apply (descFace HD 0 p Hp Hp ε).
Defined.

Definition pshF0A: Functor (gF0 X 0) unitGroupoid := terminalFunctor _.

Definition fgPrefix0: (tt: (νStrictGpdAt 0).(prefix)) = tt := eq_refl.

Lemma frt0:
  pshF0A ⨟ᶠ transportGroupoidFunctor (f_equal νFrame fgPrefix0) =
  transportGroupoidFunctor (descTotal DescZ) ⨟ᶠ proj (this X).
Proof.
  apply (functorEqPath unitGroupoid.(groupoidStrictness)).
  refine (Build_FunctorEq (fun _ => hunit_ext _ _) _).
  intros x y f. now apply hunit_ext.
Defined.

Definition fgThis0:
  νFillerEqvType fgPrefix0 (pshFiller0 (g X)) (this X) :=
  fillerIsoOfPrefix fgPrefix0 (descTotal DescZ) pshF0A frt0.

Definition fgPathStep0:
  ((tt; pshFiller0 (g X)): (νStrictGpdAt 1).(prefix)) = (tt; this X) :=
  extendCong (T := νStrictGpdTel) fgPrefix0 (νFillerEq fgPrefix0 fgThis0).

Lemma fgFrameStep0:
  FrtInv fgPathStep0 (tower1 (g X)) (next X) (DescS DescZ).
Proof.
  unfold FrtInv.
  apply (functorEqPath (νFrame ((tt; this X): (νStrictGpdAt 1).(prefix))).(groupoidStrictness)).
  apply (νFaceEq (dcTop := prefixDepsCohs
    ((tt; this X): (νStrictGpdAt 1).(prefix)))).
  intros p k dc c ε.
  destruct c as [|p k dc' c'].
  2: { pose proof (cohsChainStage c') as HS. now discriminate HS. }
  apply pathFunctorEq.
  rewrite functorAssocEq.
  rewrite (νFaceRewPrefixNil fgPathStep0 ε).
  rewrite <- functorAssocEq.
  assert (hf:
    mkPshFrame (g X) (towerPshDeps (g X) (tower1 (g X))) ⨟ᶠ
      νFace (dcTop := prefixDepsCohs
        ((tt; pshFiller0 (g X)): (νStrictGpdAt 1).(prefix))) DepsCohsChainNil ε =
    (g X).(GFace) 0 0 leR_O ε ⨟ᶠ graphUnit pshF0A).
  { apply (functorEqPath (total (pshFiller0 (g X))).(groupoidStrictness)).
    pose proof (mkPshLayerFace (g X)
      (towerPshDeps (g X) (tower1 (g X))).(_pshPaintings (g X))
      (towerPshDeps (g X) (tower1 (g X))).(_pshRestrs (g X)) leR_O ε) as h.
    unfold νFace; cbn [cohsChainNext cohsChainExt getFrame getPainting].
    rewrite functorIdL, functorIdR.
    now exact h. }
  rewrite hf, functorAssocEq.
  rewrite (fillerIsoOfPrefixWhole fgPrefix0 (descTotal DescZ) pshF0A frt0).
  rewrite descTotalS.
  rewrite (descFace DescZ 0 0 leR_O leR_O ε).
  apply (functorEqPath (total (this X)).(groupoidStrictness)).
  unshelve econstructor; now intros.
Defined.

(** Assemble the stagewise filler isomorphisms into a chain of prefix
    paths between the reconstructed tower and its source. The state records
    the frame identification and the agreement of the two finite
    unfoldings. *)

Fixpoint descAt (m: nat): Desc ((νStrictGpdPack m X).2) :=
  match m with
  | 0 => DescZ
  | S m => DescS (descAt m)
  end.

Definition FgState (m: nat)
  (P: {Xp: (νStrictGpdAt m.+1).(prefix) &T νStrictGpdFrom m.+1 Xp})
  (e: P.1 = (νStrictGpdPack m.+1 X).1): Type :=
  { HP: (pshApprox (g X) m.+1; pshFrom (g X) m.+1) = P &T
    FrtInv (rew <- [fun Q: {Xp: (νStrictGpdAt m.+1).(prefix) &T νStrictGpdFrom m.+1 Xp}
                      => Q.1 = (νStrictGpdPack m.+1 X).1] HP in e)
      (pshTw (g X) m) ((νStrictGpdPack m.+1 X).2) (descAt m.+1) }.

(** At each positive level, identify the two approximations before
    constructing the filler isomorphism and the next frame square. *)

Lemma fgStep (m: nat)
  (P: {Xp: (νStrictGpdAt m.+1).(prefix) &T νStrictGpdFrom m.+1 Xp})
  (e: P.1 = (νStrictGpdPack m.+1 X).1) (s: FgState m P e):
  { E: νFillerEqvType e (this P.2) (this ((νStrictGpdPack m.+1 X).2)) &T
    FgState m.+1 ((P.1; this P.2); next P.2)
      (extendCong (T := νStrictGpdTel) e (νFillerEq e E)) }.
Proof.
  destruct s as (HP, s); revert e s; destruct HP; intros e s; cbn in s |- *.
  now exact
    (fgThis e (pshTw (g X) m) ((νStrictGpdPack m.+1 X).2) (descAt m.+1) s;
     (eq_refl;
      fgFrameStep e (pshTw (g X) m) (pshTwRp (g X) m)
        ((νStrictGpdPack m.+1 X).2) (descAt m.+1) s)).
Defined.

(** The state at every level: at level [0] the prefix path is the
    canonical one, above it the state of [fgStep]. *)

Definition FgChainState (m: nat):
  (νStrictGpdPack m (f (g X))).1 = (νStrictGpdPack m X).1 -> Type :=
  match m with
  | 0 => fun e => e = fgPrefix0
  | S m => FgState m (νStrictGpdPack m.+1 (f (g X)))
  end.

Lemma fgChainStep (m: nat)
  (e: (νStrictGpdPack m (f (g X))).1 = (νStrictGpdPack m X).1)
  (s: FgChainState m e):
  { h: rew [νFillerType] e in this (νStrictGpdPack m (f (g X))).2
       = this (νStrictGpdPack m X).2 &T
    FgChainState m.+1 (extendCong (T := νStrictGpdTel) e h) }.
Proof.
  destruct m as [|m]; cbn in s.
  - subst e. now exact (νFillerEq fgPrefix0 fgThis0; (eq_refl; fgFrameStep0)).
  - pose (st := fgStep m _ e s).
    now exact (νFillerEq e st.1; st.2).
Defined.

Definition fg: f (g X) = X :=
  limitEqOfChain (f (g X)) X FgChainState eq_refl fgChainStep.

End FG.
End νStrictGpdRoundtripOn.

Module νStrictGpdRoundtrip (A: LayerSig).
Module Maps := Constructions A.
Include νStrictGpdRoundtripOn A Maps.Core Maps.
End νStrictGpdRoundtrip.

Module νStrictGpdRoundtripSimplicial :=
  νStrictGpdRoundtripOn SimplicialLayer νStrictGpdSimplicial ConstructionsSimplicial.
Module νStrictGpdRoundtripCubical :=
  νStrictGpdRoundtripOn CubicalLayer νStrictGpdCubical ConstructionsCubical.
