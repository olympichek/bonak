(** Reassociation of the generated identification at every ladder depth. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Successor.
From Bonak.Lib Require Import Equiv.
From Bonak Require Import Limit.
Import Logic.EqNotations.

From Bonak.Equiv.Gpd Require PathTactics.

Set Primitive Projections.
Set Keyed Unification.
Module Association (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Import A.

Module Export Succ := Bonak.Equiv.Gpd.νGpdRoundtrip.Successor.Successor A Base Translations.
#[local] Arguments Desc {X n Xpre}.
#[local] Arguments FrtDeps {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtFramesType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _frDepsA {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descChain {X n Xpre S0}.
#[local] Arguments frTr {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPshDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments pshTw {X}.
#[local] Arguments FrtPaintingTopType {X M XpB0 S0 HD p k dcB cB} F {XA XB}.
#[local] Arguments mkFrtPaintingsOfRestr {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments mkFrtRestrTypesAndFrames {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments descTop {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtRestrDataDef {X M XpB0 S0 HD p k dcB cB F}.
#[local] Arguments FrtRestrFramesDef {X M XpB0 S0 HD p k dcB cB F}.
#[local] Arguments proj1FrtDeps {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments fgFrtOf {X}.
#[local] Arguments fgFrpOf {X}.
#[local] Arguments descAt {X}.
#[local] Arguments descCell {X m XpB SB}.
#[local] Arguments mkFrtPaintingTypes {X} M {p k framesA framesB eqvs pshFrames cells} frt {paintingsA paintingsB}.
#[local] Arguments mkCellValues {X} M {p k}.
#[local] Arguments frtPaintingsOfRestrTotal {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments FgTower {X}.
#[local] Arguments FgFrt {X}.
#[local] Arguments FgFrp {X}.
#[local] Arguments FgRestrData {X}.
#[local] Arguments fgDeps {X}.
#[local] Arguments fgThisOfFrames {X m XpA XpB0 S0}.

#[local] Arguments frtCellPair {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments DescS {X n Xpre S0}.
#[local] Arguments FrtDepsCohs {X} M {XpB0 S0} HD {p k dcB}.
#[local] Arguments FrtFramesNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPaintingsNextType {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPtStep {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcF {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtDcB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtTopNext {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtPairLawAt {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments FrtRestr0At {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments descCellFace {X n XpB SB}.
Ltac totalReplaceHyp := fun H C L =>
  let TY := type of L in
  let TY := eval cbv beta in TY in
  lazymatch TY with @eq ?T ?old ?new =>
    let Pred := constr:(fun rr:T => ltac:(let RR := context C [rr] in now exact RR)) in
    let Hnew := fresh "Htotal" in
    pose proof (@eq_rect T old Pred H new L) as Hnew;
    cbv beta in Hnew;
    clear H; rename Hnew into H
  end.

Ltac totalNormalizeHyp H TM TR := PathTactics.totalNormalizeHyp totalReplaceHyp H TM TR.

Section FG.
Variable X: νGpds.

Definition FrtIdentificationAssocAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
    (mkPshPaintings (g X) PX)
    (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val)): Type :=
  forall t: (g X).(G0) M.+1,
  (= frames.1.2 t; paintings.1.2 t) =
  f_equal unassoc (= frames.2 t; paintings.2 t).

Fixpoint FrtIdentificationAssocChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
    (mkPshPaintings (g X) PX)
    (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val)), Type.
Proof.
  destruct p as [|p]; intros k dcB cB F XA XB TX PX top val frames paintings.
  - now exact (FrtIdentificationAssocAt F XA XB TX PX top val frames paintings).
  - now refine ({_: FrtIdentificationAssocChain M _ _ HD p _ _
      (DepsCohsChainCons cB) (proj1FrtDeps F)
      (F.(_frDepsA); XA)%extradepsrestr
      (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
      (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
      (fun t => (top t).1) (fun t => ((top t).2; val t)) frames.1 paintings.1 &T
      FrtIdentificationAssocAt F XA XB TX PX top val frames paintings}).
Defined.

Lemma frtPaintingsOfRestrAssocChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
  (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall u, mkPainting XB (descTop HD cB u))
  (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cB) val
        ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q))
:
  let frames := (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q in
  let paintings := mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E in
  FrtIdentificationAssocChain M HD p cB F XA XB TX PX (descTop HD cB) val frames paintings.
Proof.
  revert k dcB cB Hlen F XA XB TX PX val Q E.
  induction p as [|p IH]; intros k dcB cB Hlen F XA XB TX PX val Q E frames paintings.
  - now exact (frtPaintingsOfRestrTotal M HD 0 cB Hlen F XA XB TX PX val Q E).
  - split.
    + unfold frames, paintings.
      now apply IH.
    + now exact (frtPaintingsOfRestrTotal M HD p.+1 cB Hlen F XA XB TX PX val Q E).
Defined.

Lemma fgIdentificationAssocOf (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt) (Q: FgRestrData m W frt frp):
  FrtIdentificationAssocChain m (descAt m) m DepsCohsChainNil (fgDeps m W frt frp)
    (TopRestrDep (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m))))
    (TopRestrDep (this (next ((νGpdPack m X).2))))
    (TopTrDep (T := frTr (fgDeps m W frt frp))
      (fgThisOfFrames W (pshTw m) (descAt m) frt frp
        (fgFrtOf m W frt frp Q)))
    (TopPshDep (g X) m (P := frtPshDeps (fgDeps m W frt frp)))
    (descTop (descAt m) DepsCohsChainNil)
    (fun u => (descCell (descAt m.+1) u).2)
    (fgFrtOf m W frt frp Q) (fgFrpOf m W frt frp Q).
Proof.
  unfold fgFrpOf.
  lazymatch goal with
  | |- context [mkFrtPaintingsOfRestr ?M ?HD ?p ?cb ?hl ?F ?XA ?XB ?TX ?PX ?val ?QQ ?E] =>
    now exact (frtPaintingsOfRestrAssocChain M HD p cb hl F XA XB TX PX val QQ E)
  end.
Defined.

Lemma restrCellCohRZero {p k} (dc3: DepsCohs3 p k)
  (Q: nat) (HQ: Q <= k) (HR: 0 <= Q) (ε ω: arity) (z: CellBelow dc3):
  restrCellCoh dc3 Q HQ 0 HR ε ω z.1 z.2
  = (=(mkDepsCohs dc3.(_depsCohs2)).(_cohs).2 Q HQ 0 HR ε ω z.1;
     eq_sym (nth_lmap _ z.2.1 ω)).
Proof. now reflexivity. Defined.

(** The dimension-zero painting clause, encoded as a total-path square. *)
Definition frtRestrictionTotalZero (M: nat) (XpB0: (νGpdAt M).(prefix)) (S0: νGpdFrom M XpB0)
  (HD: Desc (X := X) S0) (p k: nat) (dcB: DepsCohs p k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair)
  (PT: FrtPtStep FC cB' Hlen' frames paintings Hpair HR)
  (ε: arity) (u: (g X).(G0) M.+1) := ltac:(
    pose proof (eq_existT_curried_eq
      (P := fun x: FC.(_fcF).(_frDepsA).(_frames).2 => FC.(_fcF).(_frDepsA).(_paintings).2 x)
      (HR ε u) (PT.2.2.2.2 ε u)) as PP;
    totalNormalizeHyp PP (@totalPathMap) (@totalPathComposeRight);
    now exact PP).

(** Reading a face through any chosen prefix of the descent chain. *)
Lemma chain3Factor {P K} {dcTop: DepsCohs3 P K}
  {pa ka} {dcA: DepsCohs3 pa ka} (a: DepsCohs3Chain dcTop dcA)
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcTop dcB)
  (n: nat) (Hlen: cohs3ChainLen b = (cohs3ChainLen a + n)%nat):
  {tail: DepsCohs3Chain dcA dcB &T
    {_: cohs3ChainCompose a tail = b &T cohs3ChainLen tail = n}}.
Proof.
  destruct (chainSplit n b (leR_eq_r (eq_sym Hlen) (leR_add_l (cohs3ChainLen a))))
    as (pM & kM & dcM & aH & aL & Heq & Hn).
  assert (addCancelR: forall n za zb: nat, za + n = zb + n -> za = zb).
  {
    intro j; induction j as [|j IH]; intros za zb H.
    - now rewrite <- 2 plus_n_O in H.
    - rewrite <- 2 plus_n_Sm in H.
      now exact (IH za zb (f_equal Nat.pred H)).
  }
  assert (HeqLen: cohs3ChainLen aH = cohs3ChainLen a).
  {
    apply (addCancelR n).
    now exact (eq_sym (f_equal (fun j => cohs3ChainLen aH + j)%nat Hn)
      • eq_sym (cohs3ChainLenCompose aH aL)
      • f_equal cohs3ChainLen Heq • Hlen).
  }
  pose proof (chain3PackEq (pM; (kM; (dcM; aH)))
    (pa; (ka; (dcA; a))) HeqLen) as Epack.
  now exact (@eq_rect (Chain3Pack dcTop) (pM; (kM; (dcM; aH)))
    (fun s => {tail: DepsCohs3Chain s.2.2.1 dcB &T
      {_: cohs3ChainCompose s.2.2.2 tail = b &T cohs3ChainLen tail = n}})
    (aL; (Heq; Hn)) (pa; (ka; (dcA; a))) Epack).
Defined.

Lemma faceDeep3Compose {P K} {dcTop: DepsCohs3 P K}
  {pa ka} {dcA: DepsCohs3 pa ka} (a: DepsCohs3Chain dcTop dcA)
  {pb kb} {dcB: DepsCohs3 pb kb} (b: DepsCohs3Chain dcA dcB)
  (q: nat) (Hq: q <= ka) (Hdim: cohs3ChainLen b + q <= kb)
  (ε: arity) d c:
  faceDeep (cohs3ChainDepsCohs2 (cohs3ChainCompose a b))
    (cohs3ChainLen b + q) Hdim ε d c
  = faceDeep (cohs3ChainDepsCohs2 a) q Hq ε d c.
Proof.
  revert Hdim; induction b; intro Hdim.
  - now reflexivity.
  - now exact (IHb (⇓ Hdim)).
Defined.

End FG.
End Association.
