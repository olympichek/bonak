(** Successor restriction identities for the backward round trip. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Translation.
From Bonak.Lib Require Import Equiv.
From Bonak Require Import Limit.
Import Logic.EqNotations.

Set Primitive Projections.
Set Keyed Unification.

Module Successor (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Import A.

Module Export RT := Bonak.Equiv.Gpd.νGpdRoundtrip.Translation.Translation A Base Translations.

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

#[local] Arguments FrtPaintingTopType {X M XpB0 S0 HD p k dcB cB} F {XA XB}.
#[local] Arguments mkFrtPaintingsOfRestr {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments mkFrtRestrTypesAndFrames {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments descTop {X M XpB0 S0} HD {p k dcB}.

#[local] Arguments FrtRestrDataDef {X M XpB0 S0 HD p k dcB cB F}.
#[local] Arguments FrtRestrFramesDef {X M XpB0 S0 HD p k dcB cB F}.

Section FG.
Variable X: νGpds.

Lemma trRestrPaintingSuccTotal {p k} (TC: TrDepsCohs p.+1 k)
  {XCA: DepsCohsExtension p.+1 k (trDepsCohsA TC.(_trBase))}
  {XCB: DepsCohsExtension p.+1 k (trDepsCohsB TC.(_trBase))}
  (TCX: TrDepsCohsExtension TC XCA XCB)
  (q: nat) (Hq: q.+1 <= k.+1) (ε: arity) (d: _) (c: _):
  (= (mkTrRestrFrames (proj1TrDepsCohs TC)).2 q.+1 Hq ε d;
     mkTrRestrPainting (AddTrCohDep TC TCX) q.+1 Hq ε d c) =
  f_equal unassoc
    (= (mkTrRestrFrames TC).2 q (⇓ Hq) ε (d; c.1);
       mkTrRestrPainting TCX q (⇓ Hq) ε (d; c.1) c.2).
Proof.
  cbn [mkTrRestrPainting].
  lazymatch goal with
  | |- @eq _ (@eq_existT_curried _ _ _ _ _ _ _
         (@eq_existT_curried_dep ?A ?x ?L ?Cc ?y ?a ?u ?c0 ?v ?cv ?b ?h)) _ =>
    now exact (eq_sym (@f_equal_unassoc_curried A L Cc x y a u v b c0 cv h))
  end.
Defined.

Lemma frtPaintingStepDownTotal {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (prev: FrtFramesPrevType F top)
  (lay: forall t, mkFrtLayerType F top prev t)
  (E: forall t: (g X).(G0) M.+1,
     rew [fun x => mkPainting XA x] ((mkFrtFrameStep F top prev lay).2 t) in
       mkPshPainting (g X) PX t
     = mkPaintingEqv TX (top t) (val t))
  (t: (g X).(G0) M.+1):
  (=prev.2 t; mkFrtPaintingStepDown F XA XB TX PX top val prev lay E t) =
  f_equal unassoc (= (mkFrtFrameStep F top prev lay).2 t; E t).
Proof.
  now exact (eq_sym (f_equal_unassoc_curried (prev.2 t) (lay t) (E t))).
Defined.

Lemma frtPaintingsOfRestrTotal (M: nat) {XpB0: (νGpdAt M).(prefix)}
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
  (t: (g X).(G0) M.+1):
  let frames := (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q in
  let paintings := mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E in
  (= frames.1.2 t; paintings.1.2 t) =
  f_equal unassoc (= frames.2 t; paintings.2 t).
Proof.
  intros frames paintings.
  unfold frames, paintings.
  destruct p as [|p]; now exact (frtPaintingStepDownTotal _ _ _ _ _ _ _ _ _ _ _).
Defined.

End FG.
End Successor.
