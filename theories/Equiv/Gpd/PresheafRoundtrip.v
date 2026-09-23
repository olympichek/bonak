(** The presheaf round trip [g ∘ f]. Projecting a candidate-filled
    cell to its presheaf cell gives the carrier equivalence. The proof
    establishes compatibility with both face maps and their chosen
    exchange paths, yielding [PresheafEquiv (g (f psh)) psh].

    The face maps of [g] use the dependency chain of a tower position.
    The recursion carries that chain to a presheaf-equipped stage, where
    the stored restriction families compute the face and exchange paths. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd νGpd.Layer
  νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd.
From Bonak.Lib Require Import Equiv.

From Bonak Require Import Limit.

From Bonak.Equiv.Gpd Require Import PathAlgebra.

Set Primitive Projections.
From Bonak Require Import νGpd.Pasting.

Set Keyed Unification.

(** Identity index transport retains the supplied value. *)
Local Definition index_cell {I: Type} (Cell: I -> Type)
  {i j: I} (e: i = j) (K: Cell i): Cell j :=
  match e with eq_refl => K end.

Module PresheafRoundtrip (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A).
Import A.

Module Export PresheafOfνGpd := Base.

(** A [DepsCohs3Chain] out of a fixed source moves its stage down by its
    length, so the stage it lands on is determined by that length. *)

Lemma cohs3ChainLenEq {P K} {dc3Top: DepsCohs3 P K} {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3): cohs3ChainLen a + p = P.
Proof.
  induction a as [|p k dc3 a IHa].
  - now reflexivity.
  - cbn. rewrite <- IHa. now exact (eq_sym (addSuccR (cohs3ChainLen a) p)).
Defined.

(** At the top of a tower the empty chain names the face at the top
    dimension. *)

Lemma gFaceC0Nil {m Xpre} (X: νGpdFrom m Xpre) (Hdim: 0 <= 0 + 0)
  (ε: arity) (d: gF0 X 1):
  gFaceC X DepsCohs3ChainNil 0 0 Hdim ε d = νFace DepsCohsChainNil ε d.1.
Proof. now reflexivity. Defined.

(** Choose descent from a rebuilding comparison and its retraction.
    The identity rebuilding path returns the given retraction exactly. *)
Local Definition descend_from_rebuild {X Y: Type} (D: X -> Y) (R: Y -> X)
  (K: forall y, D (R y) = y) {x: X} {y: Y} (h: R y = x): D x = y :=
  rew [fun z => D z = y] h in K y.

Local Lemma descend_from_rebuild_boundary {X Y: Type} (D: X -> Y) (R: Y -> X)
  (K: forall y, D (R y) = y) {x: X} {y: Y} (h: R y = x):
  K y = f_equal D h • descend_from_rebuild D R K h.
Proof.
  destruct h. now exact (eq_sym (eq_trans_refl_l (K y))).
Defined.

(** Naturality of a path-valued function in two displayed arguments.
    The target uses exactly the transported source arguments. *)
Local Lemma displayed_pair_naturality {I X: Type} {P Q: I -> Type}
  (left: I -> X) (target: X)
  (K: forall i, P i -> Q i -> left i = target)
  {i j: I} (e: i = j) (p: P i) (q: Q i):
  K i p q = f_equal left e • K j (rew [P] e in p) (rew [Q] e in q).
Proof.
  destruct e. now exact (eq_sym (eq_trans_refl_l (K i p q))).
Defined.

Section RoundTripGF.

Variable psh: νGpdPresentation arity.

(** The tower state at a position

    [pshChain] pairs each prefix with the state that produces its next
    extension; the state at [m.+1] is the presheaf-equipped stage the face
    computations of [νGpdOfPresheaf.v] are stated against. *)

Definition pshTw (m: nat): PshTower psh m (pshApprox psh m.+1) :=
  (pshChain psh m.+1).2.1.

Definition pshTwRp (m: nat): PshTowerRestrPaintings psh (pshTw m) :=
  (pshChain psh m.+1).2.2.1.

Definition pshTwRc (m: nat): PshTowerRestrCohs psh (pshTw m) (pshTwRp m) :=
  (pshChain psh m.+1).2.2.2.1.

Definition pshTwRpc (m: nat):
  PshTowerRestrPaintingCohs psh (pshTw m) (pshTwRp m) (pshTwRc m) :=
  (pshChain psh m.+1).2.2.2.2.

Definition PCTop (m: nat): PshDepsCohs2 psh m m.+1 0 :=
  towerPshDepsCohs2 psh (pshTw m) (pshTwRp m) (pshTwRc m).

(** The cells a presheaf-equipped stage names

    [pshCell] is the cell of the stage itself, [pshCandCell] the cell one
    stage up whose restriction the face maps consume, and [pshRestrFn] the
    face map between the two. Naming them makes the two stored families
    below the two components of a single identification of cells. *)

Definition PCell {m p k} (PC2: PshDepsCohs2 psh m p k): Type :=
  {d': mkFrame (pshDepsCohs psh PC2.(_pshDepsCohs psh)).(_deps) &T
       mkPainting (pshDepsCohs psh PC2.(_pshDepsCohs psh)).(_extraDeps) d'}.

Definition PCellUp {m p k} (PC2: PshDepsCohs2 psh m p k): Type :=
  {D: mkFrame (mkDepsRestr
        (depsCohs := pshDepsCohs psh PC2.(_pshDepsCohs psh))).(1) &T
      (mkPaintings (mkDepsRestr
        (depsCohs := pshDepsCohs psh PC2.(_pshDepsCohs psh));
        mkExtraDeps PC2.(_pExtraDepsCohs psh))).2 D}.

Definition pshRestrFn {m p k} (PC2: PshDepsCohs2 psh m p k)
  (j: nat) (Hj: j <= k) (α: arity) (z: PCellUp PC2): PCell PC2 :=
  restrCell PC2.(_pExtraDepsCohs psh) j Hj α z.1 z.2.

Definition pshCell {m p k} (PC: PshDepsCohs psh m p k) (d: psh.(G0) m.+1):
  {d': mkFrame (pshDepsCohs psh PC).(_deps) &T
       mkPainting (pshDepsCohs psh PC).(_extraDeps) d'} :=
  (mkPshFrame psh PC.(_pshDeps psh) d;
   mkPshPainting psh PC.(_pshExtraDeps psh) d).

Definition pshCandCell {m p k} (PC2: PshDepsCohs2 psh m p k)
  (PCX: PshDepsCohsExtension psh m PC2 PC2.(_pExtraDepsCohs psh))
  (d: psh.(G0) m.+2): PCellUp PC2 :=
  ((mkPshFrame psh (mkPshDepsRestr psh PC2) d).1;
   mkPshPainting psh (AddPshDep psh _ (mkPshDepsRestr psh PC2)
     (mkPshExtraDeps psh PCX)) d).

(** The face of a candidate-built cell is the candidate-built cell of the
    [psh]-face: the two stored presheaf-side families, paired. *)

Definition pshFaceCell {m p k} (PC2: PshDepsCohs2 psh m p k)
  (PCX: PshDepsCohsExtension psh m PC2 PC2.(_pExtraDepsCohs psh))
  (j: nat) (Hj: j <= k) (Hjp: j + p <= m.+1) (α: arity)
  (d: psh.(G0) m.+2):
  pshCell PC2.(_pshDepsCohs psh) (psh.(GFace) m.+1 (j + p) Hjp α d)
  = pshRestrFn PC2 j Hj α (pshCandCell PC2 PCX d) :=
  eq_existT_curried
    ((mkPshRestrFrames psh PC2.(_pshDepsCohs psh) PC2.(_pshRestrCohs psh)).2
       j Hj Hjp α d)
    (mkPshRestrPainting psh PCX j Hj Hjp α d).

(** Presheaf-side stages of the third rung

    A [PshDepsCohs3] carries the presheaf realization of its stage only; the
    indexed level-2 extension and its coherence paintings travel beside it,
    as they do in [mkPshDepsCohs2Next] and [PshDepsCohs3Extension]. A
    [PStage] is the three of them, and it realizes a [DepsCohs3]: descending
    a stage is descending the data it realizes. *)

Definition PStage (m p k: nat): Type :=
  {PC3: PshDepsCohs3 psh m p k &T
   {XC: DepsCohs2Extension p k (pshDepsCohs2 psh PC3.(_pshDepsCohs2 psh)) &T
    mkCoh2PaintingTypes XC}}.

Definition pDc3 {m p k} (S: PStage m p k): DepsCohs3 p k :=
  toDepsCohs3 S.2.2.

Definition pStep {m p k} (S: PStage m p.+1 k): PStage m p k.+1 :=
  (proj1PshDepsCohs3 psh S.1; (_; S.2.2.1)).

Definition STop (m: nat): PStage m m.+1 0 :=
  (towerPshDepsCohs3 psh (pshTw m) (pshTwRp m) (pshTwRc m) (pshTwRpc m);
   (towerPshExtra3 psh (pshTw m) (pshTwRp m) (pshTwRc m) (pshTwRpc m);
    towerPshCoh2Paintings psh (pshTw m) (pshTwRp m) (pshTwRc m)
      (pshTwRpc m))).

Definition STopX (m: nat):
  PshDepsCohs3Extension psh m (STop m).1 (STop m).2.1 (STop m).2.2 :=
  TopPshCoh3Dep psh m
    (towerPshCoh2Paintings psh (pshTw m) (pshTwRp m) (pshTwRc m)
       (pshTwRpc m)).

(** The exchange law on candidate-built cells

    The level-2 counterpart of [pshFaceCell]: erasing two dimensions from a
    candidate-built cell in the two orders agrees with the presheaf exchange
    law, and the identification is the pair of the two stored level-2
    families. The outer face reads the stage at tower position [m], the
    inner one the stage one position up, which is exactly how
    [mkPshRestrLayerCohType] and [mkPshRestrPaintingCohType] at the next
    stage are indexed. *)

Section RestrCellCoh.
Context {m p k} (PC3: PshDepsCohs3 psh m p k)
  (XC: DepsCohs2Extension p k (pshDepsCohs2 psh PC3.(_pshDepsCohs2 psh)))
  (C2P: mkCoh2PaintingTypes XC)
  (PCXN: PshDepsCohsExtension psh m.+1 (mkPshDepsCohs2Next psh PC3 XC C2P)
     (mkPshDepsCohs2Next psh PC3 XC C2P).(_pExtraDepsCohs psh)).

Let PC2 := PC3.(_pshDepsCohs2 psh).
Let PCX := PC3.(_pshExtraDepsCohs psh).
Let PC2N := mkPshDepsCohs2Next psh PC3 XC C2P.
Let PC2U := proj1PshDepsCohs2 psh PC2N.
Let PCXU := AddPshCohDep psh _ PC2N PCXN.

Lemma pshRestrCellCoh (HP2: mkPshRestrPaintingCohType psh PC2N PCXN)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+2) (ε ω: arity)
  (d: psh.(G0) m.+3):
  f_equal (pshCell PC2.(_pshDepsCohs psh))
    (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p) (leR_add_mono_r Hr p) ε ω d)
  • (pshFaceCell PC2 PCX r (Hr ↕ Hq) (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
       (psh.(GFace) m.+2 (q.+1 + p) Hqp ε d)
     • f_equal (pshRestrFn PC2 r (Hr ↕ Hq) ω)
         (pshFaceCell PC2U PCXU q.+1 (⇑ Hq) Hqp ε d))
  = pshFaceCell PC2 PCX q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+2 (r + p) (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
    • (f_equal (pshRestrFn PC2 q Hq ε)
         (pshFaceCell PC2U PCXU r (↑ (Hr ↕ Hq))
            (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
       • restrCellCoh (toDepsCohs3 C2P) q Hq r Hr ε ω
           (pshCandCell PC2U PCXU d).1 (pshCandCell PC2U PCXU d).2).
Proof.
  unfold pshFaceCell, pshRestrFn, pshCell, restrCell, restrCellCoh.
  rewrite 2 f_equal_eq_existT_curried.
  unshelve eapply (sigT_hex1
    (mkPshFrame psh PC2.(_pshDepsCohs psh).(_pshDeps psh))
    (mkPshPainting psh PC2.(_pshDepsCohs psh).(_pshExtraDeps psh))
    (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p) (leR_add_mono_r Hr p) ε ω d)).
  { now exact (PC2N.(_pshRestrCohs psh).2 q Hq r Hr Hqp ε ω d). }
  { rewrite <- sigT_map_eq_id_dep_sigT.
    now exact (HP2 q Hq r Hr Hqp ε ω d). }
Defined.

End RestrCellCoh.

(** Chains of presheaf-side stages

    A stage chain realizes a [DepsCohs3Chain] — descending a stage is
    descending the data it realizes — so the face computations below can be
    stated against the chain the tower's own face maps run along, without a
    change of presentation. *)

Inductive PChain {m P K} (STop: PStage m P K):
  forall {p k}, PStage m p k -> Type :=
| PChainNil: PChain STop STop
| PChainCons {p k} {S: PStage m p.+1 k}:
    PChain STop S -> PChain STop (pStep S).

Arguments PChainNil {m P K STop}.
Arguments PChainCons {m P K STop p k S} _.

Fixpoint pChain3 {m P K} {STop: PStage m P K} {p k} {S: PStage m p k}
  (C: PChain STop S): DepsCohs3Chain (pDc3 STop) (pDc3 S) :=
  match C with
  | PChainNil => DepsCohs3ChainNil
  | PChainCons C' => DepsCohs3ChainCons (pChain3 C')
  end.

Fixpoint pChainLen {m P K} {STop: PStage m P K} {p k} {S: PStage m p k}
  (C: PChain STop S): nat :=
  match C with
  | PChainNil => 0
  | PChainCons C' => (pChainLen C').+1
  end.

Lemma pChain3Len {m P K} {STop: PStage m P K} {p k} {S: PStage m p k}
  (C: PChain STop S): cohs3ChainLen (pChain3 C) = pChainLen C.
Proof. induction C; cbn; [now reflexivity | now rewrite IHC]. Defined.

(** The level-2 extension a stage on a chain out of a tower position sits
    under. It is not a field of the stage — a lifted stage has none — and
    along such a chain it is the tower's own extension descended by
    [AddPshCoh3Dep]. *)

Fixpoint pChainX {m p k} {S: PStage m p k} (C: PChain (STop m) S) {struct C}:
  PshDepsCohs3Extension psh m S.1 S.2.1 S.2.2 :=
  match C with
  | PChainNil => STopX m
  | PChainCons C' => AddPshCoh3Dep psh m _ (pChainX C')
  end.

(** The [DepsCohs2Chain] a stage chain names, and the cell it descends *)

Definition pTopCell {m P K} (STop: PStage m P K) (d: psh.(G0) m.+2) :=
  pshCell (mkPshDepsCohsNext psh STop.1.(_pshExtraDepsCohs psh)) d.

Lemma pshGetPaintingC {m P K} {STop: PStage m P K} {p k} {S: PStage m p k}
  (C: PChain STop S) (d: psh.(G0) m.+1):
  getPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (pChain3 C))))
    (pshCell S.1.(_pshDepsCohs2 psh).(_pshDepsCohs psh) d).1
    (pshCell S.1.(_pshDepsCohs2 psh).(_pshDepsCohs psh) d).2 =
  pshCell STop.1.(_pshDepsCohs2 psh).(_pshDepsCohs psh) d.
Proof.
  induction C as [|p k S C IHC].
  - now reflexivity.
  - now exact IHC.
Defined.

(** The level-1 identification for the face maps one level up

    Those run along the lift of the chain, and at level 2 the lift's source
    is [mkDepsCohs2 (pDc3 (STop m))], definitionally the tower position above.
    The endpoint data is a function of the endpoint stage alone. Lifted
    comparisons are the transports of the ordinary comparisons along the
    chosen chain equality. *)

Definition PC2Up {m p k} (S: PStage m p k): PshDepsCohs2 psh m.+1 p k.+1 :=
  proj1PshDepsCohs2 psh (mkPshDepsCohs2Next psh S.1 S.2.1 S.2.2).

Definition PCXUp {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  PshDepsCohsExtension psh m.+1 (PC2Up S) (PC2Up S).(_pExtraDepsCohs psh) :=
  AddPshCohDep psh _ (mkPshDepsCohs2Next psh S.1 S.2.1 S.2.2)
    (mkPshExtraCohs psh (pChainX C)).

Definition upC2 {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  DepsCohs2Chain (pshDepsCohs2 psh (PCTop m.+1))
    (pshDepsCohs2 psh (PC2Up S)) :=
  cohs3ChainDepsCohs2 (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)).

(** The lifted endpoint and its chain are produced by one recursion.
    The initial endpoint is literally the next tower's first projection. *)
Fixpoint liftedStageChain {m p k} {S: PStage m p k}
  (C: PChain (STop m) S):
  {U: PStage m.+1 p k.+1 &T PChain (STop m.+1) U} :=
  match C with
  | PChainNil => (pStep (STop m.+1); PChainCons PChainNil)
  | PChainCons C' =>
      let U := liftedStageChain C' in (pStep U.1; PChainCons U.2)
  end.

Definition liftedStage {m p k} {S: PStage m p k} (C: PChain (STop m) S) :=
  (liftedStageChain C).1.

Definition liftedChain {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  PChain (STop m.+1) (liftedStage C) := (liftedStageChain C).2.

Definition liftedPC2 {m p k} {S: PStage m p k} (C: PChain (STop m) S) :=
  (liftedStage C).1.(_pshDepsCohs2 psh).

Definition liftedPCX {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  PshDepsCohsExtension psh m.+1 (liftedPC2 C) (liftedPC2 C).(_pExtraDepsCohs psh) :=
  (liftedStage C).1.(_pshExtraDepsCohs psh).

Definition liftedChain2 {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  DepsCohs2Chain (pshDepsCohs2 psh (PCTop m.+1)) (pshDepsCohs2 psh (liftedPC2 C)) :=
  cohs3ChainDepsCohs2 (pChain3 (liftedChain C)).

Definition rawLiftPack {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  Chain2Pack (pshDepsCohs2 psh (PCTop m.+1)) :=
  (p; (k.+1; (pshDepsCohs2 psh (PC2Up S); upC2 C))).

Definition selectedLiftPack {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  Chain2Pack (pshDepsCohs2 psh (PCTop m.+1)) :=
  (p; (k.+1; (pshDepsCohs2 psh (liftedPC2 C); liftedChain2 C))).

(** The endpoint realization contains exactly the data read by faces:
    a presheaf-equipped level-2 stage, its extension, and its core chain. *)
Record LiftRealizer (m p k: nat) := {
  lrPC: PshDepsCohs2 psh m.+1 p k;
  lrPX: PshDepsCohsExtension psh m.+1 lrPC lrPC.(_pExtraDepsCohs psh);
  lrChain: DepsCohs2Chain (pshDepsCohs2 psh (PCTop m.+1)) (pshDepsCohs2 psh lrPC);
}.
Local Arguments lrPC {m p k} _.
Local Arguments lrPX {m p k} _.
Local Arguments lrChain {m p k} _.

Definition liftRealizerStep {m p k} (R: LiftRealizer m p.+1 k):
  LiftRealizer m p k.+1 := {|
  lrPC := proj1PshDepsCohs2 psh (lrPC R);
  lrPX := AddPshCohDep psh _ (lrPC R) (lrPX R);
  lrChain := DepsCohs2ChainCons (lrChain R);
|}.

Definition rawLiftRealizer {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  LiftRealizer m p k.+1 := {|
  lrPC := PC2Up S;
  lrPX := PCXUp C;
  lrChain := upC2 C;
|}.

Definition selectedLiftRealizer {m p k} {S: PStage m p k}
  (C: PChain (STop m) S): LiftRealizer m p k.+1 := {|
  lrPC := liftedPC2 C;
  lrPX := liftedPCX C;
  lrChain := liftedChain2 C;
|}.

Lemma liftRealizerBoundary {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  rawLiftRealizer C = selectedLiftRealizer C.
Proof.
  induction C as [|p k S C IHC].
  - now reflexivity.
  - now exact (f_equal (@liftRealizerStep m p k.+1) IHC).
Defined.

Definition forgetLiftRealizer {m p k} (R: LiftRealizer m p k):
  Chain2Pack (pshDepsCohs2 psh (PCTop m.+1)) :=
  (p; (k; (pshDepsCohs2 psh (lrPC R); lrChain R))).

Definition liftPackBoundary {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  rawLiftPack C = selectedLiftPack C :=
  f_equal (@forgetLiftRealizer m p k.+1) (liftRealizerBoundary C).

Definition liftGetFamily {m p k} (d: psh.(G0) m.+2)
  (R: LiftRealizer m p k): Type :=
  getPainting (cohsChainExt (cohs2ChainDepsCohs (lrChain R)))
    (pshCell (lrPC R).(_pshDepsCohs psh) d).1
    (pshCell (lrPC R).(_pshDepsCohs psh) d).2 =
  pshCell (PCTop m.+1).(_pshDepsCohs psh) d.

Definition liftDeepFamily {m p k} (d: psh.(G0) m.+3)
  (R: LiftRealizer m p k): Type :=
  deepCell (lrChain R) (pTopCell (STop m.+1) d) =
  pshCandCell (lrPC R) (lrPX R) d.

Definition pshGetPaintingUp {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (d: psh.(G0) m.+2): liftGetFamily d (rawLiftRealizer C) :=
  index_cell (liftGetFamily d) (eq_sym (liftRealizerBoundary C))
    (pshGetPaintingC (liftedChain C) d).

Definition pshDeepCellC {m p k} {S: PStage m p k}
  (C: PChain (STop m) S) (d: psh.(G0) m.+2):
  deepCell (cohs3ChainDepsCohs2 (pChain3 C)) (pTopCell (STop m) d) =
  pshCandCell S.1.(_pshDepsCohs2 psh) S.1.(_pshExtraDepsCohs psh) d :=
  descend_from_rebuild
    (deepCell (cohs3ChainDepsCohs2 (pChain3 C)))
    (faceRebuild (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)))
    (deepCellRebuildUp (νExt3At (pshFrom psh m.+1)) (pChain3 C))
    (pshGetPaintingUp C d).

Definition pshDeepCellUp {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (d: psh.(G0) m.+3): liftDeepFamily d (rawLiftRealizer C) :=
  index_cell (liftDeepFamily d) (eq_sym (liftRealizerBoundary C))
    (pshDeepCellC (liftedChain C) d).

Lemma deepRebuildUpC {m p k} {S: PStage m p k}
  (C: PChain (STop m) S) (x: psh.(G0) m.+2):
  deepCellRebuildUp (νExt3At (pshFrom psh m.+1)) (pChain3 C)
    (pshCell (PC2Up S).(_pshDepsCohs psh) x) =
  f_equal (deepCell (cohs3ChainDepsCohs2 (pChain3 C))) (pshGetPaintingUp C x)
    • pshDeepCellC C x.
Proof.
  now exact (descend_from_rebuild_boundary
    (deepCell (cohs3ChainDepsCohs2 (pChain3 C)))
    (faceRebuild (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)))
    (deepCellRebuildUp (νExt3At (pshFrom psh m.+1)) (pChain3 C))
    (pshGetPaintingUp C x)).
Defined.

Definition upStage {m p k} {S: PStage m p k} (C: PChain (STop m) S) :=
  liftedStage C.
Definition upC {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  PChain (STop m.+1) (upStage C) := liftedChain C.

Definition pshFaceDeepC {m p k} {S: PStage m p k}
  (C: PChain (STop m) S) (dim: nat) (Hdim: dim <= k) (Hdimp: dim + p <= m.+1)
  (ε: arity) (d: psh.(G0) m.+2):
  faceDeep (cohs3ChainDepsCohs2 (pChain3 C)) dim Hdim ε (pTopCell (STop m) d).1 (pTopCell (STop m) d).2 =
  pshCell (STop m).1.(_pshDepsCohs2 psh).(_pshDepsCohs psh)
    (psh.(GFace) m.+1 (dim + p) Hdimp ε d) :=
  f_equal (fun z => faceAt (cohs3ChainDepsCohs2 (pChain3 C)) dim Hdim ε z.1 z.2) (pshDeepCellC C d)
  • (f_equal (fun z => getPainting
       (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (pChain3 C)))) z.1 z.2)
       (eq_sym (pshFaceCell S.1.(_pshDepsCohs2 psh)
          S.1.(_pshExtraDepsCohs psh) dim Hdim Hdimp ε d))
     • pshGetPaintingC C (psh.(GFace) m.+1 (dim + p) Hdimp ε d)).

Definition pshFaceDeepUp {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k.+1) (Hdimp: dim + p <= m.+2) (ε: arity)
  (d: psh.(G0) m.+3):
  faceDeep (upC2 C) dim Hdim ε (pTopCell (STop m.+1) d).1
    (pTopCell (STop m.+1) d).2 =
  pshCell (PCTop m.+1).(_pshDepsCohs psh)
    (psh.(GFace) m.+2 (dim + p) Hdimp ε d) :=
  f_equal (fun z => faceAt (upC2 C) dim Hdim ε z.1 z.2) (pshDeepCellUp C d)
  • (f_equal (fun z => getPainting
       (cohsChainExt (cohs2ChainDepsCohs (upC2 C))) z.1 z.2)
       (eq_sym (pshFaceCell (PC2Up S) (PCXUp C) dim Hdim Hdimp ε d))
     • pshGetPaintingUp C (psh.(GFace) m.+2 (dim + p) Hdimp ε d)).

(** The bottom hexagon

    The level-2 clause at the bottom of a stage chain: the exchange law
    [faceAtCohUp] the tower carries, the four level-1 identifications — two
    along the chain, two along its lift — and the presheaf exchange law paste
    into a hexagon. It is the stored hexagon [pshRestrCellCoh] read at the top
    of the chain and from the opposite vertex, so its proof is one
    [hexReindexR] over six legs, each written as its core conjugated by the
    identifications at its two vertices. *)

(** The identification at the two vertices where a level-1 identification
    meets the exchange law is [pshDeepCellC], which is what puts
    [pshFaceDeepC] in leg-normal form. *)

Lemma hexLegDeep {m p k} {S: PStage m p k}
  (C: PChain (STop m) S) (dim: nat) (Hdim: dim <= k) (Hdimp: dim + p <= m.+1)
  (α: arity) (z: psh.(G0) m.+2):
  pshFaceDeepC C dim Hdim Hdimp α z =
  f_equal (fun w =>
    faceAt (cohs3ChainDepsCohs2 (pChain3 C)) dim Hdim α w.1 w.2)
    (pshDeepCellC C z)
  • (eq_sym (f_equal (faceRebuild (pChain3 C))
       (pshFaceCell S.1.(_pshDepsCohs2 psh) S.1.(_pshExtraDepsCohs psh)
          dim Hdim Hdimp α z))
     • eq_sym (eq_sym (pshGetPaintingC C
         (psh.(GFace) m.+1 (dim + p) Hdimp α z)))).
Proof.
  unfold pshFaceDeepC.
  rewrite eq_sym_involutive, eq_sym_map_distr.
  now reflexivity.
Defined.

(** The same for the lift, with the middle factor read through
    [faceRebuild] so that [faceAtDeepConj] applies to it. *)

Lemma pshFaceDeepUpFR {m p k} {S: PStage m p k}
  (C: PChain (STop m) S) (dim: nat) (Hdim: dim <= k.+1)
  (Hdimp: dim + p <= m.+2) (α: arity) (d: psh.(G0) m.+3):
  pshFaceDeepUp C dim Hdim Hdimp α d =
  f_equal (fun z => faceAt (upC2 C) dim Hdim α z.1 z.2)
    (pshDeepCellUp C d)
  • (f_equal (faceRebuild
       (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)))
       (eq_sym (pshFaceCell (PC2Up S) (PCXUp C) dim Hdim Hdimp α d))
     • pshGetPaintingUp C (psh.(GFace) m.+2 (dim + p) Hdimp α d)).
Proof. now reflexivity. Defined.

(** The cell the bottom of the chain sees under a rebuilt presheaf cell,
    recognized in the two ways the two legs meeting at that vertex produce
    it. Without this the vertex would be normalized differently by the two
    legs and the hexagon could not be reindexed. *)



(** A face read at the bottom of the chain, applied to an inverse: the form
    in which the core hexagon's two [f_equal (pshRestrFn …)] edges meet the
    legs that consume them. *)

Lemma faceAtHereSym {m p k} {S: PStage m p k}
  (C: PChain (STop m) S) (j: nat) (Hj: j <= k) (α: arity)
  {X Y: PCellUp S.1.(_pshDepsCohs2 psh)} (e: X = Y):
  f_equal (fun w =>
    faceAt (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α w.1 w.2) (eq_sym e)
  = eq_sym (f_equal (faceRebuild (pChain3 C))
      (f_equal (pshRestrFn S.1.(_pshDepsCohs2 psh) j Hj α) e)).
Proof.
  destruct e. now reflexivity.
Defined.

(** The leg whose inner face is read one level up. *)

Lemma hexLegUp {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (j: nat) (Hj: j <= k) (α: arity)
  (i: nat) (Hi: i <= k.+1) (Hip: i + p <= m.+2) (γ: arity)
  (d: psh.(G0) m.+3):
  f_equal (fun z =>
    faceDeep (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α z.1 z.2)
    (pshFaceDeepUp C i Hi Hip γ d)
  = vertexNorm (νExt3At (pshFrom psh m.+1)) (pChain3 C) j Hj α i Hi γ
      (pshDeepCellUp C d)
    • (f_equal (fun w =>
         faceAt (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α w.1 w.2)
         (eq_sym (pshFaceCell (PC2Up S) (PCXUp C) i Hi Hip γ d))
       • eq_sym (f_equal (fun w =>
           faceAt (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α w.1 w.2)
           (pshDeepCellC C (psh.(GFace) m.+2 (i + p) Hip γ d)))).
Proof.
  transitivity (f_equal (fun w =>
    faceAt (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α
      (deepCell (cohs3ChainDepsCohs2 (pChain3 C)) w).1
      (deepCell (cohs3ChainDepsCohs2 (pChain3 C)) w).2)
    (pshFaceDeepUp C i Hi Hip γ d)).
  { now reflexivity. }
  rewrite (pshFaceDeepUpFR C i Hi Hip γ d).
  rewrite 2 eq_trans_map_distr.
  rewrite (faceAtDeepConj (νExt3At (pshFrom psh m.+1)) (pChain3 C) j Hj α
    (eq_sym (pshFaceCell (PC2Up S) (PCXUp C) i Hi Hip γ d))).
  rewrite (deepRebuildUpC C (psh.(GFace) m.+2 (i + p) Hip γ d)).
  rewrite (eq_trans_map_distr (fun w =>
    faceAt (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α w.1 w.2)
    (f_equal (deepCell (cohs3ChainDepsCohs2 (pChain3 C)))
       (pshGetPaintingUp C (psh.(GFace) m.+2 (i + p) Hip γ d)))
    (pshDeepCellC C (psh.(GFace) m.+2 (i + p) Hip γ d))).
  rewrite (f_equal_compose (deepCell (cohs3ChainDepsCohs2 (pChain3 C)))
    (fun w => faceAt (cohs3ChainDepsCohs2 (pChain3 C)) j Hj α w.1 w.2)
    (pshGetPaintingUp C (psh.(GFace) m.+2 (i + p) Hip γ d))).
  unfold vertexNorm.
  lazymatch goal with
  | |- @eq _
      (@eq_trans ?T ?t0 ?t1 ?t4 ?xx
        (@eq_trans _ _ ?t5 _
          (@eq_trans _ _ ?t2 _ ?yy
            (@eq_trans _ _ ?t3 _ ?cc
              (@eq_sym _ _ _
                (@eq_trans _ _ _ _ ?ww ?mm))))
          _)) _ =>
      now exact_no_check (@legRegroupUp T t0 t1 t2 t3 t4 t5 xx yy cc ww mm)
  end.
Defined.

(** The stored hexagon, moved to the top of the chain and read from the
    vertex the two legs of the descent meet in. *)

Lemma pshHexCore {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+2) (ε ω: arity)
  (d: psh.(G0) m.+3):
  f_equal (faceRebuild (pChain3 C))
    (restrCellCoh (pDc3 S) q Hq r Hr ε ω
       (pshCandCell (PC2Up S) (PCXUp C) d).1
       (pshCandCell (PC2Up S) (PCXUp C) d).2)
  • (f_equal (fun w =>
       faceAt (cohs3ChainDepsCohs2 (pChain3 C)) r (Hr ↕ Hq) ω w.1 w.2)
       (eq_sym (pshFaceCell (PC2Up S) (PCXUp C) q.+1 (⇑ Hq) Hqp ε d))
     • eq_sym (f_equal (faceRebuild (pChain3 C))
         (pshFaceCell S.1.(_pshDepsCohs2 psh) S.1.(_pshExtraDepsCohs psh)
            r (Hr ↕ Hq) (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
            (psh.(GFace) m.+2 (q.+1 + p) Hqp ε d))))
  = f_equal (fun w =>
      faceAt (cohs3ChainDepsCohs2 (pChain3 C)) q Hq ε w.1 w.2)
      (eq_sym (pshFaceCell (PC2Up S) (PCXUp C) r (↑ (Hr ↕ Hq))
         (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d))
    • (eq_sym (f_equal (faceRebuild (pChain3 C))
         (pshFaceCell S.1.(_pshDepsCohs2 psh) S.1.(_pshExtraDepsCohs psh)
            q Hq (⇓ Hqp) ε
            (psh.(GFace) m.+2 (r + p)
               (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)))
       • f_equal (faceRebuild (pChain3 C))
           (f_equal (pshCell S.1.(_pshDepsCohs2 psh).(_pshDepsCohs psh))
              (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
                 (leR_add_mono_r Hr p) ε ω d))).
Proof.
  rewrite (faceAtHereSym C r (Hr ↕ Hq) ω
    (pshFaceCell (PC2Up S) (PCXUp C) q.+1 (⇑ Hq) Hqp ε d)).
  rewrite (faceAtHereSym C q Hq ε
    (pshFaceCell (PC2Up S) (PCXUp C) r (↑ (Hr ↕ Hq))
       (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)).
  now exact (hexRotate _ _ _ _ _ _
    (hexMap (faceRebuild (pChain3 C)) _ _ _ _ _ _
       (pshRestrCellCoh S.1 S.2.1 S.2.2 (mkPshExtraCohs psh (pChainX C))
          (mkPshCoh2Painting psh S.1 S.2.1 S.2.2 (pChainX C))
          q Hq r Hr Hqp ε ω d))).
Defined.

Lemma pshFaceDeepCoh {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+2) (ε ω: arity)
  (d: psh.(G0) m.+3):
  faceAtCohUp (νExt3At (pshFrom psh m.+1)) (pChain3 C) q Hq r Hr ε ω
    (deepCell (upC2 C) (pTopCell (STop m.+1) d)).1
    (deepCell (upC2 C) (pTopCell (STop m.+1) d)).2
  • (f_equal (fun z => faceDeep (cohs3ChainDepsCohs2 (pChain3 C))
       r (Hr ↕ Hq) ω z.1 z.2) (pshFaceDeepUp C q.+1 (⇑ Hq) Hqp ε d)
     • pshFaceDeepC C r (Hr ↕ Hq) (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
         (psh.(GFace) m.+2 (q.+1 + p) Hqp ε d))
  = (f_equal (fun z => faceDeep (cohs3ChainDepsCohs2 (pChain3 C))
       q Hq ε z.1 z.2)
       (pshFaceDeepUp C r (↑ (Hr ↕ Hq))
          (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
     • pshFaceDeepC C q Hq (⇓ Hqp) ε
         (psh.(GFace) m.+2 (r + p)
            (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d))
    • f_equal (pshCell (STop m).1.(_pshDepsCohs2 psh).(_pshDepsCohs psh))
        (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
           (leR_add_mono_r Hr p) ε ω d).
Proof.
  now exact_no_check (hexPaste6
    (hexLegHere (νExt3At (pshFrom psh m.+1)) (pChain3 C)
      q Hq r Hr ε ω (pshDeepCellUp C d))
    (hexLegUp C r (Hr ↕ Hq) ω q.+1 (⇑ Hq) Hqp ε d)
    (hexLegDeep C r (Hr ↕ Hq)
      (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
      (psh.(GFace) m.+2 (q.+1 + p) Hqp ε d))
    (hexLegUp C q Hq ε r (↑ (Hr ↕ Hq))
      (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
    (hexLegDeep C q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+2 (r + p)
        (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d))
    (legHomot2
      (pshCell S.1.(_pshDepsCohs2 psh).(_pshDepsCohs psh))
      (faceRebuild (pChain3 C))
      (pshCell (STop m).1.(_pshDepsCohs2 psh).(_pshDepsCohs psh))
      (pshGetPaintingC C)
      (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
        (leR_add_mono_r Hr p) ε ω d))
    (pshHexCore C q Hq r Hr Hqp ε ω d)).
Defined.

(** Aligning the descent's chain with the presheaf-equipped one

    Both are chains out of the tower position's dependency data, so they
    agree as soon as their lengths do; the identification also identifies
    the stage they land on, which is the dimension the face erases. *)

Lemma leR_addR (a b: nat): a <= a + b.
Proof.
  induction a.
  - now exact leR_O.
  - now exact (⇑ IHa).
Defined.

(** Lifting a stage chain one tower position

    The face maps one level up run along the lift of the chain by
    [chainUp1], and that lift is again a stage chain: the endpoint stage
    below realizes the lifted chain's endpoint definitionally, because its
    three components are read off the stage's own step, the level-2
    extension one [AddCoh2Dep] deep, and the coherence paintings truncated
    once. *)

(** Name the lifted chain once to share the conversion between the
    next tower position's coherence data and the lifted data. *)

(** The presheaf-equipped chain of a given length

    The [νGpdPresentation] interface supplies only an SProp bound, from which no
    chain can be extracted, so the stage chain that matches a given descent is
    synthesized from a fuel: [pDown] descends by [j] stages, stalling at stage
    [0], and carries its endpoint. *)

Definition PPack {m P K} (STop: PStage m P K): Type :=
  {p: nat &T {k: nat &T {S: PStage m p k &T PChain STop S}}}.

Definition pPackStep {m P K} {STop: PStage m P K} (s: PPack STop):
  PPack STop :=
  (match s.1 as p0 return
     {k: nat &T {S: PStage m p0 k &T PChain STop S}} -> PPack STop with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (pStep s'.2.1; PChainCons s'.2.2)))
   end) s.2.

Fixpoint pDown {m P K} (STop: PStage m P K) (j: nat): PPack STop :=
  match j with
  | 0 => (P; (K; (STop; PChainNil)))
  | S j => pPackStep (pDown STop j)
  end.

(** The chain package a stage chain presents. A face map reads only the
    level-2 projection of the chain it runs along, so this is where the
    identification with the descent's chain is taken: at level 3 the lift of
    a stage chain is not recognizable as a stage chain, at level 2 it is. *)

Definition chainPack2 {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain dc2Top dc2): Chain2Pack dc2Top := (p; (k; (dc2; c))).

Definition pPack2 {m P K} {STop': PStage m P K} (s: PPack STop'):
  Chain2Pack (pDc3 STop').(_depsCohs2) :=
  chainPack2 (cohs3ChainDepsCohs2 (pChain3 s.2.2.2)).

Definition upPack {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  PPack (STop m.+1) := (p; (k.+1; (upStage C; upC C))).





Lemma faceDeep2PackEq {P K} {dc2Top: DepsCohs2 P K} {s t: Chain2Pack dc2Top}
  (E: s = t) (dim: nat) (Hs: dim <= s.2.1) (Ht: dim <= t.2.1) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  faceDeep s.2.2.2 dim Hs ε d Q = faceDeep t.2.2.2 dim Ht ε d Q.
Proof.
  now destruct E.
Defined.







(** The lifted comparisons use transport along the chain equality in
    their definitions. Their joint action on a face is stated below. *)

(** The bottom identification as a function of the chain and of the two
    identifications the chain supplies, so that a chain identification can be
    transported through it. *)

Definition pshFaceDeepAt {m p k} (R: LiftRealizer m p k)
  (dim: nat) (Hdim: dim <= k) (Hdimp: dim + p <= m.+2) (α: arity)
  (d: psh.(G0) m.+3) (Hd: liftDeepFamily d R)
  (Hg: liftGetFamily (psh.(GFace) m.+2 (dim + p) Hdimp α d) R):
  faceDeep (lrChain R) dim Hdim α (pTopCell (STop m.+1) d).1
    (pTopCell (STop m.+1) d).2 =
  pshCell (PCTop m.+1).(_pshDepsCohs psh)
    (psh.(GFace) m.+2 (dim + p) Hdimp α d) :=
  f_equal (fun z => faceAt (lrChain R) dim Hdim α z.1 z.2) Hd
  • (f_equal (fun z => getPainting (cohsChainExt (cohs2ChainDepsCohs (lrChain R)))
       z.1 z.2)
       (eq_sym (pshFaceCell (lrPC R) (lrPX R) dim Hdim Hdimp α d)) • Hg).





Lemma pshFaceDeepCUp {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k.+1) (Hdimp: dim + p <= m.+2) (α: arity)
  (d: psh.(G0) m.+3):
  pshFaceDeepC (upC C) dim Hdim Hdimp α d =
  f_equal (fun R: LiftRealizer m p k.+1 => faceDeep (lrChain R) dim Hdim α
    (pTopCell (STop m.+1) d).1 (pTopCell (STop m.+1) d).2)
    (eq_sym (liftRealizerBoundary C)) • pshFaceDeepUp C dim Hdim Hdimp α d.
Proof.
  now exact (displayed_pair_naturality
    (P := @liftDeepFamily m p k.+1 d)
    (Q := @liftGetFamily m p k.+1 (psh.(GFace) m.+2 (dim + p) Hdimp α d))
    (fun R: LiftRealizer m p k.+1 => faceDeep (lrChain R) dim Hdim α
      (pTopCell (STop m.+1) d).1 (pTopCell (STop m.+1) d).2)
    (pshCell (PCTop m.+1).(_pshDepsCohs psh)
      (psh.(GFace) m.+2 (dim + p) Hdimp α d))
    (fun R Hd Hg => pshFaceDeepAt R dim Hdim Hdimp α d Hd Hg)
    (eq_sym (liftRealizerBoundary C)) (pshDeepCellC (upC C) d)
    (pshGetPaintingC (upC C) (psh.(GFace) m.+2 (dim + p) Hdimp α d))).
Defined.

Lemma pPackStepStage {m P K} {STop: PStage m P K} (s: PPack STop):
  (pPackStep s).1 = Nat.pred s.1.
Proof.
  destruct s as (p, s2). now destruct p.
Defined.

Lemma pDownStage {m P K} (STop: PStage m P K) (j: nat):
  (pDown STop j).1 = P - j.
Proof.
  induction j.
  - now rewrite sub0r.
  - now rewrite subSuccR, pPackStepStage, IHj.
Defined.

Lemma pPackStepLen {m P K} {STop: PStage m P K} (s: PPack STop) (p': nat)
  (e: s.1 = p'.+1):
  pChainLen (pPackStep s).2.2.2 = (pChainLen s.2.2.2).+1.
Proof.
  destruct s as (p0, (k0, (S0, C0))). cbn in e. subst p0. now reflexivity.
Defined.

Lemma pDownLen {m P K} (STop: PStage m P K) (j: nat) (Hj: j <= P):
  pChainLen (pDown STop j).2.2.2 = j.
Proof.
  induction j.
  - now reflexivity.
  - refine (pPackStepLen (pDown STop j) (P - j.+1) _
      • f_equal S (IHj (↓ Hj))).
    now exact (pDownStage STop j • subPos Hj).
Defined.

(** Taking the chain identification as a parameter allows the
    level-2 transfer to proceed by path induction on that identification. *)

(** A chain and its level-2 projection have the same length. *)

Lemma cohs3ChainDepsCohs2Len {P K} {dc3Top: DepsCohs3 P K} {p k}
  {dc3: DepsCohs3 p k} (c: DepsCohs3Chain dc3Top dc3):
  cohs2ChainLen (cohs3ChainDepsCohs2 c) = cohs3ChainLen c.
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

(** The face naturality at the bottom of the descent

    A chain of length [ℓ] out of a position of stage [M.+1] ends at stage
    [p = M.+1 - ℓ], and the face it names at dimension [dim] erases the
    [psh]-dimension [p + dim]: recognize the chain as the stage chain of that
    length, apply [pshFaceDeepC], and commute the sum. *)

Definition gfBottomPack (M: nat) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh M.+1)) dc3):
  Chain2Pack (pDc3 (STop M)).(_depsCohs2) :=
  chainPack2 (cohs3ChainDepsCohs2 a).

Lemma gfBottomLen (M: nat) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh M.+1)) dc3):
  chain2PackLen (gfBottomPack M a) =
  chain2PackLen (pPack2 (pDown (STop M) (cohs3ChainLen a))).
Proof.
  unfold chain2PackLen, gfBottomPack, pPack2, chainPack2; cbn.
  rewrite (cohs3ChainDepsCohs2Len a).
  rewrite (cohs3ChainDepsCohs2Len
    (pChain3 (pDown (STop M) (cohs3ChainLen a)).2.2.2)).
  rewrite (pChain3Len (pDown (STop M) (cohs3ChainLen a)).2.2.2).
  now exact (eq_sym (pDownLen (STop M) (cohs3ChainLen a)
    (leR_eq_r (cohs3ChainLenEq a) (leR_addR (cohs3ChainLen a) p)))).
Defined.

(** The lifted presentation of the descent's chain one tower position up, and
    the transfer it contributes: the chain identification, and nothing more. *)

Definition upG {m p k} {S: PStage m p k} (C: PChain (STop m) S):
  gfBottomPack m.+1 (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)) =
  pPack2 (upPack C) := liftPackBoundary C.

Lemma faceDeep2PackRealizer {m p k} {R R': LiftRealizer m p k}
  (E: R = R') (dim: nat) (Hs Ht: dim <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs :=
    (pshDepsCohs2 psh (PCTop m.+1)).(_depsCohs))))
  (Q: mkPainting (mkExtraDeps (pshDepsCohs2 psh (PCTop m.+1)).(_extraDepsCohs)) d):
  faceDeep2PackEq (f_equal (@forgetLiftRealizer m p k) E) dim Hs Ht ε d Q =
  f_equal (fun R0: LiftRealizer m p k => faceDeep (lrChain R0) dim Hs ε d Q) E.
Proof. now destruct E. Defined.

Lemma faceDeepUpG {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hs Ht: dim <= k.+1) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs :=
    (pshDepsCohs2 psh (PCTop m.+1)).(_depsCohs))))
  (Q: mkPainting (mkExtraDeps (pshDepsCohs2 psh (PCTop m.+1)).(_extraDepsCohs)) d):
  faceDeep2PackEq (upG C) dim Hs Ht ε d Q =
  f_equal (fun R: LiftRealizer m p k.+1 => faceDeep (lrChain R) dim Hs ε d Q)
    (liftRealizerBoundary C).
Proof. now exact (faceDeep2PackRealizer (liftRealizerBoundary C) dim Hs Ht ε d Q). Defined.

Lemma faceDeepRealizerCancel {m p k} {R R': LiftRealizer m p k}
  (E: R = R') (dim: nat) (Hdim: dim <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs :=
    (pshDepsCohs2 psh (PCTop m.+1)).(_depsCohs))))
  (Q: mkPainting (mkExtraDeps (pshDepsCohs2 psh (PCTop m.+1)).(_extraDepsCohs)) d):
  f_equal (fun R0: LiftRealizer m p k => faceDeep (lrChain R0) dim Hdim ε d Q) E •
  f_equal (fun R0: LiftRealizer m p k => faceDeep (lrChain R0) dim Hdim ε d Q)
    (eq_sym E) = eq_refl.
Proof. now destruct E. Defined.

(** Rigidity, one rung up

    A stage chain out of a fixed stage is determined by its length, exactly
    as a [DepsCohs3Chain] is, and chain-package identifications are unique.
    Together these say that the presheaf presentation a bottom lemma is
    given is determined by the chain it presents, so the lemma's value does
    not depend on which presentation it was handed. *)

Lemma pPackEqLen {m P K} {STop': PStage m P K} {p k} {S: PStage m p k}
  (C: PChain STop' S) {p' k'} {S': PStage m p' k'} (C': PChain STop' S'):
  pChainLen C = pChainLen C' ->
  ((p; (k; (S; C))): PPack STop') = (p'; (k'; (S'; C'))).
Proof.
  revert p' k' S' C'.
  induction C as [|p k S C IHC]; intros p' k' S' C' H.
  - destruct C'; [now reflexivity | now discriminate H].
  - destruct C'; [now discriminate H |].
    cbn in H. injection H as H.
    now exact (f_equal pPackStep (IHC _ _ _ _ H)).
Defined.

Lemma pPackEq {m P K} {STop': PStage m P K} (s t: PPack STop'):
  pChainLen s.2.2.2 = pChainLen t.2.2.2 -> s = t.
Proof.
  destruct s as (p, (k, (S, C))), t as (p', (k', (S', C'))).
  now exact (pPackEqLen C C').
Defined.

Lemma chain2PackDec {P K} {dc2Top: DepsCohs2 P K} (s t: Chain2Pack dc2Top):
  {s = t} + {s <> t}.
Proof.
  destruct (natDec (chain2PackLen s) (chain2PackLen t)) as [H|H].
  - now left; now exact (chain2PackEq s t H).
  - right; intro e. now exact (H (f_equal chain2PackLen e)).
Defined.

Lemma chain2PackUIP {P K} {dc2Top: DepsCohs2 P K} {s t: Chain2Pack dc2Top}
  (e e': s = t): e = e'.
Proof. now exact (UIP_dec _ chain2PackDec s t e e'). Defined.

Section BottomGen.
Context (M: nat) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh M.+1)) dc3).

(** The bottom identification, over a prescribed presentation of the chain *)

Definition gfBottomArity (s: PPack (STop M)) (E: gfBottomPack M a = pPack2 s):
  k = s.2.1 :=
  f_equal (fun z: Chain2Pack (pDc3 (STop M)).(_depsCohs2) => z.2.1) E.

Definition gfBottomDim (s: PPack (STop M)) (E: gfBottomPack M a = pPack2 s)
  (dim: nat): dim + s.1 = p + dim :=
  f_equal (fun z => dim + z) (eq_sym (f_equal (fun z => z.1) E))
  • addComm dim p.

Definition gfFaceBottomP (s: PPack (STop M)) (E: gfBottomPack M a = pPack2 s)
  (dim: nat) (Hdim: dim <= k) (Hd': p + dim <= M.+1)
  (ε: arity) (x: gF0 (pshFrom psh M.+1) 1):
  (gFaceC (pshFrom psh M.+1) a 0 dim Hdim ε x).2.1 =
  psh.(GFace) M.+1 (p + dim) Hd' ε x.2.1 :=
  f_equal (fun z: νTotal (pshFrom psh M.+2) =>
    (faceDeep (cohs3ChainDepsCohs2 a) dim Hdim ε z.1 z.2).2.1)
    (eq_sym (graphContract
      (mkPshFrame psh (towerPshDeps psh (pshTw M.+1))) x))
  • (f_equal (fun z: νTotal (pshFrom psh M.+1) => z.2.1)
       (faceDeep2PackEq E dim Hdim (leR_eq_r (gfBottomArity s E) Hdim) ε
          (pTopCell (STop M) x.2.1).1 (pTopCell (STop M) x.2.1).2)
     • (f_equal (fun z: νTotal (pshFrom psh M.+1) => z.2.1)
          (pshFaceDeepC s.2.2.2 dim (leR_eq_r (gfBottomArity s E) Hdim)
             (leR_eq (eq_sym (gfBottomDim s E dim)) Hd') ε x.2.1)
        • pshFaceDimIrr psh (gfBottomDim s E dim) ε x.2.1)).

(** Which presentation was used never matters: the two are identified by
    rigidity, the two identifications by [chain2PackUIP], and the statement
    does not mention either. *)

Lemma gfFaceBottomPIrr (s t: PPack (STop M))
  (E: gfBottomPack M a = pPack2 s) (F: gfBottomPack M a = pPack2 t)
  (dim: nat) (Hdim: dim <= k) (Hd': p + dim <= M.+1)
  (ε: arity) (x: gF0 (pshFrom psh M.+1) 1):
  gfFaceBottomP s E dim Hdim Hd' ε x = gfFaceBottomP t F dim Hdim Hd' ε x.
Proof.
  assert (Hlen: pChainLen s.2.2.2 = pChainLen t.2.2.2).
  { rewrite <- (pChain3Len s.2.2.2), <- (pChain3Len t.2.2.2),
      <- (cohs3ChainDepsCohs2Len (pChain3 s.2.2.2)),
      <- (cohs3ChainDepsCohs2Len (pChain3 t.2.2.2)).
    now exact (eq_sym (f_equal chain2PackLen E)
      • f_equal chain2PackLen F). }
  destruct (pPackEq s t Hlen).
  now exact (f_equal (fun e => gfFaceBottomP s e dim Hdim Hd' ε x)
    (chain2PackUIP E F)).
Defined.

Definition gfFaceBottomGen (dim: nat) (Hdim: dim <= k)
  (Hd': p + dim <= M.+1) (ε: arity) (x: gF0 (pshFrom psh M.+1) 1):
  (gFaceC (pshFrom psh M.+1) a 0 dim Hdim ε x).2.1 =
  psh.(GFace) M.+1 (p + dim) Hd' ε x.2.1 :=
  gfFaceBottomP (pDown (STop M) (cohs3ChainLen a))
    (chain2PackEq _ _ (gfBottomLen M a)) dim Hdim Hd' ε x.

End BottomGen.

(** The bottom identification in normal form

    Along a stage chain the presentation is the chain itself and the transfer
    vanishes; along its lift the transfer is the chain identification, which
    the bridge cancels. Both are then the same three factors: move the cell to
    its canonical form, apply the stored presheaf-side families, commute the
    dimension. *)

Definition gfFaceBottomD {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k) (Hd': p + dim <= m.+1) (ε: arity)
  (x: gF0 (pshFrom psh m.+1) 1):
  (gFaceC (pshFrom psh m.+1) (pChain3 C) 0 dim Hdim ε x).2.1 =
  psh.(GFace) m.+1 (p + dim) Hd' ε x.2.1 :=
  f_equal (fun z: νTotal (pshFrom psh m.+2) =>
    (faceDeep (cohs3ChainDepsCohs2 (pChain3 C)) dim Hdim ε z.1 z.2).2.1)
    (eq_sym (graphContract
      (mkPshFrame psh (towerPshDeps psh (pshTw m.+1))) x))
  • (f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
       (pshFaceDeepC C dim Hdim (leR_eq (eq_sym (addComm dim p)) Hd') ε x.2.1)
     • pshFaceDimIrr psh (addComm dim p) ε x.2.1).

Lemma gfFaceBottomDEq {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k) (Hd': p + dim <= m.+1) (ε: arity)
  (x: gF0 (pshFrom psh m.+1) 1):
  gfFaceBottomGen m (pChain3 C) dim Hdim Hd' ε x
  = gfFaceBottomD C dim Hdim Hd' ε x.
Proof.
  refine (gfFaceBottomPIrr m _ _ ((p; (k; (S; C))): PPack (STop m))
    _ eq_refl dim Hdim Hd' ε x • _).
  unfold gfFaceBottomP, gfFaceBottomD.
  rewrite (natUIP (gfBottomDim m (pChain3 C)
    ((p; (k; (S; C))): PPack (STop m)) eq_refl dim) (addComm dim p)).
  rewrite eq_trans_refl_l.
  now reflexivity.
Defined.

Definition gfFaceBottomU {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k.+1) (Hd': p + dim <= m.+2) (ε: arity)
  (x: gF0 (pshFrom psh m.+2) 1):
  (gFaceC (pshFrom psh m.+2)
     (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)) 0 dim Hdim ε x).2.1 =
  psh.(GFace) m.+2 (p + dim) Hd' ε x.2.1 :=
  f_equal (fun z: νTotal (pshFrom psh m.+3) =>
    (faceDeep (upC2 C) dim Hdim ε z.1 z.2).2.1)
    (eq_sym (graphContract
      (mkPshFrame psh (towerPshDeps psh (pshTw m.+2))) x))
  • (f_equal (fun z: νTotal (pshFrom psh m.+2) => z.2.1)
       (pshFaceDeepUp C dim Hdim (leR_eq (eq_sym (addComm dim p)) Hd') ε x.2.1)
     • pshFaceDimIrr psh (addComm dim p) ε x.2.1).

Lemma gfFaceBottomUEq {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k.+1) (Hd': p + dim <= m.+2) (ε: arity)
  (x: gF0 (pshFrom psh m.+2) 1):
  gfFaceBottomGen m.+1
    (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C)) dim Hdim Hd' ε x
  = gfFaceBottomU C dim Hdim Hd' ε x.
Proof.
  refine (gfFaceBottomPIrr m.+1 _ _ (upPack C) _ (upG C)
    dim Hdim Hd' ε x • _).
  unfold gfFaceBottomP, gfFaceBottomU.
  rewrite (faceDeepUpG C dim Hdim _ ε _ _).
  rewrite (pshFaceDeepCUp C dim _ _ ε x.2.1).
  rewrite (natUIP (gfBottomDim m.+1
    (chainUp1 (νExt3At (pshFrom psh m.+1)) (pChain3 C))
    (upPack C) (upG C) dim) (addComm dim p)).
  rewrite eq_trans_map_distr.
  rewrite (cancelMap (fun z: νTotal (pshFrom psh m.+2) => z.2.1) _ _
    (faceDeepRealizerCancel (liftRealizerBoundary C) dim Hdim ε
       (pTopCell (STop m.+1) x.2.1).1 (pTopCell (STop m.+1) x.2.1).2) _ _).
  now reflexivity.
Defined.


(** The bottom hexagon at the level of cells and of [psh]-dimensions

    [pshFaceDeepCoh] pastes the hexagon at a canonical cell and at the
    dimensions the chain indexes. The level-2 descent needs it at an
    arbitrary cell of the tower and at the dimensions [psh] indexes; the two
    moves are independent and are made in that order. *)

Lemma pshFaceDimIrrTrans {n q q' q'': nat} (e: q = q') (e': q' = q'')
  {Hq: q <= n} {Hq': q' <= n} {Hq'': q'' <= n} (ε: arity)
  (X: psh.(G0) n.+1):
  pshFaceDimIrr psh e (Hq := Hq) (Hq' := Hq') ε X
  • pshFaceDimIrr psh e' (Hq := Hq') (Hq' := Hq'') ε X
  = pshFaceDimIrr psh (e • e') (Hq := Hq) (Hq' := Hq'') ε X.
Proof.
  now destruct e, e'.
Defined.

Lemma projCell {m} {d d': psh.(G0) m.+1} (e: d = d'):
  f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
    (f_equal (pshCell
       (STop m).1.(_pshDepsCohs2 psh).(_pshDepsCohs psh)) e) = e.
Proof.
  now destruct e.
Defined.

Definition thU {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k.+1) (Hdimp: dim + p <= m.+2) (α: arity)
  (x: gF0 (pshFrom psh m.+1) 2):
  faceDeep (upC2 C) dim Hdim α x.1 x.2 =
  pshCell (PCTop m.+1).(_pshDepsCohs psh)
    (psh.(GFace) m.+2 (dim + p) Hdimp α x.2.1) :=
  f_equal (fun z: νTotal (pshFrom psh m.+3) =>
    faceDeep (upC2 C) dim Hdim α z.1 z.2)
    (eq_sym (graphContract
      (mkPshFrame psh (towerPshDeps psh (pshTw m.+2))) x))
  • pshFaceDeepUp C dim Hdim Hdimp α x.2.1.

Lemma gfFaceCohBottomAt {m p k} {S: PStage m p k}
  (C: PChain (STop m) S)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+2) (ε ω: arity)
  (d: psh.(G0) m.+3) (X: νTotal (pshFrom psh m.+3))
  (G: pTopCell (STop m.+1) d = X):
  faceAtCohUp (νExt3At (pshFrom psh m.+1)) (pChain3 C) q Hq r Hr ε ω
    (deepCell (upC2 C) X).1 (deepCell (upC2 C) X).2
  • (f_equal (fun z => faceDeep (cohs3ChainDepsCohs2 (pChain3 C))
       r (Hr ↕ Hq) ω z.1 z.2)
       (f_equal (fun z: νTotal (pshFrom psh m.+3) =>
          faceDeep (upC2 C) q.+1 (⇑ Hq) ε z.1 z.2) (eq_sym G)
        • pshFaceDeepUp C q.+1 (⇑ Hq) Hqp ε d)
     • pshFaceDeepC C r (Hr ↕ Hq)
         (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
         (psh.(GFace) m.+2 (q.+1 + p) Hqp ε d))
  = (f_equal (fun z => faceDeep (cohs3ChainDepsCohs2 (pChain3 C))
       q Hq ε z.1 z.2)
       (f_equal (fun z: νTotal (pshFrom psh m.+3) =>
          faceDeep (upC2 C) r (↑ (Hr ↕ Hq)) ω z.1 z.2) (eq_sym G)
        • pshFaceDeepUp C r (↑ (Hr ↕ Hq))
            (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
     • pshFaceDeepC C q Hq (⇓ Hqp) ε
         (psh.(GFace) m.+2 (r + p)
            (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d))
    • f_equal (pshCell
        (STop m).1.(_pshDepsCohs2 psh).(_pshDepsCohs psh))
        (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
           (leR_add_mono_r Hr p) ε ω d).
Proof.
  destruct G.
  rewrite 2 eq_trans_refl_l.
  now exact (pshFaceDeepCoh C q Hq r Hr Hqp ε ω d).
Defined.

Lemma gfFaceCohBottomCell {m p k} {S: PStage m p k}
  (C: PChain (STop m) S)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+2) (ε ω: arity)
  (x: gF0 (pshFrom psh m.+1) 2):
  faceAtCohUp (νExt3At (pshFrom psh m.+1)) (pChain3 C) q Hq r Hr ε ω
    (deepCell (upC2 C) x).1 (deepCell (upC2 C) x).2
  • (f_equal (fun z => faceDeep (cohs3ChainDepsCohs2 (pChain3 C))
       r (Hr ↕ Hq) ω z.1 z.2) (thU C q.+1 (⇑ Hq) Hqp ε x)
     • pshFaceDeepC C r (Hr ↕ Hq)
         (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
         (psh.(GFace) m.+2 (q.+1 + p) Hqp ε x.2.1))
  = (f_equal (fun z => faceDeep (cohs3ChainDepsCohs2 (pChain3 C))
       q Hq ε z.1 z.2)
       (thU C r (↑ (Hr ↕ Hq)) (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω x)
     • pshFaceDeepC C q Hq (⇓ Hqp) ε
         (psh.(GFace) m.+2 (r + p)
            (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω x.2.1))
    • f_equal (pshCell
        (STop m).1.(_pshDepsCohs2 psh).(_pshDepsCohs psh))
        (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
           (leR_add_mono_r Hr p) ε ω x.2.1).
Proof.
  unfold thU.
  now exact (gfFaceCohBottomAt C q Hq r Hr Hqp ε ω x.2.1 x
    (graphContract (mkPshFrame psh (towerPshDeps psh (pshTw m.+2))) x)).
Defined.

(** The two normal-form bottoms, read through the level-0 projection. *)

Lemma bottomUThU {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k.+1) (Hd': p + dim <= m.+2)
  (Hdimp: dim + p <= m.+2) (ε: arity) (x: gF0 (pshFrom psh m.+1) 2):
  gfFaceBottomU C dim Hdim Hd' ε x
  = f_equal (fun z: νTotal (pshFrom psh m.+2) => z.2.1)
      (thU C dim Hdim Hdimp ε x)
    • pshFaceDimIrr psh (addComm dim p) ε x.2.1.
Proof.
  unfold gfFaceBottomU, thU.
  rewrite eq_trans_map_distr.
  rewrite (f_equal_compose
    (fun z: νTotal (pshFrom psh m.+3) =>
       faceDeep (upC2 C) dim Hdim ε z.1 z.2)
    (fun z: νTotal (pshFrom psh m.+2) => z.2.1)
    (eq_sym (graphContract
      (mkPshFrame psh (towerPshDeps psh (pshTw m.+2))) x))).
  now exact (eq_trans_assoc _ _ _).
Defined.

Lemma bottomDAt {m p k} {S: PStage m p k} (C: PChain (STop m) S)
  (dim: nat) (Hdim: dim <= k) (Hd': p + dim <= m.+1)
  (Hdimp: dim + p <= m.+1) (ω: arity) (W: psh.(G0) m.+2):
  gfFaceBottomD C dim Hdim Hd' ω (pTopCell (STop m) W)
  = f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
      (pshFaceDeepC C dim Hdim Hdimp ω W)
    • pshFaceDimIrr psh (addComm dim p) ω W.
Proof.
  unfold gfFaceBottomD.
  now exact (eq_trans_refl_l _).
Defined.

Lemma bottomDNat {m p k} {St: PStage m p k}
  (C: PChain (STop m) St)
  (dim: nat) (Hdim: dim <= k) (Hd': p + dim <= m.+1) (ω: arity)
  {y z: νTotal (pshFrom psh m.+2)} (θ: y = z):
  gfFaceBottomD C dim Hdim Hd' ω y
  • f_equal (psh.(GFace) m.+1 (p + dim) Hd' ω)
      (f_equal (fun w: νTotal (pshFrom psh m.+2) => w.2.1) θ)
  = f_equal (fun w: νTotal (pshFrom psh m.+1) => w.2.1)
      (f_equal (fun w: νTotal (pshFrom psh m.+2) =>
         faceDeep (cohs3ChainDepsCohs2 (pChain3 C)) dim Hdim ω w.1 w.2) θ)
    • gfFaceBottomD C dim Hdim Hd' ω z.
Proof.
  now destruct θ; cbn; rewrite eq_trans_refl_l.
Defined.

(** The cell-level hexagon, read through the level-0 projection: the
    [pshCell] wrapper on the presheaf exchange law disappears. *)

Lemma gfFaceCohBottomProj {m p k} {St: PStage m p k}
  (C: PChain (STop m) St)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+2) (ε ω: arity)
  (x: gF0 (pshFrom psh m.+1) 2):
  f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
    (faceAtCohUp (νExt3At (pshFrom psh m.+1)) (pChain3 C) q Hq r Hr ε ω
       (deepCell (upC2 C) x).1 (deepCell (upC2 C) x).2)
  • (f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
       (f_equal (fun z: νTotal (pshFrom psh m.+2) =>
          faceDeep (cohs3ChainDepsCohs2 (pChain3 C)) r (Hr ↕ Hq) ω z.1 z.2)
          (thU C q.+1 (⇑ Hq) Hqp ε x))
     • f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
         (pshFaceDeepC C r (Hr ↕ Hq) (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
            (psh.(GFace) m.+2 (q.+1 + p) Hqp ε x.2.1)))
  = (f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
       (f_equal (fun z: νTotal (pshFrom psh m.+2) =>
          faceDeep (cohs3ChainDepsCohs2 (pChain3 C)) q Hq ε z.1 z.2)
          (thU C r (↑ (Hr ↕ Hq)) (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω x))
     • f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
         (pshFaceDeepC C q Hq (⇓ Hqp) ε
            (psh.(GFace) m.+2 (r + p)
               (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω x.2.1)))
    • psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
        (leR_add_mono_r Hr p) ε ω x.2.1.
Proof.
  now exact_no_check (hexMapProj (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
    _ _ _ _ _ _
    (projCell (psh.(GFaceCoh) m.+1 (q + p) (⇓ Hqp) (r + p)
       (leR_add_mono_r Hr p) ε ω x.2.1))
    (gfFaceCohBottomCell C q Hq r Hr Hqp ε ω x)).
Defined.

(** The bottom of the level-2 descent, in the presentation the descent
    supplies. *)

(** The only nontrivial normalization among the upper dimension paths.
    It is deliberately checked independently of the tower-sized hexagon. *)
Lemma gfFaceBottomDimFuse {m p q: nat}
  (Hpq1: p + q.+1 <= m.+2) (ε: arity)
  (X: psh.(G0) m.+3):
  pshFaceDimIrr psh (addComm q.+1 p)
      (Hq := leR_eq (eq_sym (addComm q.+1 p)) Hpq1)
      (Hq' := Hpq1) ε X
  • pshFaceDimIrr psh (eq_sym (plusSuccR p q))
      (Hq := Hpq1)
      (Hq' := leR_eq (eq_sym (plusSuccR p q)) Hpq1) ε X
  = pshFaceDimIrr psh (f_equal S (addComm q p))
      (Hq := leR_eq (eq_sym (addComm q.+1 p)) Hpq1)
      (Hq' := leR_eq (eq_sym (plusSuccR p q)) Hpq1) ε X.
Proof.
  rewrite (pshFaceDimIrrTrans (addComm q.+1 p)
    (eq_sym (plusSuccR p q)) ε X).
  now rewrite (natUIP (addComm q.+1 p • eq_sym (plusSuccR p q))
    (f_equal S (addComm q p))).
Qed.

Lemma gfFaceCohBottom {m p k} {St: PStage m p k}
  (C: PChain (STop m) St)
  (q: nat) (Hq: q <= k) (r: nat) (Hr: r <= q) (ε ω: arity)
  (Hpq: p + q <= m.+1) (Hpr: p + r <= p + q) (Hpq1: p + q.+1 <= m.+2)
  (x: gF0 (pshFrom psh m.+1) 2):
  f_equal (fun z: νTotal (pshFrom psh m.+1) => z.2.1)
    (gFaceCohC (pshFrom psh m.+1) (pChain3 C) 0 q Hq r Hr ε ω x)
  • (gfFaceBottomD C r (Hr ↕ Hq) (Hpr ↕ Hpq) ω
       (gFaceC (pshFrom psh m.+1) (pChain3 C) 1 q.+1 (⇑ Hq) ε x)
     • f_equal (psh.(GFace) m.+1 (p + r) (Hpr ↕ Hpq) ω)
         (gfFaceBottomU C q.+1 (⇑ Hq) Hpq1 ε x
          • pshFaceDimIrr psh (eq_sym (plusSuccR p q)) ε x.2.1))
  = (gfFaceBottomD C q Hq Hpq ε
       (gFaceC (pshFrom psh m.+1) (pChain3 C) 1 r (Hr ↕ (↑ Hq)) ω x)
     • f_equal (psh.(GFace) m.+1 (p + q) Hpq ε)
         (gfFaceBottomU C r (Hr ↕ (↑ Hq)) (Hpr ↕ (↑ Hpq)) ω x))
    • psh.(GFaceCoh) m.+1 (p + q) Hpq (p + r) Hpr ε ω x.2.1.
Proof.
  eapply hex_transport_glue.
  - now exact (bottomUThU C q.+1 (⇑ Hq) Hpq1
      (leR_eq (eq_sym (addComm q.+1 p)) Hpq1) ε x).
  - now exact (gfFaceBottomDimFuse Hpq1 ε x.2.1).
  - now exact (bottomUThU C r (Hr ↕ (↑ Hq)) (Hpr ↕ (↑ Hpq))
      (leR_eq (eq_sym (addComm r p)) (Hpr ↕ (↑ Hpq))) ω x).
  - now exact (bottomDNat C r (Hr ↕ Hq) (Hpr ↕ Hpq) ω
      (thU C q.+1 (⇑ Hq)
        (leR_eq (eq_sym (addComm q.+1 p)) Hpq1) ε x)).
  - now exact (bottomDAt C r (Hr ↕ Hq) (Hpr ↕ Hpq)
      (leR_eq (eq_sym (addComm r p)) (Hpr ↕ Hpq)) ω
      (psh.(GFace) m.+2 (q.+1 + p)
        (leR_eq (eq_sym (addComm q.+1 p)) Hpq1) ε x.2.1)).
  - now exact (bottomDNat C q Hq Hpq ε
      (thU C r (Hr ↕ (↑ Hq))
        (leR_eq (eq_sym (addComm r p)) (Hpr ↕ (↑ Hpq))) ω x)).
  - now exact (bottomDAt C q Hq Hpq
      (leR_eq (eq_sym (addComm q p)) Hpq) ε
      (psh.(GFace) m.+2 (r + p)
        (leR_eq (eq_sym (addComm r p)) (Hpr ↕ (↑ Hpq))) ω x.2.1)).
  - now exact_no_check (gfFaceCohBottomProj C q Hq r Hr
      (leR_eq (eq_sym (addComm q.+1 p)) Hpq1) ε ω x).
  - now exact (pshFaceCohDimIrr psh (addComm q p) (addComm r p)
      (Hq := ⇓ (leR_eq (eq_sym (addComm q.+1 p)) Hpq1))
      (Hq' := Hpq) (Hr := leR_add_mono_r Hr p) (Hr' := Hpr)
      ε ω x.2.1).
Qed.

(** Recognizing the descent's chain as a stage chain, one rung up from
    [gfBottomPack]. *)

Definition pPack3 {m P K} {STop': PStage m P K} (s: PPack STop'):
  Chain3Pack (pDc3 STop') :=
  (s.1; (s.2.1; (pDc3 s.2.2.1; pChain3 s.2.2.2))).

Lemma gfBottom3Len (M: nat)
  (s: Chain3Pack (νDepsCohs3At (pshFrom psh M.+1))):
  chain3PackLen s
  = chain3PackLen (pPack3 (pDown (STop M) (chain3PackLen s))).
Proof.
  unfold chain3PackLen, pPack3; cbn.
  rewrite (pChain3Len (pDown (STop M)
    (cohs3ChainLen s.2.2.2)).2.2.2).
  now exact (eq_sym (pDownLen (STop M) (cohs3ChainLen s.2.2.2)
    (leR_eq_r (cohs3ChainLenEq s.2.2.2)
       (leR_addR (cohs3ChainLen s.2.2.2) s.1)))).
Defined.

(** The pointwise member of the named pack family. *)
Definition gfFaceCohBottomPred (M: nat)
  (s: Chain3Pack (νDepsCohs3At (pshFrom psh M.+1)))
  (q: nat) (Hq: q <= s.2.1) (r: nat) (Hr: r <= q) (ε ω: arity)
  (Hpq: s.1 + q <= M.+1) (Hpr: s.1 + r <= s.1 + q)
  (Hpq1: s.1 + q.+1 <= M.+2) (x: gF0 (pshFrom psh M.+1) 2): Prop :=
  f_equal (fun z: νTotal (pshFrom psh M.+1) => z.2.1)
    (gFaceCohC (pshFrom psh M.+1) s.2.2.2 0 q Hq r Hr ε ω x)
  • (gfFaceBottomGen M s.2.2.2 r (Hr ↕ Hq) (Hpr ↕ Hpq) ω
       (gFaceC (pshFrom psh M.+1) s.2.2.2 1 q.+1 (⇑ Hq) ε x)
     • f_equal (psh.(GFace) M.+1 (s.1 + r) (Hpr ↕ Hpq) ω)
         (gfFaceBottomGen M.+1
            (chainUp1 (νExt3At (pshFrom psh M.+1)) s.2.2.2)
            q.+1 (⇑ Hq) Hpq1 ε x
          • pshFaceDimIrr psh (eq_sym (plusSuccR s.1 q)) ε x.2.1))
  = (gfFaceBottomGen M s.2.2.2 q Hq Hpq ε
       (gFaceC (pshFrom psh M.+1) s.2.2.2 1 r (Hr ↕ (↑ Hq)) ω x)
     • f_equal (psh.(GFace) M.+1 (s.1 + q) Hpq ε)
         (gfFaceBottomGen M.+1
            (chainUp1 (νExt3At (pshFrom psh M.+1)) s.2.2.2)
            r (Hr ↕ (↑ Hq)) (Hpr ↕ (↑ Hpq)) ω x))
    • psh.(GFaceCoh) M.+1 (s.1 + q) Hpq (s.1 + r) Hpr ε ω x.2.1.

Definition gfFaceCohBottomFam (M: nat)
  (s: Chain3Pack (νDepsCohs3At (pshFrom psh M.+1))): Type :=
  forall (q: nat) (Hq: q <= s.2.1) (r: nat) (Hr: r <= q) (ε ω: arity)
    (Hpq: s.1 + q <= M.+1) (Hpr: s.1 + r <= s.1 + q)
    (Hpq1: s.1 + q.+1 <= M.+2) (x: gF0 (pshFrom psh M.+1) 2),
  gfFaceCohBottomPred M s q Hq r Hr ε ω Hpq Hpr Hpq1 x.

Lemma gfFaceCohBottomAtPack (M: nat) (t: PPack (STop M)):
  gfFaceCohBottomFam M (pPack3 t).
Proof.
  unfold gfFaceCohBottomFam, gfFaceCohBottomPred; cbn [pPack3].
  intros q Hq r Hr ε ω Hpq Hpr Hpq1 x.
  eapply hex_replace_four.
  - now exact (gfFaceBottomDEq t.2.2.2 r (Hr ↕ Hq) (Hpr ↕ Hpq) ω
      (gFaceC (pshFrom psh M.+1) (pChain3 t.2.2.2)
         1 q.+1 (⇑ Hq) ε x)).
  - now exact (gfFaceBottomUEq t.2.2.2 q.+1 (⇑ Hq) Hpq1 ε x).
  - now exact (gfFaceBottomDEq t.2.2.2 q Hq Hpq ε
      (gFaceC (pshFrom psh M.+1) (pChain3 t.2.2.2)
         1 r (Hr ↕ (↑ Hq)) ω x)).
  - now exact (gfFaceBottomUEq t.2.2.2 r (Hr ↕ (↑ Hq))
      (Hpr ↕ (↑ Hpq)) ω x).
  - now exact (gfFaceCohBottom t.2.2.2 q Hq r Hr ε ω
      Hpq Hpr Hpq1 x).
Qed.

Lemma gfFaceCohBottomPack (M: nat) (t: PPack (STop M))
  (s: Chain3Pack (νDepsCohs3At (pshFrom psh M.+1)))
  (E: pPack3 t = s)
  (q: nat) (Hq: q <= s.2.1) (r: nat) (Hr: r <= q) (ε ω: arity)
  (Hpq: s.1 + q <= M.+1) (Hpr: s.1 + r <= s.1 + q)
  (Hpq1: s.1 + q.+1 <= M.+2) (x: gF0 (pshFrom psh M.+1) 2):
  gfFaceCohBottomPred M s q Hq r Hr ε ω Hpq Hpr Hpq1 x.
Proof.
  now exact ((rew [gfFaceCohBottomFam M] E in
    gfFaceCohBottomAtPack M t) q Hq r Hr ε ω Hpq Hpr Hpq1 x).
Qed.

Lemma gfFaceCohBottomGen (M p k: nat) (dc3: DepsCohs3 p k)
  (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh M.+1)) dc3)
  (q: nat) (Hq: q <= k) (r: nat) (Hr: r <= q) (ε ω: arity)
  (Hpq: p + q <= M.+1) (Hpr: p + r <= p + q)
  (Hpq1: p + q.+1 <= M.+2) (x: gF0 (pshFrom psh M.+1) 2):
  gfFaceCohBottomPred M
    ((p; (k; (dc3; a))): Chain3Pack
      (νDepsCohs3At (pshFrom psh M.+1)))
    q Hq r Hr ε ω Hpq Hpr Hpq1 x.
Proof.
  now exact (gfFaceCohBottomPack M
    (pDown (STop M) (cohs3ChainLen a))
    ((p; (k; (dc3; a))): Chain3Pack
      (νDepsCohs3At (pshFrom psh M.+1)))
    (eq_sym (chain3PackEq _ _
      (gfBottom3Len M
        ((p; (k; (dc3; a))): Chain3Pack
          (νDepsCohs3At (pshFrom psh M.+1))))))
    q Hq r Hr ε ω Hpq Hpr Hpq1 x).
Qed.

(** The levelwise equivalences and the naturality descent

    An explicit equation [L = n + m.+1] records the tower level reached after
    [n] relative steps from position [m.+1]. [natUIP] normalizes this equation
    at the base case, leaving the equivalences independent of transports along
    the descent. The base case is the projection of a candidate-filled cell to
    the [psh]-cell it is built from, an equivalence because the identification
    component of such a cell lives in a based path space. *)

Fixpoint gfEquiv (m n: nat) {struct n}:
  forall (L: nat), L = n + m.+1 ->
  Equiv (gF0 (pshFrom psh m.+1) n) (psh.(G0) L) :=
  match n return forall (L: nat), L = n + m.+1 ->
    Equiv (gF0 (pshFrom psh m.+1) n) (psh.(G0) L) with
  | 0 => fun L HL =>
      rew [fun l => Equiv (νTotal (pshFrom psh m.+1)) (psh.(G0) l)]
        (eq_sym HL) in
      graphEquiv (mkPshFrame psh (towerPshDeps psh (pshTw m)))
  | S n => fun L HL => gfEquiv m.+1 n L (HL • plusSuccR n m.+1)
  end.

(** The descent carries the chain: a relative step moves the tower position
    up and lifts the chain, which keeps the endpoint stage — hence the erased
    dimension [p + dim] — fixed while the offset grows. *)

Fixpoint gfFaceEquivGen (m n: nat) {struct n}:
  forall (p k: nat) (dc3: DepsCohs3 p k)
    (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh m.+1)) dc3)
    (L: nat) (HL: L = n + m.+1) (HL2: L.+1 = n.+1 + m.+1)
    (dim: nat) (Hd: dim <= n + k) (Hd': p + dim <= L) (ε: arity)
    (x: gF0 (pshFrom psh m.+1) n.+1),
  gfEquiv m n L HL (gFaceC (pshFrom psh m.+1) a n dim Hd ε x) =
  psh.(GFace) L (p + dim) Hd' ε (gfEquiv m n.+1 L.+1 HL2 x).
Proof.
  destruct n; intros.
  - set (HLs := eq_sym HL).
    rewrite (natUIP HL (eq_sym HLs)).
    clearbody HLs. clear HL.
    destruct HLs.
    cbn [gfEquiv].
    rewrite (natUIP (HL2 • plusSuccR 0 m.+1) eq_refl).
    now exact (gfFaceBottomGen m a dim Hd Hd' ε x).
  - now exact (gfFaceEquivGen m.+1 n p k.+1 _
      (chainUp1 (νExt3At (pshFrom psh m.+1)) a) L
      (HL • plusSuccR n m.+1) (HL2 • plusSuccR n.+1 m.+1)
      dim (leR_eq_r (plusSuccR n k) Hd) Hd' ε x).
Defined.

(** The value of the descent at the bottom. [plusSuccR] reduces at the two
    concrete depths, so both sides are already convertible except for two
    [natUIP] transports over pairs of convertible level equations, which
    [natUIP2] removes. *)

Lemma gfFaceEquivGen0 (m p k: nat) (dc3: DepsCohs3 p k)
  (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh m.+1)) dc3)
  (dim: nat) (Hd: dim <= 0 + k) (Hd': p + dim <= 0 + m.+1) (ε: arity)
  (x: gF0 (pshFrom psh m.+1) 1):
  gfFaceEquivGen m 0 p k dc3 a (0 + m.+1) eq_refl eq_refl dim Hd Hd' ε x
  = gfFaceBottomGen m a dim Hd Hd' ε x.
Proof.
  cbn [gfFaceEquivGen].
  rewrite (natUIP2 (natUIP (eq_refl: 0 + m.+1 = 0 + m.+1)
    (eq_sym (eq_sym eq_refl))) eq_refl).
  cbn [eq_ind_r eq_ind eq_sym eq_rect].
  rewrite (natUIP2 (natUIP (eq_refl • plusSuccR 0 m.+1)
    (eq_refl: (0 + m.+1).+1 = 0 + m.+2)) eq_refl).
  now reflexivity.
Defined.

Lemma gfFaceEquivGen1 (m p k: nat) (dc3: DepsCohs3 p k)
  (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh m.+1)) dc3)
  (dim: nat) (Hd: dim <= 1 + k) (Hd': p + dim <= (0 + m.+1).+1) (ε: arity)
  (x: gF0 (pshFrom psh m.+1) 2):
  gfFaceEquivGen m 1 p k dc3 a (0 + m.+1).+1 eq_refl eq_refl dim Hd Hd' ε x
  = gfFaceBottomGen m.+1 (chainUp1 (νExt3At (pshFrom psh m.+1)) a)
      dim Hd Hd' ε x.
Proof.
  now exact (gfFaceEquivGen0 m.+1 p k.+1 _
    (chainUp1 (νExt3At (pshFrom psh m.+1)) a) dim Hd Hd' ε x).
Defined.

(** The level-2 descent. *)

Fixpoint gfFaceCohEquivGen (m n: nat) {struct n}:
  forall (p k: nat) (dc3: DepsCohs3 p k)
    (a: DepsCohs3Chain (νDepsCohs3At (pshFrom psh m.+1)) dc3)
    (L: nat) (HL: L = n + m.+1) (HL2: L.+1 = n.+1 + m.+1)
    (HL3: L.+2 = n.+2 + m.+1)
    (q: nat) (Hq: q <= n + k) (r: nat) (Hr: r <= q) (ε ω: arity)
    (Hpq: p + q <= L) (Hpr: p + r <= p + q) (Hpq1: p + q.+1 <= L.+1)
    (x: gF0 (pshFrom psh m.+1) n.+2),
  f_equal (gfEquiv m n L HL)
    (gFaceCohC (pshFrom psh m.+1) a n q Hq r Hr ε ω x)
  • (gfFaceEquivGen m n p k dc3 a L HL HL2 r (Hr ↕ Hq) (Hpr ↕ Hpq) ω
       (gFaceC (pshFrom psh m.+1) a n.+1 q.+1 (⇑ Hq) ε x)
     • f_equal (psh.(GFace) L (p + r) (Hpr ↕ Hpq) ω)
         (gfFaceEquivGen m n.+1 p k dc3 a L.+1 HL2 HL3 q.+1 (⇑ Hq)
            Hpq1 ε x
          • pshFaceDimIrr psh (eq_sym (plusSuccR p q)) ε
              (gfEquiv m n.+2 L.+2 HL3 x)))
  = (gfFaceEquivGen m n p k dc3 a L HL HL2 q Hq Hpq ε
       (gFaceC (pshFrom psh m.+1) a n.+1 r (Hr ↕ (↑ Hq)) ω x)
     • f_equal (psh.(GFace) L (p + q) Hpq ε)
         (gfFaceEquivGen m n.+1 p k dc3 a L.+1 HL2 HL3 r (Hr ↕ (↑ Hq))
            (Hpr ↕ (↑ Hpq)) ω x))
    • psh.(GFaceCoh) L (p + q) Hpq (p + r) Hpr ε ω
        (gfEquiv m n.+2 L.+2 HL3 x).
Proof.
  destruct n; intros.
  2: { now exact (gfFaceCohEquivGen m.+1 n p k.+1 _
         (chainUp1 (νExt3At (pshFrom psh m.+1)) a) L
         (HL • plusSuccR n m.+1) (HL2 • plusSuccR n.+1 m.+1)
         (HL3 • plusSuccR n.+2 m.+1)
         q (leR_eq_r (plusSuccR n k) Hq) r Hr ε ω Hpq Hpr Hpq1 x). }
  set (HLs := eq_sym HL).
  rewrite (natUIP HL (eq_sym HLs)).
  clearbody HLs. clear HL.
  destruct HLs.
  rewrite (natUIP HL2 eq_refl).
  rewrite (natUIP HL3 eq_refl).
  rewrite (gfFaceEquivGen0 m p k dc3 a r (Hr ↕ Hq) (Hpr ↕ Hpq) ω
    (gFaceC (pshFrom psh m.+1) a 1 q.+1 (⇑ Hq) ε x)).
  rewrite (gfFaceEquivGen0 m p k dc3 a q Hq Hpq ε
    (gFaceC (pshFrom psh m.+1) a 1 r (Hr ↕ (↑ Hq)) ω x)).
  rewrite (gfFaceEquivGen1 m p k dc3 a q.+1 (⇑ Hq) Hpq1 ε x).
  rewrite (gfFaceEquivGen1 m p k dc3 a r (Hr ↕ (↑ Hq))
    (Hpr ↕ (↑ Hpq)) ω x).
  now exact (gfFaceCohBottomGen m p k dc3 a q Hq r Hr ε ω Hpq Hpr Hpq1 x).
Defined.

(** Assemble the carrier, face, and exchange clauses of [g ∘ f]. *)

Definition gfF0Equiv (n: nat): Equiv (gF0 (f psh) n) (psh.(G0) n) :=
  match n with
  | 0 => graphEquiv
      (B := GDom (mkFrame (toDepsRestr ((νGpdAt 0).(data) tt).(restrFrames))))
      (fun _: psh.(G0) 0 => tt)
  | S n => gfEquiv 0 n n.+1 (plusOneR n)
  end.

(** At the bottom level the tower carries no presheaf frame data yet: the
    candidate filler is the based path space at the unit frame, and the face
    is the layer the presheaf frame map stores, read by [nth_lam]. *)

Lemma gfFaceBottom0 (q: nat) (Hq: q <= 0) (ε: arity) (x: gF0 (f psh) 1):
  (gFaceC (f psh) DepsCohs3ChainNil 0 q (leR_eq_r (plus_n_O 0) Hq) ε x).2.1 =
  psh.(GFace) 0 q Hq ε x.2.1.
Proof.
  destruct q; [| now destruct (leR_O_contra Hq)].
  rewrite (gFaceC0Nil (f psh) (leR_eq_r (plus_n_O 0) Hq) ε x).
  destruct x as (D, (d, e)).
  unfold νFace.
  rewrite e.
  now rewrite nth_lam.
Defined.
(** The bottom coherence hexagon. *)

Definition pshCell0 (d: psh.(G0) 0): νTotal (f psh) :=
  (tt; (d; eq_refl)).

Definition pshCell1 (d: psh.(G0) 1): νTotal (pshFrom psh 1) :=
  (mkPshFrame psh (towerPshDeps psh (pshTw 0)) d; (d; eq_refl)).

Definition C1: PChain (STop 0) (pStep (STop 0)) :=
  PChainCons PChainNil.

Definition pshFaceDeep1 (dim: nat) (Hdim: dim <= 1)
  (Hdp: dim + 0 <= 1) (α: arity) (d: psh.(G0) 2):
  gFaceC (f psh) DepsCohs3ChainNil 1 dim Hdim α
    (pTopCell (STop 0) d)
  = pshCell1 (psh.(GFace) 1 (dim + 0) Hdp α d) :=
  pshFaceDeepC C1 dim Hdim Hdp α d.

Definition pshFaceCell0S (H: 0 <= 0) (α: arity) (d: psh.(G0) 1):
  pshCell0 (psh.(GFace) 0 0 H α d)
  = gFaceC (f psh) DepsCohs3ChainNil 0 0 H α (pshCell1 d) :=
  eq_existT_curried
    ((PCTop 0).(_pshDepsCohs psh).(_pshDeps psh).(_pshRestrs psh).2
       0 H H α d)
    ((PCTop 0).(_pshDepsCohs psh).(_pshRestrPaintings psh).2
       0 H H α d).

Lemma baseOuterProj {A0: Type} {x y: {a: A0 &T tt = tt}} (e: x = y):
  f_equal (fun z: {u: unit &T {a: A0 &T u = tt}} => z.2.1)
    (eq_sym (eq_existT_curried eq_refl (eq_sym e)))
  = f_equal (fun z => z.1) e.
Proof. now destruct e. Defined.

Lemma baseInnerProj {A0: Type} {x y: {a: A0 &T tt = tt}} (e: x = y):
  f_equal (fun z => z.1) e =
  eq_ind_r (fun z: {a: A0 &T tt = tt} => z.1 = y.1) eq_refl e.
Proof. now destruct e. Defined.

Lemma pshFaceCell0SProj (H: 0 <= 0) (α: arity) (d: psh.(G0) 1):
  f_equal (fun z: νTotal (f psh) => z.2.1)
    (eq_sym (pshFaceCell0S H α d))
  = gfFaceBottom0 0 H α (pshCell1 d).
Proof.
  unfold pshFaceCell0S, gfFaceBottom0; cbn.
  rewrite baseOuterProj, baseInnerProj.
  now reflexivity.
Defined.

Definition baseFace (H: 0 <= 0) (α: arity)
  (z: νTotal (pshFrom psh 1)): νTotal (f psh) :=
  gFaceC (f psh) DepsCohs3ChainNil 0 0 H α z.

Definition S1: PStage 0 0 1 := pStep (STop 0).

Definition PC2E: PshDepsCohs2 psh 0 0 1 :=
  S1.1.(_pshDepsCohs2 psh).

Definition PCXE:
  PshDepsCohsExtension psh 0 PC2E PC2E.(_pExtraDepsCohs psh) :=
  S1.1.(_pshExtraDepsCohs psh).

Definition baseRestrFrame (H: 0 <= 0) (α: arity)
  (D: mkFrame (pshDepsCohs psh PC2E.(_pshDepsCohs psh)).(_deps)) : unit :=
  tt.

Definition baseRestrPainting (H: 0 <= 0) (α: arity)
  (D: mkFrame (pshDepsCohs psh PC2E.(_pshDepsCohs psh)).(_deps))
  (Q: mkPainting
    (pshDepsCohs psh PC2E.(_pshDepsCohs psh)).(_extraDeps) D):
  this (f psh) (baseRestrFrame H α D) :=
  nth Q.1 α.

Definition baseRestrFn2 (H: 0 <= 0) (α: arity)
  (z: PCell PC2E): νTotal (f psh) :=
  (baseRestrFrame H α z.1; baseRestrPainting H α z.1 z.2).

Definition baseCohCore (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2) :=
  restrCellCoh (νDepsCohs3At (f psh)) 0 Hq 0 Hr ε ω
    (deepCell
      (cohs3ChainDepsCohs2
        (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil))
      (pTopCell (STop 0) d)).1
    (deepCell
      (cohs3ChainDepsCohs2
        (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil))
      (pTopCell (STop 0) d)).2.

Lemma pshRestrCellCoh0Stored (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2):
  f_equal pshCell0 (psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d)
  • (pshFaceCell0S (Hr ↕ Hq) ω
       (psh.(GFace) 1 (1 + 0) leR_refl ε d)
     • f_equal (baseRestrFn2 (Hr ↕ Hq) ω)
         (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d))
  = pshFaceCell0S Hq ε
      (psh.(GFace) 1 (0 + 0) (Hr ↕ (↑ Hq)) ω d)
    • (f_equal (baseRestrFn2 Hq ε)
         (pshFaceCell PC2E PCXE
            0 (Hr ↕ (↑ Hq)) (Hr ↕ (↑ Hq)) ω d)
       • baseCohCore Hq Hr ε ω d).
Proof.
  unfold pshFaceCell0S, baseRestrFn2, pshFaceCell, pshCell0, baseCohCore,
    restrCellCoh.
  rewrite 2 f_equal_eq_existT_curried.
  unshelve eapply (sigT_hex1
    (fun _: psh.(G0) 0 => tt)
    (fun d0 => ((d0; eq_refl): {d': psh.(G0) 0 &T tt = tt}))
    (psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d)).
  - unfold baseRestrFrame.
    now exact ((PCTop 0).(_pshRestrCohs psh).2
      0 Hq 0 Hr leR_refl ε ω d).
  - unfold baseRestrPainting.
    rewrite <- sigT_map_eq_id_dep_sigT.
    now exact ((STop 0).1.(_pshRestrPaintingCohs psh).2
      0 Hq 0 Hr leR_refl ε ω d).
Defined.

Lemma pshRestrCellCoh0Rot (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2):
  baseCohCore Hq Hr ε ω d
  • (eq_sym (f_equal (baseRestrFn2 (Hr ↕ Hq) ω)
       (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d))
     • eq_sym (pshFaceCell0S (Hr ↕ Hq) ω
       (psh.(GFace) 1 (1 + 0) leR_refl ε d)))
  = eq_sym (f_equal (baseRestrFn2 Hq ε)
       (pshFaceCell PC2E PCXE
          0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d))
    • (eq_sym (pshFaceCell0S Hq ε
         (psh.(GFace) 1 (0 + 0) (Hr ↕ ↑ Hq) ω d))
       • f_equal pshCell0 (psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d)).
Proof.
  now exact (hexRotate _ _ _ _ _ _
    (pshRestrCellCoh0Stored Hq Hr ε ω d)).
Defined.

Lemma baseVertexQ (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
    0 Hq ε 0 (Hr ↕ ↑ Hq) ω (pshDeepCellC C1 d)
  = f_equal (baseFace Hq ε)
      (f_equal (fun z =>
         faceAt (cohs3ChainDepsCohs2 (pChain3 C1))
           0 (Hr ↕ ↑ Hq) ω z.1 z.2)
        (pshDeepCellC C1 d)).
Proof. now reflexivity. Defined.

Lemma baseVertexR (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
    0 (Hr ↕ Hq) ω 1 (⇑ Hq) ε (pshDeepCellC C1 d)
  = f_equal (baseFace (Hr ↕ Hq) ω)
      (f_equal (fun z =>
         faceAt (cohs3ChainDepsCohs2 (pChain3 C1))
           1 (⇑ Hq) ε z.1 z.2)
        (pshDeepCellC C1 d)).
Proof. now reflexivity. Defined.

Lemma baseDeepR (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  f_equal (baseFace (Hr ↕ Hq) ω)
    (pshFaceDeep1 1 (⇑ Hq) leR_refl ε d)
  = vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
      0 (Hr ↕ Hq) ω 1 (⇑ Hq) ε (pshDeepCellC C1 d)
    • (eq_sym (f_equal (baseRestrFn2 (Hr ↕ Hq) ω)
         (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d))
       • eq_refl).
Proof.
  unfold pshFaceDeep1.
  rewrite (hexLegDeep C1 1 (⇑ Hq) leR_refl ε d).
  rewrite 2 eq_trans_map_distr.
  rewrite (baseVertexR Hq Hr ε ω d).
  unfold baseRestrFn2, baseRestrFrame, baseRestrPainting.
  cbn.
  rewrite 2 eq_trans_refl_l.
  rewrite <- eq_sym_map_distr.
  rewrite (f_equal_compose
    (faceRebuild (pChain3 C1))
    (baseFace (Hr ↕ Hq) ω)
    (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d)).
  now reflexivity.
Defined.

Lemma baseDeepQ (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  f_equal (baseFace Hq ε)
    (pshFaceDeep1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)
  = vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
      0 Hq ε 0 (Hr ↕ ↑ Hq) ω (pshDeepCellC C1 d)
    • (eq_sym (f_equal (baseRestrFn2 Hq ε)
         (pshFaceCell PC2E PCXE 0
            (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d))
       • eq_refl).
Proof.
  unfold pshFaceDeep1.
  rewrite (hexLegDeep C1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d).
  rewrite 2 eq_trans_map_distr.
  rewrite (baseVertexQ Hq Hr ε ω d).
  unfold baseRestrFn2, baseRestrFrame, baseRestrPainting.
  cbn.
  rewrite 2 eq_trans_refl_l.
  rewrite <- eq_sym_map_distr.
  rewrite (f_equal_compose
    (faceRebuild (pChain3 C1))
    (baseFace Hq ε)
    (pshFaceCell PC2E PCXE 0
       (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)).
  now reflexivity.
Defined.

Lemma baseCoreConv (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  f_equal (faceRebuild DepsCohs3ChainNil)
    (restrCellCoh (νDepsCohs3At (f psh)) 0 Hq 0 Hr ε ω
      (pshCandCell PC2E PCXE d).1
      (pshCandCell PC2E PCXE d).2)
  = baseCohCore Hq Hr ε ω d.
Proof.
  cbn [faceRebuild].
  rewrite RewLemmas.f_equal_id.
  unfold baseCohCore, PC2E, PCXE, S1, C1.
  now reflexivity.
Defined.

Lemma baseCohLeg (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  gFaceCohC (f psh) DepsCohs3ChainNil 0 0 Hq 0 Hr ε ω
    (pTopCell (STop 0) d)
  = vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
      0 Hq ε 0 (Hr ↕ ↑ Hq) ω (pshDeepCellC C1 d)
    • (baseCohCore Hq Hr ε ω d
       • eq_sym (vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
           0 (Hr ↕ Hq) ω 1 (⇑ Hq) ε (pshDeepCellC C1 d))).
Proof.
  unfold gFaceCohC.
  rewrite (hexLegHere (νExt3At (f psh)) DepsCohs3ChainNil
    0 Hq 0 Hr ε ω (pshDeepCellC C1 d)).
  rewrite (baseCoreConv Hq Hr ε ω d).
  now reflexivity.
Defined.

Lemma hexReindex2 {T: Type}
  {v0 v1 w0 w1 w2 w3 w4 w5: T}
  (m0: v0 = w0) (m1: v1 = w1)
  (B0: w0 = w1) (B1: w1 = w2) (B2: w2 = w3)
  (B3: w0 = w4) (B4: w4 = w5) (B5: w5 = w3)
  (H: B0 • (B1 • B2) = B3 • (B4 • B5)):
  (m0 • (B0 • eq_sym m1)) • ((m1 • B1) • B2)
  = ((m0 • B3) • B4) • B5.
Proof.
  now rewrite <- 5 eq_trans_assoc, eq_trans_sym_cancel_l, H.
Defined.

Lemma baseDeepRRefl (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  eq_sym (f_equal (baseRestrFn2 (Hr ↕ Hq) ω)
    (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d)) • eq_refl
  = eq_sym (f_equal (baseRestrFn2 (Hr ↕ Hq) ω)
      (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d)).
Proof. now reflexivity. Defined.

Lemma baseDeepQRefl (Hq Hr: 0 <= 0) (ε ω: arity) (d: psh.(G0) 2):
  eq_sym (f_equal (baseRestrFn2 Hq ε)
    (pshFaceCell PC2E PCXE 0
      (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)) • eq_refl
  = eq_sym (f_equal (baseRestrFn2 Hq ε)
      (pshFaceCell PC2E PCXE 0
        (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)).
Proof. now reflexivity. Defined.

Lemma pshFaceDeepCoh0 (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2):
  gFaceCohC (f psh) DepsCohs3ChainNil 0 0 Hq 0 Hr ε ω
      (pTopCell (STop 0) d)
  • (f_equal (baseFace (Hr ↕ Hq) ω)
       (pshFaceDeep1 1 (⇑ Hq) leR_refl ε d)
     • eq_sym (pshFaceCell0S (Hr ↕ Hq) ω
         (psh.(GFace) 1 (1 + 0) leR_refl ε d)))
  = (f_equal (baseFace Hq ε)
       (pshFaceDeep1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)
     • eq_sym (pshFaceCell0S Hq ε
         (psh.(GFace) 1 (0 + 0) (Hr ↕ ↑ Hq) ω d)))
    • f_equal pshCell0 (psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d).
Proof.
  rewrite (baseCohLeg Hq Hr ε ω d).
  rewrite (baseDeepR Hq Hr ε ω d).
  rewrite (baseDeepQ Hq Hr ε ω d).
  rewrite (baseDeepRRefl Hq Hr ε ω d).
  rewrite (baseDeepQRefl Hq Hr ε ω d).
  now exact_no_check (hexReindex2
    (vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
      0 Hq ε 0 (Hr ↕ ↑ Hq) ω (pshDeepCellC C1 d))
    (vertexNorm (νExt3At (f psh)) DepsCohs3ChainNil
      0 (Hr ↕ Hq) ω 1 (⇑ Hq) ε (pshDeepCellC C1 d))
    (baseCohCore Hq Hr ε ω d)
    (eq_sym (f_equal (baseRestrFn2 (Hr ↕ Hq) ω)
      (pshFaceCell PC2E PCXE 1 (⇑ Hq) leR_refl ε d)))
    (eq_sym (pshFaceCell0S (Hr ↕ Hq) ω
      (psh.(GFace) 1 (1 + 0) leR_refl ε d)))
    (eq_sym (f_equal (baseRestrFn2 Hq ε)
      (pshFaceCell PC2E PCXE 0
        (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)))
    (eq_sym (pshFaceCell0S Hq ε
      (psh.(GFace) 1 (0 + 0) (Hr ↕ ↑ Hq) ω d)))
    (f_equal pshCell0 (psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d))
    (pshRestrCellCoh0Rot Hq Hr ε ω d)).
Defined.

Lemma projCell0 {d d': psh.(G0) 0} (e: d = d'):
  f_equal (fun z: νTotal (f psh) => z.2.1) (f_equal pshCell0 e) = e.
Proof. now destruct e. Defined.

Lemma gfFaceBottom0Natural (H: 0 <= 0) (α: arity)
  {x y: νTotal (pshFrom psh 1)} (e: x = y):
  f_equal (fun z: νTotal (f psh) => z.2.1)
      (f_equal (baseFace H α) e)
    • gfFaceBottom0 0 H α y
  = gfFaceBottom0 0 H α x
    • f_equal (psh.(GFace) 0 0 H α)
        (f_equal (fun z: νTotal (pshFrom psh 1) => z.2.1) e).
Proof.
  destruct e.
  rewrite eq_trans_refl_l, eq_trans_refl_r.
  now reflexivity.
Defined.

Lemma pshFaceDeepCoh0Proj (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2):
  f_equal (fun z: νTotal (f psh) => z.2.1)
    (gFaceCohC (f psh) DepsCohs3ChainNil 0 0 Hq 0 Hr ε ω
      (pTopCell (STop 0) d))
  • (gfFaceBottom0 0 (Hr ↕ Hq) ω
       (gFaceC (f psh) DepsCohs3ChainNil 1 1 (⇑ Hq) ε
         (pTopCell (STop 0) d))
     • f_equal (psh.(GFace) 0 0 (Hr ↕ Hq) ω)
         (f_equal (fun z: νTotal (pshFrom psh 1) => z.2.1)
           (pshFaceDeep1 1 (⇑ Hq) leR_refl ε d)))
  = (gfFaceBottom0 0 Hq ε
       (gFaceC (f psh) DepsCohs3ChainNil 1 0 (Hr ↕ ↑ Hq) ω
         (pTopCell (STop 0) d))
     • f_equal (psh.(GFace) 0 0 Hq ε)
         (f_equal (fun z: νTotal (pshFrom psh 1) => z.2.1)
           (pshFaceDeep1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)))
    • psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d.
Proof.
  pose proof (pshFaceDeepCoh0 Hq Hr ε ω d) as Hc.
  apply (f_equal (fun e0: _ = _ =>
    f_equal (fun z: νTotal (f psh) => z.2.1) e0)) in Hc.
  rewrite 4 (eq_trans_map_distr
    (fun z: νTotal (f psh) => z.2.1)) in Hc.
  rewrite (pshFaceCell0SProj (Hr ↕ Hq) ω
    (psh.(GFace) 1 (1 + 0) leR_refl ε d)) in Hc.
  rewrite (pshFaceCell0SProj Hq ε
    (psh.(GFace) 1 (0 + 0) (Hr ↕ ↑ Hq) ω d)) in Hc.
  rewrite (projCell0 (psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d)) in Hc.
  rewrite (gfFaceBottom0Natural (Hr ↕ Hq) ω
    (pshFaceDeep1 1 (⇑ Hq) leR_refl ε d)) in Hc.
  rewrite (gfFaceBottom0Natural Hq ε
    (pshFaceDeep1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω d)) in Hc.
  now exact Hc.
Defined.

Lemma gfFaceCohBottom0Canonical (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2):
  f_equal (fun z: νTotal (f psh) => z.2.1)
    (gFaceCohC (f psh) DepsCohs3ChainNil 0 0 Hq 0 Hr ε ω
       (pTopCell (STop 0) d))
  • (gfFaceBottom0 0 (Hr ↕ Hq) ω
       (gFaceC (f psh) DepsCohs3ChainNil 1 1 (⇑ Hq) ε
          (pTopCell (STop 0) d))
     • f_equal (psh.(GFace) 0 0 (Hr ↕ Hq) ω)
         (gfFaceBottomGen 0
            (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil)
            1 (⇑ Hq) (⇑ Hq) ε (pTopCell (STop 0) d)))
  = (gfFaceBottom0 0 Hq ε
       (gFaceC (f psh) DepsCohs3ChainNil 1 0 (Hr ↕ ↑ Hq) ω
          (pTopCell (STop 0) d))
     • f_equal (psh.(GFace) 0 0 Hq ε)
         (gfFaceBottomGen 0
            (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil)
            0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω
            (pTopCell (STop 0) d)))
    • psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω d.
Proof.
  rewrite (gfFaceBottomDEq C1 1 (⇑ Hq) (⇑ Hq) ε
    (pTopCell (STop 0) d)).
  rewrite (gfFaceBottomDEq C1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω
    (pTopCell (STop 0) d)).
  rewrite (bottomDAt C1 1 (⇑ Hq) (⇑ Hq) (⇑ Hq) ε d).
  rewrite (bottomDAt C1 0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq)
    (Hr ↕ ↑ Hq) ω d).
  rewrite (natUIP (addComm 1 0) eq_refl), (natUIP (addComm 0 0) eq_refl).
  cbn [pshFaceDimIrr].
  rewrite 2 eq_trans_refl_r.
  now exact (pshFaceDeepCoh0Proj Hq Hr ε ω d).
Defined.

Lemma gfFaceCohBottom0At (Hq Hr: 0 <= 0) (ε ω: arity)
  (d: psh.(G0) 2) (X: gF0 (f psh) 2)
  (G: pTopCell (STop 0) d = X):
  f_equal (fun z: νTotal (f psh) => z.2.1)
    (gFaceCohC (f psh) DepsCohs3ChainNil 0 0 Hq 0 Hr ε ω X)
  • (gfFaceBottom0 0 (Hr ↕ Hq) ω
       (gFaceC (f psh) DepsCohs3ChainNil 1 1 (⇑ Hq) ε X)
     • f_equal (psh.(GFace) 0 0 (Hr ↕ Hq) ω)
         (gfFaceBottomGen 0
            (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil)
            1 (⇑ Hq) (⇑ Hq) ε X))
  = (gfFaceBottom0 0 Hq ε
       (gFaceC (f psh) DepsCohs3ChainNil 1 0 (Hr ↕ ↑ Hq) ω X)
     • f_equal (psh.(GFace) 0 0 Hq ε)
         (gfFaceBottomGen 0
            (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil)
            0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω X))
    • psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω X.2.1.
Proof.
  destruct G.
  now exact (gfFaceCohBottom0Canonical Hq Hr ε ω d).
Defined.

Lemma gfFaceCohBottom0 (Hq Hr: 0 <= 0) (ε ω: arity)
  (X: gF0 (f psh) 2):
  f_equal (fun z: νTotal (f psh) => z.2.1)
    (gFaceCohC (f psh) DepsCohs3ChainNil 0 0 Hq 0 Hr ε ω X)
  • (gfFaceBottom0 0 (Hr ↕ Hq) ω
       (gFaceC (f psh) DepsCohs3ChainNil 1 1 (⇑ Hq) ε X)
     • f_equal (psh.(GFace) 0 0 (Hr ↕ Hq) ω)
         (gfFaceBottomGen 0
            (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil)
            1 (⇑ Hq) (⇑ Hq) ε X))
  = (gfFaceBottom0 0 Hq ε
       (gFaceC (f psh) DepsCohs3ChainNil 1 0 (Hr ↕ ↑ Hq) ω X)
     • f_equal (psh.(GFace) 0 0 Hq ε)
         (gfFaceBottomGen 0
            (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil)
            0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω X))
    • psh.(GFaceCoh) 0 0 Hq 0 Hr ε ω X.2.1.
Proof.
  now exact (gfFaceCohBottom0At Hq Hr ε ω X.2.1 X
    (graphContract
      (mkPshFrame psh (towerPshDeps psh (pshTw 1))) X)).
Defined.

Lemma gfFaceEquivTop (n q: nat) (Hq: q <= n) (ε: arity)
  (x: gF0 (f psh) n.+1):
  gfF0Equiv n ((g (f psh)).(GFace) n q Hq ε x) =
  psh.(GFace) n q Hq ε (gfF0Equiv n.+1 x).
Proof.
  destruct n.
  - unfold gfF0Equiv.
    now exact (gfFaceBottom0 q Hq ε x).
  - now exact (gfFaceEquivGen 0 n 0 1 _
      (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil) n.+1
      (plusOneR n) (plusOneR n.+1) q (leR_eq_r (plusOneR n) Hq) Hq ε x).
Defined.

Lemma gfFaceCohTop (n q: nat) (Hq: q <= n) (r: nat) (Hr: r <= q)
  (ε ω: arity) (X: gF0 (f psh) n.+2):
  f_equal (gfF0Equiv n) ((g (f psh)).(GFaceCoh) n q Hq r Hr ε ω X)
  • (gfFaceEquivTop n r (Hr ↕ Hq) ω
       ((g (f psh)).(GFace) n.+1 q.+1 (⇑ Hq) ε X)
     • f_equal (psh.(GFace) n r (Hr ↕ Hq) ω)
         (gfFaceEquivTop n.+1 q.+1 (⇑ Hq) ε X))
  = (gfFaceEquivTop n q Hq ε
       ((g (f psh)).(GFace) n.+1 r (Hr ↕ ↑ Hq) ω X)
     • f_equal (psh.(GFace) n q Hq ε)
         (gfFaceEquivTop n.+1 r (Hr ↕ ↑ Hq) ω X))
    • psh.(GFaceCoh) n q Hq r Hr ε ω (gfF0Equiv n.+2 X).
Proof.
  destruct n.
  - destruct q; [| now destruct (leR_O_contra Hq)].
    destruct r; [| now destruct (leR_O_contra Hr)].
    unfold gfF0Equiv, gfFaceEquivTop.
    rewrite 2 gfFaceEquivGen0.
    now exact (gfFaceCohBottom0 Hq Hr ε ω X).
  - now exact (gfFaceCohEquivGen 0 n 0 1 _
      (chainUp1 (νExt3At (f psh)) DepsCohs3ChainNil) n.+1
      (plusOneR n) (plusOneR n.+1) (plusOneR n.+2)
      q (leR_eq_r (plusOneR n) Hq) r Hr ε ω Hq Hr (⇑ Hq) X).
Defined.

Definition gfFaceCohEquiv:
  rewFaceCoh (@faceDataPath (g (f psh)) psh gfF0Equiv gfFaceEquivTop)
    (g (f psh)).(GFaceCoh) = psh.(GFaceCoh) :=
  @faceCohEquivIntro (g (f psh)) psh
    gfF0Equiv gfFaceEquivTop gfFaceCohTop.

Definition gf: PresheafEquiv (g (f psh)) psh :=
  Build_PresheafEquiv (g (f psh)) psh
    gfF0Equiv gfFaceEquivTop gfFaceCohEquiv.

End RoundTripGF.

End PresheafRoundtrip.
