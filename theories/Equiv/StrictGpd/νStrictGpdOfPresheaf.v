(** Reconstruction of indexed strict groupoids from face presentations.
    Presheaf frames are functors, and presheaf paintings are displayed
    sections over them. The staged records follow the recursive dependencies. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT RewLemmas HSet LeSProp Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category.Groupoid Require Import Section GraphFiber.
From Bonak.Presheaf.StrictGpd Require Import Presentation.
From Bonak.Equiv.StrictGpd Require Import Tower Face.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νStrictGpdOfPresheafOn (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S).
Import A S.
Module Tower := TowerOn A S.
Import Tower.
Module Export Faces := F.
Module Export Extensionality := FaceExtensionalityOn A S F.

Local Lemma sectionLamTotal {G H: HSetGroupoid} {E: arity -> Family H}
  {F: Functor G H} (s: forall ε, Section (E ε) F) ε:
  sectionTotal (lam s) ⨟ᶠ totalMap (nth E ε) ≐ sectionTotal (s ε).
Proof.
  refine (feqWhiskerR (sectionTotalMap _) _ •ᶠ _).
  refine (feqAssoc _ _ _ •ᶠ _).
  refine (feqWhiskerL _ (nth_lam s ε) •ᶠ _).
  now apply feqSym, sectionTotalMap.
Defined.

Local Lemma sectionSigmaHead {C G H: HSetGroupoid} (E: Family H)
  (U: arity -> Functor G H) {F: Functor C G}
  (s: Section (layer E U) F) {P: Family (total (layer E U))}
  (t: Section P (sectionTotal s)) ε:
  sectionTotal (sectionSigma s t) ⨟ᶠ totalMap (layerHead E U P ε) ≐
  sectionTotal s ⨟ᶠ layerProj E U ε.
Proof.
  refine (feqWhiskerL _ (layerHeadTotal E U P ε) •ᶠ _).
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  now apply feqWhiskerR, sectionSigmaFst.
Defined.

Section Reconstruction.
Variable psh: νStrictGpdPresentation arity.

Fixpoint mkPshFrameTypes (m: nat) {p k}: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
      { _: mkPshFrameTypes m frames.1 &T Functor (psh.(G0) m) frames.2 }
  end.

Fixpoint mkPshPaintingTypes (m: nat) {p k}:
  forall {frames: mkFrameTypes p k}, mkPshFrameTypes m frames ->
  mkPaintingTypes p k frames -> Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p => fun frames pshFrames paintings =>
      { _: mkPshPaintingTypes m pshFrames.1 paintings.1 &T
        Section paintings.2 pshFrames.2 }
  end.

Class PshRestrBlock (m: nat) {p k} {frames: mkFrameTypes p k}
  (pshFrames: mkPshFrameTypes m frames) (block: RestrFrameTypeBlock p k) := {
  PshRestrTypesDef: block.(RestrFrameTypesDef) -> Type;
  PshFramesDef: forall {R} (Q: PshRestrTypesDef R),
    mkPshFrameTypes m.+1 (block.(FrameDef) R);
}.

Definition mkPshRestrTypesStep {m p k} {frames: mkFrameTypes p.+1 k}
  (pshFrames: mkPshFrameTypes m frames)
  {prev: RestrFrameTypeBlock p k.+1}
  (prevPsh: PshRestrBlock m pshFrames.1 prev)
  (R: mkRestrFrameTypesStep frames prev): Type :=
  { Q: prevPsh.(PshRestrTypesDef) R.1 &T
    forall q (Hq: q <= k) (Hqp: q + p <= m) (ε: arity),
      psh.(GFace) m (q + p) Hqp ε ⨟ᶠ pshFrames.2 ≐
      (prevPsh.(PshFramesDef) Q).2 ⨟ᶠ R.2 q Hq ε }.

Definition mkPshLayer {m p k} {frames: mkFrameTypes p.+1 k}
  {pshFrames: mkPshFrameTypes m frames}
  {paintings: mkPaintingTypes p.+1 k frames}
  (pshPaintings: mkPshPaintingTypes m pshFrames paintings)
  {prev: RestrFrameTypeBlock p k.+1}
  {prevPsh: PshRestrBlock m pshFrames.1 prev}
  {R: mkRestrFrameTypesStep frames prev}
  (Q: mkPshRestrTypesStep pshFrames prevPsh R) (Hp: p <= m):
  Section (mkLayer (paintings := paintings) R) ((prevPsh.(PshFramesDef) Q.1).2) :=
  lam (fun ε => intoPull _ _ (castBase (Q.2 0 leR_O Hp ε)
    (sectionPrecompose (psh.(GFace) m p Hp ε) pshPaintings.2))).

Lemma mkPshLayerFace {m p k} {frames: mkFrameTypes p.+1 k}
  {pshFrames: mkPshFrameTypes m frames}
  {paintings: mkPaintingTypes p.+1 k frames}
  (pshPaintings: mkPshPaintingTypes m pshFrames paintings)
  {prev: RestrFrameTypeBlock p k.+1}
  {prevPsh: PshRestrBlock m pshFrames.1 prev}
  {R: mkRestrFrameTypesStep frames prev}
  (Q: mkPshRestrTypesStep pshFrames prevPsh R) (Hp: p <= m) ε:
  sectionTotal (mkPshLayer pshPaintings Q Hp) ⨟ᶠ
    layerProj paintings.2 (fun ω => R.2 0 leR_O ω) ε ≐
  psh.(GFace) m p Hp ε ⨟ᶠ sectionTotal pshPaintings.2.
Proof.
  unfold mkPshLayer, layerProj.
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  refine (feqWhiskerR (sectionLamTotal _ ε) _ •ᶠ _).
  refine (sectionIntoPullTotal _ _ _ •ᶠ _).
  refine (sectionCastTotal _ _ •ᶠ _).
  now apply sectionPrecomposeTotal.
Defined.

Fixpoint mkPshRestrTypesAndFrames (m: nat) {p k}:
  forall (Hp: p <= m.+1)
    {frames: mkFrameTypes p k} (pshFrames: mkPshFrameTypes m frames)
    {paintings: mkPaintingTypes p k frames}
    (pshPaintings: mkPshPaintingTypes m pshFrames paintings),
  PshRestrBlock m pshFrames (mkRestrFrameTypesAndFrames paintings) :=
  match p return forall (Hp: p <= m.+1)
    (frames: mkFrameTypes p k) (pshFrames: mkPshFrameTypes m frames)
    (paintings: mkPaintingTypes p k frames)
    (pshPaintings: mkPshPaintingTypes m pshFrames paintings),
    PshRestrBlock m pshFrames (mkRestrFrameTypesAndFrames paintings) with
  | 0 => fun Hp frames pshFrames paintings pshPaintings =>
    Build_PshRestrBlock m 0 k frames pshFrames
      (mkRestrFrameTypesAndFrames paintings)
      (fun _ => unit) (fun _ _ => (tt; terminalFunctor _))
  | S p => fun Hp frames pshFrames paintings pshPaintings =>
    let prevPsh :=
      mkPshRestrTypesAndFrames m (↓ Hp) pshFrames.1 pshPaintings.1 in
    Build_PshRestrBlock m p.+1 k frames pshFrames
      (mkRestrFrameTypesAndFrames paintings)
      (fun R => mkPshRestrTypesStep pshFrames prevPsh R)
      (fun R Q => (prevPsh.(PshFramesDef) Q.1;
        sectionTotal (mkPshLayer pshPaintings Q (⇓ Hp))))
  end.

Class PshDepsRestr (m p k: nat) := {
  _pdeps: DepsRestr p k;
  _pshBound: p <= m.+1;
  _pshFrames: mkPshFrameTypes m _pdeps.(_frames);
  _pshPaintings: mkPshPaintingTypes m _pshFrames _pdeps.(_paintings);
  _pshRestrs: (mkPshRestrTypesAndFrames m _pshBound _pshFrames
    _pshPaintings).(PshRestrTypesDef) _pdeps.(_restrFrames);
}.

#[local] Instance proj1PshDepsRestr {m p k} (P: PshDepsRestr m p.+1 k):
  PshDepsRestr m p k.+1 := {|
  _pdeps := P.(_pdeps).(1)%depsrestr;
  _pshBound := ↓ P.(_pshBound);
  _pshFrames := P.(_pshFrames).1;
  _pshPaintings := P.(_pshPaintings).1;
  _pshRestrs := P.(_pshRestrs).1;
|}.

Definition mkPshFrames {m p k} (P: PshDepsRestr m p k):
  mkPshFrameTypes m.+1 (mkFrames P.(_pdeps)) :=
  (mkPshRestrTypesAndFrames m P.(_pshBound) P.(_pshFrames)
    P.(_pshPaintings)).(PshFramesDef) P.(_pshRestrs).

Definition mkPshFrame {m p k} (P: PshDepsRestr m p k):
  Functor (psh.(G0) m.+1) (mkFrame P.(_pdeps)) := (mkPshFrames P).2.

Definition mkPshFiller {m p} (P: PshDepsRestr m p 0):
  Family (mkFrame P.(_pdeps)) := graphFiber (mkPshFrame P).

Inductive PshDepsExtension (m: nat):
  forall {p k} (P: PshDepsRestr m p k),
  DepsRestrExtension p k P.(_pdeps) -> Type :=
| TopPshDep {p} {P: PshDepsRestr m p 0}:
    PshDepsExtension m P (TopRestrDep (mkPshFiller P))
| AddPshDep {p k} (P: PshDepsRestr m p.+1 k)
    {X: DepsRestrExtension p.+1 k P.(_pdeps)}:
    PshDepsExtension m P X ->
    PshDepsExtension m (proj1PshDepsRestr P) (AddRestrDep P.(_pdeps) X).
Arguments TopPshDep {m p P}.
Arguments AddPshDep {m p k} P {X} _.

Fixpoint mkPshPainting {m p k} {P: PshDepsRestr m p k}
  {X: DepsRestrExtension p k P.(_pdeps)} (PX: PshDepsExtension m P X):
  Section (mkPainting X) (mkPshFrame P) :=
  match PX with
  | TopPshDep => graphSection (mkPshFrame _)
  | AddPshDep P' PX' => sectionSigma
      (mkPshLayer P'.(_pshPaintings) P'.(_pshRestrs) (⇓ P'.(_pshBound)))
      (mkPshPainting PX')
  end.

Fixpoint mkPshPaintingsPrefix {m p k}:
  forall {P: PshDepsRestr m p k} {X: DepsRestrExtension p k P.(_pdeps)}
  (PX: PshDepsExtension m P X),
  mkPshPaintingTypes m.+1 (mkPshFrames P).1 (mkPaintingsPrefix X) :=
  match p with
  | 0 => fun _ _ _ => tt
  | S p => fun P X PX =>
      (mkPshPaintingsPrefix (AddPshDep P PX); mkPshPainting (AddPshDep P PX))
  end.

Definition mkPshPaintings {m p k} {P: PshDepsRestr m p k}
  {X: DepsRestrExtension p k P.(_pdeps)} (PX: PshDepsExtension m P X):
  mkPshPaintingTypes m.+1 (mkPshFrames P) (mkPaintings X) :=
  (mkPshPaintingsPrefix PX; mkPshPainting PX).

Lemma pshFaceDimIrr {n q q'} (e: q = q') {Hq: q <= n} {Hq': q' <= n}
  (ε: arity): psh.(GFace) n q Hq ε ≐ psh.(GFace) n q' Hq' ε.
Proof. destruct e. now apply feqRefl. Defined.

Definition mkPshRestrPaintingType {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  (restrPaintings: mkRestrPaintingTypes X): Type :=
  forall q (Hq: q <= k) (Hqp: q + p <= m) (ε: arity),
  psh.(GFace) m (q + p) Hqp ε ⨟ᶠ sectionTotal P.(_pshPaintings).2 ≐
  sectionTotal (mkPshPainting (AddPshDep P PX)) ⨟ᶠ totalMap (restrPaintings.2 q Hq ε).

Fixpoint mkPshRestrPaintingTypes {m p k}:
  forall (P: PshDepsRestr m p k) {X: DepsRestrExtension p k P.(_pdeps)}
    (PX: PshDepsExtension m P X)
    (restrPaintings: mkRestrPaintingTypes X), Type :=
  match p return forall (P: PshDepsRestr m p k)
    (X: DepsRestrExtension p k P.(_pdeps)) (PX: PshDepsExtension m P X)
    (restrPaintings: mkRestrPaintingTypes X), Type with
  | 0 => fun _ _ _ _ => unit
  | S p => fun P X PX restrPaintings =>
      { _: mkPshRestrPaintingTypes (proj1PshDepsRestr P) (AddPshDep P PX)
             restrPaintings.1 &T mkPshRestrPaintingType P PX restrPaintings }
  end.

Class PshDepsCohs (m p k: nat) := {
  _pshDeps: PshDepsRestr m p k;
  _pExtraDeps: DepsRestrExtension p k _pshDeps.(_pdeps);
  _pshExtraDeps: PshDepsExtension m _pshDeps _pExtraDeps;
  _pRestrPaintings: mkRestrPaintingTypes _pExtraDeps;
  _pshRestrPaintings: mkPshRestrPaintingTypes _pshDeps _pshExtraDeps _pRestrPaintings;
  _pCohs: mkCohFrameTypes _pRestrPaintings;
}.

Definition pshDepsCohs {m p k} (PC: PshDepsCohs m p k): DepsCohs p k := {|
  _deps := PC.(_pshDeps).(_pdeps);
  _extraDeps := PC.(_pExtraDeps);
  _restrPaintings := PC.(_pRestrPaintings);
  _cohs := PC.(_pCohs);
|}.

#[local] Instance proj1PshDepsCohs {m p k} (PC: PshDepsCohs m p.+1 k):
  PshDepsCohs m p k.+1 := {|
  _pshDeps := proj1PshDepsRestr PC.(_pshDeps);
  _pExtraDeps := (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))%extradepsrestr;
  _pshExtraDeps := AddPshDep PC.(_pshDeps) PC.(_pshExtraDeps);
  _pRestrPaintings := PC.(_pRestrPaintings).1;
  _pshRestrPaintings := PC.(_pshRestrPaintings).1;
  _pCohs := PC.(_pCohs).1;
|}.

Definition mkPshRestrFramesType {m p k} (PC: PshDepsCohs m p k): Type :=
  (mkPshRestrTypesAndFrames m.+1 (⇑ PC.(_pshDeps).(_pshBound))
    (mkPshFrames PC.(_pshDeps))
    (mkPshPaintings PC.(_pshExtraDeps))).(PshRestrTypesDef)
  (mkRestrFrames (depsCohs := pshDepsCohs PC)).

Definition mkPshFramesNext {m p k} (PC: PshDepsCohs m p k)
  (Q: mkPshRestrFramesType PC):
  mkPshFrameTypes m.+2 (mkFrames (mkDepsRestr (depsCohs := pshDepsCohs PC))) :=
  (mkPshRestrTypesAndFrames m.+1 (⇑ PC.(_pshDeps).(_pshBound))
    (mkPshFrames PC.(_pshDeps))
    (mkPshPaintings PC.(_pshExtraDeps))).(PshFramesDef) Q.

Lemma mkPshRestrFrameStepShifted {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity):
  psh.(GFace) m.+1 (q.+1 + p) Hqp ε ⨟ᶠ mkPshFrame PC.(_pshDeps) ≐
  (mkPshFramesNext (proj1PshDepsCohs PC) Q).2 ⨟ᶠ
    (mkRestrFrames (depsCohs := pshDepsCohs PC)).2 q Hq ε.
Proof.
  apply layerMapCone.
  - refine (feqAssoc _ _ _ •ᶠ _).
    refine (feqWhiskerL _ (sectionProj _) •ᶠ _).
    refine (Q.2 q.+1 (⇑ Hq) Hqp ε •ᶠ _).
    now apply feqSym, feqWhiskerR, sectionProj.
  - intro ω.
    refine (feqAssoc _ _ _ •ᶠ _).
    refine (feqWhiskerL _ (mkPshLayerFace _ _ _ ω) •ᶠ _).
    refine (feqSym (feqAssoc _ _ _) •ᶠ _).
    refine (feqWhiskerR
      (feqSym (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ω)) _ •ᶠ _).
    refine (feqAssoc _ _ _ •ᶠ _).
    refine (feqWhiskerL _ (PC.(_pshRestrPaintings).2 q Hq (⇓ Hqp) ε) •ᶠ _).
    refine (feqSym (feqAssoc _ _ _) •ᶠ _).
    apply feqWhiskerR, feqSym.
    now exact (mkPshLayerFace
      (mkPshPaintings (AddPshDep PC.(_pshDeps) PC.(_pshExtraDeps)))
      Q (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ω).
Defined.

Lemma mkPshRestrFrameStep {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity):
  psh.(GFace) m.+1 (q + p.+1) Hqp ε ⨟ᶠ mkPshFrame PC.(_pshDeps) ≐
  (mkPshFramesNext (proj1PshDepsCohs PC) Q).2 ⨟ᶠ
    (mkRestrFrames (depsCohs := pshDepsCohs PC)).2 q Hq ε.
Proof.
  refine (feqWhiskerR
    (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
      (Hq' := leR_add_shift Hqp) ε) _ •ᶠ _).
  now apply mkPshRestrFrameStepShifted.
Defined.

Fixpoint mkPshRestrFrames {m p k} (PC: PshDepsCohs m p k) {struct p}:
  mkPshRestrFramesType PC.
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    intros q Hq Hqp ε. unshelve econstructor; now intros.
  - now exact (mkPshRestrFrames m p k.+1 (proj1PshDepsCohs PC);
      mkPshRestrFrameStep PC (mkPshRestrFrames m p k.+1 (proj1PshDepsCohs PC))).
Defined.

#[local] Instance mkPshDepsRestr {m p k} (PC: PshDepsCohs m p k):
  PshDepsRestr m.+1 p.+1 k := {|
  _pdeps := mkDepsRestr (depsCohs := pshDepsCohs PC);
  _pshBound := ⇑ PC.(_pshDeps).(_pshBound);
  _pshFrames := mkPshFrames PC.(_pshDeps);
  _pshPaintings := mkPshPaintings PC.(_pshExtraDeps);
  _pshRestrs := mkPshRestrFrames PC;
|}.

Inductive PshDepsCohsExtension (m: nat):
  forall {p k} (PC: PshDepsCohs m p k),
  DepsCohsExtension p k (pshDepsCohs PC) -> Type :=
| TopPshCohDep {p} {PC: PshDepsCohs m p 0}:
    PshDepsCohsExtension m PC (TopCohDep (mkPshFiller (mkPshDepsRestr PC)))
| AddPshCohDep {p k} (PC: PshDepsCohs m p.+1 k)
    {XC: DepsCohsExtension p.+1 k (pshDepsCohs PC)}:
    PshDepsCohsExtension m PC XC ->
    PshDepsCohsExtension m (proj1PshDepsCohs PC)
      (AddCohDep (pshDepsCohs PC) XC).
Arguments TopPshCohDep {m p PC}.
Arguments AddPshCohDep {m p k} PC {XC} _.

Fixpoint mkPshExtraDeps {m p k} {PC: PshDepsCohs m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC)}
  (PCX: PshDepsCohsExtension m PC XC):
  PshDepsExtension m.+1 (mkPshDepsRestr PC) (mkExtraDeps XC) :=
  match PCX with
  | TopPshCohDep => TopPshDep
  | AddPshCohDep PC' PCX' => AddPshDep (mkPshDepsRestr PC') (mkPshExtraDeps PCX')
  end.

Fixpoint mkPshRestrPainting {m p k} {PC: PshDepsCohs m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC)}
  (PCX: PshDepsCohsExtension m PC XC) q {struct q}:
  forall (Hq: q <= k) (Hqp: q + p <= m.+1) (ε: arity),
  psh.(GFace) m.+1 (q + p) Hqp ε ⨟ᶠ sectionTotal (mkPshPainting PC.(_pshExtraDeps)) ≐
  sectionTotal (mkPshPainting (AddPshDep (mkPshDepsRestr PC) (mkPshExtraDeps PCX))) ⨟ᶠ
    totalMap ((mkRestrPaintings XC).2 q Hq ε).
Proof.
  destruct q; intros Hq Hqp ε.
  - refine (feqSym (mkPshLayerFace
      (mkPshPaintings PC.(_pshExtraDeps)) (mkPshRestrFrames PC) Hqp ε) •ᶠ _).
    now apply feqSym, sectionSigmaHead.
  - destruct PCX as [| p' k' PC' XC' PCX'].
    + now destruct (leR_O_contra Hq).
    + refine (feqWhiskerL _ (sectionSigmaTotal _ _) •ᶠ _).
      refine (feqSym (feqAssoc _ _ _) •ᶠ _).
      refine (_ •ᶠ feqSym (sectionSigmaMap _ _ _ _)).
      apply feqWhiskerR.
      refine (feqWhiskerR
        (pshFaceDimIrr (plus_n_Sm q p')
          (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε) _ •ᶠ _).
      now exact (mkPshRestrPainting m p'.+1 k' PC' XC' PCX' q (⇓ Hq)
        (leR_eq (plus_n_Sm q p') Hqp) ε).
Defined.

Fixpoint mkPshRestrPaintingsPrefix {m p k}:
  forall {PC: PshDepsCohs m p k}
    {XC: DepsCohsExtension p k (pshDepsCohs PC)}
    (PCX: PshDepsCohsExtension m PC XC),
  mkPshRestrPaintingTypes (proj1PshDepsRestr (mkPshDepsRestr PC))
    (AddPshDep (mkPshDepsRestr PC) (mkPshExtraDeps PCX))
    (mkRestrPaintingsPrefix XC) :=
  match p return forall (PC: PshDepsCohs m p k)
    (XC: DepsCohsExtension p k (pshDepsCohs PC))
    (PCX: PshDepsCohsExtension m PC XC),
    mkPshRestrPaintingTypes (proj1PshDepsRestr (mkPshDepsRestr PC))
      (AddPshDep (mkPshDepsRestr PC) (mkPshExtraDeps PCX))
      (mkRestrPaintingsPrefix XC) with
  | 0 => fun _ _ _ => tt
  | S p => fun PC XC PCX =>
      (mkPshRestrPaintingsPrefix (AddPshCohDep PC PCX);
       mkPshRestrPainting (AddPshCohDep PC PCX))
  end.

Definition mkPshRestrPaintings {m p k} {PC: PshDepsCohs m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC)}
  (PCX: PshDepsCohsExtension m PC XC):
  mkPshRestrPaintingTypes (mkPshDepsRestr PC) (mkPshExtraDeps PCX)
    (mkRestrPaintings XC) :=
  (mkPshRestrPaintingsPrefix PCX; mkPshRestrPainting PCX).

Inductive PshCohsChain {m P K} (PCTop: PshDepsCohs m P K):
  forall {p k}, PshDepsCohs m p k -> Type :=
| PshCohsChainNil: PshCohsChain PCTop PCTop
| PshCohsChainCons {p k} {PC: PshDepsCohs m p.+1 k}:
    PshCohsChain PCTop PC -> PshCohsChain PCTop (proj1PshDepsCohs PC).
Arguments PshCohsChainNil {m P K PCTop}.
Arguments PshCohsChainCons {m P K PCTop p k PC} _.

Fixpoint pshCohsChainCohs {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC):
  DepsCohsChain (pshDepsCohs PCTop) (pshDepsCohs PC) :=
  match C with
  | PshCohsChainNil => DepsCohsChainNil
  | PshCohsChainCons C' => DepsCohsChainCons (pshCohsChainCohs C')
  end.

Lemma pshGetFrame {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC):
  mkPshFrame (mkPshDepsRestr PCTop) ⨟ᶠ getFrame (cohsChainNext (pshCohsChainCohs C)) ≐
  mkPshFrame (mkPshDepsRestr PC).
Proof.
  induction C.
  - unshelve econstructor; now intros.
  - refine (feqSym (feqAssoc _ _ _) •ᶠ _).
    refine (feqWhiskerR IHC _ •ᶠ _).
    now apply sectionProj.
Defined.

Lemma pshGetPainting {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC):
  sectionTotal (mkPshPainting PC.(_pshExtraDeps)) ⨟ᶠ
    getPainting (cohsChainExt (pshCohsChainCohs C)) ≐
  sectionTotal (mkPshPainting PCTop.(_pshExtraDeps)).
Proof.
  induction C.
  - unshelve econstructor; now intros.
  - refine (feqSym (feqAssoc _ _ _) •ᶠ _).
    refine (feqWhiskerR (sectionSigmaAssoc _ _) _ •ᶠ _).
    now exact IHC.
Defined.

Lemma pshνFace {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC)
  (Hp: p <= m.+1) (ε: arity):
  mkPshFrame (mkPshDepsRestr PCTop) ⨟ᶠ νFace (pshCohsChainCohs C) ε ≐
  psh.(GFace) m.+1 p Hp ε ⨟ᶠ sectionTotal (mkPshPainting PCTop.(_pshExtraDeps)).
Proof.
  unfold νFace.
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  refine (feqWhiskerR (feqSym (feqAssoc _ _ _)) _ •ᶠ _).
  refine (feqWhiskerR (feqWhiskerR (pshGetFrame C) _) _ •ᶠ _).
  refine (feqWhiskerR
    (mkPshLayerFace (mkPshPaintings PC.(_pshExtraDeps))
      (mkPshRestrFrames PC) Hp ε) _ •ᶠ _).
  refine (feqAssoc _ _ _ •ᶠ _).
  now apply feqWhiskerL, pshGetPainting.
Defined.

Class PshTower (m: nat) (X: (νStrictGpdAt m.+1).(prefix)) := {
  _twFrames: mkPshFrameTypes m (νTowerDeps X).(_frames);
  _twPaintings: mkPshPaintingTypes m _twFrames (νTowerDeps X).(_paintings);
  _twRestrs: (mkPshRestrTypesAndFrames m leR_refl _twFrames
    _twPaintings).(PshRestrTypesDef) (νTowerDeps X).(_restrFrames);
}.

Definition towerPshDeps {m X} (T: PshTower m X): PshDepsRestr m m.+1 0 := {|
  _pdeps := νTowerDeps X;
  _pshBound := leR_refl;
  _pshFrames := T.(_twFrames);
  _pshPaintings := T.(_twPaintings);
  _pshRestrs := T.(_twRestrs);
|}.

(** Naturality of painting restrictions at the candidate extension,
    carried alongside the tower state. *)

Definition PshTowerRestrPaintings {m X} (T: PshTower m X): Type :=
  mkPshRestrPaintingTypes (towerPshDeps T) TopPshDep
    (((νStrictGpdAt m.+1).(data) X).(restrPaintings)
      (mkPshFiller (towerPshDeps T))).

Definition towerPshDepsCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T): PshDepsCohs m m.+1 0 := {|
  _pshDeps := towerPshDeps T;
  _pExtraDeps := TopRestrDep (mkPshFiller (towerPshDeps T));
  _pshExtraDeps := TopPshDep;
  _pRestrPaintings := ((νStrictGpdAt m.+1).(data) X).(restrPaintings)
    (mkPshFiller (towerPshDeps T));
  _pshRestrPaintings := rp;
  _pCohs := ((νStrictGpdAt m.+1).(data) X).(cohFrames)
    (mkPshFiller (towerPshDeps T));
|}.

(** Extend the reconstructed frame, painting, and restriction data at
    the candidate filler, following [mkνStrictGpdData]. *)

Definition towerStep {m X} (T: PshTower m X) (rp: PshTowerRestrPaintings T):
  PshTower m.+1 (X; mkPshFiller (towerPshDeps T)) :=
  Build_PshTower m.+1 (X; mkPshFiller (towerPshDeps T))
    (mkPshFrames (towerPshDeps T))
    (mkPshPaintings (TopPshDep (P := towerPshDeps T)))
    (mkPshRestrFrames (towerPshDepsCohs T rp)).

Definition towerStepRestrPaintings {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T):
  PshTowerRestrPaintings (towerStep T rp) :=
  mkPshRestrPaintings (TopPshCohDep (PC := towerPshDepsCohs T rp)).

(** At level 0, the candidate filler pairs a point with an
    identification in the [unit] frame. The level-1 state consists of
    [unit] prefixes and constant frame maps. *)

Definition pshFiller0: Family unitGroupoid := graphFiber (terminalFunctor (psh.(G0) 0)).

Definition tower1: PshTower 0 (tt; pshFiller0).
Proof.
  unshelve esplit.
  - now exact (tt; terminalFunctor _).
  - now exact (tt; graphSection (terminalFunctor _)).
  - unshelve esplit. now exact tt.
    intros q Hq Hqp ε. unshelve econstructor; now intros.
Defined.

Definition tower1RestrPaintings: PshTowerRestrPaintings tower1.
Proof.
  unshelve esplit.
  - now exact tt.
  - intros q Hq Hqp ε. destruct q.
    + refine (feqSym (mkPshLayerFace
        (towerPshDeps tower1).(_pshPaintings)
        (towerPshDeps tower1).(_pshRestrs) leR_O ε) •ᶠ _).
      now apply feqSym, sectionSigmaHead.
    + now destruct (leR_O_contra Hq).
Defined.

(** Closing the tower

    [pshChain] recursively pairs each prefix with the state that produces
    its next extension. Its bonding equations hold by conversion, so
    [this] and [next] of the resulting tower compute to the candidate
    filler and to the tower one level up. *)

Definition PshState (l: nat): (νStrictGpdAt l).(prefix) -> Type :=
  match l with
  | 0 => fun _ => unit
  | l.+1 => fun X => {T: PshTower l X &T PshTowerRestrPaintings T}
  end.

Definition pshExtend (l: nat):
  forall (X: (νStrictGpdAt l).(prefix)), PshState l X ->
  {E: mkExtensionType X &T PshState l.+1 (X; E)} :=
  match l return forall X: (νStrictGpdAt l).(prefix), PshState l X ->
    {E: mkExtensionType X &T PshState l.+1 (X; E)} with
  | 0 => fun X =>
    match X as X0 return PshState 0 X0 ->
      {E: mkExtensionType (X0: (νStrictGpdAt 0).(prefix)) &T
       PshState 1 ((X0: (νStrictGpdAt 0).(prefix)); E)} with
    | tt => fun _ => (pshFiller0; (tower1; tower1RestrPaintings))
    end
  | l.+1 => fun X s => (mkPshFiller (towerPshDeps s.1);
      (towerStep s.1 s.2; towerStepRestrPaintings s.1 s.2))
  end.

Fixpoint pshChain (l: nat): {X: (νStrictGpdAt l).(prefix) &T PshState l X} :=
  match l with
  | 0 => (tt; tt)
  | l.+1 =>
    let s := pshChain l in
    let e := pshExtend l s.1 s.2 in
    ((s.1; e.1); e.2)
  end.

Definition pshApprox (l: nat): (νStrictGpdAt l).(prefix) := (pshChain l).1.

Definition pshTw (m: nat): PshTower m (pshApprox m.+1) := (pshChain m.+1).2.1.

Definition pshTwRp (m: nat): PshTowerRestrPaintings (pshTw m) :=
  (pshChain m.+1).2.2.

(** [pshApprox] is definitionally coherent, so its bonding proof is
    reflexivity. *)

Definition pshFrom (n: nat): νStrictGpdFrom n (pshApprox n) :=
  ofChain (T := νStrictGpdTel) pshApprox (fun _ => eq_refl) n.

Definition f: νStrictGpds := pshFrom 0.

End Reconstruction.
Arguments PshCohsChainNil {psh m P K PCTop}.
Arguments PshCohsChainCons {psh m P K PCTop p k PC} _.
End νStrictGpdOfPresheafOn.

Module νStrictGpdOfPresheaf (A: LayerSig).
Module Base := νStrictGpd.νStrictGpd A.
Module FaceOperations := FaceOn A Base.
Include νStrictGpdOfPresheafOn A Base FaceOperations.
End νStrictGpdOfPresheaf.

Module Type ReconstructionSig (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S).
Include νStrictGpdOfPresheafOn A S F.
End ReconstructionSig.

Module νStrictGpdOfPresheafSimplicial :=
  νStrictGpdOfPresheafOn SimplicialLayer νStrictGpdSimplicial FaceSimplicial.
Module νStrictGpdOfPresheafCubical :=
  νStrictGpdOfPresheafOn CubicalLayer νStrictGpdCubical FaceCubical.
