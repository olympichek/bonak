(** The translation theory of νGpds: staged translation data between two
    towers, from which the equivalence one level up is rebuilt by
    construction.

    Two towers are levelwise equivalent when their stored frames and
    paintings correspond stage by stage. That correspondence is carried as
    data: equivalences between the two towers' frames and paintings, the
    paths stating that they commute with the two towers' restriction
    operations, and, one truncation level up from the set-level theory,
    the 2-cells stating that those paths commute with the stored frame
    coherences. From these a third instantiation of the block pattern of
    [νGpd] rebuilds the equivalence one level up: the frame translations
    are equivalences by construction, each stage a [sigTEquiv]/[layerEquiv]
    composite of the stage below and the stored painting equivalences.

    Sides: [A] is the target of the translations, [B] the source; frame
    translations go [B -> A] ([eqvFun] of the stored equivalences), and so
    do the painting equivalences, fibrewise over them. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Limit νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd.
From Bonak.Lib Require Import Equiv.
From Bonak.Equiv.Gpd Require Import PresheafOfνGpd PathAlgebra.

Set Primitive Projections.
Set Keyed Unification.

Module νGpdEquiv (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A).
Import A.

Module Export PresheafOfνGpd := Base.

(** Lifting equivalences through the layer former

    The layer counterpart of [sigTEquiv]: a layer is a weak product, so
    pointwise equivalences of its components lift to an equivalence of
    layers, with [ext] from the layer interface proving both inverse laws. *)

Definition layerEquiv {B C: arity -> HGpd}
  (e: forall ε, Equiv (B ε) (C ε)): Equiv (Layer B) (Layer C).
Proof.
  unshelve refine (qinvEquiv (lmap (fun ε => (e ε).(eqvFun)))
    (lmap (fun ε => invEq (e ε))) _ _).
  - intro l. apply ext; intro ε. rewrite 2 nth_lmap. now apply retEq.
  - intro l. apply ext; intro ε. rewrite 2 nth_lmap. now apply secEq.
Defined.

Lemma layerEquivNth {B C: arity -> HGpd} (e: forall ε, Equiv (B ε) (C ε))
  (l: Layer B) (ε: arity): nth (layerEquiv e l) ε = e ε (nth l ε).
Proof.
  now exact (nth_lmap (fun ε => (e ε).(eqvFun)) l ε).
Defined.

(** Equivalence lists over two towers of dependencies *)

Fixpoint mkFrameEqvTypes {p k}:
  mkFrameTypes p k -> mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p => fun framesA framesB =>
      { _: mkFrameEqvTypes framesA.1 framesB.1 &T
        Equiv framesB.2 framesA.2 }
  end.

Fixpoint mkPaintingEqvTypes {p k}:
  forall {framesA framesB: mkFrameTypes p k},
  mkFrameEqvTypes framesA framesB ->
  mkPaintingTypes p k framesA -> mkPaintingTypes p k framesB -> Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p => fun framesA framesB eqvs paintingsA paintingsB =>
      { _: mkPaintingEqvTypes eqvs.1 paintingsA.1 paintingsB.1 &T
        forall d: framesB.2,
          Equiv (paintingsB.2 d) (paintingsA.2 (eqvs.2 d)) }
  end.

(** The translation block

    The types of the translation coherences at stages <= p (the frame
    equivalences commute with the two towers' restrictions), together
    with the next-level frame equivalences they determine. The two
    definitions are mutually dependent, so [mkTrRestrTypesAndFrames]
    constructs them together. *)

Class TrRestrBlock {p k} {framesA framesB: mkFrameTypes p k}
  (eqvs: mkFrameEqvTypes framesA framesB)
  (blockA blockB: RestrFrameTypeBlock p k) := {
  TrRestrTypesDef: blockA.(RestrFrameTypesDef) ->
    blockB.(RestrFrameTypesDef) -> Type;
  FrameEqvDef: forall {RA RB} (Q: TrRestrTypesDef RA RB),
    mkFrameEqvTypes (blockA.(FrameDef) RA) (blockB.(FrameDef) RB);
}.

Definition mkTrRestrTypesStep {p k} {framesA framesB: mkFrameTypes p.+1 k}
  (eqvs: mkFrameEqvTypes framesA framesB)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  (prevTr: TrRestrBlock eqvs.1 prevA prevB)
  (RA: mkRestrFrameTypesStep framesA prevA)
  (RB: mkRestrFrameTypesStep framesB prevB): Type :=
  { Q: prevTr.(TrRestrTypesDef) RA.1 RB.1 &T
    forall q (Hq: q <= k) (ε: arity) (d: (prevB.(FrameDef) RB.1).2),
      eqvs.2 (RB.2 q Hq ε d) =
      RA.2 q Hq ε ((prevTr.(FrameEqvDef) Q).2 d) }.

(** The layer equivalence: componentwise, the stored painting equivalence
    followed by transport along the diagonal translation coherence *)

Definition mkTrLayerEquiv {p k} {framesA framesB: mkFrameTypes p.+1 k}
  {eqvs: mkFrameEqvTypes framesA framesB}
  {paintingsA: mkPaintingTypes p.+1 k framesA}
  {paintingsB: mkPaintingTypes p.+1 k framesB}
  (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  {prevTr: TrRestrBlock eqvs.1 prevA prevB}
  {RA: mkRestrFrameTypesStep framesA prevA}
  {RB: mkRestrFrameTypesStep framesB prevB}
  (Q: mkTrRestrTypesStep eqvs prevTr RA RB)
  (d: (prevB.(FrameDef) RB.1).2):
  Equiv (mkLayer RB.2 (painting := paintingsB.2) d)
    (mkLayer RA.2 (painting := paintingsA.2)
      ((prevTr.(FrameEqvDef) Q.1).2 d)) :=
  layerEquiv (fun ε => compEquiv
    (pEqvs.2 (RB.2 0 leR_O ε d))
    (rewEquiv (fun x => paintingsA.2 x) (Q.2 0 leR_O ε d))).

Fixpoint mkTrRestrTypesAndFrames {p k}:
  forall {framesA framesB: mkFrameTypes p k}
    (eqvs: mkFrameEqvTypes framesA framesB)
    {paintingsA: mkPaintingTypes p k framesA}
    {paintingsB: mkPaintingTypes p k framesB}
    (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB),
  TrRestrBlock eqvs (mkRestrFrameTypesAndFrames paintingsA)
    (mkRestrFrameTypesAndFrames paintingsB) :=
  match p return forall (framesA framesB: mkFrameTypes p k)
    (eqvs: mkFrameEqvTypes framesA framesB)
    (paintingsA: mkPaintingTypes p k framesA)
    (paintingsB: mkPaintingTypes p k framesB)
    (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB),
    TrRestrBlock eqvs (mkRestrFrameTypesAndFrames paintingsA)
      (mkRestrFrameTypesAndFrames paintingsB) with
  | 0 => fun framesA framesB eqvs paintingsA paintingsB pEqvs =>
      Build_TrRestrBlock 0 k framesA framesB eqvs
        (mkRestrFrameTypesAndFrames paintingsA)
        (mkRestrFrameTypesAndFrames paintingsB)
        (fun _ _ => unit)
        (fun _ _ _ => (tt; idEquiv))
  | S p => fun framesA framesB eqvs paintingsA paintingsB pEqvs =>
      let prevTr := mkTrRestrTypesAndFrames eqvs.1 pEqvs.1 in
      Build_TrRestrBlock p.+1 k framesA framesB eqvs
        (mkRestrFrameTypesAndFrames paintingsA)
        (mkRestrFrameTypesAndFrames paintingsB)
        (fun RA RB => mkTrRestrTypesStep eqvs prevTr RA RB)
        (fun RA RB Q =>
          (prevTr.(FrameEqvDef) Q.1;
           sigTEquiv ((prevTr.(FrameEqvDef) Q.1).2)
             (fun d => mkTrLayerEquiv pEqvs Q d)))
  end.

(** The translation-equipped pair of dependencies *)

Class TrDepsRestr (p k: nat) := {
  _depsA: DepsRestr p k;
  _depsB: DepsRestr p k;
  _frameEqvs: mkFrameEqvTypes _depsA.(_frames) _depsB.(_frames);
  _paintingEqvs: mkPaintingEqvTypes _frameEqvs
    _depsA.(_paintings) _depsB.(_paintings);
  _trRestrs: (mkTrRestrTypesAndFrames _frameEqvs
    _paintingEqvs).(TrRestrTypesDef)
    _depsA.(_restrFrames) _depsB.(_restrFrames);
}.

#[local]
Instance proj1TrDepsRestr {p k} (T: TrDepsRestr p.+1 k): TrDepsRestr p k.+1 :=
{|
  _depsA := T.(_depsA).(1);
  _depsB := T.(_depsB).(1);
  _frameEqvs := T.(_frameEqvs).1;
  _paintingEqvs := T.(_paintingEqvs).1;
  _trRestrs := T.(_trRestrs).1;
|}.

(** The computed next-level frame equivalences; their [eqvFun] is the
    frame translation one level up. *)

Definition mkFrameEqvs {p k} (T: TrDepsRestr p k):
  mkFrameEqvTypes (mkFrames T.(_depsA)) (mkFrames T.(_depsB)) :=
  (mkTrRestrTypesAndFrames T.(_frameEqvs)
    T.(_paintingEqvs)).(FrameEqvDef) T.(_trRestrs).

Definition mkFrameEqv {p k} (T: TrDepsRestr p k):
  Equiv (mkFrame T.(_depsB)) (mkFrame T.(_depsA)) := (mkFrameEqvs T).2.

(** The extension layer: relating the two towers' painting extensions

    At the top, an equivalence between the fillers, fibrewise over the
    frame translation. *)

Inductive TrDepsExtension:
  forall {p k} (T: TrDepsRestr p k),
  DepsRestrExtension p k T.(_depsA) ->
  DepsRestrExtension p k T.(_depsB) -> Type :=
| TopTrDep {p} {T: TrDepsRestr p 0}
    {EA: mkFrame T.(_depsA) -> HGpd} {EB: mkFrame T.(_depsB) -> HGpd}
    (fillerEqvs: forall d: mkFrame T.(_depsB),
      Equiv (EB d) (EA (mkFrameEqv T d))):
    TrDepsExtension T (TopRestrDep EA) (TopRestrDep EB)
| AddTrDep {p k} (T: TrDepsRestr p.+1 k)
    {XA: DepsRestrExtension p.+1 k T.(_depsA)}
    {XB: DepsRestrExtension p.+1 k T.(_depsB)}:
    TrDepsExtension T XA XB ->
    TrDepsExtension (proj1TrDepsRestr T)
      (AddRestrDep T.(_depsA) XA) (AddRestrDep T.(_depsB) XB).

Arguments TopTrDep {p T EA EB} _.
Arguments AddTrDep {p k} T {XA XB} _.

(** The painting equivalences over the frame translation, corresponding to
    [mkPainting]: the filler equivalence at the top, a
    [sigTEquiv]-composite of the layer equivalence and the recursive one
    below. Each case has the constructor structure used by [mkPainting]. *)

Fixpoint mkPaintingEqv {p k} {T: TrDepsRestr p k}
  {XA: DepsRestrExtension p k T.(_depsA)}
  {XB: DepsRestrExtension p k T.(_depsB)}
  (TX: TrDepsExtension T XA XB):
  forall d: mkFrame T.(_depsB),
  Equiv (mkPainting XB d) (mkPainting XA (mkFrameEqv T d)) :=
  match TX with
  | TopTrDep fillerEqvs => fun d => fillerEqvs d
  | AddTrDep T' TX' => fun d =>
      sigTEquiv (mkTrLayerEquiv T'.(_paintingEqvs) T'.(_trRestrs) d)
        (fun l => mkPaintingEqv TX' (d; l))
  end.

Fixpoint mkPaintingEqvsPrefix {p k}:
  forall {T: TrDepsRestr p k}
    {XA: DepsRestrExtension p k T.(_depsA)}
    {XB: DepsRestrExtension p k T.(_depsB)}
    (TX: TrDepsExtension T XA XB),
  mkPaintingEqvTypes (mkFrameEqvs T).1
    (mkPaintingsPrefix XA) (mkPaintingsPrefix XB) :=
  match p with
  | 0 => fun _ _ _ _ => tt
  | S p => fun T XA XB TX =>
      (mkPaintingEqvsPrefix (AddTrDep T TX);
       mkPaintingEqv (AddTrDep T TX))
  end.

Definition mkPaintingEqvs {p k} {T: TrDepsRestr p k}
  {XA: DepsRestrExtension p k T.(_depsA)}
  {XB: DepsRestrExtension p k T.(_depsB)}
  (TX: TrDepsExtension T XA XB):
  mkPaintingEqvTypes (mkFrameEqvs T) (mkPaintings XA) (mkPaintings XB) :=
  (mkPaintingEqvsPrefix TX; mkPaintingEqv TX).

(** Translation coherence data for [DepsCohs]

    The remaining translation data: the paths stating that the painting
    equivalences commute with the two towers' restr paintings
    ([mkTrRestrPaintingType]), and, one truncation level up, the 2-cells
    stating that the frame commutations commute with the two towers'
    coherence frames ([mkTrCohType]). The latter are what the set-level
    theory discharged by [UIP] in [mkTrRestrLayer]; here they are stored
    stage by stage, in a block mirroring [CohFrameTypeBlock], because the
    2-cell at a stage is stated over the next-level commutations already
    built at the stages below. *)

Definition mkTrRestrPaintingType {p k} (T: TrDepsRestr p.+1 k)
  {XA: DepsRestrExtension p.+1 k T.(_depsA)}
  {XB: DepsRestrExtension p.+1 k T.(_depsB)}
  (TX: TrDepsExtension T XA XB)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB): Type :=
  forall q (Hq: q <= k) (ε: arity) (d: mkFrame T.(_depsB).(1))
    (c: (mkPaintings (T.(_depsB); XB)).2 d),
  rew [T.(_depsA).(_paintings).2] T.(_trRestrs).2 q Hq ε d in
    T.(_paintingEqvs).2 (T.(_depsB).(_restrFrames).2 q Hq ε d)
      (rpB.2 q Hq ε d c) =
  rpA.2 q Hq ε (mkFrameEqv (proj1TrDepsRestr T) d)
    (mkPaintingEqv (AddTrDep T TX) d c).

Fixpoint mkTrRestrPaintingTypes {p k}:
  forall (T: TrDepsRestr p k)
    {XA: DepsRestrExtension p k T.(_depsA)}
    {XB: DepsRestrExtension p k T.(_depsB)}
    (TX: TrDepsExtension T XA XB)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB), Type :=
  match p return forall (T: TrDepsRestr p k)
    (XA: DepsRestrExtension p k T.(_depsA))
    (XB: DepsRestrExtension p k T.(_depsB))
    (TX: TrDepsExtension T XA XB)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB), Type with
  | 0 => fun _ _ _ _ _ _ => unit
  | S p => fun T XA XB TX rpA rpB =>
      { _: mkTrRestrPaintingTypes (proj1TrDepsRestr T) (AddTrDep T TX)
             rpA.1 rpB.1 &T
        mkTrRestrPaintingType T TX rpA rpB }
  end.

Lemma trLayerEqvNth {p k} {framesA framesB: mkFrameTypes p.+1 k}
  {eqvs: mkFrameEqvTypes framesA framesB}
  {paintingsA: mkPaintingTypes p.+1 k framesA}
  {paintingsB: mkPaintingTypes p.+1 k framesB}
  (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  {prevTr: TrRestrBlock eqvs.1 prevA prevB}
  {RA: mkRestrFrameTypesStep framesA prevA}
  {RB: mkRestrFrameTypesStep framesB prevB}
  (Q: mkTrRestrTypesStep eqvs prevTr RA RB)
  (d: (prevB.(FrameDef) RB.1).2)
  (l: mkLayer RB.2 (painting := paintingsB.2) d) (ω: arity):
  nth (mkTrLayerEquiv pEqvs Q d l) ω =
  compEquiv (pEqvs.2 (RB.2 0 leR_O ω d))
    (rewEquiv (fun x => paintingsA.2 x) (Q.2 0 leR_O ω d))
    (nth l ω).
Proof.
  now exact (layerEquivNth _ l ω).
Defined.

Class TrDepsCohsBase (p k: nat) := {
  _trDeps: TrDepsRestr p k;
  _tExtA: DepsRestrExtension p k _trDeps.(_depsA);
  _tExtB: DepsRestrExtension p k _trDeps.(_depsB);
  _trExt: TrDepsExtension _trDeps _tExtA _tExtB;
  _tRpA: mkRestrPaintingTypes _tExtA;
  _tRpB: mkRestrPaintingTypes _tExtB;
  _trRestrPaintings: mkTrRestrPaintingTypes _trDeps _trExt _tRpA _tRpB;
  _tCohsA: mkCohFrameTypes _tRpA;
  _tCohsB: mkCohFrameTypes _tRpB;
}.

Definition trDepsCohsA {p k} (TC: TrDepsCohsBase p k): DepsCohs p k := {|
  _deps := TC.(_trDeps).(_depsA);
  _extraDeps := TC.(_tExtA);
  _restrPaintings := TC.(_tRpA);
  _cohs := TC.(_tCohsA);
|}.

Definition trDepsCohsB {p k} (TC: TrDepsCohsBase p k): DepsCohs p k := {|
  _deps := TC.(_trDeps).(_depsB);
  _extraDeps := TC.(_tExtB);
  _restrPaintings := TC.(_tRpB);
  _cohs := TC.(_tCohsB);
|}.

#[local]
Instance proj1TrDepsCohsBase {p k} (TC: TrDepsCohsBase p.+1 k):
  TrDepsCohsBase p k.+1 :=
{|
  _trDeps := proj1TrDepsRestr TC.(_trDeps);
  _tExtA := (TC.(_trDeps).(_depsA); TC.(_tExtA))%extradepsrestr;
  _tExtB := (TC.(_trDeps).(_depsB); TC.(_tExtB))%extradepsrestr;
  _trExt := AddTrDep TC.(_trDeps) TC.(_trExt);
  _tRpA := TC.(_tRpA).1;
  _tRpB := TC.(_tRpB).1;
  _trRestrPaintings := TC.(_trRestrPaintings).1;
  _tCohsA := TC.(_tCohsA).1;
  _tCohsB := TC.(_tCohsB).1;
|}.

Definition mkTrRestrFramesType {p k} (TC: TrDepsCohsBase p k): Type :=
  (mkTrRestrTypesAndFrames (mkFrameEqvs TC.(_trDeps))
    (mkPaintingEqvs TC.(_trExt))).(TrRestrTypesDef)
  (mkRestrFrames (depsCohs := trDepsCohsA TC))
  (mkRestrFrames (depsCohs := trDepsCohsB TC)).

Definition mkTrFrameEqvsNext {p k} (TC: TrDepsCohsBase p k)
  (Q: mkTrRestrFramesType TC):
  mkFrameEqvTypes (mkFrames (mkDepsRestr (depsCohs := trDepsCohsA TC)))
    (mkFrames (mkDepsRestr (depsCohs := trDepsCohsB TC))) :=
  (mkTrRestrTypesAndFrames (mkFrameEqvs TC.(_trDeps))
    (mkPaintingEqvs TC.(_trExt))).(FrameEqvDef) Q.

(** The next-level translation data determined by a stage of [Q]: the
    frame equivalence at the stage below is read off its prefix. *)
Definition mkTrDepsRestrOf {p k} (TC: TrDepsCohsBase p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohsBase TC)): TrDepsRestr p.+1 k.+1 := {|
  _depsA := mkDepsRestr (depsCohs := trDepsCohsA (proj1TrDepsCohsBase TC));
  _depsB := mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC));
  _frameEqvs := mkFrameEqvs (proj1TrDepsCohsBase TC).(_trDeps);
  _paintingEqvs := mkPaintingEqvs (proj1TrDepsCohsBase TC).(_trExt);
  _trRestrs := Q;
|}.

Definition mkTrCohType {p k} (TC: TrDepsCohsBase p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohsBase TC)): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
    (d: mkFrame (mkDepsRestr
      (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).(1)),
  f_equal (fun x => TC.(_trDeps).(_frameEqvs).2 x)
    (TC.(_tCohsB).2 q Hq r Hr ε ω d)
  • (TC.(_trDeps).(_trRestrs).2 r (Hr ↕ Hq) ω
       ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).2
          q.+1 (⇑ Hq) ε d)
     • f_equal (fun x => TC.(_trDeps).(_depsA).(_restrFrames).2 r (Hr ↕ Hq) ω x)
         (Q.2 q.+1 (⇑ Hq) ε d))
  = TC.(_trDeps).(_trRestrs).2 q Hq ε
      ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).2
         r (Hr ↕ ↑ Hq) ω d)
    • (f_equal (fun x => TC.(_trDeps).(_depsA).(_restrFrames).2 q Hq ε x)
         (Q.2 r (Hr ↕ ↑ Hq) ω d)
       • TC.(_tCohsA).2 q Hq r Hr ε ω
           ((mkFrameEqvs (proj1TrDepsRestr (mkTrDepsRestrOf TC Q))).2 d)).

Lemma mkTrRestrLayer {p k} (TC: TrDepsCohsBase p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohsBase TC))
  (HC: mkTrCohType TC Q)
  (q: nat) (Hq: q <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC)))):
  rew [mkLayer TC.(_trDeps).(_depsA).(_restrFrames).2]
      (Q.2 q.+1 (⇑ Hq) ε d.1) in
    mkTrLayerEquiv TC.(_trDeps).(_paintingEqvs) TC.(_trDeps).(_trRestrs)
      ((mkRestrFrames
         (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).2 q.+1 (⇑ Hq) ε d.1)
      (mkRestrLayer TC.(_tRpB).2 TC.(_tCohsB).2 q Hq ε d.1 d.2)
  = mkRestrLayer TC.(_tRpA).2 TC.(_tCohsA).2 q Hq ε
      ((mkTrFrameEqvsNext (proj1TrDepsCohsBase TC) Q).2 d).1
      ((mkTrFrameEqvsNext (proj1TrDepsCohsBase TC) Q).2 d).2.
Proof.
  unfold mkRestrLayer.
  apply (lmap2_rew_eq
    (P := fun x => TC.(_trDeps).(_depsA).(_paintings).2 x)
    (rf0 := fun a x => TC.(_trDeps).(_depsA).(_restrFrames).2 0 leR_O a x));
    intros ω a.
  eapply (rew_cohLayer_hex
    (P := fun x => TC.(_trDeps).(_depsA).(_paintings).2 x)
    (rf0 := fun x => TC.(_trDeps).(_depsA).(_restrFrames).2 0 leR_O ω x)
    (F := fun m c => TC.(_trDeps).(_paintingEqvs).2 m c)
    (G := fun n c => TC.(_tRpA).2 q Hq ε n c)).
  - now exact (TC.(_trRestrPaintings).2 q Hq ε
      ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).2
         0 leR_O ω d.1) a).
  - now exact (HC q Hq 0 leR_O ε ω d.1).
Defined.

Lemma mkTrRestrFrameStep {p k} (TC: TrDepsCohsBase p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohsBase TC))
  (HC: mkTrCohType TC Q)
  (q: nat) (Hq: q <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC)))):
  mkFrameEqv TC.(_trDeps)
    ((mkRestrFrames (depsCohs := trDepsCohsB TC)).2 q Hq ε d) =
  (mkRestrFrames (depsCohs := trDepsCohsA TC)).2 q Hq ε
    ((mkTrFrameEqvsNext (proj1TrDepsCohsBase TC) Q).2 d).
Proof.
  unshelve eapply eq_existT_curried.
  - now exact (Q.2 q.+1 (⇑ Hq) ε d.1).
  - now exact (mkTrRestrLayer TC Q HC q Hq ε d).
Defined.

Class TrCohBlock {p k} (TC: TrDepsCohsBase p k) := {
  TrCohTypesDef: Type;
  TrRestrFramesDef: TrCohTypesDef -> mkTrRestrFramesType TC;
}.

Fixpoint mkTrCohTypesAndRestrFrames {p k}:
  forall TC: TrDepsCohsBase p k, TrCohBlock TC :=
  match p return forall TC: TrDepsCohsBase p k, TrCohBlock TC with
  | 0 => fun TC => {|
      TrCohTypesDef := unit;
      TrRestrFramesDef _ := (tt; fun q Hq ε d => eq_refl)
    |}
  | S p => fun TC =>
      let prev := mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase TC) in
      {|
        TrCohTypesDef :=
          { Q: prev.(TrCohTypesDef) &T mkTrCohType TC (prev.(TrRestrFramesDef) Q) };
        TrRestrFramesDef Q :=
          (prev.(TrRestrFramesDef) Q.1;
           mkTrRestrFrameStep TC (prev.(TrRestrFramesDef) Q.1) Q.2)
      |}
  end.

Definition mkTrCohTypes {p k} (TC: TrDepsCohsBase p k): Type :=
  (mkTrCohTypesAndRestrFrames TC).(TrCohTypesDef).

Class TrDepsCohs (p k: nat) := {
  _trBase: TrDepsCohsBase p k;
  _trCohs: mkTrCohTypes _trBase;
}.

Definition mkTrRestrFrames {p k} (TC: TrDepsCohs p k):
  mkTrRestrFramesType TC.(_trBase) :=
  (mkTrCohTypesAndRestrFrames TC.(_trBase)).(TrRestrFramesDef) TC.(_trCohs).

#[local]
Instance proj1TrDepsCohs {p k} (TC: TrDepsCohs p.+1 k): TrDepsCohs p k.+1 :=
{|
  _trBase := proj1TrDepsCohsBase TC.(_trBase);
  _trCohs := TC.(_trCohs).1;
|}.

#[local]
Instance mkTrDepsRestr {p k} (TC: TrDepsCohs p k): TrDepsRestr p.+1 k := {|
  _depsA := mkDepsRestr (depsCohs := trDepsCohsA TC.(_trBase));
  _depsB := mkDepsRestr (depsCohs := trDepsCohsB TC.(_trBase));
  _frameEqvs := mkFrameEqvs TC.(_trBase).(_trDeps);
  _paintingEqvs := mkPaintingEqvs TC.(_trBase).(_trExt);
  _trRestrs := mkTrRestrFrames TC;
|}.

(** Translation data for [DepsCohsExtension] one level up *)

Inductive TrDepsCohsExtension:
  forall {p k} (TC: TrDepsCohs p k),
  DepsCohsExtension p k (trDepsCohsA TC.(_trBase)) ->
  DepsCohsExtension p k (trDepsCohsB TC.(_trBase)) -> Type :=
| TopTrCohDep {p} {TC: TrDepsCohs p 0}
    {EA: mkFrame (mkDepsRestr (depsCohs := trDepsCohsA TC.(_trBase))) -> HGpd}
    {EB: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB TC.(_trBase))) -> HGpd}
    (fillerEqvs: forall d,
      Equiv (EB d) (EA (mkFrameEqv (mkTrDepsRestr TC) d))):
    TrDepsCohsExtension TC (TopCohDep EA) (TopCohDep EB)
| AddTrCohDep {p k} (TC: TrDepsCohs p.+1 k)
    {XCA: DepsCohsExtension p.+1 k (trDepsCohsA TC.(_trBase))}
    {XCB: DepsCohsExtension p.+1 k (trDepsCohsB TC.(_trBase))}:
    TrDepsCohsExtension TC XCA XCB ->
    TrDepsCohsExtension (proj1TrDepsCohs TC)
      (AddCohDep (trDepsCohsA TC.(_trBase)) XCA)
      (AddCohDep (trDepsCohsB TC.(_trBase)) XCB).

Arguments TopTrCohDep {p TC EA EB} _.
Arguments AddTrCohDep {p k} TC {XCA XCB} _.

Fixpoint mkTrExtraDeps {p k} {TC: TrDepsCohs p k}
  {XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase))}
  {XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase))}
  (TCX: TrDepsCohsExtension TC XCA XCB):
  TrDepsExtension (mkTrDepsRestr TC) (mkExtraDeps XCA) (mkExtraDeps XCB) :=
  match TCX with
  | TopTrCohDep fillerEqvs => TopTrDep fillerEqvs
  | AddTrCohDep TC' TCX' =>
      AddTrDep (mkTrDepsRestr TC') (mkTrExtraDeps TCX')
  end.

(** The next-level restr-painting commutations

    The definition follows [mkRestrPainting] by recursion on the offset [q]. At
    [q = 0] both sides are the diagonal layer component; at [q.+1] the
    pair decomposes into the layer case and the recursive call one stage
    up, with identical transport paths on both sides, so the two match
    directly. *)

Fixpoint mkTrRestrPainting {p k} {TC: TrDepsCohs p k}
  {XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase))}
  {XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase))}
  (TCX: TrDepsCohsExtension TC XCA XCB) q {struct q}:
  forall (Hq: q <= k) (ε: arity)
    (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB TC.(_trBase))).(1))
    (c: (mkPaintings ((mkDepsRestr (depsCohs := trDepsCohsB TC.(_trBase)));
           mkExtraDeps XCB)).2 d),
  rew [(mkDepsRestr (depsCohs := trDepsCohsA TC.(_trBase))).(_paintings).2]
      (mkTrRestrFrames TC).2 q Hq ε d in
    mkPaintingEqv TC.(_trBase).(_trExt)
      ((mkDepsRestr (depsCohs := trDepsCohsB TC.(_trBase))).(_restrFrames).2
         q Hq ε d)
      ((mkRestrPaintings XCB).2 q Hq ε d c) =
  (mkRestrPaintings XCA).2 q Hq ε
    (mkFrameEqv (proj1TrDepsRestr (mkTrDepsRestr TC)) d)
    (mkPaintingEqv (AddTrDep (mkTrDepsRestr TC) (mkTrExtraDeps TCX)) d c).
Proof.
  destruct q; intros.
  - now exact (eq_sym
      (trLayerEqvNth (mkPaintingEqvs TC.(_trBase).(_trExt)) (mkTrRestrFrames TC)
        d c.1 ε)).
  - destruct TCX as [| p' k' TC' XCA' XCB' TCX'].
    + now destruct (leR_O_contra Hq).
    + unshelve eapply (eq_existT_curried_dep
        (Q := mkPainting TC'.(_trBase).(_tExtA))).
      * now exact (mkTrRestrLayer TC'.(_trBase)
          (mkTrRestrFrames (proj1TrDepsCohs TC')) TC'.(_trCohs).2
          q (⇓ Hq) ε (d; c.1)).
      * now exact (mkTrRestrPainting p'.+1 k' TC' XCA' XCB' TCX' q (⇓ Hq) ε
          (d; c.1) c.2).
Defined.

Fixpoint mkTrRestrPaintingsPrefix {p k}:
  forall {TC: TrDepsCohs p k}
    {XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase))}
    {XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase))}
    (TCX: TrDepsCohsExtension TC XCA XCB),
  mkTrRestrPaintingTypes (proj1TrDepsRestr (mkTrDepsRestr TC))
    (AddTrDep (mkTrDepsRestr TC) (mkTrExtraDeps TCX))
    (mkRestrPaintingsPrefix XCA) (mkRestrPaintingsPrefix XCB) :=
  match p return forall (TC: TrDepsCohs p k)
    (XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase)))
    (XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase)))
    (TCX: TrDepsCohsExtension TC XCA XCB),
    mkTrRestrPaintingTypes (proj1TrDepsRestr (mkTrDepsRestr TC))
      (AddTrDep (mkTrDepsRestr TC) (mkTrExtraDeps TCX))
      (mkRestrPaintingsPrefix XCA) (mkRestrPaintingsPrefix XCB) with
  | 0 => fun _ _ _ _ => tt
  | S p => fun TC XCA XCB TCX =>
      (mkTrRestrPaintingsPrefix (AddTrCohDep TC TCX);
       mkTrRestrPainting (AddTrCohDep TC TCX))
  end.

Definition mkTrRestrPaintings {p k} {TC: TrDepsCohs p k}
  {XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase))}
  {XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase))}
  (TCX: TrDepsCohsExtension TC XCA XCB):
  mkTrRestrPaintingTypes (mkTrDepsRestr TC) (mkTrExtraDeps TCX)
    (mkRestrPaintings XCA) (mkRestrPaintings XCB) :=
  (mkTrRestrPaintingsPrefix TCX; mkTrRestrPainting TCX).

Class TrDepsCohs2Base (p k: nat) := {
  _trCohsL: TrDepsCohs p k;
  _tXCA: DepsCohsExtension p k (trDepsCohsA _trCohsL.(_trBase));
  _tXCB: DepsCohsExtension p k (trDepsCohsB _trCohsL.(_trBase));
  _trCX: TrDepsCohsExtension _trCohsL _tXCA _tXCB;
  _tCpA: mkCohPaintingTypes _tXCA;
  _tCpB: mkCohPaintingTypes _tXCB;
  _tC2A: mkCoh2FrameTypes _tCpA;
  _tC2B: mkCoh2FrameTypes _tCpB;
}.

Definition trDepsCohs2A {p k} (TC2: TrDepsCohs2Base p k): DepsCohs2 p k := {|
  _depsCohs := trDepsCohsA TC2.(_trCohsL).(_trBase);
  _extraDepsCohs := TC2.(_tXCA);
  _cohPaintings := TC2.(_tCpA);
  _coh2Frames := TC2.(_tC2A);
|}.

Definition trDepsCohs2B {p k} (TC2: TrDepsCohs2Base p k): DepsCohs2 p k := {|
  _depsCohs := trDepsCohsB TC2.(_trCohsL).(_trBase);
  _extraDepsCohs := TC2.(_tXCB);
  _cohPaintings := TC2.(_tCpB);
  _coh2Frames := TC2.(_tC2B);
|}.

#[local]
Instance proj1TrDepsCohs2Base {p k} (TC2: TrDepsCohs2Base p.+1 k):
  TrDepsCohs2Base p k.+1 := {|
  _trCohsL := proj1TrDepsCohs TC2.(_trCohsL);
  _tXCA := AddCohDep _ TC2.(_tXCA);
  _tXCB := AddCohDep _ TC2.(_tXCB);
  _trCX := AddTrCohDep TC2.(_trCohsL) TC2.(_trCX);
  _tCpA := TC2.(_tCpA).1;
  _tCpB := TC2.(_tCpB).1;
  _tC2A := TC2.(_tC2A).1;
  _tC2B := TC2.(_tC2B).1;
|}.

Definition mkTrDepsCohsBase {p k} (TC2: TrDepsCohs2Base p k):
  TrDepsCohsBase p.+1 k := {|
  _trDeps := mkTrDepsRestr TC2.(_trCohsL);
  _tExtA := mkExtraDeps TC2.(_tXCA);
  _tExtB := mkExtraDeps TC2.(_tXCB);
  _trExt := mkTrExtraDeps TC2.(_trCX);
  _tRpA := mkRestrPaintings TC2.(_tXCA);
  _tRpB := mkRestrPaintings TC2.(_tXCB);
  _trRestrPaintings := mkTrRestrPaintings TC2.(_trCX);
  _tCohsA := mkCohFrames TC2.(_tCpA) TC2.(_tC2A);
  _tCohsB := mkCohFrames TC2.(_tCpB) TC2.(_tC2B);
|}.

(** The part of [TrDepsCohs2Base] the stored painting 2-cells depend on:
    everything but the two towers' [coh2Frames]. Stating the clause over
    it lets the stage recursion of [mkTrCohPainting] refine its data
    through the constructor of [TrDepsCohs2Extension]. *)
Class TrDepsCohs2Core (p k: nat) := {
  _cTrCohsL: TrDepsCohs p k;
  _cXCA: DepsCohsExtension p k (trDepsCohsA _cTrCohsL.(_trBase));
  _cXCB: DepsCohsExtension p k (trDepsCohsB _cTrCohsL.(_trBase));
  _cTrCX: TrDepsCohsExtension _cTrCohsL _cXCA _cXCB;
  _cCpA: mkCohPaintingTypes _cXCA;
  _cCpB: mkCohPaintingTypes _cXCB;
}.

Definition coreOf {p k} (TC2: TrDepsCohs2Base p k): TrDepsCohs2Core p k := {|
  _cTrCohsL := TC2.(_trCohsL); _cXCA := TC2.(_tXCA); _cXCB := TC2.(_tXCB);
  _cTrCX := TC2.(_trCX); _cCpA := TC2.(_tCpA); _cCpB := TC2.(_tCpB);
|}.



(** The translation coherence data for [DepsCohs2]

    The 2-cells stating that the painting commutations
    ([mkTrRestrPaintingType]) commute with the two towers' painting
    coherences: the painting-level hexagon over the stored frame 2-cell
    [mkTrCohType]. It is the last stored translation datum; the frame
    3-cell it sits over is a proposition by [GUIP]. *)

Definition mkTrCohPaintingType {p k} (C: TrDepsCohs2Core p.+1 k): Type :=
  let TCB := C.(_cTrCohsL).(_trBase) in
  let TR1 := mkTrDepsRestr (proj1TrDepsCohs C.(_cTrCohsL)) in
  let RPA := mkRestrPaintings (trDepsCohsA TCB; C.(_cXCA))%extradepscohs in
  let RPB := mkRestrPaintings (trDepsCohsB TCB; C.(_cXCB))%extradepscohs in
  let TRP := mkTrRestrPaintings (AddTrCohDep C.(_cTrCohsL) C.(_cTrCX)) in
  let FE := (mkFrameEqvs (proj1TrDepsRestr TR1)).2 in
  let PE := (mkPaintingEqvs (AddTrDep TR1
    (mkTrExtraDeps (AddTrCohDep C.(_cTrCohsL) C.(_cTrCX))))).2 in
  let PA := fun x => GDom (TCB.(_trDeps).(_depsA).(_paintings).2 x) in
  forall q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
    (d: mkFrame (mkDepsRestr
      (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TCB))).(1))
    (c: (mkPaintings (mkDepsRestr;
      mkExtraDeps (trDepsCohsB TCB; C.(_cXCB))%extradepscohs)%extradepsrestr).2 d),
  rew [fun π: TCB.(_trDeps).(_frameEqvs).2
         (TCB.(_trDeps).(_depsB).(_restrFrames).2 q Hq ε
           (TR1.(_depsB).(_restrFrames).2 r (Hr ↕ ↑ Hq) ω d))
       = TCB.(_trDeps).(_depsA).(_restrFrames).2 r (Hr ↕ Hq) ω
           (TR1.(_depsA).(_restrFrames).2 q.+1 (⇑ Hq) ε
             (FE d)) =>
       rew [PA] π in
       TCB.(_trDeps).(_paintingEqvs).2 _
         (TCB.(_tRpB).2 q Hq ε _ (RPB.2 r (Hr ↕ ↑ Hq) ω d c))
       = TCB.(_tRpA).2 r (Hr ↕ Hq) ω _
           (RPA.2 q.+1 (⇑ Hq) ε _
             (PE d c))]
    C.(_cTrCohsL).(_trCohs).2 q Hq r Hr ε ω d in
  (sigT_map_eq (Q := PA) (fun y c => TCB.(_trDeps).(_paintingEqvs).2 y c)
     (C.(_cCpB).2 q Hq r Hr ε ω d c)
   ⊙[PA] (TCB.(_trRestrPaintings).2 r (Hr ↕ Hq) ω
            (TR1.(_depsB).(_restrFrames).2 q.+1 (⇑ Hq) ε d)
            (RPB.2 q.+1 (⇑ Hq) ε d c)
          ⊙[PA] sigT_map_eq (Q := PA) (fun y c => TCB.(_tRpA).2 r (Hr ↕ Hq) ω y c)
                  (TRP.2 q.+1 (⇑ Hq) ε d c)))
  = TCB.(_trRestrPaintings).2 q Hq ε
      (TR1.(_depsB).(_restrFrames).2 r (Hr ↕ ↑ Hq) ω d)
      (RPB.2 r (Hr ↕ ↑ Hq) ω d c)
    ⊙[PA] (sigT_map_eq (Q := PA) (fun y c => TCB.(_tRpA).2 q Hq ε y c)
             (TRP.2 r (Hr ↕ ↑ Hq) ω d c)
           ⊙[PA] C.(_cCpA).2 q Hq r Hr ε ω
                   (FE d)
                   (PE d c)).

Fixpoint mkTrCohPaintingTypes {p k}: forall (TC2: TrDepsCohs2Base p k), Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun TC2 =>
    { R: mkTrCohPaintingTypes (proj1TrDepsCohs2Base TC2) &T
         mkTrCohPaintingType (coreOf TC2) }
  end.

(** The layer 2-cell of the next stage: the translation hexagon of layers,
    reduced pointwise to the permutohedral lemma [rew_coh2Layer_perm4],
    whose two content premises are the stored painting hexagon and the
    frame 3-cell by [GUIP]. *)
Definition mkTrCohLayerType {p k} (TC2: TrDepsCohs2Base p.+1 k)
  (Q: mkTrCohTypes (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))
  q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).(1).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).(1).(_restrFrames).2
    (painting := (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).(1).(_paintings).2) d): Type :=
  rew [fun r0 : mkFrameEqv (proj1TrDepsRestr TC2.(_trCohsL).(_trBase).(_trDeps)) ((mkTrDepsRestr TC2.(_trCohsL)).(_depsB).(_restrFrames).2 q Hq ε ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).2 r (Hr ↕ ↑ Hq) ω (d; l))).1 = (mkRestrFrames (depsCohs := trDepsCohsA (proj1TrDepsCohsBase TC2.(_trCohsL).(_trBase)))).2 r.+1 (⇑ (Hr ↕ Hq)) ω ((mkRestrFrames (depsCohs := trDepsCohsA (proj1TrDepsCohsBase (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2))))).2 q.+2 (⇑ (⇑ Hq)) ε (sigTEquiv ((mkTrRestrTypesAndFrames ((mkTrRestrTypesAndFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_frameEqvs).1 (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_paintingEqvs).1).(FrameEqvDef) (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_trRestrs).1).1 (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1.1).(FrameEqvDef) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1).1).2 (fun d0 => mkTrLayerEquiv (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1 ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) d0) (d; l)).1) => rew [fun t : mkFrame (proj1TrDepsRestr TC2.(_trCohsL).(_trBase).(_trDeps)).(_depsA) => mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 t] r0 in mkTrLayerEquiv TC2.(_trCohsL).(_trBase).(_trDeps).(_paintingEqvs) TC2.(_trCohsL).(_trBase).(_trDeps).(_trRestrs) ((mkTrDepsRestr TC2.(_trCohsL)).(_depsB).(_restrFrames).2 q Hq ε ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).2 r (Hr ↕ ↑ Hq) ω (d; l))).1 (mkRestrLayer (trDepsCohsB TC2.(_trCohsL).(_trBase)).(_restrPaintings).2 (trDepsCohsB TC2.(_trCohsL).(_trBase)).(_cohs).2 q Hq ε ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).2 r (Hr ↕ ↑ Hq) ω (d; l)).1 ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).2 r (Hr ↕ ↑ Hq) ω (d; l)).2) = mkRestrLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_restrPaintings).2 (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_cohs).2 r (Hr ↕ Hq) ω ((mkRestrFrames (depsCohs := trDepsCohsA (proj1TrDepsCohsBase (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2))))).2 q.+2 (⇑ (⇑ Hq)) ε (sigTEquiv ((mkTrRestrTypesAndFrames ((mkTrRestrTypesAndFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_frameEqvs).1 (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_paintingEqvs).1).(FrameEqvDef) (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_trRestrs).1).1 (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1.1).(FrameEqvDef) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1).1).2 (fun d0 => mkTrLayerEquiv (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1 ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) d0) (d; l)).1) (mkRestrLayer (trDepsCohsA (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2))).(_restrPaintings).2 (trDepsCohsA (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2))).(_cohs).2 q.+1 (⇑ Hq) ε (sigTEquiv ((mkTrRestrTypesAndFrames ((mkTrRestrTypesAndFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_frameEqvs).1 (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_paintingEqvs).1).(FrameEqvDef) (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_trRestrs).1).1 (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1.1).(FrameEqvDef) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1).1).2 (fun d0 => mkTrLayerEquiv (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1 ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) d0) (d; l)).1 (sigTEquiv ((mkTrRestrTypesAndFrames ((mkTrRestrTypesAndFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_frameEqvs).1 (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_paintingEqvs).1).(FrameEqvDef) (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trDeps).(_trRestrs).1).1 (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1.1).(FrameEqvDef) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1).1).2 (fun d0 => mkTrLayerEquiv (mkPaintingEqvs (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)).(_trExt)).1 ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) d0) (d; l)).2)] Q.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d in (sigT_map_eq (Q := fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)) (fun (a : mkFrame (proj1TrDepsRestr TC2.(_trCohsL).(_trBase).(_trDeps)).(_depsB)) (b : mkLayer TC2.(_trCohsL).(_trBase).(_trDeps).(_depsB).(_restrFrames).2 a) => mkTrLayerEquiv TC2.(_trCohsL).(_trBase).(_trDeps).(_paintingEqvs) TC2.(_trCohsL).(_trBase).(_trDeps).(_trRestrs) a b) (mkCohLayer TC2.(_tCpB).2 TC2.(_tC2B).2 q Hq r Hr ε ω d l) ⊙[fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)] (mkTrRestrLayer TC2.(_trCohsL).(_trBase) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase TC2.(_trCohsL).(_trBase))).(TrRestrFramesDef) TC2.(_trCohsL).(_trCohs).1) TC2.(_trCohsL).(_trCohs).2 r (Hr ↕ Hq) ω ((mkRestrFrames (depsCohs := trDepsCohsB (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).2 q.+1 (⇑ Hq) ε (d; l)) ⊙[fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)] sigT_map_eq (Q := fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)) (mkRestrLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_restrPaintings).2 (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_cohs).2 r (Hr ↕ Hq) ω) (mkTrRestrLayer (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2 q.+1 (⇑ Hq) ε (d; l)))) = mkTrRestrLayer TC2.(_trCohsL).(_trBase) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase TC2.(_trCohsL).(_trBase))).(TrRestrFramesDef) TC2.(_trCohsL).(_trCohs).1) TC2.(_trCohsL).(_trCohs).2 q Hq ε ((mkRestrFrames (depsCohs := trDepsCohsB (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).2 r (Hr ↕ ↑ Hq) ω (d; l)) ⊙[fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)] (sigT_map_eq (Q := fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)) (mkRestrLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_restrPaintings).2 (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_cohs).2 q Hq ε) (mkTrRestrLayer (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2 r (Hr ↕ ↑ Hq) ω (d; l)) ⊙[fun x => GDom (mkLayer (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_deps).(_restrFrames).2 x)] mkCohLayer TC2.(_tCpA).2 TC2.(_tC2A).2 q Hq r Hr ε ω (sigTEquiv ((mkTrRestrTypesAndFrames (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_frameEqvs).1 (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_paintingEqvs).1).(FrameEqvDef) (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_trRestrs).1).2 (fun d0 : ((mkRestrFrameTypesAndFrames (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_depsB).(_paintings).1).(FrameDef) (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_depsB).(_restrFrames).1).2 => mkTrLayerEquiv (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_paintingEqvs) (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_trRestrs) d0) (d; l)).1 (sigTEquiv ((mkTrRestrTypesAndFrames (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_frameEqvs).1 (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_paintingEqvs).1).(FrameEqvDef) (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_trRestrs).1).2 (fun d0 : ((mkRestrFrameTypesAndFrames (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_depsB).(_paintings).1).(FrameDef) (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_depsB).(_restrFrames).1).2 => mkTrLayerEquiv (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_paintingEqvs) (proj1TrDepsRestr (mkTrDepsRestrOf (mkTrDepsCohsBase TC2) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1; mkTrRestrFrameStep (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)) ((mkTrCohTypesAndRestrFrames (proj1TrDepsCohsBase (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))).(TrRestrFramesDef) Q.1) Q.2))).(_trRestrs) d0) (d; l)).2).

Lemma mkTrCohLayer {p k} (TC2: TrDepsCohs2Base p.+1 k)
  (Q: mkTrCohTypes (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))
  (trCohPainting: mkTrCohPaintingType (coreOf TC2))
  q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).(1).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).(1).(_restrFrames).2
    (painting := (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase (mkTrDepsCohsBase TC2)))).(1).(_paintings).2) d):
  mkTrCohLayerType TC2 Q q Hq r Hr ε ω d l.
Proof.
    unfold mkTrCohLayerType.
  eapply (lmap2_hex_rew_eq
      (P := fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_paintings).2 x)
      (rf0 := fun a x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_restrFrames).2 0 leR_O a x)
      (SA := fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsB).(_paintings).2 x)
      (ufA := fun a x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsB).(_restrFrames).2 0 leR_O a x)
      (SB := fun x => (mkDepsCohs (trDepsCohs2A TC2)).(1).(_deps).(_paintings).2 x)
      (ufB := fun a x => (mkDepsCohs (trDepsCohs2A TC2)).(1).(_deps).(_restrFrames).2 0 leR_O a x)
      (NA := fun dd ω0 c => rew [fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_paintings).2 x] TC2.(_trCohsL).(_trBase).(_trDeps).(_trRestrs).2 0 leR_O ω0 dd in TC2.(_trCohsL).(_trBase).(_trDeps).(_paintingEqvs).2 _ c)
      (NB := fun dd ω0 c => rew [fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_paintings).2 x] TC2.(_trCohsL).(_trBase).(_tCohsA).2 r (Hr ↕ Hq) 0 leR_O ω ω0 dd in TC2.(_trCohsL).(_trBase).(_tRpA).2 r (Hr ↕ Hq) ω _ c)
      (NC := fun dd ω0 c => rew [fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_paintings).2 x] TC2.(_trCohsL).(_trBase).(_tCohsA).2 q Hq 0 leR_O ε ω0 dd in TC2.(_trCohsL).(_trBase).(_tRpA).2 q Hq ε _ c)).
    intro ζ; unfold lmap2_hex_pointwise.
    eapply (Lemmas.rew_coh2Layer_perm4
      (S0 := fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_paintings).2 x)
      (rf0 := fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_restrFrames).2 0 leR_O ζ x)
      (SY := fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsB).(_paintings).2 x)
      (uf0 := fun x => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsB).(_restrFrames).2 0 leR_O ζ x)
      (S1 := fun x => (mkDepsCohs (trDepsCohs2A TC2)).(1).(_deps).(_paintings).2 x)
      (ufB := fun x => (mkDepsCohs (trDepsCohs2A TC2)).(1).(_deps).(_restrFrames).2 0 leR_O ζ x)
      (ufC := fun x => (mkDepsCohs (trDepsCohs2A TC2)).(1).(_deps).(_restrFrames).2 0 leR_O ζ x)
      (S2A := fun x => (mkDepsCohs (trDepsCohs2B TC2)).(1).(_deps).(_paintings).2 x)
      (S2C := fun x => (mkPaintings
          (mkDepsRestr (depsCohs := (trDepsCohs2A TC2).(_depsCohs).(1));
           mkExtraDeps ((trDepsCohs2A TC2).(_depsCohs); (trDepsCohs2A TC2).(_extraDepsCohs)))).2 x)
      (fA := mkFrameEqv (proj1TrDepsRestr TC2.(_trCohsL).(_trBase).(_trDeps)))
      (fB := ((mkCohFrameTypesAndRestrFrames (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_restrPaintings).1).(RestrFramesDef) (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_cohs).1).2 r.+1 (⇑ (Hr ↕ Hq)) ω)
      (fC := ((mkCohFrameTypesAndRestrFrames (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_restrPaintings).1).(RestrFramesDef) (trDepsCohsA TC2.(_trCohsL).(_trBase)).(_cohs).1).2 q.+1 (⇑ Hq) ε)
      (Rq1 := fun z c => (mkTrDepsRestr TC2.(_trCohsL)).(_paintingEqvs).1.2 z c)
      (rfq := fun y => TC2.(_trCohsL).(_trBase).(_trDeps).(_frameEqvs).2 y)
      (rfs := fun y => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_restrFrames).2 r (Hr ↕ Hq) ω y)
      (rfr := fun y => TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_restrFrames).2 q Hq ε y)
      (Fq := fun y c => TC2.(_trCohsL).(_trBase).(_trDeps).(_paintingEqvs).2 y c)
      (Fs := fun y c => TC2.(_trCohsL).(_trBase).(_tRpA).2 r (Hr ↕ Hq) ω y c)
      (Fr := fun y c => TC2.(_trCohsL).(_trBase).(_tRpA).2 q Hq ε y c)
      (gq := fun dd => TC2.(_trCohsL).(_trBase).(_trDeps).(_trRestrs).2 0 leR_O ζ dd)
      (gs := fun dd => TC2.(_trCohsL).(_trBase).(_tCohsA).2 r (Hr ↕ Hq) 0 leR_O ω ζ dd)
      (gr := fun dd => TC2.(_trCohsL).(_trBase).(_tCohsA).2 q Hq 0 leR_O ε ζ dd)).
    2: now apply TC2.(_trCohsL).(_trBase).(_trDeps).(_depsA).(_frames).2.(GUIP).
    Unshelve.
    2: now exact (TC2.(_trCohsL).(_trCohs).2 q Hq r Hr ε ω _).
    now exact (trCohPainting q Hq r Hr ε ω _ (nth l ζ)).
Defined.

(** The frame 2-cell of the next stage: the stage below contributes the
    frame part, [mkTrCohLayer] the layer part. *)
Lemma mkTrCohStep {p k} (TC2: TrDepsCohs2Base p.+1 k)
  (Q: mkTrCohTypes (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2)))
  (trCohPainting: mkTrCohPaintingType (coreOf TC2)):
  mkTrCohType (mkTrDepsCohsBase TC2)
    ((mkTrCohTypesAndRestrFrames
       (mkTrDepsCohsBase (proj1TrDepsCohs2Base TC2))).(TrRestrFramesDef) Q).
Proof.
  intros q Hq r Hr ε ω d.
  unfold mkTrRestrFrameStep.
  cbn [mkTrDepsCohsBase _trDeps _trRestrs _tCohsA _tCohsB _frameEqvs
    mkTrDepsRestr mkTrRestrFrames mkTrCohTypesAndRestrFrames TrRestrFramesDef
    mkCohFrames mkCoh2FrameTypesAndCohFrames CohFramesDef mkFrameEqvs
    mkTrRestrTypesAndFrames FrameEqvDef projT1 projT2].
  unshelve eapply (Lemmas.eq_existT_curried_hex
    (mkFrameEqv (proj1TrDepsRestr TC2.(_trCohsL).(_trBase).(_trDeps)))
    (fun a b => mkTrLayerEquiv TC2.(_trCohsL).(_trBase).(_trDeps).(_paintingEqvs)
      TC2.(_trCohsL).(_trBase).(_trDeps).(_trRestrs) a b) _ _ _ _).
  - now exact (Q.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d.1).
  - now exact (mkTrCohLayer TC2 Q trCohPainting q Hq r Hr ε ω d.1 d.2).
Defined.

Fixpoint mkTrCohs {p k} (TC2: TrDepsCohs2Base p k)
  (trCohPaintings: mkTrCohPaintingTypes TC2):
  mkTrCohTypes (mkTrDepsCohsBase TC2).
Proof.
  destruct p.
  - unshelve esplit.
    + now exact tt.
    + intros q Hq r Hr ε ω d. now trivial.
  - now exact (mkTrCohs p k.+1 (proj1TrDepsCohs2Base TC2) trCohPaintings.1;
      mkTrCohStep TC2 _ trCohPaintings.2).
Defined.

(** The translation data for [DepsCohs2], and the level above it *)

Class TrDepsCohs2 (p k: nat) := {
  _trCohs2Base: TrDepsCohs2Base p k;
  _trCohPaintings: mkTrCohPaintingTypes _trCohs2Base;
}.

#[local]
Instance mkTrDepsCohs {p k} (TC2: TrDepsCohs2 p k): TrDepsCohs p.+1 k := {|
  _trBase := mkTrDepsCohsBase TC2.(_trCohs2Base);
  _trCohs := mkTrCohs TC2.(_trCohs2Base) TC2.(_trCohPaintings);
|}.

#[local]
Instance proj1TrDepsCohs2 {p k} (TC2: TrDepsCohs2 p.+1 k):
  TrDepsCohs2 p k.+1 :=
{|
  _trCohs2Base := proj1TrDepsCohs2Base TC2.(_trCohs2Base);
  _trCohPaintings := TC2.(_trCohPaintings).1;
|}.

(** Translation data for [DepsCohs2Extension] one level up: the filler
    equivalences at the top, over the frame equivalence of the level just
    built. *)

Inductive TrDepsCohs2Extension:
  forall {p k} (TC2: TrDepsCohs2 p k),
  DepsCohs2Extension p k (trDepsCohs2A TC2.(_trCohs2Base)) ->
  DepsCohs2Extension p k (trDepsCohs2B TC2.(_trCohs2Base)) -> Type :=
| TopTrCoh2Dep {p} {TC2: TrDepsCohs2 p 0}
    {EA: mkFrame (mkDepsRestr
      (depsCohs := mkDepsCohs (trDepsCohs2A TC2.(_trCohs2Base)))) -> HGpd}
    {EB: mkFrame (mkDepsRestr
      (depsCohs := mkDepsCohs (trDepsCohs2B TC2.(_trCohs2Base)))) -> HGpd}
    (fillerEqvs: forall d,
      Equiv (EB d) (EA (mkFrameEqv (mkTrDepsRestr (mkTrDepsCohs TC2)) d))):
    TrDepsCohs2Extension TC2 (TopCoh2Dep EA) (TopCoh2Dep EB)
| AddTrCoh2Dep {p k} (TC2: TrDepsCohs2 p.+1 k)
    {XA: DepsCohs2Extension p.+1 k (trDepsCohs2A TC2.(_trCohs2Base))}
    {XB: DepsCohs2Extension p.+1 k (trDepsCohs2B TC2.(_trCohs2Base))}:
    TrDepsCohs2Extension TC2 XA XB ->
    TrDepsCohs2Extension (proj1TrDepsCohs2 TC2)
      (AddCoh2Dep (trDepsCohs2A TC2.(_trCohs2Base)) XA)
      (AddCoh2Dep (trDepsCohs2B TC2.(_trCohs2Base)) XB).

Arguments TopTrCoh2Dep {p TC2 EA EB} _.
Arguments AddTrCoh2Dep {p k} TC2 {XA XB} _.

Fixpoint mkTrExtraCohs {p k} {TC2: TrDepsCohs2 p k}
  {XA: DepsCohs2Extension p k (trDepsCohs2A TC2.(_trCohs2Base))}
  {XB: DepsCohs2Extension p k (trDepsCohs2B TC2.(_trCohs2Base))}
  (TCX: TrDepsCohs2Extension TC2 XA XB):
  TrDepsCohsExtension (mkTrDepsCohs TC2) (mkExtraCohs XA) (mkExtraCohs XB) :=
  match TCX with
  | TopTrCoh2Dep fillerEqvs => TopTrCohDep fillerEqvs
  | AddTrCoh2Dep TC2' TCX' =>
      AddTrCohDep (mkTrDepsCohs TC2') (mkTrExtraCohs TCX')
  end.

(** The data from which the next level's [TrDepsCohs2Base] is built: the
    translation data of the current level with the filler equivalences,
    and the two towers' painting 2-coherences. *)

Class TrDepsCohs3Base (p k: nat) := {
  _trCohs2: TrDepsCohs2 p k;
  _tXC2A: DepsCohs2Extension p k (trDepsCohs2A _trCohs2.(_trCohs2Base));
  _tXC2B: DepsCohs2Extension p k (trDepsCohs2B _trCohs2.(_trCohs2Base));
  _trCX2: TrDepsCohs2Extension _trCohs2 _tXC2A _tXC2B;
  _tC2pA: mkCoh2PaintingTypes _tXC2A;
  _tC2pB: mkCoh2PaintingTypes _tXC2B;
}.

#[local]
Instance mkTrDepsCohs2Base {p k} (TC3: TrDepsCohs3Base p k):
  TrDepsCohs2Base p.+1 k :=
{|
  _trCohsL := mkTrDepsCohs TC3.(_trCohs2);
  _tXCA := mkExtraCohs TC3.(_tXC2A);
  _tXCB := mkExtraCohs TC3.(_tXC2B);
  _trCX := mkTrExtraCohs TC3.(_trCX2);
  _tCpA := mkCohPaintings TC3.(_tXC2A);
  _tCpB := mkCohPaintings TC3.(_tXC2B);
  _tC2A := mkCoh2Frames TC3.(_tXC2A) TC3.(_tC2pA);
  _tC2B := mkCoh2Frames TC3.(_tXC2B) TC3.(_tC2pB);
|}.

#[local]
Instance proj1TrDepsCohs3Base {p k} (TC3: TrDepsCohs3Base p.+1 k):
  TrDepsCohs3Base p k.+1 :=
{|
  _trCohs2 := proj1TrDepsCohs2 TC3.(_trCohs2);
  _tXC2A := (trDepsCohs2A TC3.(_trCohs2).(_trCohs2Base); TC3.(_tXC2A))%extradepscohs2;
  _tXC2B := (trDepsCohs2B TC3.(_trCohs2).(_trCohs2Base); TC3.(_tXC2B))%extradepscohs2;
  _trCX2 := AddTrCoh2Dep TC3.(_trCohs2) TC3.(_trCX2);
  _tC2pA := TC3.(_tC2pA).1;
  _tC2pB := TC3.(_tC2pB).1;
|}.

(** The translation core of the next level *)
Definition mkTrDepsCohs2Core {p k} (TC2: TrDepsCohs2 p k)
  {XA: DepsCohs2Extension p k (trDepsCohs2A TC2.(_trCohs2Base))}
  {XB: DepsCohs2Extension p k (trDepsCohs2B TC2.(_trCohs2Base))}
  (TCX: TrDepsCohs2Extension TC2 XA XB): TrDepsCohs2Core p.+1 k := {|
  _cTrCohsL := mkTrDepsCohs TC2;
  _cXCA := mkExtraCohs XA; _cXCB := mkExtraCohs XB;
  _cTrCX := mkTrExtraCohs TCX;
  _cCpA := mkCohPaintings XA; _cCpB := mkCohPaintings XB;
|}.

(** The next-level painting 2-cells, by recursion on the offset [r] as in
    [mkCohPainting]: at [r = 0] both towers' painting coherences and the
    next-level painting commutations are components, and the hexagon
    collapses to the stored commutation at the face
    ([rew_coh2Painting_restr0_split]); at [r.+1] the pair path
    decomposes into the layer hexagon [mkTrCohLayer] and the recursive
    call one stage up ([eq_existT_curried_dep_hex]). *)
Definition mkTrCohPainting {p k} (TC2: TrDepsCohs2 p k)
  {XA: DepsCohs2Extension p k (trDepsCohs2A TC2.(_trCohs2Base))}
  {XB: DepsCohs2Extension p k (trDepsCohs2B TC2.(_trCohs2Base))}
  (TCX: TrDepsCohs2Extension TC2 XA XB):
  mkTrCohPaintingType (mkTrDepsCohs2Core TC2 TCX).
Proof.
  intros q Hq r.
  generalize dependent q.
  generalize dependent TCX.
  generalize dependent XB.
  generalize dependent XA.
  generalize dependent TC2.
  generalize dependent k.
  generalize dependent p.
  induction r as [|r mkTrCohPainting].
  - intros p k TC2 XA XB TCX q Hq Hr ε ω d c.
    unfold mkTrCohPaintingType; cbv zeta.
    cbn.
    unfold mkTrRestrLayer.
    rewrite (sigT_fst_lmap2_rew_eq
      (P := fun x => mkPainting TC2.(_trCohs2Base).(_trCohsL).(_trBase).(_tExtA) x)
      (rf0 := fun a x => (mkRestrFrames (depsCohs := trDepsCohsA TC2.(_trCohs2Base).(_trCohsL).(_trBase))).2 0 leR_O a x)).
    now eapply (Lemmas.rew_coh2Painting_restr0_split
      (P := fun x => mkPainting TC2.(_trCohs2Base).(_trCohsL).(_trBase).(_tExtA) x)
      (Sq := fun x => mkPainting TC2.(_trCohs2Base).(_trCohsL).(_trBase).(_tExtB) x)
      (Sr := fun d0 => {a: mkLayer (mkRestrFrames (depsCohs := trDepsCohsA TC2.(_trCohs2Base).(_trCohsL).(_trBase))).2 d0 &T
        mkPainting (mkExtraDeps TC2.(_trCohs2Base).(_tXCA)) (d0; a)})
      (r0 := fun x => (mkRestrFrames (depsCohs := trDepsCohsA TC2.(_trCohs2Base).(_trCohsL).(_trBase))).2 0 leR_O ω x)
      (rq := fun m => (mkFrameEqvs TC2.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps)).2 m)
      (rr := fun n => (mkRestrFrames (depsCohs := trDepsCohsA TC2.(_trCohs2Base).(_trCohsL).(_trBase))).2 q Hq ε n)
      (fun m c => mkPaintingEqv TC2.(_trCohs2Base).(_trCohsL).(_trBase).(_trExt) m c)
      (fun n c => mkRestrPainting TC2.(_trCohs2Base).(_tXCA) q Hq ε n c)
      _ _ _ _ _ _ _
      (fun b0 => mkRestrPainting TC2.(_trCohs2Base).(_tXCB) q Hq ε _ b0)
      (fun b0 => mkPaintingEqv (AddTrDep (mkTrDepsRestr TC2.(_trCohs2Base).(_trCohsL)) (mkTrExtraDeps TC2.(_trCohs2Base).(_trCX))) _ b0)).
  - intros p k TC2 XA XB TCX q Hq Hr ε ω d c.
    destruct q; [now destruct (leR_O_contra Hr) |].
    destruct TCX as [| p' k' TC2' XA' XB' TCX']; [now destruct (leR_O_contra Hq) |].
    destruct c as [l c].
    unfold mkTrCohPaintingType; cbv zeta.
    unshelve eapply (eq_existT_curried_dep_hex_split
      (A1 := mkFrame (proj1TrDepsRestr TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps)).(_depsB))
      (A3 := mkFrame (mkDepsRestr (depsCohs := trDepsCohsA
        (proj1TrDepsCohsBase TC2'.(_trCohs2Base).(_trCohsL).(_trBase)))).(1))
      (A2 := mkFrame (mkDepsRestr (depsCohs := trDepsCohsA
        (proj1TrDepsCohsBase TC2'.(_trCohs2Base).(_trCohsL).(_trBase)))).(1))
      (B := mkFrame (proj1TrDepsRestr TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps)).(_depsA))
      (P1 := fun a => (mkLayer TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps).(_depsB).(_restrFrames).2 a).(GDom))
      (R1 := fun a u => (mkPainting TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_tExtB) (a; u)).(GDom))
      (P3 := fun a => (mkLayer (mkRestrFrames (depsCohs := trDepsCohsA
        (proj1TrDepsCohsBase TC2'.(_trCohs2Base).(_trCohsL).(_trBase)))).2 a).(GDom))
      (R3 := fun a u => (mkPainting (mkExtraDeps
        (trDepsCohsA TC2'.(_trCohs2Base).(_trCohsL).(_trBase); TC2'.(_trCohs2Base).(_tXCA))%extradepscohs) (a; u)).(GDom))
      (P2 := fun a => (mkLayer (mkRestrFrames (depsCohs := trDepsCohsA
        (proj1TrDepsCohsBase TC2'.(_trCohs2Base).(_trCohsL).(_trBase)))).2 a).(GDom))
      (R2 := fun a u => (mkPainting (mkExtraDeps
        (trDepsCohsA TC2'.(_trCohs2Base).(_trCohsL).(_trBase); TC2'.(_trCohs2Base).(_tXCA))%extradepscohs) (a; u)).(GDom))
      (P' := fun b => (mkLayer TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps).(_depsA).(_restrFrames).2 b).(GDom))
      (R' := fun b u => (mkPainting TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_tExtA) (b; u)).(GDom))
      (mkFrameEqv (proj1TrDepsRestr TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps)))
      (fun d0 l0 => mkTrLayerEquiv TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps).(_paintingEqvs)
        TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trDeps).(_trRestrs) d0 l0)
      (fun d0 l0 c0 => mkPaintingEqv TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_trExt) (d0; l0) c0)
      ((mkRestrFrames (depsCohs := trDepsCohsA
        (proj1TrDepsCohsBase TC2'.(_trCohs2Base).(_trCohsL).(_trBase)))).2 r.+1 (Hr ↕ Hq) ω)
      (fun d0 l0 => mkRestrLayer TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_tRpA).2 TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_tCohsA).2 r (⇓ (Hr ↕ Hq)) ω d0 l0)
      (fun d0 l0 c0 => mkRestrPainting TC2'.(_trCohs2Base).(_tXCA) r (⇓ (Hr ↕ Hq)) ω (d0; l0) c0)
      ((mkRestrFrames (depsCohs := trDepsCohsA
        (proj1TrDepsCohsBase TC2'.(_trCohs2Base).(_trCohsL).(_trBase)))).2 q.+1 Hq ε)
      (fun d0 l0 => mkRestrLayer TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_tRpA).2 TC2'.(_trCohs2Base).(_trCohsL).(_trBase).(_tCohsA).2 q (⇓ Hq) ε d0 l0)
      (fun d0 l0 c0 => mkRestrPainting TC2'.(_trCohs2Base).(_tXCA) q (⇓ Hq) ε (d0; l0) c0)).
    + now exact (mkTrCohLayer TC2'.(_trCohs2Base)
        (mkTrCohs (proj1TrDepsCohs2Base TC2'.(_trCohs2Base)) TC2'.(_trCohPaintings).1)
        TC2'.(_trCohPaintings).2 q (⇓ Hq) r (⇓ Hr) ε ω d l).
    + now exact (mkTrCohPainting p'.+1 k' TC2' XA' XB' TCX' q (⇓ Hq) (⇓ Hr) ε ω (d; l) c).
Defined.

Fixpoint mkTrCohPaintingsPrefix {p k} (TC3: TrDepsCohs3Base p k) {struct p}:
  mkTrCohPaintingTypes (proj1TrDepsCohs2Base (mkTrDepsCohs2Base TC3)).
Proof.
  destruct p.
  - now exact tt.
  - unshelve esplit.
    + now exact (mkTrCohPaintingsPrefix p k.+1 (proj1TrDepsCohs3Base TC3)).
    + now exact (mkTrCohPainting (proj1TrDepsCohs2 TC3.(_trCohs2))
        (AddTrCoh2Dep TC3.(_trCohs2) TC3.(_trCX2))).
Defined.

Definition mkTrCohPaintings {p k} (TC3: TrDepsCohs3Base p k):
  mkTrCohPaintingTypes (mkTrDepsCohs2Base TC3) :=
  (mkTrCohPaintingsPrefix TC3; mkTrCohPainting TC3.(_trCohs2) TC3.(_trCX2)).

(** The tower of translation data and the levelwise equivalence

    The translation data at a pair of prefixes, in the shape of
    [νGpdData]: the rung-0 data of the level, and the higher rungs as
    functions of the fillers of the levels above, computed from the level
    below by the constructions of the rungs. The datum a level contributes
    is the equivalence of its fillers over the frame equivalence; a
    levelwise equivalence of two towers is a limit over the telescope of
    such data, as the towers themselves are. *)

Section TrTowerData.
Context {n: nat} {XpA XpB: (νGpdAt n).(prefix)}.

Definition mkTowerTrDeps
  (fe: mkFrameEqvTypes (νTowerDeps XpA).(_frames) (νTowerDeps XpB).(_frames))
  (pe: mkPaintingEqvTypes fe (νTowerDeps XpA).(_paintings)
    (νTowerDeps XpB).(_paintings))
  (tr: (mkTrRestrTypesAndFrames fe pe).(TrRestrTypesDef)
    (νTowerDeps XpA).(_restrFrames) (νTowerDeps XpB).(_restrFrames)):
  TrDepsRestr n 0 := {|
  _depsA := νTowerDeps XpA; _depsB := νTowerDeps XpB;
  _frameEqvs := fe; _paintingEqvs := pe; _trRestrs := tr;
|}.

Context (fe: mkFrameEqvTypes (νTowerDeps XpA).(_frames) (νTowerDeps XpB).(_frames))
  (pe: mkPaintingEqvTypes fe (νTowerDeps XpA).(_paintings)
    (νTowerDeps XpB).(_paintings))
  (tr: (mkTrRestrTypesAndFrames fe pe).(TrRestrTypesDef)
    (νTowerDeps XpA).(_restrFrames) (νTowerDeps XpB).(_restrFrames)).

Definition νFillerEqvOver (EA: νFillerType XpA) (EB: νFillerType XpB): Type :=
  forall d: νFrame XpB, Equiv (EB d) (EA (mkFrameEqv (mkTowerTrDeps fe pe tr) d)).

Context {EA: νFillerType XpA} {EB: νFillerType XpB} (fEqv: νFillerEqvOver EA EB).

Definition towerTrRpType: Type :=
  mkTrRestrPaintingTypes (mkTowerTrDeps fe pe tr)
    (TopTrDep (T := mkTowerTrDeps fe pe tr) fEqv)
    ((νDataAt XpA).(restrPaintings) EA) ((νDataAt XpB).(restrPaintings) EB).

Definition towerTrDepsCohsBase (rp: towerTrRpType): TrDepsCohsBase n 0 := {|
  _trDeps := mkTowerTrDeps fe pe tr;
  _tExtA := TopRestrDep EA; _tExtB := TopRestrDep EB;
  _trExt := TopTrDep (T := mkTowerTrDeps fe pe tr) fEqv;
  _tRpA := (νDataAt XpA).(restrPaintings) EA;
  _tRpB := (νDataAt XpB).(restrPaintings) EB;
  _trRestrPaintings := rp;
  _tCohsA := (νDataAt XpA).(cohFrames) EA;
  _tCohsB := (νDataAt XpB).(cohFrames) EB;
|}.

Context (rp: towerTrRpType) (cohs: mkTrCohTypes (towerTrDepsCohsBase rp)).

Definition towerTrDepsCohs: TrDepsCohs n 0 :=
  {| _trBase := towerTrDepsCohsBase rp; _trCohs := cohs |}.

Definition νFillerEqvOver1
  (EA': νFillerType ((XpA; EA): (νGpdAt n.+1).(prefix)))
  (EB': νFillerType ((XpB; EB): (νGpdAt n.+1).(prefix))): Type :=
  forall d, Equiv (EB' d) (EA' (mkFrameEqv (mkTrDepsRestr towerTrDepsCohs) d)).

Context {EA': νFillerType ((XpA; EA): (νGpdAt n.+1).(prefix))}
  {EB': νFillerType ((XpB; EB): (νGpdAt n.+1).(prefix))}
  (fEqv': νFillerEqvOver1 EA' EB').

Definition towerTrDepsCohs2Base: TrDepsCohs2Base n 0 := {|
  _trCohsL := towerTrDepsCohs;
  _tXCA := TopCohDep EA'; _tXCB := TopCohDep EB';
  _trCX := TopTrCohDep (TC := towerTrDepsCohs) fEqv';
  _tCpA := (νDataAt XpA).(cohPaintings) EA EA';
  _tCpB := (νDataAt XpB).(cohPaintings) EB EB';
  _tC2A := (νDataAt XpA).(coh2Frames) EA EA';
  _tC2B := (νDataAt XpB).(coh2Frames) EB EB';
|}.

Context (cohPs: mkTrCohPaintingTypes towerTrDepsCohs2Base).

Definition towerTrDepsCohs2: TrDepsCohs2 n 0 :=
  {| _trCohs2Base := towerTrDepsCohs2Base; _trCohPaintings := cohPs |}.

Definition νFillerEqvOver2
  (EA'': νFillerType (((XpA; EA); EA'): (νGpdAt n.+2).(prefix)))
  (EB'': νFillerType (((XpB; EB); EB'): (νGpdAt n.+2).(prefix))): Type :=
  forall d, Equiv (EB'' d)
    (EA'' (mkFrameEqv (mkTrDepsRestr (mkTrDepsCohs towerTrDepsCohs2)) d)).

Context {EA'': νFillerType (((XpA; EA); EA'): (νGpdAt n.+2).(prefix))}
  {EB'': νFillerType (((XpB; EB); EB'): (νGpdAt n.+2).(prefix))}
  (fEqv'': νFillerEqvOver2 EA'' EB'').

Definition towerTrDepsCohs3Base: TrDepsCohs3Base n 0 := {|
  _trCohs2 := towerTrDepsCohs2;
  _tXC2A := TopCoh2Dep (depsCohs2 := trDepsCohs2A towerTrDepsCohs2Base)
    (EA'': mkFrame (mkDepsRestr (depsCohs := mkDepsCohs
      (trDepsCohs2A towerTrDepsCohs2Base))) -> HGpd);
  _tXC2B := TopCoh2Dep (depsCohs2 := trDepsCohs2B towerTrDepsCohs2Base)
    (EB'': mkFrame (mkDepsRestr (depsCohs := mkDepsCohs
      (trDepsCohs2B towerTrDepsCohs2Base))) -> HGpd);
  _trCX2 := TopTrCoh2Dep (TC2 := towerTrDepsCohs2) fEqv'';
  _tC2pA := (νDataAt XpA).(coh2Paintings) EA EA' EA'';
  _tC2pB := (νDataAt XpB).(coh2Paintings) EB EB' EB'';
|}.

End TrTowerData.

Class TrTower n (XpA XpB: (νGpdAt n).(prefix)) := {
  _twFrameEqvs: mkFrameEqvTypes (νTowerDeps XpA).(_frames)
    (νTowerDeps XpB).(_frames);
  _twPaintingEqvs: mkPaintingEqvTypes _twFrameEqvs
    (νTowerDeps XpA).(_paintings) (νTowerDeps XpB).(_paintings);
  _twTrRestrs: (mkTrRestrTypesAndFrames _twFrameEqvs _twPaintingEqvs)
    .(TrRestrTypesDef)
    (νTowerDeps XpA).(_restrFrames) (νTowerDeps XpB).(_restrFrames);
  _twTrRestrPaintings: forall (EA: νFillerType XpA) (EB: νFillerType XpB)
    (fEqv: νFillerEqvOver _twFrameEqvs _twPaintingEqvs _twTrRestrs EA EB),
    towerTrRpType _twFrameEqvs _twPaintingEqvs _twTrRestrs fEqv;
  _twTrCohs: forall (EA: νFillerType XpA) (EB: νFillerType XpB)
    (fEqv: νFillerEqvOver _twFrameEqvs _twPaintingEqvs _twTrRestrs EA EB),
    mkTrCohTypes (towerTrDepsCohsBase _twFrameEqvs _twPaintingEqvs _twTrRestrs
      fEqv (_twTrRestrPaintings EA EB fEqv));
  _twTrCohPaintings: forall (EA: νFillerType XpA) (EB: νFillerType XpB)
    (fEqv: νFillerEqvOver _twFrameEqvs _twPaintingEqvs _twTrRestrs EA EB)
    (EA': νFillerType ((XpA; EA): (νGpdAt n.+1).(prefix)))
    (EB': νFillerType ((XpB; EB): (νGpdAt n.+1).(prefix)))
    (fEqv': νFillerEqvOver1 _twFrameEqvs _twPaintingEqvs _twTrRestrs fEqv
      (_twTrRestrPaintings EA EB fEqv) (_twTrCohs EA EB fEqv) EA' EB'),
    mkTrCohPaintingTypes (towerTrDepsCohs2Base _twFrameEqvs _twPaintingEqvs
      _twTrRestrs fEqv (_twTrRestrPaintings EA EB fEqv) (_twTrCohs EA EB fEqv)
      fEqv');
}.

Section TrTowerStep.
Context {n: nat} {XpA XpB: (νGpdAt n).(prefix)} (W: TrTower n XpA XpB).

Definition towerTrDeps: TrDepsRestr n 0 :=
  mkTowerTrDeps W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs).

Definition towerFillerEqv (EA: νFillerType XpA) (EB: νFillerType XpB): Type :=
  νFillerEqvOver W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs) EA EB.

Context {EA: νFillerType XpA} {EB: νFillerType XpB}
  (fEqv: towerFillerEqv EA EB).

Definition towerCohs: TrDepsCohs n 0 :=
  towerTrDepsCohs W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs) fEqv
    (W.(_twTrRestrPaintings) EA EB fEqv) (W.(_twTrCohs) EA EB fEqv).

Definition towerFillerEqv1
  (EA': νFillerType ((XpA; EA): (νGpdAt n.+1).(prefix)))
  (EB': νFillerType ((XpB; EB): (νGpdAt n.+1).(prefix))): Type :=
  νFillerEqvOver1 W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs) fEqv
    (W.(_twTrRestrPaintings) EA EB fEqv) (W.(_twTrCohs) EA EB fEqv) EA' EB'.

Definition towerCohs2 {EA'} {EB'} (fEqv': towerFillerEqv1 EA' EB'):
  TrDepsCohs2 n 0 :=
  towerTrDepsCohs2 W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs) fEqv
    (W.(_twTrRestrPaintings) EA EB fEqv) (W.(_twTrCohs) EA EB fEqv) fEqv'
    (W.(_twTrCohPaintings) EA EB fEqv EA' EB' fEqv').

Definition trTowerStep: TrTower n.+1 (XpA; EA) (XpB; EB) :=
  Build_TrTower n.+1 (XpA; EA) (XpB; EB)
    (mkFrameEqvs towerTrDeps)
    (mkPaintingEqvs (TopTrDep (T := towerTrDeps) fEqv))
    (mkTrRestrFrames towerCohs)
    (fun EA' EB' fEqv' =>
      mkTrRestrPaintings (TopTrCohDep (TC := towerCohs) fEqv'))
    (fun EA' EB' fEqv' =>
      mkTrCohs (towerCohs2 fEqv').(_trCohs2Base)
        (towerCohs2 fEqv').(_trCohPaintings))
    (fun EA' EB' fEqv' EA'' EB'' fEqv'' =>
      mkTrCohPaintings (towerTrDepsCohs3Base W.(_twFrameEqvs)
        W.(_twPaintingEqvs) W.(_twTrRestrs) fEqv
        (W.(_twTrRestrPaintings) EA EB fEqv) (W.(_twTrCohs) EA EB fEqv) fEqv'
        (W.(_twTrCohPaintings) EA EB fEqv EA' EB' fEqv') fEqv'')).

End TrTowerStep.

Definition trTower0 (XpA XpB: (νGpdAt 0).(prefix)): TrTower 0 XpA XpB :=
  Build_TrTower 0 XpA XpB tt tt tt (fun _ _ _ => tt) (fun _ _ _ => tt)
    (fun _ _ _ _ _ _ => tt).

(** The telescope of translation prefixes: a translation prefix at level
    [n.+1] is one at level [n] with a filler equivalence over the frame
    equivalence its data compute; the tower of data is a function of it. *)

Record TrAt n (XpA XpB: (νGpdAt n).(prefix)) := {
  trPrefix: Type;
  trData: trPrefix -> TrTower n XpA XpB;
}.

Arguments trPrefix {n XpA XpB} _.
Arguments trData {n XpA XpB} _ _.

Fixpoint trAt n: forall XpA XpB: (νGpdAt n).(prefix), TrAt n XpA XpB :=
  match n with
  | 0 => fun XpA XpB => {| trPrefix := unit; trData := fun _ => trTower0 XpA XpB |}
  | S n => fun XpA XpB => {|
      trPrefix := { P: (trAt n XpA.1 XpB.1).(trPrefix) &T
        towerFillerEqv ((trAt n XpA.1 XpB.1).(trData) P) XpA.2 XpB.2 };
      trData := fun P => trTowerStep ((trAt n XpA.1 XpB.1).(trData) P.1) P.2;
    |}
  end.

Definition trTel (SA SB: νGpds): Telescope := {|
  stage m := (trAt m (νGpdPack m SA).1 (νGpdPack m SB).1).(trPrefix);
  datum m P := towerFillerEqv
    ((trAt m (νGpdPack m SA).1 (νGpdPack m SB).1).(trData) P)
    (this ((νGpdPack m SA).2)) (this ((νGpdPack m SB).2));
  extend m P E := ((P; E):
    (trAt m.+1 (νGpdPack m.+1 SA).1 (νGpdPack m.+1 SB).1).(trPrefix));
  bond m P := P.1;
  head m P := P.2;
  bondExtend m P E := eq_refl;
  extendHead m P := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

(** The levelwise equivalence of two νGpds *)
Definition νGpdsEquiv (SA SB: νGpds): Type := Limit (trTel SA SB) 0 tt.

End νGpdEquiv.

(** Translation data over a fixed instance of the two constructions. *)
Module Type TranslationSig (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A).
Include νGpdEquiv A Base.
End TranslationSig.
