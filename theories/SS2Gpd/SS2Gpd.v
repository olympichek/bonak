Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet Notation LeSProp Limit Lib.Coh2Shapes.
From Bonak Require Import SSGpd.Lemmas SSGpd.Coh3Shapes SS2Gpd.H2Gpd.
From Bonak.SS2Gpd.Lemmas Require Import Coh3Painting0 Coh3Frame Coh3Painting Coh3Layer.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module SS2Gpd.

(** A telescope of [p] frame types at fixed total index [p + k].
    The offset [k] increases when a frame type is projected away. *)

Fixpoint mkFrameTypes p k: Type :=
  match p with
  | 0 => unit
  | S p => { frames: mkFrameTypes p k.+1 &T H2Gpd }
  end.

(** Painting families over the corresponding [p] frame types. *)

Fixpoint mkPaintingTypes p k: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
    { paintings: mkPaintingTypes p k.+1 frames.1 &T frames.2 -> H2Gpd }
  end.

(** A helper type so as to mutually build the types of restrFrames and
    the body of frames using a single fixpoint *)

Class RestrFrameTypeBlock p k := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> mkFrameTypes p.+1 k;
}.

(** Build restriction-map types together with the next frame telescope.
    Each new frame is a dependent pair of an earlier frame and a painting
    over its zero restriction. Keeping the restriction maps as parameters
    lets the two components be constructed by recursion on [p]. *)

Generalizable Variables p k frames.

Definition mkRestrFrameType
  `(prevFrames: mkFrameTypes p.+1 k.+1)
   (frames: mkFrameTypes p.+1 k) :=
  forall q (Hq: q <= k), prevFrames.2 -> frames.2.

Definition mkRestrFrameTypesStep `(frames: mkFrameTypes p.+1 k)
  (prev: RestrFrameTypeBlock p k.+1) :=
  { R: prev.(RestrFrameTypesDef) &T mkRestrFrameType (prev.(FrameDef) R) frames }.

Definition mkLayer `{frames: mkFrameTypes p.+1 k}
  {prevFrames: mkFrameTypes p.+1 k.+1}
  (restrFrame: mkRestrFrameType prevFrames frames)
  {painting: frames.2 -> H2Gpd}
  (d: prevFrames.2) :=
  painting (restrFrame 0 leR_O d).

Fixpoint mkRestrFrameTypesAndFrames {p k}:
  forall `(paintings: mkPaintingTypes p k frames), RestrFrameTypeBlock p k :=
  match p with
  | 0 => fun frames paintings =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; g2unit): mkFrameTypes 1 k
    |}
  | p.+1 => fun frames paintings =>
    let prev :=
      mkRestrFrameTypesAndFrames paintings.1 in
    let frames' := prev.(FrameDef) in
    {|
      RestrFrameTypesDef := mkRestrFrameTypesStep frames prev;
      FrameDef R :=
        (frames' R.1; { d: (frames' R.1).2 &
          mkLayer R.2 (painting := paintings.2) d }): mkFrameTypes p.+2 k
    |}
  end.

Definition mkRestrFrameTypes `(paintings: mkPaintingTypes p k frames) :=
  (mkRestrFrameTypesAndFrames paintings).(RestrFrameTypesDef).

Class DepsRestr p k := {
  _frames: mkFrameTypes p k;
  _paintings: mkPaintingTypes p k _frames;
  _restrFrames: mkRestrFrameTypes _paintings;
}.

Instance toDepsRestr `{paintings: mkPaintingTypes p k frames}
  (restrFrames: mkRestrFrameTypes paintings) : DepsRestr p k :=
  {| _restrFrames := restrFrames |}.

#[local]
Instance proj1DepsRestr `(deps: DepsRestr p.+1 k): DepsRestr p k.+1 :=
{|
  _frames := deps.(_frames).1;
  _paintings := deps.(_paintings).1;
  _restrFrames := deps.(_restrFrames).1;
|}.

Declare Scope depsrestr_scope.
Delimit Scope depsrestr_scope with depsrestr.
Bind Scope depsrestr_scope with DepsRestr.
Notation "x .(1)" := (proj1DepsRestr x%_depsrestr)
  (at level 1, left associativity, format "x .(1)"): depsrestr_scope.

Definition mkFrames `(deps: DepsRestr p k): mkFrameTypes p.+1 k :=
  (mkRestrFrameTypesAndFrames
    deps.(_paintings)).(FrameDef) deps.(_restrFrames).

Definition mkFrame `(deps: DepsRestr p k): H2Gpd := (mkFrames deps).2.

Inductive DepsRestrExtension p: forall k, DepsRestr p k -> Type :=
| TopRestrDep {deps} (E: mkFrame deps -> H2Gpd): DepsRestrExtension p 0 deps
| AddRestrDep {k} deps:
  DepsRestrExtension p.+1 k deps -> DepsRestrExtension p k.+1 deps.(1).

Arguments TopRestrDep {p deps}.
Arguments AddRestrDep {p k} deps.

Declare Scope extra_depsrestr_scope.
Delimit Scope extra_depsrestr_scope with extradepsrestr.
Bind Scope extra_depsrestr_scope with DepsRestrExtension.
Notation "( x ; y )" := (AddRestrDep x y)
  (at level 0, format "( x ; y )"): extra_depsrestr_scope.

(** At the top, the supplied family [E] is the new painting family. *)

Generalizable Variables deps.

Fixpoint mkPainting `(extraDeps: DepsRestrExtension p k deps):
  mkFrame deps -> H2Gpd :=
  match extraDeps with
  | TopRestrDep E => fun d => E d
  | AddRestrDep deps extraDeps => fun (d: mkFrame deps.(1)) =>
      {l: mkLayer deps.(_restrFrames).2 d & mkPainting extraDeps (d; l)}
  end.

Fixpoint mkPaintingsPrefix {p k}:
  forall `(extraDeps: DepsRestrExtension p k deps),
    mkPaintingTypes p k.+1 (mkFrames deps).1 :=
  match p with
  | 0 => fun _ _ => tt
  | S p => fun deps extraDeps =>
      (mkPaintingsPrefix (deps; extraDeps)%extradepsrestr;
       mkPainting (deps; extraDeps)%extradepsrestr)
  end.

Definition mkPaintings {p k}: forall `(extraDeps: DepsRestrExtension p k deps),
  mkPaintingTypes p.+1 k (mkFrames deps) :=
  fun deps extraDeps => (mkPaintingsPrefix extraDeps; mkPainting extraDeps).

Definition mkRestrPaintingType
  `(extraDeps: DepsRestrExtension p.+1 k deps) :=
  forall q (Hq: q <= k) (d: mkFrame deps.(1)),
  (mkPaintings (deps; extraDeps)).2 d ->
  deps.(_paintings).2 (deps.(_restrFrames).2 q Hq d).

Fixpoint mkRestrPaintingTypes {p}:
  forall `(extraDeps: DepsRestrExtension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkRestrPaintingTypes (deps; extraDeps) &T
      mkRestrPaintingType extraDeps }
  end.

(** A helper type so as to mutually build the types of cohFrames and
    the body of restrFrames using a single fixpoint *)

Class CohFrameTypeBlock `{extraDeps: DepsRestrExtension p k deps} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef -> mkRestrFrameTypes (mkPaintings extraDeps)
}.

Definition mkCohFrameType `{extraDeps: DepsRestrExtension p.+1 k deps}
  (prevRestrFrames: mkRestrFrameTypes (mkPaintings (deps; extraDeps))): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q)
    (d: mkFrame (toDepsRestr prevRestrFrames).(1)),
  deps.(_restrFrames).2 q Hq (prevRestrFrames.2 r (Hr ↕ (↑ Hq)) d) =
  deps.(_restrFrames).2 r (Hr ↕ Hq) (prevRestrFrames.2 q.+1 (⇑ Hq) d).

Definition mkCohFrameTypesStep `{extraDeps: DepsRestrExtension p.+1 k deps}
  (prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))): Type :=
  { Q: prev.(CohFrameTypesDef) &T mkCohFrameType (prev.(RestrFramesDef) Q) }.

Definition mkRestrLayer `{extraDeps: DepsRestrExtension p.+1 k deps}
  {prevRestrFrames: mkRestrFrameTypes (mkPaintings (deps;extraDeps))}
  (restrPainting: mkRestrPaintingType extraDeps)
  (cohFrame: mkCohFrameType prevRestrFrames)
  q (Hq: q <= k)
  (d: mkFrame (toDepsRestr prevRestrFrames).(1))
  (l: mkLayer prevRestrFrames.2 d):
  mkLayer deps.(_restrFrames).2 (prevRestrFrames.2 q.+1 (⇑ Hq) d) :=
  rew [deps.(_paintings).2] cohFrame q Hq 0 leR_O d in
    restrPainting q Hq _ l.

(** Given painting restrictions, build frame-coherence types together
    with the next frame restrictions. A coherence witness transports the
    restricted painting to the required zero-restriction fiber. *)

Fixpoint mkCohFrameTypesAndRestrFrames {p k}:
  forall `{extraDeps: DepsRestrExtension p k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps), CohFrameTypeBlock :=
  match p with
  | 0 =>
    fun deps extraDeps restrPaintings =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ => tt)
    |}
  | S p =>
    fun deps extraDeps restrPaintings =>
    let prev := mkCohFrameTypesAndRestrFrames restrPaintings.1 in
    let restrFrames := prev.(RestrFramesDef) in
    {|
      CohFrameTypesDef := mkCohFrameTypesStep prev;
      RestrFramesDef Q :=
      let restrFrame q (Hq: q <= k)
        (d: mkFrame (toDepsRestr (restrFrames Q.1))) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) d.1;
           mkRestrLayer restrPaintings.2 Q.2 q _ d.1 d.2)
      in (restrFrames Q.1; restrFrame)
    |}
  end.

Definition mkCohFrameTypes `{extraDeps: DepsRestrExtension p k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps) :=
  (mkCohFrameTypesAndRestrFrames restrPaintings).(CohFrameTypesDef).

Class DepsCohs p k := {
  _deps: DepsRestr p k;
  _extraDeps: DepsRestrExtension p k _deps;
  _restrPaintings: mkRestrPaintingTypes _extraDeps;
  _cohs: mkCohFrameTypes _restrPaintings;
}.

#[local]
Instance toDepsCohs `{extraDeps: DepsRestrExtension p k deps}
  {restrPaintings: mkRestrPaintingTypes extraDeps}
  (cohs: mkCohFrameTypes restrPaintings): DepsCohs p k :=
  {| _cohs := cohs |}.

#[local]
Instance proj1DepsCohs `(depsCohs: DepsCohs p.+1 k): DepsCohs p k.+1 :=
{|
  _deps := depsCohs.(_deps).(1);
  _extraDeps := (depsCohs.(_deps); depsCohs.(_extraDeps));
  _restrPaintings := depsCohs.(_restrPaintings).1;
  _cohs := depsCohs.(_cohs).1;
|}.

Declare Scope depscohs_scope.
Delimit Scope depscohs_scope with depscohs.
Bind Scope depscohs_scope with DepsCohs.
Notation "x .(1)" := (proj1DepsCohs x%depscohs)
  (at level 1, left associativity, format "x .(1)"): depscohs_scope.

(** Instantiate the restriction construction with the stored frame
    coherences. *)

Definition mkRestrFrames `{depsCohs: DepsCohs p k} :=
  (mkCohFrameTypesAndRestrFrames depsCohs.(_restrPaintings)).(RestrFramesDef)
    depsCohs.(_cohs).

(** Assemble the next frame and painting telescopes with the restriction
    maps selected by the supplied frame-coherence witnesses. *)

Definition mkDepsRestr `{depsCohs: DepsCohs p k} :=
  toDepsRestr mkRestrFrames.

(** Select the last restriction map from the constructed telescope.
    Its source frame uses the preceding restriction maps, while its
    target is the last frame of the input telescope. *)

Definition mkRestrFrame `{depsCohs: DepsCohs p k}:
  forall q (Hq: q <= k),
  mkFrame mkDepsRestr.(1) -> mkFrame depsCohs.(_deps) :=
  mkRestrFrames.2.

Inductive DepsCohsExtension p: forall k (depsCohs: DepsCohs p k), Type :=
| TopCohDep `{depsCohs: DepsCohs p 0}
  (E: mkFrame mkDepsRestr -> H2Gpd):
  DepsCohsExtension p 0 depsCohs
| AddCohDep {k} (depsCohs: DepsCohs p.+1 k):
  DepsCohsExtension p.+1 k depsCohs -> DepsCohsExtension p k.+1 depsCohs.(1).

Arguments TopCohDep {p depsCohs}.
Arguments AddCohDep {p k}.

Declare Scope extra_depscohs_scope.
Delimit Scope extra_depscohs_scope with extradepscohs.
Bind Scope extra_depscohs_scope with DepsCohsExtension.
Notation "( x ; y )" := (AddCohDep x y)
  (at level 0, format "( x ; y )"): extra_depscohs_scope.

Generalizable Variables depsCohs.

Fixpoint mkExtraDeps `(extraDepsCohs: DepsCohsExtension p k depsCohs):
  DepsRestrExtension p.+1 k mkDepsRestr.
Proof.
  destruct extraDepsCohs.
  - now constructor.
  - apply (AddRestrDep mkDepsRestr
    (mkExtraDeps p.+1 k depsCohs extraDepsCohs)).
Defined.

Fixpoint mkRestrPainting `(extraDepsCohs: DepsCohsExtension p k depsCohs)
  q {struct q}:
  forall (Hq: q <= k) (d: mkFrame mkDepsRestr.(1)),
    (mkPaintings (mkDepsRestr; mkExtraDeps extraDepsCohs)).2 d ->
    mkDepsRestr.(_paintings).2 (mkDepsRestr.(_restrFrames).2 q Hq d).
Proof.
  destruct q as [|q]; intros Hq d [l c].
  - exact l.
  - destruct extraDepsCohs as [|k0 depsCohs0 extraDepsCohs0].
    + now destruct (leR_O_contra Hq).
    + unshelve eapply existT.
      * exact (mkRestrLayer depsCohs0.(_restrPaintings).2 depsCohs0.(_cohs).2
          q (⇓ Hq) d l).
      * exact (mkRestrPainting _ _ _ extraDepsCohs0 q (⇓ Hq) (d; l) c).
Defined.

Fixpoint mkRestrPaintingsPrefix {p k}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs),
  mkRestrPaintingTypes
    (mkDepsRestr; mkExtraDeps extraDepsCohs)%extradepsrestr :=
  match p with
  | 0 => fun _ _ => tt
  | S p =>
    fun depsCohs extraDepsCohs =>
      (mkRestrPaintingsPrefix (depsCohs; extraDepsCohs)%extradepscohs;
       mkRestrPainting (depsCohs; extraDepsCohs)%extradepscohs)
  end.

Definition mkRestrPaintings {p k}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs),
  mkRestrPaintingTypes (mkExtraDeps extraDepsCohs) :=
  fun depsCohs extraDepsCohs => (mkRestrPaintingsPrefix extraDepsCohs; mkRestrPainting extraDepsCohs).

(** Frame hexagons compare the two routes of three restrictions. *)

Definition mkCoh2FrameType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs)
  (prevCohFrames: mkCohFrameTypes
    (mkRestrPaintings (depsCohs; extraDepsCohs))): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
    (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1)),
  hexagonal_coherence
    (fun x => depsCohs.(_deps).(_restrFrames).2 q _ x)
    (fun x => depsCohs.(_deps).(_restrFrames).2 s (Hs ↕ (Hr ↕ Hq)) x)
    (fun x => depsCohs.(_deps).(_restrFrames).2 r _ x)
    (prevCohFrames.2 r (Hr ↕ ↑ Hq) s Hs d)
    (prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) d)
    (prevCohFrames.2 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) d)
    (depsCohs.(_cohs).2 q Hq s (Hs ↕ Hr)
      (mkRestrFrame r.+1 (⇑ (Hr ↕ ↑ Hq)) d))
    (depsCohs.(_cohs).2 q Hq r Hr
      (mkRestrFrame s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) d))
    (depsCohs.(_cohs).2 r (Hr ↕ Hq) s Hs
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) d)).

Definition mkCohPaintingInstanceType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs)
  q (Hq: q <= k) r (Hr: r <= q)
  (d: mkFrame (mkDepsRestr (depsCohs := depsCohs.(1))).(1))
  (c: (mkPaintings (mkDepsRestr;
      mkExtraDeps (depsCohs; extraDepsCohs))).2 d): Type :=
  rew [depsCohs.(_deps).(_paintings).2] depsCohs.(_cohs).2 q Hq r Hr d in
  depsCohs.(_restrPaintings).2 q Hq _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 r _ d c) =
  depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 q.+1 _ d c).

Definition mkCohPaintingType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs) :=
  forall q (Hq: q <= k) r (Hr: r <= q) (d: _) (c: _),
    mkCohPaintingInstanceType extraDepsCohs q Hq r Hr d c.

Fixpoint mkCohPaintingTypes {p}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k depsCohs extraDepsCohs =>
    { R: mkCohPaintingTypes (depsCohs; extraDepsCohs) &T
         mkCohPaintingType extraDepsCohs }
  end.

Definition mkCohLayerType `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  q (Hq: q <= k) r (Hr: r <= q)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
  (l: mkLayer mkRestrFrame d): Type :=
  rew [mkLayer _] prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) d in
  mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 q Hq _
    (mkRestrLayer (mkRestrPaintings extraDepsCohs).1.2 prevCohFrames.2
      r (Hr ↕ ↑ Hq) d l) =
  mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 r (Hr ↕ Hq) _
    (mkRestrLayer (mkRestrPaintings extraDepsCohs).1.2 prevCohFrames.2
      q.+1 (⇑ Hq) d l).

Definition mkCohLayer `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  (cohPainting: mkCohPaintingType extraDepsCohs)
  (coh2Frame: mkCoh2FrameType extraDepsCohs prevCohFrames)
  q (Hq: q <= k) r (Hr: r <= q)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
  (l: mkLayer mkRestrFrame d):
  mkCohLayerType q Hq r Hr d l.
Proof.
  unfold mkCohLayerType, mkRestrLayer.
  eapply (rew_cohLayer_hex
    (P := fun x => depsCohs.(_deps).(_paintings).2 x)
    (rf0 := fun x => depsCohs.(_deps).(_restrFrames).2 0 leR_O x)
    (F := depsCohs.(_restrPaintings).2 q Hq )
    (G := depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) )).
  - now exact (cohPainting q Hq r Hr
      (((mkCohFrameTypesAndRestrFrames (mkRestrPaintings extraDepsCohs).1.1)
        .(RestrFramesDef) prevCohFrames.1).2 0 leR_O d) l).
  - now apply (coh2Frame q Hq r Hr 0 leR_O d).
Defined.

Class Coh2FrameTypeBlock `{extraDepsCohs: DepsCohsExtension p k depsCohs} := {
  Coh2FrameTypesDef: Type;
  CohFramesDef: Coh2FrameTypesDef -> mkCohFrameTypes (mkRestrPaintings extraDepsCohs);
}.

Definition mkCoh2FrameTypesStep
  `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (prev: Coh2FrameTypeBlock
    (extraDepsCohs := (depsCohs; extraDepsCohs)%extradepscohs)): Type :=
  { R: prev.(Coh2FrameTypesDef) &T
    mkCoh2FrameType extraDepsCohs (prev.(CohFramesDef) R) }.

Fixpoint mkCoh2FrameTypesAndCohFrames {p k}:
  forall `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs),
  Coh2FrameTypeBlock (extraDepsCohs := extraDepsCohs).
Proof.
  destruct p.
  - intros depsCohs extraDepsCohs cohPaintings.
    unshelve econstructor.
    + now exact unit.
    + intros _. unshelve esplit. now exact tt. now intros.
  - intros depsCohs extraDepsCohs cohPaintings.
    set (prev := mkCoh2FrameTypesAndCohFrames p k.+1
      depsCohs.(1)%depscohs
      (depsCohs; extraDepsCohs)%extradepscohs cohPaintings.1).
    unshelve econstructor.
    + now exact (mkCoh2FrameTypesStep cohPaintings prev).
    + intros Q.
      set (h := prev.(CohFramesDef) Q.1).
      unshelve esplit. now exact h.
      intros q Hq r Hr d.
      unshelve eapply eq_existT_curried.
      * now exact (h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) d.1).
      * now exact (mkCohLayer cohPaintings.2 Q.2 q Hq r Hr d.1 d.2).
Defined.

Definition mkCoh2FrameTypes `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs) :=
  (mkCoh2FrameTypesAndCohFrames cohPaintings).(Coh2FrameTypesDef).

Definition mkCohFrames `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (coh2Frames: mkCoh2FrameTypes cohPaintings):
  mkCohFrameTypes (mkRestrPaintings extraDepsCohs) :=
  (mkCoh2FrameTypesAndCohFrames cohPaintings).(CohFramesDef) coh2Frames.

Definition mkCohFrame `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (coh2Frames: mkCoh2FrameTypes cohPaintings):
  mkCohFrameType (mkRestrFrames (depsCohs :=
    toDepsCohs (mkCohFrames cohPaintings coh2Frames).1)) :=
  (mkCohFrames cohPaintings coh2Frames).2.

Class DepsCohs2 p k := {
  _depsCohs: DepsCohs p k;
  _extraDepsCohs: DepsCohsExtension p k _depsCohs;
  _cohPaintings: mkCohPaintingTypes _extraDepsCohs;
  _coh2Frames: mkCoh2FrameTypes _cohPaintings;
}.

#[local]
Instance toDepsCohs2 `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  {cohPaintings: mkCohPaintingTypes extraDepsCohs}
  (coh2Frames: mkCoh2FrameTypes cohPaintings): DepsCohs2 p k :=
  {| _coh2Frames := coh2Frames |}.

#[local]
Instance proj1DepsCohs2 `(depsCohs2: DepsCohs2 p.+1 k): DepsCohs2 p k.+1 :=
{|
  _depsCohs := depsCohs2.(_depsCohs).(1);
  _extraDepsCohs := (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs));
  _cohPaintings := depsCohs2.(_cohPaintings).1;
  _coh2Frames := depsCohs2.(_coh2Frames).1;
|}.

Declare Scope depscohs2_scope.
Delimit Scope depscohs2_scope with depscohs2.
Bind Scope depscohs2_scope with DepsCohs2.
Notation "x .(1)" := (proj1DepsCohs2 x%depscohs2)
  (at level 1, left associativity, format "x .(1)"): depscohs2_scope.

#[local]
Instance mkDepsCohs `(depsCohs2: DepsCohs2 p k): DepsCohs p.+1 k :=
{|
  _deps := mkDepsRestr;
  _extraDeps := mkExtraDeps depsCohs2.(_extraDepsCohs);
  _restrPaintings := mkRestrPaintings depsCohs2.(_extraDepsCohs);
  _cohs := mkCohFrames depsCohs2.(_cohPaintings) depsCohs2.(_coh2Frames);
|}.

Inductive DepsCohs2Extension p: forall k (depsCohs2: DepsCohs2 p k), Type :=
| TopCoh2Dep `{depsCohs2: DepsCohs2 p 0}
  (E: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs depsCohs2)) -> H2Gpd):
  DepsCohs2Extension p 0 depsCohs2
| AddCoh2Dep {k} (depsCohs2: DepsCohs2 p.+1 k):
  DepsCohs2Extension p.+1 k depsCohs2 ->
  DepsCohs2Extension p k.+1 depsCohs2.(1).

Arguments TopCoh2Dep {p depsCohs2}.
Arguments AddCoh2Dep {p k}.

Declare Scope extra_depscohs2_scope.
Delimit Scope extra_depscohs2_scope with extradepscohs2.
Bind Scope extra_depscohs2_scope with DepsCohs2Extension.
Notation "( x ; y )" := (AddCoh2Dep x y)
  (at level 0, format "( x ; y )"): extra_depscohs2_scope.

Fixpoint mkExtraCohs `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  DepsCohsExtension p.+1 k (mkDepsCohs depsCohs2).
Proof.
  destruct extraDepsCohs2.
  - now constructor.
  - apply (AddCohDep (mkDepsCohs depsCohs2)).
    now exact (mkExtraCohs p.+1 k depsCohs2 extraDepsCohs2).
Defined.

Local Fixpoint mkCohPaintingRec (r: nat) {struct r}:
  forall p k (depsCohs2: DepsCohs2 p k)
    (extraDepsCohs2: DepsCohs2Extension p k depsCohs2)
    q (Hq: q <= k) (Hr: r <= q) (d: _) (c: _),
  mkCohPaintingInstanceType (mkExtraCohs extraDepsCohs2) q Hq r Hr d c.
Proof.
  destruct r as [|r].
  - intros p k depsCohs2 extraDepsCohs2 q Hq Hr d c.
    now reflexivity.
  - intros p k depsCohs2 extraDepsCohs2 q Hq Hr d c.
    destruct q; [now contradict Hq |].
    destruct extraDepsCohs2; [now contradict Hq |].
    destruct c as [l c].
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting depsCohs2.(_depsCohs).(_extraDeps))).
    + now exact (mkCohLayer depsCohs2.(_cohPaintings).2 depsCohs2.(_coh2Frames).2
        q (⇓ Hq) r (⇓ Hr) d l).
    + now exact (mkCohPaintingRec r p.+1 k depsCohs2 extraDepsCohs2
        q (⇓ Hq) (⇓ Hr) (d; l) c).
Defined.


Definition mkCohPainting `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingType (mkExtraCohs extraDepsCohs2) :=
  fun q Hq r Hr d c => mkCohPaintingRec r p k depsCohs2 extraDepsCohs2 q Hq Hr d c.

Fixpoint mkCohPaintingsPrefix `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2) {struct p}:
  @mkCohPaintingTypes p k.+1 (mkDepsCohs depsCohs2).(1)
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)%extradepscohs.
Proof.
  destruct p.
  - now exact tt.
  - unshelve esplit.
    + now exact (mkCohPaintingsPrefix p k.+1 depsCohs2.(1)%depscohs2
        (depsCohs2; extraDepsCohs2)%extradepscohs2).
    + now exact (mkCohPainting (depsCohs2; extraDepsCohs2)%extradepscohs2).
Defined.

Definition mkCohPaintings `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingTypes (mkExtraCohs extraDepsCohs2) :=
  (mkCohPaintingsPrefix extraDepsCohs2; mkCohPainting extraDepsCohs2).

Definition mkCoh2PaintingSourcePainting {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (d: mkFrame ((mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1)))).(1)): H2Gpd :=
  (mkPaintings ((mkDepsRestr (depsCohs := mkDepsCohs depsCohs2)).(1).(1);
    mkExtraDeps ((mkDepsCohs depsCohs2).(1); (mkDepsCohs depsCohs2;
      mkExtraCohs extraDepsCohs2)))).2 d.

Definition mkCoh2PaintingFrameEndpointType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1)): Type :=
  depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 q Hq
    (mkRestrFrame (depsCohs := depsCohs2.(_depsCohs).(1)) r (Hr ↕ ↑ Hq)
      (mkRestrFrame s (Hs ↕ ↑ (Hr ↕ ↑ Hq)) d)) =
  depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 s (Hs ↕ (Hr ↕ Hq))
    (mkRestrFrame (depsCohs := depsCohs2.(_depsCohs).(1)) r.+1 (⇑ Hr ↕ ⇑ Hq)
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) d)).

Definition mkCoh2PaintingEndpointType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1))
  (c: mkCoh2PaintingSourcePainting depsCohs2 extraDepsCohs2 d)
  (coh2FrameEndpoint: mkCoh2PaintingFrameEndpointType
    depsCohs2 q Hq r Hr s Hs d): Type :=
  let restrPainting1 := mkRestrPainting
    (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs)) in
  let restrPainting2 := mkRestrPainting ((mkDepsCohs depsCohs2).(1);
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)) in
  rew [depsCohs2.(_depsCohs).(_deps).(_paintings).2] coh2FrameEndpoint in
  depsCohs2.(_depsCohs).(_restrPaintings).2 q Hq _
    (restrPainting1 r (Hr ↕ ↑ Hq) _
      (restrPainting2 s (Hs ↕ ↑ (Hr ↕ ↑ Hq)) d c)) =
  depsCohs2.(_depsCohs).(_restrPaintings).2 s (Hs ↕ (Hr ↕ Hq)) _
    (restrPainting1 r.+1 (⇑ Hr ↕ ⇑ Hq) _
      (restrPainting2 q.+2 (⇑ (⇑ Hq)) d c)).

(** Keep the dependent hexagon named to limit conversion work when
    eliminating its painting argument. *)
Definition mkCoh2PaintingInstanceType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1))
  (c: mkCoh2PaintingSourcePainting depsCohs2 extraDepsCohs2 d): Type :=
  let depsCohs := depsCohs2.(_depsCohs) in
  let restrPainting2 := mkRestrPainting ((mkDepsCohs depsCohs2).(1);
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)) in
  hexagonal_coherence_dep
    (Q := fun x => G2Dom (depsCohs.(_deps).(_paintings).2 x))
    (depsCohs.(_restrPaintings).2 q Hq )
    (depsCohs.(_restrPaintings).2 s (Hs ↕ (Hr ↕ Hq)) )
    (depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) )
    (depsCohs2.(_coh2Frames).2 q Hq r Hr s Hs d)
    (mkCohPainting (depsCohs2; extraDepsCohs2) r (Hr ↕ ↑ Hq) s Hs d c)
    (mkCohPainting (depsCohs2; extraDepsCohs2)
      q.+1 (⇑ Hq) r.+1 (⇑ Hr) d c)
    (mkCohPainting (depsCohs2; extraDepsCohs2)
      q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) d c)
    (depsCohs2.(_cohPaintings).2 q Hq s (Hs ↕ Hr)
      (mkRestrFrame r.+1 (⇑ (Hr ↕ ↑ Hq)) d)
      (restrPainting2 r.+1 (⇑ (Hr ↕ ↑ Hq)) d c))
    (depsCohs2.(_cohPaintings).2 q Hq r Hr
      (mkRestrFrame s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) d)
      (restrPainting2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) d c))
    (depsCohs2.(_cohPaintings).2 r (Hr ↕ Hq) s Hs
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) d)
      (restrPainting2 q.+2 (⇑ (⇑ Hq)) d c)).

Definition mkCoh2PaintingType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2): Type :=
  forall
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1))
  (c: mkCoh2PaintingSourcePainting depsCohs2 extraDepsCohs2 d),
  mkCoh2PaintingInstanceType depsCohs2 extraDepsCohs2
    q Hq r Hr s Hs d c.

Fixpoint mkCoh2PaintingTypes {p}:
  forall {k} {depsCohs2: DepsCohs2 p k}
    (extraDepsCohs2: DepsCohs2Extension p k depsCohs2), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k depsCohs2 extraDepsCohs2 =>
    { R: @mkCoh2PaintingTypes p k.+1 depsCohs2.(1)%depscohs2
        (depsCohs2; extraDepsCohs2)%extradepscohs2 &T
         mkCoh2PaintingType depsCohs2 extraDepsCohs2 }
  end.

Definition mkCoh2LayerType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (prevCoh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2;extraDepsCohs2)))
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames (mkCohPaintings
    (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(_restrFrames).2 d): Type :=
  let depsCohs := depsCohs2.(_depsCohs) in
  let depsCohs' := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1) in
  hexagonal_coherence_dep
    (Q := fun x => G2Dom (mkLayer depsCohs.(_deps).(_restrFrames).2 x))
    (mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 q Hq )
    (mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2
      s (Hs ↕ (Hr ↕ Hq)) )
    (mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 r (Hr ↕ Hq) )
    (prevCoh2Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs)    d)
    (mkCohLayer (mkCohPaintings extraDepsCohs2).1.2
      prevCoh2Frames.2 r (Hr ↕ ↑ Hq) s Hs   d l)
    (mkCohLayer (mkCohPaintings extraDepsCohs2).1.2
      prevCoh2Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr)   d l)
    (mkCohLayer (mkCohPaintings extraDepsCohs2).1.2
      prevCoh2Frames.2 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr))   d l)
    (mkCohLayer depsCohs2.(_cohPaintings).2
      depsCohs2.(_coh2Frames).2 q Hq s (Hs ↕ Hr)
      (mkRestrFrame (depsCohs := depsCohs') r.+1 (⇑ (Hr ↕ ↑ Hq))  (d; l)).1
      (mkRestrFrame (depsCohs := depsCohs') r.+1 (⇑ (Hr ↕ ↑ Hq))  (d; l)).2)
    (mkCohLayer depsCohs2.(_cohPaintings).2
      depsCohs2.(_coh2Frames).2 q Hq r Hr
      (mkRestrFrame (depsCohs := depsCohs') s (↑ (↑ (Hs ↕ (Hr ↕ Hq))))  (d; l)).1
      (mkRestrFrame (depsCohs := depsCohs') s (↑ (↑ (Hs ↕ (Hr ↕ Hq))))  (d; l)).2)
    (mkCohLayer depsCohs2.(_cohPaintings).2
      depsCohs2.(_coh2Frames).2 r (Hr ↕ Hq) s Hs
      (mkRestrFrame (depsCohs := depsCohs') q.+2 (⇑ (⇑ Hq))  (d; l)).1
      (mkRestrFrame (depsCohs := depsCohs') q.+2 (⇑ (⇑ Hq))  (d; l)).2).


Definition mkCoh3FrameType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (prevCoh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2;extraDepsCohs2))): Type :=
  let depsCohs' := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1) in
  forall q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) t (Ht: t <= s)
  (d: mkFrame (mkDepsRestr (depsCohs := depsCohs'.(1))).(1)),
  permutahedral_coherence
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (prevCoh2Frames.2 r (Hr ↕ ↑ Hq) s Hs t Ht d)
    (prevCoh2Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) t (↑ (Ht ↕ Hs)) d)
    (prevCoh2Frames.2 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) t Ht d)
    (prevCoh2Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) d)
    (depsCohs2.(_coh2Frames).2 q Hq s (Hs ↕ Hr) t Ht
      (mkRestrFrame (depsCohs := depsCohs'.(1)) r.+2 (⇑ (⇑ (Hr ↕ ↑ Hq))) d))
    (depsCohs2.(_coh2Frames).2 q Hq r Hr t (Ht ↕ Hs)
      (mkRestrFrame (depsCohs := depsCohs'.(1)) s.+1 (⇑ (↑ (↑ (Hs ↕ (Hr ↕ Hq))))) d))
    (depsCohs2.(_coh2Frames).2 r (Hr ↕ Hq) s Hs t Ht
      (mkRestrFrame (depsCohs := depsCohs'.(1)) q.+3 (⇑ (⇑ (⇑ Hq))) d))
    (depsCohs2.(_coh2Frames).2 q Hq r Hr s Hs
    (((mkCohFrameTypesAndRestrFrames
        (mkRestrPaintings (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)).1.1)
      .(RestrFramesDef) ((mkCoh2FrameTypesAndCohFrames
          (mkCohPaintings (depsCohs2; extraDepsCohs2)).1)
        .(CohFramesDef) prevCoh2Frames.1).1).2
       t (↑ (Ht ↕ (↑ (Hs ↕ Hr) ↕ ↑ (⇑ Hq)))) d)).

Definition mkCoh2Layer {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (prevCoh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2;extraDepsCohs2)))
  (coh2Painting: mkCoh2PaintingType depsCohs2 extraDepsCohs2)
  (coh3Frame: mkCoh3FrameType depsCohs2 extraDepsCohs2 prevCoh2Frames)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(_restrFrames).2 d):
  mkCoh2LayerType depsCohs2 extraDepsCohs2 prevCoh2Frames q Hq r Hr s Hs d l.
Proof.
  unfold mkCoh2LayerType, mkCohLayer.
  eapply (rew_coh2Layer_perm4
    (S2 := fun x => (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(_paintings).2 x)
    (S1 := fun x => (mkDepsCohs depsCohs2).(1).(_deps).(_paintings).2 x)
    (S0 := fun x => depsCohs2.(_depsCohs).(_deps).(_paintings).2 x)
    (uf0 := fun x => (mkDepsCohs depsCohs2).(1).(_deps).(_restrFrames).2 0 leR_O x)
    (rf0 := fun x => depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 0 leR_O x)
    (Rr := (mkDepsCohs depsCohs2).(1).(_restrPaintings).2 r (Hr ↕ ↑ Hq))
    (Rs := (mkDepsCohs depsCohs2).(1).(_restrPaintings).2 s (Hs ↕ (Hr ↕ ↑ Hq)))
    (Rq1 := (mkDepsCohs depsCohs2).(1).(_restrPaintings).2 q.+1 (⇑ Hq))
    (Rr1 := (mkDepsCohs depsCohs2).(1).(_restrPaintings).2 r.+1 (⇑ Hr ↕ ⇑ Hq))
    (Fq := depsCohs2.(_depsCohs).(_restrPaintings).2 q Hq)
    (Fr := depsCohs2.(_depsCohs).(_restrPaintings).2 r (Hr ↕ Hq))
    (Fs := depsCohs2.(_depsCohs).(_restrPaintings).2 s ((Hs ↕ Hr) ↕ Hq))
    (gq := fun x => depsCohs2.(_depsCohs).(_cohs).2 q Hq 0 leR_O x)
    (gr := fun x => depsCohs2.(_depsCohs).(_cohs).2 r (Hr ↕ Hq) 0 leR_O x)
    (gs := fun x => depsCohs2.(_depsCohs).(_cohs).2 s ((Hs ↕ Hr) ↕ Hq) 0 leR_O x)
    (KA2 := fun x => depsCohs2.(_depsCohs).(_cohs).2 q Hq s (Hs ↕ Hr) x)
    (KA4 := fun x => depsCohs2.(_depsCohs).(_cohs).2 q Hq r Hr x)
    (KA6 := fun x => depsCohs2.(_depsCohs).(_cohs).2 r (Hr ↕ Hq) s Hs x)
    (HKA2 := fun x c => depsCohs2.(_cohPaintings).2 q Hq s (Hs ↕ Hr) x c)
    (HKA4 := fun x c => depsCohs2.(_cohPaintings).2 q Hq r Hr x c)
    (HKA6 := fun x c => depsCohs2.(_cohPaintings).2 r (Hr ↕ Hq) s Hs x c)).
  - now exact (coh2Painting q Hq r Hr s Hs
      (((mkCohFrameTypesAndRestrFrames
          (mkRestrPaintings (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)).1.1)
        .(RestrFramesDef) ((mkCoh2FrameTypesAndCohFrames
            (mkCohPaintings (depsCohs2; extraDepsCohs2)).1)
          .(CohFramesDef) prevCoh2Frames.1).1).2 0 leR_O d) l).
  - now apply (coh3Frame q Hq r Hr s Hs 0 leR_O d).
Defined.

Class Coh3FrameTypeBlock `{extraDepsCohs2: DepsCohs2Extension p k depsCohs2} := {
  Coh3FrameTypesDef: Type;
  Coh2FramesDef: Coh3FrameTypesDef -> mkCoh2FrameTypes (mkCohPaintings extraDepsCohs2);
}.

Definition mkCoh3FrameTypesStep
  `{extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2}
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2)
  (prev: Coh3FrameTypeBlock
    (extraDepsCohs2 := (depsCohs2; extraDepsCohs2)%extradepscohs2)): Type :=
  { R: prev.(Coh3FrameTypesDef) &T
    mkCoh3FrameType depsCohs2 extraDepsCohs2 (prev.(Coh2FramesDef) R) }.

Fixpoint mkCoh3FrameTypesAndCoh2Frames {p k}:
  forall `{extraDepsCohs2: DepsCohs2Extension p k depsCohs2}
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2),
  Coh3FrameTypeBlock (extraDepsCohs2 := extraDepsCohs2).
Proof.
  destruct p.
  - intros depsCohs2 extraDepsCohs2 coh2Paintings.
    unshelve econstructor.
    + now exact unit.
    + intros _. unshelve esplit.
      * now exact tt.
      * intros q Hq r Hr s Hs d.
        now trivial.
  - intros depsCohs2 extraDepsCohs2 coh2Paintings.
    set (prev := mkCoh3FrameTypesAndCoh2Frames p k.+1
      depsCohs2.(1)%depscohs2
      (depsCohs2; extraDepsCohs2)%extradepscohs2 coh2Paintings.1).
    unshelve econstructor.
    + now exact (mkCoh3FrameTypesStep coh2Paintings prev).
    + intros Q.
      set (h := prev.(Coh2FramesDef) Q.1).
      unshelve esplit.
      * now exact h.
      * intros q Hq r Hr s Hs [d l].
        unshelve eapply eq_existT_curried_hex.
        -- now exact (h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) d).
        -- now exact (mkCoh2Layer depsCohs2 extraDepsCohs2 h
             coh2Paintings.2 Q.2 q Hq r Hr s Hs d l).
Defined.

Definition mkCoh3FrameTypes `{extraDepsCohs2: DepsCohs2Extension p k depsCohs2}
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2) :=
  (mkCoh3FrameTypesAndCoh2Frames coh2Paintings).(Coh3FrameTypesDef).

Definition mkCoh2Frames `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2)
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2)
  (coh3Frames: mkCoh3FrameTypes coh2Paintings):
  mkCoh2FrameTypes (mkCohPaintings extraDepsCohs2) :=
  (mkCoh3FrameTypesAndCoh2Frames coh2Paintings).(Coh2FramesDef) coh3Frames.

Class DepsCohs3 p k := {
  _depsCohs2: DepsCohs2 p k;
  _extraDepsCohs2: DepsCohs2Extension p k _depsCohs2;
  _coh2Paintings: mkCoh2PaintingTypes _extraDepsCohs2;
  _coh3Frames: mkCoh3FrameTypes _coh2Paintings;
}.

#[local]
Instance toDepsCohs3 `{extraDepsCohs2: DepsCohs2Extension p k depsCohs2}
  {coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2}
  (coh3Frames: mkCoh3FrameTypes coh2Paintings): DepsCohs3 p k :=
  {| _coh3Frames := coh3Frames |}.

#[local]
Instance proj1DepsCohs3 `(depsCohs3: DepsCohs3 p.+1 k): DepsCohs3 p k.+1 :=
{|
  _depsCohs2 := depsCohs3.(_depsCohs2).(1);
  _extraDepsCohs2 := (depsCohs3.(_depsCohs2); depsCohs3.(_extraDepsCohs2));
  _coh2Paintings := depsCohs3.(_coh2Paintings).1;
  _coh3Frames := depsCohs3.(_coh3Frames).1;
|}.

Declare Scope depscohs3_scope.
Delimit Scope depscohs3_scope with depscohs3.
Bind Scope depscohs3_scope with DepsCohs3.
Notation "x .(1)" := (proj1DepsCohs3 x%depscohs3)
  (at level 1, left associativity, format "x .(1)"): depscohs3_scope.

#[local]
Instance mkDepsCohs2 `(depsCohs3: DepsCohs3 p k): DepsCohs2 p.+1 k :=
{|
  _depsCohs := mkDepsCohs depsCohs3.(_depsCohs2);
  _extraDepsCohs := mkExtraCohs depsCohs3.(_extraDepsCohs2);
  _cohPaintings := mkCohPaintings depsCohs3.(_extraDepsCohs2);
  _coh2Frames := mkCoh2Frames depsCohs3.(_extraDepsCohs2) depsCohs3.(_coh2Paintings)
    depsCohs3.(_coh3Frames);
|}.

Inductive DepsCohs3Extension p: forall k (depsCohs3: DepsCohs3 p k), Type :=
| TopCoh3Dep `{depsCohs3: DepsCohs3 p 0}
  (E: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs (mkDepsCohs2 depsCohs3))) -> H2Gpd)
  : DepsCohs3Extension p 0 depsCohs3
| AddCoh3Dep {k} (depsCohs3: DepsCohs3 p.+1 k):
  DepsCohs3Extension p.+1 k depsCohs3 ->
  DepsCohs3Extension p k.+1 depsCohs3.(1).

Arguments TopCoh3Dep {p depsCohs3}.
Arguments AddCoh3Dep {p k}.

Declare Scope extra_depscohs3_scope.
Delimit Scope extra_depscohs3_scope with extradepscohs3.
Bind Scope extra_depscohs3_scope with DepsCohs3Extension.
Notation "( x ; y )" := (AddCoh3Dep x y)
  (at level 0, format "( x ; y )"): extra_depscohs3_scope.

Fixpoint mkExtraCohs2 `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3):
  DepsCohs2Extension p.+1 k (mkDepsCohs2 depsCohs3).
Proof.
  destruct extraDepsCohs3.
  - now constructor.
  - apply (AddCoh2Dep (mkDepsCohs2 depsCohs3)).
    now exact (mkExtraCohs2 p.+1 k depsCohs3 extraDepsCohs3).
Defined.

Local Definition mkCoh2Painting_restr0 {p k}
  (deps3: DepsCohs3 p k) (extra3: DepsCohs3Extension p k deps3)
  q (Hq: q <= k) r (Hr: r <= q) (d: _) (c: _):
  mkCoh2PaintingInstanceType (mkDepsCohs2 deps3) (mkExtraCohs2 extra3)
    q Hq r Hr 0 leR_O d c.
Proof.
  unfold mkCoh2PaintingInstanceType; cbv zeta.
  lazymatch goal with
  | |- context [@hexagonal_coherence_dep _ _ _ _ ?S _ ?SR ?P] =>
    now eapply (rew_coh2Painting_restr0
      (P := P) (S := S) (SR := SR))
  end.
Defined.

(** A sigma painting combines the layer and recursive painting hexagons. *)
Local Definition mkCoh2Painting_step {p k}
  (depsCohs3: DepsCohs3 p.+1 k)
  (extraDepsCohs3: DepsCohs3Extension p.+1 k depsCohs3)
  q (Hq: q.+1 <= k.+1) r (Hr: r.+1 <= q.+1) s (Hs: s.+1 <= r.+1)
  (d: _) (l: _) (c: _)
  (Rec: mkCoh2PaintingInstanceType (mkDepsCohs2 depsCohs3)
    (mkExtraCohs2 extraDepsCohs3) q (⇓ Hq) r (⇓ Hr) s (⇓ Hs) (d; l) c):
  mkCoh2PaintingInstanceType (mkDepsCohs2 depsCohs3.(1))
    (mkExtraCohs2 (depsCohs3; extraDepsCohs3))
    q.+1 Hq r.+1 Hr s.+1 Hs d (l; c).
Proof.
  unfold mkCoh2PaintingInstanceType; cbv zeta.
  unshelve eapply (eq_existT_curried_hex_dep
    (A1 := ((mkRestrFrameTypesAndFrames
        (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_paintings).1)
      .(FrameDef)
        (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).1).2)
    (B := ((mkRestrFrameTypesAndFrames
        depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_paintings).1)
      .(FrameDef)
        depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_restrFrames).1).2)
    (P1 := fun a => (mkLayer
      (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
      a).(G2Dom))
    (R1 := fun a u => (mkPainting
      (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_extraDeps) (a; u)).(G2Dom))
    (P' := fun b => (mkLayer
      depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_restrFrames).2 b).(G2Dom))
    (R' := fun b u => (mkPainting
      depsCohs3.(_depsCohs2).(_depsCohs).(_extraDeps) (b; u)).(G2Dom))
    ((mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
      q.+1 Hq )
    (fun d0 l0 => mkRestrLayer
      depsCohs3.(_depsCohs2).(_depsCohs).(_restrPaintings).2
      depsCohs3.(_depsCohs2).(_depsCohs).(_cohs).2 q (⇓ Hq) d0 l0)
    (fun d0 l0 c0 => mkRestrPainting
      depsCohs3.(_depsCohs2).(_extraDepsCohs) q (⇓ Hq) (d0; l0) c0)
    ((mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
      s.+1 (Hs ↕ (Hr ↕ Hq)) )
    (fun d0 l0 => mkRestrLayer
      depsCohs3.(_depsCohs2).(_depsCohs).(_restrPaintings).2
      depsCohs3.(_depsCohs2).(_depsCohs).(_cohs).2
      s (⇓ (Hs ↕ (Hr ↕ Hq))) d0 l0)
    (fun d0 l0 c0 => mkRestrPainting
      depsCohs3.(_depsCohs2).(_extraDepsCohs)
      s (⇓ (Hs ↕ (Hr ↕ Hq))) (d0; l0) c0)
    ((mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
      r.+1 (Hr ↕ Hq) )
    (fun d0 l0 => mkRestrLayer
      depsCohs3.(_depsCohs2).(_depsCohs).(_restrPaintings).2
      depsCohs3.(_depsCohs2).(_depsCohs).(_cohs).2 r (⇓ (Hr ↕ Hq)) d0 l0)
    (fun d0 l0 c0 => mkRestrPainting
      depsCohs3.(_depsCohs2).(_extraDepsCohs) r (⇓ (Hr ↕ Hq)) (d0; l0) c0)).
  + now exact (mkCoh2Layer depsCohs3.(_depsCohs2) depsCohs3.(_extraDepsCohs2)
      (mkCoh2Frames (depsCohs3.(_depsCohs2); depsCohs3.(_extraDepsCohs2))
        depsCohs3.(1).(_coh2Paintings) depsCohs3.(1).(_coh3Frames))
      depsCohs3.(_coh2Paintings).2 depsCohs3.(_coh3Frames).2 q (⇓ Hq) r (⇓ Hr) s (⇓ Hs) d l).
  + now exact Rec.
Defined.

Local Fixpoint mkCoh2PaintingRec (s: nat) {struct s}:
  forall p k (depsCohs3: DepsCohs3 p k)
    (extraDepsCohs3: DepsCohs3Extension p k depsCohs3)
    q (Hq: q <= k) r (Hr: r <= q) (Hs: s <= r) (d: _) (c: _),
  mkCoh2PaintingInstanceType (mkDepsCohs2 depsCohs3)
    (mkExtraCohs2 extraDepsCohs3) q Hq r Hr s Hs d c.
Proof.
  destruct s as [|s].
  - intros p k depsCohs3 extraDepsCohs3 q Hq r Hr Hs d c.
    now exact (mkCoh2Painting_restr0 depsCohs3 extraDepsCohs3 q Hq r Hr d c).
  - intros p k depsCohs3 extraDepsCohs3 q Hq r Hr Hs d c.
    destruct r; [now contradiction |].
    destruct q; [now contradiction |].
    destruct extraDepsCohs3; [now contradiction |].
    destruct c as [l c].
    now exact (mkCoh2Painting_step depsCohs3 extraDepsCohs3 q Hq r Hr s Hs d l c
      (mkCoh2PaintingRec s p.+1 k depsCohs3 extraDepsCohs3
        q (⇓ Hq) r (⇓ Hr) (⇓ Hs) (d; l) c)).
Defined.

Definition mkCoh2Painting `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3):
  mkCoh2PaintingType (mkDepsCohs2 depsCohs3) (mkExtraCohs2 extraDepsCohs3) :=
  fun q Hq r Hr s Hs d c =>
    mkCoh2PaintingRec s p k depsCohs3 extraDepsCohs3 q Hq r Hr Hs d c.

Fixpoint mkCoh2PaintingsPrefix `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3) {struct p}:
  @mkCoh2PaintingTypes p k.+1 (mkDepsCohs2 depsCohs3).(1)%depscohs2
    (mkDepsCohs2 depsCohs3; mkExtraCohs2 extraDepsCohs3)%extradepscohs2.
Proof.
  destruct p.
  - now exact tt.
  - unshelve esplit.
    + now exact (mkCoh2PaintingsPrefix p k.+1 depsCohs3.(1)%depscohs3
        (depsCohs3; extraDepsCohs3)%extradepscohs3).
    + now exact (mkCoh2Painting (depsCohs3; extraDepsCohs3)%extradepscohs3).
Defined.

Definition mkCoh2Paintings `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3):
  mkCoh2PaintingTypes (mkExtraCohs2 extraDepsCohs3) :=
  (mkCoh2PaintingsPrefix extraDepsCohs3; mkCoh2Painting extraDepsCohs3).

Definition mkCoh3PaintingSourceFrame {p k}
  (depsCohs3: DepsCohs3 p.+1 k): H2Gpd :=
  mkFrame (mkDepsRestr
    (depsCohs := (mkDepsCohs (mkDepsCohs2 depsCohs3)).(1).(1).(1))).(1).

Definition mkCoh3PaintingSourcePainting {p k}
  (depsCohs3: DepsCohs3 p.+1 k)
  (extraDepsCohs3: DepsCohs3Extension p.+1 k depsCohs3):
  mkCoh3PaintingSourceFrame depsCohs3 -> H2Gpd :=
  mkCoh2PaintingSourcePainting (mkDepsCohs2 depsCohs3).(1)
    (mkDepsCohs2 depsCohs3; mkExtraCohs2 extraDepsCohs3).

Definition mkCoh3PaintingInstanceType {p k}
  (depsCohs3: DepsCohs3 p.+1 k)
  (extraDepsCohs3: DepsCohs3Extension p.+1 k depsCohs3)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) t (Ht: t <= s)
  (d: mkCoh3PaintingSourceFrame depsCohs3)
  (c: mkCoh3PaintingSourcePainting depsCohs3 extraDepsCohs3 d): Type :=
  let deps2 := (mkDepsCohs2 depsCohs3).(1)%depscohs2 in
  let extra2 := (mkDepsCohs2 depsCohs3; mkExtraCohs2 extraDepsCohs3)%extradepscohs2 in
  let rf := mkRestrFrame (depsCohs := (mkDepsCohs deps2).(1).(1)) in
  let rp := mkRestrPainting ((mkDepsCohs deps2).(1);
    (mkDepsCohs deps2; mkExtraCohs extra2)) in
  permutahedral_coherence_dep
    (depsCohs3.(_coh3Frames).2 q Hq r Hr s Hs t Ht d)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (mkCoh2Painting (depsCohs3; extraDepsCohs3)
      r (Hr ↕ ↑ Hq) s Hs t Ht d c)
    (mkCoh2Painting (depsCohs3; extraDepsCohs3)
      q.+1 (⇑ Hq) r.+1 (⇑ Hr) t (↑ (Ht ↕ Hs)) d c)
    (mkCoh2Painting (depsCohs3; extraDepsCohs3)
      q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) t Ht d c)
    (mkCoh2Painting (depsCohs3; extraDepsCohs3)
      q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) d c)
    (depsCohs3.(_coh2Paintings).2 q Hq s (Hs ↕ Hr) t Ht
      (rf r.+2 (⇑ (⇑ (Hr ↕ ↑ Hq))) d)
      (rp r.+2 (⇑ (⇑ (Hr ↕ ↑ Hq))) d c))
    (depsCohs3.(_coh2Paintings).2 q Hq r Hr t (Ht ↕ Hs)
      (rf s.+1 (⇑ (↑ (↑ (Hs ↕ (Hr ↕ Hq))))) d)
      (rp s.+1 (⇑ (↑ (↑ (Hs ↕ (Hr ↕ Hq))))) d c))
    (depsCohs3.(_coh2Paintings).2 r (Hr ↕ Hq) s Hs t Ht
      (rf q.+3 (⇑ (⇑ (⇑ Hq))) d)
      (rp q.+3 (⇑ (⇑ (⇑ Hq))) d c))
    (depsCohs3.(_coh2Paintings).2 q Hq r Hr s Hs
      (rf t (↑ (↑ (↑ (Ht ↕ (Hs ↕ (Hr ↕ Hq)))))) d)
      (rp t (↑ (↑ (↑ (Ht ↕ (Hs ↕ (Hr ↕ Hq)))))) d c)).

Definition mkCoh3PaintingType {p k}
  (depsCohs3: DepsCohs3 p.+1 k)
  (extraDepsCohs3: DepsCohs3Extension p.+1 k depsCohs3): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) t (Ht: t <= s)
    (d: mkCoh3PaintingSourceFrame depsCohs3)
    (c: mkCoh3PaintingSourcePainting depsCohs3 extraDepsCohs3 d),
    mkCoh3PaintingInstanceType depsCohs3 extraDepsCohs3 q Hq r Hr s Hs t Ht d c.

Fixpoint mkCoh3PaintingTypes {p}:
  forall {k} {depsCohs3: DepsCohs3 p k}
    (extraDepsCohs3: DepsCohs3Extension p k depsCohs3), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p => fun k depsCohs3 extraDepsCohs3 =>
    { R: @mkCoh3PaintingTypes p k.+1 depsCohs3.(1)%depscohs3
        (depsCohs3; extraDepsCohs3)%extradepscohs3 &T
      mkCoh3PaintingType depsCohs3 extraDepsCohs3 }
  end.

Local Opaque mkCohLayer mkCoh2Layer.

Definition mkCoh3LayerType {p k}
  (depsCohs3: DepsCohs3 p.+1 k)
  (extraDepsCohs3: DepsCohs3Extension p.+1 k depsCohs3)
  (prevCoh3Frames: mkCoh3FrameTypes (mkCoh2Paintings (depsCohs3; extraDepsCohs3)))
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) t (Ht: t <= s)
  (d: _) (l: _): Type :=
  let deps2 := mkDepsCohs2 depsCohs3 in
  let extra2 := mkExtraCohs2 extraDepsCohs3 in
  let cf2 := mkCoh2Frames (mkExtraCohs2 (depsCohs3; extraDepsCohs3))
    (mkCoh2Paintings (depsCohs3; extraDepsCohs3)) prevCoh3Frames in
  let cl := mkCoh2Layer deps2.(1) (deps2; extra2) cf2.1
    (mkCoh2Paintings extraDepsCohs3).1.2 prevCoh3Frames.2 in
  let cl0 := mkCoh2Layer depsCohs3.(_depsCohs2) depsCohs3.(_extraDepsCohs2)
    deps2.(_coh2Frames).1 depsCohs3.(_coh2Paintings).2 depsCohs3.(_coh3Frames).2 in
  let rf := mkRestrFrame (depsCohs := (toDepsCohs (mkCohFrames
    (depsCohs := (mkDepsCohs (mkDepsCohs2 depsCohs3)).(1).(1))
    (extraDepsCohs := ((mkDepsCohs (mkDepsCohs2 depsCohs3)).(1);
      mkExtraCohs (mkDepsCohs2 depsCohs3; mkExtraCohs2 extraDepsCohs3)))
    (mkCohPaintings (mkDepsCohs2 depsCohs3; mkExtraCohs2 extraDepsCohs3)).1
    (mkCoh2Frames (mkExtraCohs2 (depsCohs3; extraDepsCohs3))
      (mkCoh2Paintings (depsCohs3; extraDepsCohs3)) prevCoh3Frames).1)).(1)) in
  permutahedral_coherence_dep
    (prevCoh3Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) t.+1 (⇑ Ht) d)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (cl r (Hr ↕ ↑ Hq) s Hs t Ht d l)
    (cl q.+1 (⇑ Hq) r.+1 (⇑ Hr) t (↑ (Ht ↕ Hs)) d l)
    (cl q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) t Ht d l)
    (cl q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) d l)
    (cl0 q Hq s (Hs ↕ Hr) t Ht
      (rf r.+2 (⇑ (⇑ (Hr ↕ ↑ Hq))) (d; l)).1
      (rf r.+2 (⇑ (⇑ (Hr ↕ ↑ Hq))) (d; l)).2)
    (cl0 q Hq r Hr t (Ht ↕ Hs)
      (rf s.+1 (⇑ (↑ (↑ (Hs ↕ (Hr ↕ Hq))))) (d; l)).1
      (rf s.+1 (⇑ (↑ (↑ (Hs ↕ (Hr ↕ Hq))))) (d; l)).2)
    (cl0 r (Hr ↕ Hq) s Hs t Ht
      (rf q.+3 (⇑ (⇑ (⇑ Hq))) (d; l)).1
      (rf q.+3 (⇑ (⇑ (⇑ Hq))) (d; l)).2)
    (cl0 q Hq r Hr s Hs
      (rf t (↑ (↑ (↑ (Ht ↕ (Hs ↕ (Hr ↕ Hq)))))) (d; l)).1
      (rf t (↑ (↑ (↑ (Ht ↕ (Hs ↕ (Hr ↕ Hq)))))) (d; l)).2).

Local Transparent mkCohLayer mkCoh2Layer.

Local Opaque rew_cohLayer_hex rew_coh2Layer_perm4.

Definition mkCoh3Layer {p k}
  (depsCohs3: DepsCohs3 p.+1 k)
  (extraDepsCohs3: DepsCohs3Extension p.+1 k depsCohs3)
  (prevCoh3Frames: mkCoh3FrameTypes (mkCoh2Paintings (depsCohs3; extraDepsCohs3)))
  (coh3Painting: mkCoh3PaintingType depsCohs3 extraDepsCohs3)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) t (Ht: t <= s)
  (d: _) (l: _) :
  mkCoh3LayerType depsCohs3 extraDepsCohs3 prevCoh3Frames q Hq r Hr s Hs t Ht d l.
Proof.
  unfold mkCoh3LayerType.
  cbv beta zeta.
  (* Select the source layer's zero restriction map. *)
  let LT := type of l in
  lazymatch LT with
  | G2Dom (@mkLayer _ _ _ _ ?rf _ _) =>
    let e0 := constr:(rf 0 leR_O) in
    let hp := constr:(coh3Painting q Hq r Hr s Hs t Ht (e0 d) l) in
    eapply rew_coh3Layer_perm5 with (x := d) (dE_0_0_U := e0)
      (kABCD_nil := fun x => prevCoh3Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) t.+1 (⇑ Ht) x)
      (kBCDE_nil := fun x => prevCoh3Frames.2 r (Hr ↕ ↑ Hq) s Hs t Ht 0 leR_O x)
      (kABDE_nil := fun x => prevCoh3Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) t (↑ (Ht ↕ Hs)) 0 leR_O x)
      (kACDE_nil := fun x => prevCoh3Frames.2 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) t Ht 0 leR_O x)
      (kABCE_nil := fun x => prevCoh3Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) 0 leR_O x)
      (kABCD_E := fun x => depsCohs3.(_coh3Frames).2 q Hq r Hr s Hs t Ht x)
      (kACDE_B := fun x => depsCohs3.(_coh3Frames).2 q Hq s (Hs ↕ Hr) t Ht 0 leR_O x)
      (kABDE_C := fun x => depsCohs3.(_coh3Frames).2 q Hq r Hr t (Ht ↕ Hs) 0 leR_O x)
      (kBCDE_A := fun x => depsCohs3.(_coh3Frames).2 r (Hr ↕ Hq) s Hs t Ht 0 leR_O x)
      (kABCE_D := fun x => depsCohs3.(_coh3Frames).2 q Hq r Hr s Hs 0 leR_O x)
        (HhABC_DE := depsCohs3.(_coh2Paintings).2 q Hq r Hr s Hs)
        (HhABD_CE := depsCohs3.(_coh2Paintings).2 q Hq r Hr t (Ht ↕ Hs))
        (HhACD_BE := depsCohs3.(_coh2Paintings).2 q Hq s (Hs ↕ Hr) t Ht)
        (HhBCD_AE := depsCohs3.(_coh2Paintings).2 r (Hr ↕ Hq) s Hs t Ht)
        (HP := hp)
  end.
  now apply depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_frames).2.(G2UIP).
Defined.

Local Transparent rew_cohLayer_hex rew_coh2Layer_perm4.

Fixpoint mkCoh3Frames p k
  (depsCohs3: DepsCohs3 p k)
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3)
  (coh3Paintings: mkCoh3PaintingTypes extraDepsCohs3):
  mkCoh3FrameTypes (mkCoh2Paintings extraDepsCohs3).
Proof.
  destruct p.
  - unshelve esplit.
    + now exact tt.
    + intros q Hq r Hr s Hs t Ht d.
      now reflexivity.
  - pose (h := mkCoh3Frames p k.+1 depsCohs3.(1)%depscohs3
      (depsCohs3; extraDepsCohs3)%extradepscohs3 coh3Paintings.1).
    unshelve esplit.
    + now exact h.
    + intros q Hq r Hr s Hs t Ht [d l].
      unshelve eapply eq_existT_curried_perm4 with
        (P := h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) t.+1 (⇑ Ht) d).
      now exact (mkCoh3Layer depsCohs3 extraDepsCohs3 h coh3Paintings.2
        q Hq r Hr s Hs t Ht d l).
Defined.

Class DepsCohs4 p k := {
  _depsCohs3: DepsCohs3 p k;
  _extraDepsCohs3: DepsCohs3Extension p k _depsCohs3;
  _coh3Paintings: mkCoh3PaintingTypes _extraDepsCohs3;
}.

#[local]
Instance toDepsCohs4 `{extraDepsCohs3: DepsCohs3Extension p k depsCohs3}
  (coh3Paintings: mkCoh3PaintingTypes extraDepsCohs3): DepsCohs4 p k :=
  {| _coh3Paintings := coh3Paintings |}.

#[local]
Instance proj1DepsCohs4 `(depsCohs4: DepsCohs4 p.+1 k): DepsCohs4 p k.+1 :=
{|
  _depsCohs3 := depsCohs4.(_depsCohs3).(1)%depscohs3;
  _extraDepsCohs3 := (depsCohs4.(_depsCohs3); depsCohs4.(_extraDepsCohs3))%extradepscohs3;
  _coh3Paintings := depsCohs4.(_coh3Paintings).1;
|}.

Declare Scope depscohs4_scope.
Delimit Scope depscohs4_scope with depscohs4.
Bind Scope depscohs4_scope with DepsCohs4.
Notation "x .(1)" := (proj1DepsCohs4 x%depscohs4)
  (at level 1, left associativity, format "x .(1)"): depscohs4_scope.

#[local]
Instance mkDepsCohs3 `(depsCohs4: DepsCohs4 p k): DepsCohs3 p.+1 k :=
{|
  _depsCohs2 := mkDepsCohs2 depsCohs4.(_depsCohs3);
  _extraDepsCohs2 := mkExtraCohs2 depsCohs4.(_extraDepsCohs3);
  _coh2Paintings := mkCoh2Paintings depsCohs4.(_extraDepsCohs3);
  _coh3Frames := mkCoh3Frames p k depsCohs4.(_depsCohs3)
    depsCohs4.(_extraDepsCohs3) depsCohs4.(_coh3Paintings);
|}.

Inductive DepsCohs4Extension p: forall k (depsCohs4: DepsCohs4 p k), Type :=
| TopCoh4Dep `{depsCohs4: DepsCohs4 p 0}
  (E: mkFrame (mkDepsRestr
    (depsCohs := mkDepsCohs (mkDepsCohs2 (mkDepsCohs3 depsCohs4)))) -> H2Gpd)
  : DepsCohs4Extension p 0 depsCohs4
| AddCoh4Dep {k} (depsCohs4: DepsCohs4 p.+1 k):
  DepsCohs4Extension p.+1 k depsCohs4 ->
  DepsCohs4Extension p k.+1 depsCohs4.(1)%depscohs4.

Arguments TopCoh4Dep {p depsCohs4}.
Arguments AddCoh4Dep {p k}.

Declare Scope extra_depscohs4_scope.
Delimit Scope extra_depscohs4_scope with extradepscohs4.
Bind Scope extra_depscohs4_scope with DepsCohs4Extension.
Notation "( x ; y )" := (AddCoh4Dep x y)
  (at level 0, format "( x ; y )"): extra_depscohs4_scope.

Fixpoint mkExtraCohs3 `{depsCohs4: DepsCohs4 p k}
  (extraDepsCohs4: DepsCohs4Extension p k depsCohs4):
  DepsCohs3Extension p.+1 k (mkDepsCohs3 depsCohs4).
Proof.
  destruct extraDepsCohs4.
  - now constructor.
  - apply (AddCoh3Dep (mkDepsCohs3 depsCohs4)).
    now exact (mkExtraCohs3 p.+1 k depsCohs4 extraDepsCohs4).
Defined.

(** The zero restriction projects away the newest sigma component.
    Keep the rank abstract so that comparing its boundary does not unfold
    the earlier layers of the tower. *)

Local Opaque eq_existT_curried_hex mkCoh2Layer.

Local Lemma mkCoh2Frames_head {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2)
  (coh3Frames: mkCoh3FrameTypes coh2Paintings)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: _) (l: _):
  let h := mkCoh2Frames (depsCohs2; extraDepsCohs2) coh2Paintings.1 coh3Frames.1 in
  (mkCoh2Frames extraDepsCohs2 coh2Paintings coh3Frames).2 q Hq r Hr s Hs (d; l) =
  eq_existT_curried_hex _ _ _ _ _ _
    (h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) d)
    (mkCoh2Layer depsCohs2 extraDepsCohs2 h coh2Paintings.2 coh3Frames.2
      q Hq r Hr s Hs d l).
Proof. now reflexivity. Defined.
Local Transparent eq_existT_curried_hex mkCoh2Layer.

Local Definition transport_hexagonal_coherence_dep {A1 A2 A3 B: Type}
  {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {Q: B -> Type}
  {f1: A1 -> B} {f2: A2 -> B} {f3: A3 -> B}
  {F1: forall x, P1 x -> Q (f1 x)}
  {F2: forall x, P2 x -> Q (f2 x)}
  {F3: forall x, P3 x -> Q (f3 x)}
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  {u0: P1 x0} {u1: P1 x1} {u2: P2 x2} {u3: P2 x3}
  {u4: P3 x4} {u5: P3 x5}
  {p1: x0 = x1} {p2: x2 = x3} {p3: x4 = x5}
  {h1: f1 x1 = f2 x2} {h2: f1 x0 = f3 x4} {h3: f3 x5 = f2 x3}
  {H H': hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3}
  {q1: rew [P1] p1 in u0 = u1}
  {q2: rew [P2] p2 in u2 = u3}
  {q3: rew [P3] p3 in u4 = u5}
  {k1: rew [Q] h1 in F1 x1 u1 = F2 x2 u2}
  {k2: rew [Q] h2 in F1 x0 u0 = F3 x4 u4}
  {k3: rew [Q] h3 in F3 x5 u5 = F2 x3 u3}
  (E: H = H') (h: hexagonal_coherence_dep F1 F2 F3 H q1 q2 q3 k1 k2 k3):
  hexagonal_coherence_dep F1 F2 F3 H' q1 q2 q3 k1 k2 k3 :=
  rew [fun C => hexagonal_coherence_dep F1 F2 F3 C q1 q2 q3 k1 k2 k3] E in h.

Local Opaque eq_existT_curried_dep sigT_map_eq rew_coh2Layer_perm4
  permutahedral_coherence_dep hexagonal_coherence_dep eq_existT_curried_hex
  eq_existT_curried_hex_dep rew_coh2Painting_restr0.

Local Definition mkDepsCohs3WithFrames {p k}
  (base: DepsCohs3 p k) (extra: DepsCohs3Extension p k base)
  (frames: mkCoh3FrameTypes (mkCoh2Paintings extra)): DepsCohs3 p.+1 k :=
  {| _depsCohs2 := mkDepsCohs2 base;
     _extraDepsCohs2 := mkExtraCohs2 extra;
     _coh2Paintings := mkCoh2Paintings extra;
     _coh3Frames := frames |}.

(** Use the chosen cap's sigma families and maps when projecting away
    the newest painting component. *)
Local Lemma mkCoh3Painting_restr0 {p k}
  (base: DepsCohs3 p k) (extra: DepsCohs3Extension p k base)
  (frames: mkCoh3FrameTypes (mkCoh2Paintings extra))
  (paintingExtra: DepsCohs3Extension p.+1 k (mkDepsCohs3WithFrames base extra frames))
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkCoh3PaintingSourceFrame (mkDepsCohs3WithFrames base extra frames))
  (c: mkCoh3PaintingSourcePainting (mkDepsCohs3WithFrames base extra frames) paintingExtra d):
  mkCoh3PaintingInstanceType (mkDepsCohs3WithFrames base extra frames)
    paintingExtra q Hq r Hr s Hs 0 leR_O d c.
Proof.
  destruct c as [l c].
  unfold mkCoh3PaintingInstanceType; cbv zeta.
  cbn [mkDepsCohs3WithFrames mkCoh2Paintings].
  lazymatch goal with
  | |- ?prefix ?face1 ?face3 ?face5 ?cap ?face2 ?face4 ?face6 ?Bottom =>
    let cap := eval cbn [mkCoh2Painting mkCoh2PaintingRec nat_rect] in cap in
    let cap := eval cbv beta iota zeta delta [mkCoh2Painting_step] in cap in
    lazymatch cap with
    | context [@eq_existT_curried_hex_dep _ _ _ _ _ ?cap_UExtra _
        _ _ _ _ ?cap_TExtra _ _ ?cap_PaintA _ _ ?cap_PaintB _ _ ?cap_PaintC] =>
      let Higher := constr:(@mkCoh2Painting _ _ _ paintingExtra
        q Hq r Hr s Hs (d; l) c) in
      let FrameEq := constr:(mkCoh2Frames_head (mkDepsCohs2 base)
        (mkExtraCohs2 extra) (mkCoh2Paintings extra) frames
        q Hq r Hr s Hs d l) in
      let HigherCap := constr:(transport_hexagonal_coherence_dep FrameEq Higher) in
      now eapply rew_coh3Painting_restr0 with
        (Hcoh2Painting := Bottom) (UExtra := cap_UExtra) (TExtra := cap_TExtra)
        (PaintA := cap_PaintA) (PaintB := cap_PaintB) (PaintC := cap_PaintC)
        (Higherκ := HigherCap)
    | _ => fail "selected paired cap not exposed"
    end
  end.
Defined.

Local Transparent eq_existT_curried_dep sigT_map_eq rew_coh2Layer_perm4
  permutahedral_coherence_dep hexagonal_coherence_dep eq_existT_curried_hex
  eq_existT_curried_hex_dep rew_coh2Painting_restr0.


Local Lemma mkCoh3Painting_zero `{depsCohs4: DepsCohs4 p k}
  (extraDepsCohs4: DepsCohs4Extension p k depsCohs4)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (d: mkCoh3PaintingSourceFrame (mkDepsCohs3 depsCohs4))
  (c: mkCoh3PaintingSourcePainting (mkDepsCohs3 depsCohs4)
    (mkExtraCohs3 extraDepsCohs4) d):
  mkCoh3PaintingInstanceType (mkDepsCohs3 depsCohs4)
    (mkExtraCohs3 extraDepsCohs4) q Hq r Hr s Hs 0 leR_O d c.
Proof.
  now exact (mkCoh3Painting_restr0
    depsCohs4.(_depsCohs3) depsCohs4.(_extraDepsCohs3)
    (mkCoh3Frames p k depsCohs4.(_depsCohs3) depsCohs4.(_extraDepsCohs3)
      depsCohs4.(_coh3Paintings))
    (mkExtraCohs3 extraDepsCohs4) q Hq r Hr s Hs d c).
Defined.

(** The sigma constructor uses the chosen hexagons over their sigma
    frames. These transparent adapters expose those boundaries. *)
Local Definition mkCoh2Painting_cell {p k}
  {depsCohs2: DepsCohs2 p.+1 k}
  {extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2}
  {q} {Hq: q <= k} {r} {Hr: r <= q} {s} {Hs: s <= r} {d: _} {c: _}
  (h: mkCoh2PaintingInstanceType depsCohs2 extraDepsCohs2
    q Hq r Hr s Hs d c):
  ltac:(let T := constr:(mkCoh2PaintingInstanceType depsCohs2 extraDepsCohs2
    q Hq r Hr s Hs d c) in
    let T := eval cbv beta zeta delta [mkCoh2PaintingInstanceType] in T in exact T) := h.

Local Definition mkCoh2Painting_sigma_source {p k} (deps3: DepsCohs3 p.+1 k): Type :=
  H2Gpd.G2Dom (mkFrame (mkDepsRestr (depsCohs :=
    (mkDepsCohs (mkDepsCohs2 deps3)).(1).(1))).(1)).

(** Keep unfolding policies local to boundary conversion and sigma
    assembly, restoring the default policy before painting recursion. *)
Section Coh2PaintingSigmaFrameCell.
Local Opaque eq_existT_curried_dep eq_existT_curried_hex
  eq_existT_curried_hex_dep mkCohLayer mkCoh2Layer.

Local Definition mkCoh2Painting_sigma_frame_cell {p k}
  (deps3: DepsCohs3 p.+1 k)
  (extra3: DepsCohs3Extension p.+1 k deps3)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (frame: mkCoh2Painting_sigma_source deps3)
  (painting: H2Gpd.G2Dom (mkCoh2PaintingSourcePainting (mkDepsCohs2 deps3)
    (mkExtraCohs2 extra3) frame))
  (h: mkCoh2PaintingInstanceType (mkDepsCohs2 deps3) (mkExtraCohs2 extra3)
    q Hq r Hr s Hs frame painting) :=
  transport_hexagonal_coherence_dep
    (@mkCoh2Frames_head p k deps3.(_depsCohs2)
      deps3.(_extraDepsCohs2) deps3.(_coh2Paintings) deps3.(_coh3Frames)
      q Hq r Hr s Hs frame.1 frame.2) h.
End Coh2PaintingSigmaFrameCell.

Section Coh2PaintingSigmaCell.
Local Opaque eq_existT_curried_dep eq_existT_curried_hex
  eq_existT_curried_hex_dep hexagonal_coherence_dep hexagonal_coherence
  mkCohLayer mkCoh2Layer.

Local Definition mkCoh2Painting_sigma_cell {p k}
  (deps3: DepsCohs3 p.+1 k)
  (extra3: DepsCohs3Extension p.+1 k deps3)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  (frame: mkCoh2Painting_sigma_source deps3)
  (painting: H2Gpd.G2Dom (mkCoh2PaintingSourcePainting (mkDepsCohs2 deps3)
    (mkExtraCohs2 extra3) frame))
  (h: mkCoh2PaintingInstanceType (mkDepsCohs2 deps3) (mkExtraCohs2 extra3)
    q Hq r Hr s Hs frame painting):
  ltac:(let Lower := constr:(@mkCoh2Layer p k deps3.(_depsCohs2)
      deps3.(_extraDepsCohs2)
      (mkCoh2Frames (deps3.(_depsCohs2);deps3.(_extraDepsCohs2))
        deps3.(_coh2Paintings).1 deps3.(_coh3Frames).1)
      deps3.(_coh2Paintings).2 deps3.(_coh3Frames).2
      q Hq r Hr s Hs frame.1 frame.2) in
    let TL := type of Lower in
    let TL := eval cbv beta zeta delta [mkCoh2LayerType] in TL in
    lazymatch TL with
    | @hexagonal_coherence_dep ?A1 ?A2 ?A3 ?B ?P1 ?P2 ?P3 ?Q
      ?f1 ?f2 ?f3 ?F1 ?F2 ?F3 ?x0 ?x1 ?x2 ?x3 ?x4 ?x5
      ?u0 ?u1 ?u2 ?u3 ?u4 ?u5 ?p1 ?p2 ?p3 ?h1 ?h2 ?h3
      ?H ?q1 ?q2 ?q3 ?k1 ?k2 ?k3 =>
      let Upper := constr:(@mkCoh2Painting_sigma_frame_cell p k deps3 extra3 q Hq r Hr s Hs frame painting h) in
      let TU := type of Upper in
      lazymatch TU with
      | @hexagonal_coherence_dep ?nA1 ?nA2 ?nA3 ?nB ?nP1 ?nP2 ?nP3 ?nQ
        ?nf1 ?nf2 ?nf3 ?nF1 ?nF2 ?nF3 ?nx0 ?nx1 ?nx2 ?nx3 ?nx4 ?nx5
        ?nu0 ?nu1 ?nu2 ?nu3 ?nu4 ?nu5 ?np1 ?np2 ?np3 ?nh1 ?nh2 ?nh3
        ?nH ?nq1 ?nq2 ?nq3 ?nk1 ?nk2 ?nk3 =>
        let Partial := constr:(@eq_existT_curried_hex_dep
          A1 A2 A3 B P1 (fun x u => nP1 (x;u))
          P2 (fun x u => nP2 (x;u)) P3 (fun x u => nP3 (x;u))
          Q (fun x u => nQ (x;u))
          f1 F1 (fun x u => nF1 (x;u))
          f2 F2 (fun x u => nF2 (x;u))
          f3 F3 (fun x u => nF3 (x;u))
          x0 x1 x2 x3 x4 x5
          u0 nu0 u1 nu1 u2 nu2 u3 nu3 u4 nu4 u5 nu5
          p1 q1 nq1 h1 k1 nk1 p2 q2 nq2 h2 k2 nk2
          p3 q3 nq3 h3 k3 nk3 H Lower) in
        let TP := type of Partial in
        let TP := eval cbv beta zeta in TP in
        lazymatch TP with forall _ : ?Domain, _ => exact Domain end
      end
    end).
Proof.
  (now exact
    (@mkCoh2Painting_sigma_frame_cell p k deps3 extra3 q Hq r Hr s Hs frame painting h)).
Defined.
End Coh2PaintingSigmaCell.

Section Coh3PaintingSigma.
Local Opaque hexagonal_coherence_dep hexagonal_coherence
  permutahedral_coherence_dep permutahedral_coherence
  eq_existT_curried_dep eq_existT_curried_hex eq_existT_curried_hex_dep
  mkCohLayer mkCoh2Layer.
Local Strategy 10 [mkCohPainting mkCoh2Painting mkCohFrames mkCoh2Frames
  mkCoh3Frames mkCohLayer mkCoh2Layer mkCoh3Layer].
Local Strategy 20 [eq_existT_curried_dep eq_existT_curried_hex
  eq_existT_curried_hex_dep eq_existT_curried_perm4 eq_existT_curried_perm4_dep].

(** Combine the layer cell with the recursive painting, presenting its
    four restricted faces over their sigma frames. *)
Local Definition mkCoh3Painting_step {p k}
  (depsCohs4: DepsCohs4 p.+1 k)
  (extraDepsCohs4: DepsCohs4Extension p.+1 k depsCohs4)
  q (Hq: q.+1 <= k.+1) r (Hr: r.+1 <= q.+1)
  s (Hs: s.+1 <= r.+1) t (Ht: t.+1 <= s.+1)
  (d: mkCoh3PaintingSourceFrame (mkDepsCohs3 depsCohs4.(1)%depscohs4))
  (full: mkCoh3PaintingSourcePainting (mkDepsCohs3 depsCohs4.(1)%depscohs4)
    (mkExtraCohs3 (depsCohs4; extraDepsCohs4)%extradepscohs4) d)
  (Rec: mkCoh3PaintingInstanceType (mkDepsCohs3 depsCohs4)
    (mkExtraCohs3 extraDepsCohs4) q (⇓ Hq) r (⇓ Hr) s (⇓ Hs) t (⇓ Ht)
    (d; full.1) full.2):
  mkCoh3PaintingInstanceType (mkDepsCohs3 depsCohs4.(1)%depscohs4)
    (mkExtraCohs3 (depsCohs4; extraDepsCohs4)%extradepscohs4)
    q.+1 Hq r.+1 Hr s.+1 Hs t.+1 Ht d full.
Proof.
  destruct full as [l c].
  unfold mkCoh3PaintingInstanceType; cbv beta zeta.
  pose (DP4 := mkCoh3Layer depsCohs4.(_depsCohs3) depsCohs4.(_extraDepsCohs3)
    (mkCoh3Frames _ _ depsCohs4.(_depsCohs3).(1)%depscohs3
      (depsCohs4.(_depsCohs3); depsCohs4.(_extraDepsCohs3))%extradepscohs3
      depsCohs4.(_coh3Paintings).1)
    depsCohs4.(_coh3Paintings).2 q (⇓ Hq) r (⇓ Hr) s (⇓ Hs) t (⇓ Ht) d l).
  let TD := type of Rec in
  let TD := eval cbv beta zeta delta [mkCoh3PaintingInstanceType] in TD in
  lazymatch TD with
  | @permutahedral_coherence_dep ?nX2 ?nX1 ?nX0 ?nTU ?nT ?nS2 ?nS1 ?nS0 ?nPU ?nPT ?nuf0 ?nrf0
    ?nfA ?nfB ?nfC ?nrfq ?nrfs ?nrfr ?ngq ?ngs ?ngr ?nrur ?nrus ?nruq1 ?nrur1 ?nKA2 ?nKA4 ?nKA6
    ?nu0 ?nu1 ?nu2 ?nu3 ?nu4 ?nu5 ?neU1 ?neU2 ?neU3 ?ne2 ?ne4 ?ne6 ?nzs1 ?nzs2 ?nzr1 ?nzr2 ?nzq1
    ?nzq2 ?npIs ?npIr ?npIq ?npV0 ?npV1 ?npV2 ?npV3 ?npV4 ?npV5 ?nK1 ?nK3 ?nK5 ?nHH1 ?nHH3 ?nHH5
    ?nκ ?nHH2 ?nHH4 ?nHH6 ?nHHA ?nP ?nU ?nF0 ?nFA ?nFB ?nFC ?nFq ?nFs ?nFr ?nRr ?nRs ?nRq1 ?nRr1
    ?nHgq ?nHgs ?nHgr ?nHKA2 ?nHKA4 ?nHKA6 ?na0 ?na1 ?na2 ?na3 ?na4 ?na5 ?naS1 ?naS2 ?naR1 ?naR2
    ?naQ1 ?naQ2 ?nheU1 ?nheU2 ?nheU3 ?nhe2 ?nhe4 ?nhe6 ?nhpIs ?nhpIr ?nhpIq ?nhpV0 ?nhpV1 ?nhpV2
    ?nhpV3 ?nhpV4 ?nhpV5 ?nHK1 ?nHK3 ?nHK5 ?nDHH1 ?nDHH3 ?nDHH5 ?nDκ ?nDHH2 ?nDHH4 ?nDHH6 ?nDHHA
    =>
    let CDHH1 := constr:(mkCoh2Painting_cell nDHH1) in
    let CDHH3 := constr:(mkCoh2Painting_cell nDHH3) in
    let CDHH5 := constr:(mkCoh2Painting_cell nDHH5) in
    let CDκ := constr:(mkCoh2Painting_cell nDκ) in
    let SigmaFace4 := constr:(eq_existT_curried_perm4_dep
      (RS2 := nS2) (RS1 := nS1) (RS0 := nS0) (RPU := nPU) (RPT := nPT)
      (da0 := na0) (da1 := na1) (da2 := na2) (da3 := na3)
      (da4 := na4) (da5 := na5) (daS1 := naS1) (daS2 := naS2)
      (daR1 := naR1) (daR2 := naR2) (daQ1 := naQ1) (daQ2 := naQ2)
      DP4 nU nF0 nFA nFB nFC nFq nFs nFr nRr nRs nRq1 nRr1
      nHgq nHgs nHgr nHKA2 nHKA4 nHKA6
      nheU1 nheU2 nheU3 nhe2 nhe4 nhe6 nhpIs nhpIr nhpIq
      nhpV0 nhpV1 nhpV2 nhpV3 nhpV4 nhpV5 nHK1 nHK3 nHK5
      CDHH1 CDHH3 CDHH5 CDκ) in
    let canonical := ltac:(fun face =>
      lazymatch face with
      | ?cell ?qc ?hqc ?rc ?hrc ?sc ?hsc ?xc ?ac =>
        constr:(@mkCoh2Painting_sigma_cell p k
          depsCohs4.(_depsCohs3) depsCohs4.(_extraDepsCohs3)
          qc hqc rc hrc sc hsc xc ac face)
      end) in
    let Qst := canonical nDHH2 in
    let Qrt := canonical nDHH4 in
    let Rst := canonical nDHH6 in
    let Qrs := canonical nDHHA in
    now exact_no_check (SigmaFace4 Qst Qrt Rst Qrs Rec)
  end.
Defined.
End Coh3PaintingSigma.


Local Fixpoint mkCoh3PaintingRec (t: nat) {struct t}:
  forall p k (depsCohs4: DepsCohs4 p k)
    (extraDepsCohs4: DepsCohs4Extension p k depsCohs4)
    q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (Ht: t <= s)
    (d: _) (c: _),
  mkCoh3PaintingInstanceType (mkDepsCohs3 depsCohs4)
    (mkExtraCohs3 extraDepsCohs4) q Hq r Hr s Hs t Ht d c.
Proof.
  destruct t as [|t].
  - intros p k depsCohs4 extraDepsCohs4 q Hq r Hr s Hs Ht d c.
    now exact (mkCoh3Painting_zero extraDepsCohs4 q Hq r Hr s Hs d c).
  - intros p k depsCohs4 extraDepsCohs4 q Hq r Hr s Hs Ht d c.
    destruct s; [now contradiction |].
    destruct r; [now contradiction |].
    destruct q; [now contradiction |].
    destruct extraDepsCohs4; [now contradiction |].
    destruct c as [l c].
    now exact (mkCoh3Painting_step depsCohs4 extraDepsCohs4
      q Hq r Hr s Hs t Ht d (l; c)
      (mkCoh3PaintingRec t p.+1 k depsCohs4 extraDepsCohs4
        q (⇓ Hq) r (⇓ Hr) s (⇓ Hs) (⇓ Ht) (d; l) c)).
Defined.

Definition mkCoh3Painting `{depsCohs4: DepsCohs4 p k}
  (extraDepsCohs4: DepsCohs4Extension p k depsCohs4):
  mkCoh3PaintingType (mkDepsCohs3 depsCohs4) (mkExtraCohs3 extraDepsCohs4) :=
  fun q Hq r Hr s Hs t Ht d c =>
    mkCoh3PaintingRec t p k depsCohs4 extraDepsCohs4 q Hq r Hr s Hs Ht d c.

Fixpoint mkCoh3PaintingsPrefix `{depsCohs4: DepsCohs4 p k}
  (extraDepsCohs4: DepsCohs4Extension p k depsCohs4) {struct p}:
  @mkCoh3PaintingTypes p k.+1 (mkDepsCohs3 depsCohs4).(1)%depscohs3
    (mkDepsCohs3 depsCohs4; mkExtraCohs3 extraDepsCohs4)%extradepscohs3.
Proof.
  destruct p.
  - now exact tt.
  - unshelve esplit.
    + now exact (mkCoh3PaintingsPrefix p k.+1 depsCohs4.(1)%depscohs4
        (depsCohs4; extraDepsCohs4)%extradepscohs4).
    + now exact (mkCoh3Painting (depsCohs4; extraDepsCohs4)%extradepscohs4).
Defined.

Definition mkCoh3Paintings `{depsCohs4: DepsCohs4 p k}
  (extraDepsCohs4: DepsCohs4Extension p k depsCohs4):
  mkCoh3PaintingTypes (mkExtraCohs3 extraDepsCohs4) :=
  (mkCoh3PaintingsPrefix extraDepsCohs4; mkCoh3Painting extraDepsCohs4).

Class SS2GpdData p := {
  frames: mkFrameTypes p 0;
  paintings: mkPaintingTypes p 0 frames;
  restrFrames: mkRestrFrameTypes paintings;
  restrPaintings E: mkRestrPaintingTypes (TopRestrDep E);
  cohFrames E: mkCohFrameTypes (restrPaintings E);
  cohPaintings E E': mkCohPaintingTypes
    (depsCohs := toDepsCohs (deps := toDepsRestr restrFrames) (cohFrames E))
    (TopCohDep E');
  coh2Frames E E': mkCoh2FrameTypes (cohPaintings E E');
  coh2Paintings E E' E'': mkCoh2PaintingTypes
    (depsCohs2 := toDepsCohs2 (coh2Frames E E'))
    (TopCoh2Dep E'');
  coh3Frames E E' E'': mkCoh3FrameTypes (coh2Paintings E E' E'');
  coh3Paintings E E' E'' E''': mkCoh3PaintingTypes
    (depsCohs3 := toDepsCohs3 (coh3Frames E E' E''))
    (TopCoh3Dep E''');
}.

Section SS2GpdData.
Variable p: nat.
Variable C: SS2GpdData p.
Variable E: mkFrame (toDepsRestr C.(restrFrames)) -> H2Gpd.

#[local]
Instance mkSS2GpdData: SS2GpdData p.+1 :=
{|
  frames := mkFrames _;
  paintings := mkPaintings _;
  restrFrames := mkRestrFrames;
  restrPaintings E' := mkRestrPaintings (TopCohDep E');
  cohFrames E' := mkCohFrames (C.(cohPaintings) E E') (C.(coh2Frames) E E');
  cohPaintings E' E'' := mkCohPaintings
    (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(coh2Frames) E E')) E'');
  coh2Frames E' E'' := mkCoh2Frames
    (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(coh2Frames) E E')) E'')
    (C.(coh2Paintings) E E' E'') (C.(coh3Frames) E E' E'');
  coh2Paintings E' E'' E''' := mkCoh2Paintings
    (TopCoh3Dep (depsCohs3 := toDepsCohs3 (C.(coh3Frames) E E' E'')) E''');
  coh3Frames E' E'' E''' := mkCoh3Frames _ _ _
    (TopCoh3Dep (depsCohs3 := toDepsCohs3 (C.(coh3Frames) E E' E'')) E''')
    (C.(coh3Paintings) E E' E'' E''');
  coh3Paintings E' E'' E''' E'''' := mkCoh3Paintings
    (TopCoh4Dep (depsCohs4 := toDepsCohs4 (C.(coh3Paintings) E E' E'' E''')) E'''');
|}.
End SS2GpdData.

Class SS2Gpd p := {
  prefix: Type;
  data: prefix -> SS2GpdData p;
}.

Definition mkPrefix p {C: SS2Gpd p}: Type :=
  { D: C.(prefix) &T mkFrame (toDepsRestr (C.(data) D).(restrFrames)) -> H2Gpd }.

#[local]
Instance mkSS2Gpd0: SS2Gpd 0.
Proof.
  unshelve esplit.
  - now exact g2unit.
  - unshelve esplit; now trivial.
Defined.

#[local]
Instance mkSS2Gpd {p} (C: SS2Gpd p): SS2Gpd p.+1 :=
{|
  prefix := mkPrefix p;
  data := fun D: mkPrefix p => mkSS2GpdData p (C.(data) D.1) D.2;
|}.

(** The construction stage with a prefix of [n] filler families. *)
Fixpoint SS2GpdAt n: SS2Gpd n :=
  match n with
  | O => mkSS2Gpd0
  | n.+1 => mkSS2Gpd (SS2GpdAt n)
  end.

(** The ω-limit tower

    Prefixes form a telescope: a prefix one level up is definitionally a
    Σ-type over the one below, so extending is pairing and the bonding map
    and the head are its two projections. Its limits are augmented
    semi-simplicial objects. *)

Definition mkExtensionType {p} {C: SS2Gpd p} (D: C.(prefix)): Type :=
  mkFrame (toDepsRestr (C.(data) D).(restrFrames)) -> H2Gpd.

Definition SS2GpdTel: Telescope := {|
  stage l := (SS2GpdAt l).(prefix);
  datum l X := mkExtensionType X;
  extend l X E := ((X; E): (SS2GpdAt l.+1).(prefix));
  bond l Y := Y.1;
  head l Y := Y.2;
  bondExtend l X E := eq_refl;
  extendHead l Y := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

Definition SS2GpdFrom n (X: (SS2GpdAt n).(prefix)): Type := Limit SS2GpdTel n X.

(** The limit over the empty prefix. *)
Definition SS2Gpds := SS2GpdFrom 0 tt.


End SS2Gpd.
