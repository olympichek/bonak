Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet Notation LeSProp
  Limit.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module SSSet.

(** A telescope of [p] frame types at fixed total index [p + k].
    The offset [k] increases when a frame type is projected away. *)

Fixpoint mkFrameTypes p k: Type :=
  match p with
  | 0 => unit
  | S p => { frames: mkFrameTypes p k.+1 &T HSet }
  end.

(** A telescope of painting families over the corresponding frame types. *)

Fixpoint mkPaintingTypes p k: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
    { paintings: mkPaintingTypes p k.+1 frames.1 &T frames.2 -> HSet }
  end.

(** Restriction types and the frame telescope they determine are built
    together: extending a frame requires a restriction to its new layer. *)

Class RestrFrameTypeBlock p k := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> mkFrameTypes p.+1 k;
}.

(** At each stage, [mkRestrFrameTypesStep] adds a restriction map for
    every face index [q <= k]. The zero-face restriction determines
    [mkLayer], and pairing a frame with that layer extends the frame
    telescope. [mkRestrFrameTypesAndFrames] builds the restriction types
    and this dependent frame construction by recursion on [p]. *)

Generalizable Variables p k frames.

Definition mkRestrFrameTypesStep `(frames: mkFrameTypes p.+1 k)
  (prev: RestrFrameTypeBlock p k.+1) :=
  { R: prev.(RestrFrameTypesDef) &T
    forall q (Hq: q <= k), (prev.(FrameDef) R).2 -> frames.2 }.

Definition mkLayer `{paintings: mkPaintingTypes p.+1 k frames}
  {prev: RestrFrameTypeBlock p k.+1}
  (restrFrames: mkRestrFrameTypesStep frames prev)
  (d: (prev.(FrameDef) restrFrames.1).2) :=
  paintings.2 (restrFrames.2 0 leR_O d).

Fixpoint mkRestrFrameTypesAndFrames {p k}:
  forall `(paintings: mkPaintingTypes p k frames), RestrFrameTypeBlock p k :=
  match p with
  | 0 => fun frames paintings =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; hunit): mkFrameTypes 1 k
    |}
  | p.+1 => fun frames paintings =>
    let prev :=
      mkRestrFrameTypesAndFrames paintings.1 in
    let frames' := prev.(FrameDef) in
    {|
      RestrFrameTypesDef := mkRestrFrameTypesStep frames prev;
      FrameDef R :=
        (frames' R.1; { d: (frames' R.1).2 &
          mkLayer (paintings := paintings) R d }): mkFrameTypes p.+2 k
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
  (restrFrames: mkRestrFrameTypes paintings): DepsRestr p k :=
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

Definition mkFrame `(deps: DepsRestr p k): HSet := (mkFrames deps).2.

Inductive DepsRestrExtension p: forall k, DepsRestr p k -> Type :=
| TopRestrDep {deps} (E: mkFrame deps -> HSet): DepsRestrExtension p 0 deps
| AddRestrDep {k} deps:
  DepsRestrExtension p.+1 k deps -> DepsRestrExtension p k.+1 deps.(1).

Arguments TopRestrDep {p deps}.
Arguments AddRestrDep {p k} deps.

Declare Scope extra_depsrestr_scope.
Delimit Scope extra_depsrestr_scope with extradepsrestr.
Bind Scope extra_depsrestr_scope with DepsRestrExtension.
Notation "( x ; y )" := (AddRestrDep x y)
  (at level 0, format "( x ; y )"): extra_depsrestr_scope.

(** At a [TopRestrDep E], the painting family is [E]. Each [AddRestrDep]
    adds one layer to the painting and moves the frame up one stage. *)

Generalizable Variables deps.

Fixpoint mkPainting `(extraDeps: DepsRestrExtension p k deps):
  mkFrame deps -> HSet :=
  match extraDeps with
  | TopRestrDep E => fun d => E d
  | AddRestrDep deps extraDeps => fun (d: mkFrame deps.(1)) =>
      {l: mkLayer deps.(_restrFrames) d & mkPainting extraDeps (d; l)}
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

(** Frame-coherence types and the restriction maps they determine are
    built together, using the supplied painting restrictions. *)

Class CohFrameTypeBlock `{extraDeps: DepsRestrExtension p k deps} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef -> mkRestrFrameTypes (mkPaintings extraDeps)
}.

(** The coherence step adds the face-exchange equation. Its instance
    with lower face zero supplies the transport in [mkRestrLayer]. *)

Definition mkCohFrameTypesStep `{extraDeps: DepsRestrExtension p.+1 k deps}
  (prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))): Type :=
  { Q: prev.(CohFrameTypesDef) &T
    forall q (Hq: q <= k) r (Hr: r <= q) d,
    deps.(_restrFrames).2 q Hq ((prev.(RestrFramesDef) Q).2 r (Hr ↕ (↑ Hq)) d) =
    deps.(_restrFrames).2 r (Hr ↕ Hq) ((prev.(RestrFramesDef) Q).2 q.+1 (⇑ Hq) d) }.

Definition mkRestrLayer `{extraDeps: DepsRestrExtension p.+1 k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps)
  {prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))}
  (cohFrames: mkCohFrameTypesStep prev)
  q (Hq: q <= k)
  (d: mkFrame (toDepsRestr (prev.(RestrFramesDef) cohFrames.1)).(1)):
  mkLayer (paintings := mkPaintings (deps; extraDeps))
    (prev.(RestrFramesDef) cohFrames.1) d ->
  mkLayer (paintings := deps.(_paintings)) deps.(_restrFrames)
    ((prev.(RestrFramesDef) cohFrames.1).2 q.+1 (⇑ Hq) d) :=
  fun c =>
    rew [deps.(_paintings).2] cohFrames.2 q Hq 0 leR_O d in
    restrPaintings.2 q Hq
      ((prev.(RestrFramesDef) cohFrames.1).2 0 leR_O d) c.

(** Recursion on [p] builds the frame-coherence telescope and the
    next-level frame restrictions. Each restriction pairs the recursive
    frame restriction at [q.+1] with the layer restriction at [q]. *)

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
      let restrFrame q (Hq: q <= k) (d: mkFrame (toDepsRestr (restrFrames Q.1))) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) d.1;
           mkRestrLayer restrPaintings Q q _ d.1 d.2)
      in (restrFrames Q.1; restrFrame)
    |}
  end.

(** At [p = 0], the frame-coherence telescope is [unit]. *)

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

(** Assemble the next-level frames, paintings, and frame restrictions
    into [DepsRestr p.+1 k]. The frames and paintings are computed from
    the stored dependencies and extension; the restrictions use the
    frame coherences. *)

Definition mkDepsRestr `{depsCohs: DepsCohs p k} :=
  toDepsRestr mkRestrFrames.

(** The last frame restriction in the constructed telescope.
    Both its source frame and its restriction maps come from the same
    instantiated block, so the source has the layer structure needed by
    the constructed restriction. *)

Definition mkRestrFrame `{depsCohs: DepsCohs p k}:
  forall q (Hq: q <= k),
  mkFrame mkDepsRestr.(1) -> mkFrame depsCohs.(_deps) :=
  mkRestrFrames.2.

Inductive DepsCohsExtension p: forall k (depsCohs: DepsCohs p k), Type :=
| TopCohDep `{depsCohs: DepsCohs p 0}
  (E: mkFrame mkDepsRestr -> HSet):
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
    mkDepsRestr.(_paintings).2 (mkDepsRestr.(_restrFrames).2 q Hq d) :=
  match q with
  | 0 => fun _ _ '(l; _) => l
  | q.+1 =>
    match extraDepsCohs with
    | TopCohDep E => fun Hq _ _ => match leR_O_contra Hq with end
    | AddCohDep depsCohs extraDepsCohs => fun Hq d '(l; c) =>
      (mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) q (⇓ Hq) d l;
       mkRestrPainting extraDepsCohs q (⇓ Hq) (d; l) c)
    end
  end.

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

Definition mkCohPaintingType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs) :=
  forall q (Hq: q <= k) r (Hr: r <= q)
    (d: mkFrame mkDepsRestr.(1))
    (c: (mkPaintings (mkDepsRestr;
      mkExtraDeps (depsCohs; extraDepsCohs))).2 d),
  rew [depsCohs.(_deps).(_paintings).2] depsCohs.(_cohs).2 q Hq r Hr d in
  depsCohs.(_restrPaintings).2 q Hq _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 r _ d c) =
  depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 q.+1 _ d c).

Fixpoint mkCohPaintingTypes {p}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k depsCohs extraDepsCohs =>
    { R: mkCohPaintingTypes (depsCohs; extraDepsCohs) &T
         mkCohPaintingType extraDepsCohs }
  end.

Lemma mkCoh2Frame `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs)
  (prevCohFrames: mkCohFrameTypes
     (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
     (mkRestrPaintings extraDepsCohs).1):
  forall q (Hq: q <= k) r (Hr: r <= q)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1)),
  (f_equal
    (fun x => depsCohs.(_deps).(_restrFrames).2 q _ x)
    (prevCohFrames.2 r (Hr ↕ ↑ Hq) 0 leR_O d)
  • depsCohs.(_cohs).2 q Hq 0 leR_O (mkRestrFrame r.+1 (⇑ (Hr ↕ ↑ Hq)) d))
  • f_equal
      (fun x => depsCohs.(_deps).(_restrFrames).2 0 leR_O x)
      (prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) d) =
  depsCohs.(_cohs).2 q Hq r Hr (mkRestrFrame 0 leR_O d)
  • (f_equal
      (fun x => depsCohs.(_deps).(_restrFrames).2 r _ x)
      (prevCohFrames.2 q.+1 (⇑ Hq) 0 leR_O d)
  • depsCohs.(_cohs).2 r (Hr ↕ Hq) 0 leR_O (mkRestrFrame q.+2 (⇑ (⇑ Hq)) d)).
Proof.
  now intros; apply depsCohs.(_deps).(_frames).2.(UIP).
Defined.

Definition mkCohLayer `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  q {Hq: q <= k} r {Hr: r <= q}
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
  (l: mkLayer mkRestrFrames d):
  rew [mkLayer _] prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) d in
    mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) q Hq _
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1 _ r (Hr ↕ ↑ Hq) d l) =
    mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) r (Hr ↕ Hq) _
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1 _ q.+1 (⇑ Hq) d l).
Proof.
  unfold mkRestrLayer.
  eapply (rew_cohLayer_hex
    (P := fun x => depsCohs.(_deps).(_paintings).2 x)
    (rf0 := fun x => depsCohs.(_deps).(_restrFrames).2 0 leR_O x)
    (F := fun m c => depsCohs.(_restrPaintings).2 q Hq m c)
    (G := fun m c => depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) m c)).
  now exact (cohPaintings.2 q Hq r Hr _ l).
  now exact (mkCoh2Frame extraDepsCohs prevCohFrames q Hq r Hr d).
Defined.

Fixpoint mkCohFrames `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs) {struct p}:
  mkCohFrameTypes (mkRestrPaintings extraDepsCohs).
Proof.
  destruct p.
  - unshelve esplit. now exact tt. now intros.
  - unshelve esplit.
    + now exact (mkCohFrames p k.+1 depsCohs.(1)%depscohs
      (depsCohs; extraDepsCohs)%extradepscohs cohPaintings.1).
    + intros q Hq r Hr d. unshelve eapply eq_existT_curried.
      now exact ((mkCohFrames p k.+1 depsCohs.(1)%depscohs
        (depsCohs; extraDepsCohs)%extradepscohs
        cohPaintings.1).2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) d.1).
      now exact (mkCohLayer cohPaintings q r d.1 d.2).
Defined.

Class DepsCohs2 p k := {
  _depsCohs: DepsCohs p k;
  _extraDepsCohs: DepsCohsExtension p k _depsCohs;
  _cohPaintings: mkCohPaintingTypes _extraDepsCohs;
}.

#[local]
Instance toDepsCohs2 `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs): DepsCohs2 p k :=
  {| _cohPaintings := cohPaintings |}.

#[local]
Instance proj1DepsCohs2 `(depsCohs2: DepsCohs2 p.+1 k): DepsCohs2 p k.+1 :=
{|
  _depsCohs := depsCohs2.(_depsCohs).(1);
  _extraDepsCohs := (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs));
  _cohPaintings := depsCohs2.(_cohPaintings).1;
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
  _cohs := mkCohFrames depsCohs2.(_cohPaintings);
|}.

Inductive DepsCohs2Extension p: forall k (depsCohs2: DepsCohs2 p k), Type :=
| TopCoh2Dep `{depsCohs2: DepsCohs2 p 0}
  (E: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs depsCohs2)) -> HSet)
: DepsCohs2Extension p 0 depsCohs2
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

Fixpoint mkCohPainting `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingType (mkExtraCohs extraDepsCohs2).
Proof.
  red; intros *. destruct c as (l, c), r.
  - (* r = 0 *)
    now reflexivity.
  - (* For positive [r], the bounds force positive [q] and an
       [AddCoh2Dep] extension. *)
    destruct q.
    { exfalso; now apply leR_O_contra in Hr. }
    destruct extraDepsCohs2.
    { exfalso; now apply leR_O_contra in Hq. }
    simpl.
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting depsCohs2.(_depsCohs).(_extraDeps))).
    + now exact
      (mkCohLayer depsCohs2.(_cohPaintings) q r (Hr := ⇓ Hr) d l).
    + now exact (mkCohPainting p.+1 k depsCohs2 extraDepsCohs2
      q (⇓ Hq) r (⇓ Hr) (d; l) c).
Defined.

Fixpoint mkCohPaintings `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2) {struct p}:
  mkCohPaintingTypes (mkExtraCohs extraDepsCohs2).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkCohPainting extraDepsCohs2).
  - unshelve esplit. now exact (mkCohPaintings p k.+1
      depsCohs2.(1)%depscohs2 (depsCohs2; extraDepsCohs2)%extradepscohs2).
    now exact (mkCohPainting extraDepsCohs2).
Defined.

Class SSSetData p := {
  frames: mkFrameTypes p 0;
  paintings: mkPaintingTypes p 0 frames;
  restrFrames: mkRestrFrameTypes paintings;
  restrPaintings E: mkRestrPaintingTypes (TopRestrDep E);
  cohFrames E: mkCohFrameTypes (restrPaintings E);
  cohPaintings E E': mkCohPaintingTypes
    (depsCohs := toDepsCohs (deps := toDepsRestr restrFrames) (cohFrames E))
    (TopCohDep E');
}.

Section SSSetData.
Variable p: nat.
Variable C: SSSetData p.
Variable E: mkFrame (toDepsRestr C.(restrFrames)) -> HSet.

#[local]
Instance mkSSSetData: SSSetData p.+1 :=
{|
  frames := mkFrames _;
  paintings := mkPaintings _;
  restrFrames := mkRestrFrames;
  restrPaintings E' := mkRestrPaintings (TopCohDep E');
  cohFrames E' := mkCohFrames (C.(cohPaintings) E E');
  cohPaintings E' E'' :=
    mkCohPaintings (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(cohPaintings) E E')) E'');
|}.
End SSSetData.

Class SSSet p := {
  prefix: Type;
  data: prefix -> SSSetData p;
}.

(** Extend a prefix by its next family of fillers. *)
Definition mkPrefix p {C: SSSet p}: Type :=
  { D: C.(prefix) &T mkFrame (toDepsRestr (C.(data) D).(restrFrames)) -> HSet }.

(** The initial prefix has no filler families. *)
#[local]
Instance mkSSSet0: SSSet 0.
Proof.
  unshelve esplit.
  - now exact hunit.
  - unshelve esplit; try now trivial.
Defined.

#[local]
Instance mkSSSet {p} (C: SSSet p): SSSet p.+1 :=
{|
  prefix := mkPrefix p;
  data := fun D: mkPrefix p => mkSSSetData p (C.(data) D.1) D.2;
|}.

(** The construction stage with a prefix of [n] filler families. *)
Fixpoint SSSetAt n: SSSet n :=
  match n with
  | O => mkSSSet0
  | n.+1 => mkSSSet (SSSetAt n)
  end.

(** The ω-limit tower

    Prefixes form a telescope: a prefix one level up is definitionally a
    Σ-type over the one below, so extending is pairing and the bonding map
    and the head are its two projections. Its limits are augmented
    semi-simplicial sets. *)

Definition mkExtensionType {p} {C: SSSet p} (D: C.(prefix)): Type :=
  mkFrame (toDepsRestr (C.(data) D).(restrFrames)) -> HSet.

Definition SSSetTel: Telescope := {|
  stage l := (SSSetAt l).(prefix);
  datum l X := mkExtensionType X;
  extend l X E := ((X; E): (SSSetAt l.+1).(prefix));
  bond l Y := Y.1;
  head l Y := Y.2;
  bondExtend l X E := eq_refl;
  extendHead l Y := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

Definition SSSetFrom n (X: (SSSetAt n).(prefix)): Type := Limit SSSetTel n X.

(** The limit over the empty prefix. *)
Definition SSSets := SSSetFrom 0 tt.

End SSSet.

(** The first filler family is the augmentation, in geometric dimension
    [-1]. Fixing it to the unit set gives ordinary semi-simplicial sets. *)

Definition AugmentedSemiSimplicial := SSSet.SSSets.
Definition SemiSimplicial := SSSet.SSSetFrom 1 (tt; fun _ => hunit).

Example SemiSimplicial4 := Eval compute in
  (SSSet.SSSetAt 4).(SSSet.prefix _).

Example TrivialAugmentedSemiSimplicial: AugmentedSemiSimplicial :=
  ana (T := SSSet.SSSetTel) tt (fun n X _ => hunit).

Example TrivialSemiSimplicial: SemiSimplicial :=
  next TrivialAugmentedSemiSimplicial.

Example TrivialSemiSimplicial2 := Eval compute in
  (approx TrivialAugmentedSemiSimplicial 2 leR_O).
