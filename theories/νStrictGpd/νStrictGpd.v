(** Indexed strict groupoids over an abstract layer signature.
    A frame is the total groupoid of its next layer. A layer combines the
    pulled-back painting families, and a painting extends it by a dependent
    sum. Restrictions and their pointwise strict equalities are constructed
    recursively at every finite prefix; the generic telescope limit closes the infinite tower.
    Object fibers and arrows are h-sets, and families require no chosen lifts. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT RewLemmas HSet Notation LeSProp Limit.
From Bonak.νStrictGpd Require Import Layer.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νStrictGpd (A: LayerSig).
Import A.
Module Export LT := LayerTheory A.

Fixpoint mkFrameTypes p k: Type :=
  match p with
  | 0 => unit
  | S p => { frames: mkFrameTypes p k.+1 &T HSetGroupoid }
  end.

Fixpoint mkPaintingTypes p k: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
    { paintings: mkPaintingTypes p k.+1 frames.1 &T Family frames.2 }
  end.

Class RestrFrameTypeBlock p k := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> mkFrameTypes p.+1 k;
}.

Generalizable Variables p k frames.

Definition mkRestrFrameTypesStep `(frames: mkFrameTypes p.+1 k)
  (prev: RestrFrameTypeBlock p k.+1) :=
  {R: prev.(RestrFrameTypesDef) &T
    forall q (Hq: q <= k) (ε: arity), Functor (prev.(FrameDef) R).2 frames.2}.

Definition mkLayer `{paintings: mkPaintingTypes p.+1 k frames}
  {prev: RestrFrameTypeBlock p k.+1}
  (restrFrames: mkRestrFrameTypesStep frames prev): Family (prev.(FrameDef) restrFrames.1).2 :=
  layer paintings.2 (fun ε => restrFrames.2 0 leR_O ε).

Fixpoint mkRestrFrameTypesAndFrames {p k}:
  forall `(paintings: mkPaintingTypes p k frames), RestrFrameTypeBlock p k :=
  match p with
  | 0 => fun frames paintings =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; unitGroupoid): mkFrameTypes 1 k
    |}
  | p.+1 => fun frames paintings =>
    let prev :=
      mkRestrFrameTypesAndFrames paintings.1 in
    let frames' := prev.(FrameDef) in
    {|
      RestrFrameTypesDef := mkRestrFrameTypesStep frames prev;
      FrameDef R :=
        (frames' R.1; total (mkLayer (paintings := paintings) R)): mkFrameTypes p.+2 k
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

Definition mkFrame `(deps: DepsRestr p k): HSetGroupoid := (mkFrames deps).2.

Inductive DepsRestrExtension p: forall k, DepsRestr p k -> Type :=
| TopRestrDep {deps} (E: Family (mkFrame deps)): DepsRestrExtension p 0 deps
| AddRestrDep {k} deps:
  DepsRestrExtension p.+1 k deps -> DepsRestrExtension p k.+1 deps.(1).

Arguments TopRestrDep {p deps}.
Arguments AddRestrDep {p k} deps.

Declare Scope extra_depsrestr_scope.
Delimit Scope extra_depsrestr_scope with extradepsrestr.
Bind Scope extra_depsrestr_scope with DepsRestrExtension.
Notation "( x ; y )" := (AddRestrDep x y)
  (at level 0, format "( x ; y )"): extra_depsrestr_scope.

Generalizable Variables deps.

Fixpoint mkPainting `(extraDeps: DepsRestrExtension p k deps): Family (mkFrame deps) :=
  match extraDeps with
  | TopRestrDep E => E
  | AddRestrDep deps extraDeps => sigma (mkLayer deps.(_restrFrames)) (mkPainting extraDeps)
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

Definition mkRestrPaintingType `(extraDeps: DepsRestrExtension p.+1 k deps) :=
  forall q (Hq: q <= k) (ε: arity),
    Map (mkPainting (deps; extraDeps)) deps.(_paintings).2 (deps.(_restrFrames).2 q Hq ε).

Fixpoint mkRestrPaintingTypes {p}:
  forall `(extraDeps: DepsRestrExtension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkRestrPaintingTypes (deps; extraDeps) &T
      mkRestrPaintingType extraDeps }
  end.

Class CohFrameTypeBlock `{extraDeps: DepsRestrExtension p k deps} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef -> mkRestrFrameTypes (mkPaintings extraDeps)
}.

Definition mkCohFrameTypesStep `{extraDeps: DepsRestrExtension p.+1 k deps}
  (prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))): Type :=
  {Q: prev.(CohFrameTypesDef) &T
    forall q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity),
      (prev.(RestrFramesDef) Q).2 r (Hr ↕ (↑ Hq)) ω ⨟ᶠ deps.(_restrFrames).2 q Hq ε ≐
      (prev.(RestrFramesDef) Q).2 q.+1 (⇑ Hq) ε ⨟ᶠ deps.(_restrFrames).2 r (Hr ↕ Hq) ω}.

Definition mkRestrLayer `{extraDeps: DepsRestrExtension p.+1 k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps)
  {prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))}
  (cohFrames: mkCohFrameTypesStep prev) q (Hq: q <= k) (ε: arity):
  Map (mkLayer (paintings := mkPaintings (deps; extraDeps)) (prev.(RestrFramesDef) cohFrames.1))
    (mkLayer (paintings := deps.(_paintings)) deps.(_restrFrames))
    ((prev.(RestrFramesDef) cohFrames.1).2 q.+1 (⇑ Hq) ε) :=
  layerMap (restrPaintings.2 q Hq ε)
    (fun ω => (prev.(RestrFramesDef) cohFrames.1).2 0 leR_O ω)
    (fun ω => deps.(_restrFrames).2 0 leR_O ω)
    ((prev.(RestrFramesDef) cohFrames.1).2 q.+1 (⇑ Hq) ε)
    (fun ω => cohFrames.2 q Hq 0 leR_O ε ω).

Fixpoint mkCohFrameTypesAndRestrFrames {p k}:
  forall `{extraDeps: DepsRestrExtension p k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps), CohFrameTypeBlock :=
  match p with
  | 0 =>
    fun deps extraDeps restrPaintings =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ :=
        (tt; fun _ _ _ => terminalFunctor _): mkRestrFrameTypes (mkPaintings extraDeps)
    |}
  | S p =>
    fun deps extraDeps restrPaintings =>
    let prev := mkCohFrameTypesAndRestrFrames restrPaintings.1 in
    let restrFrames := prev.(RestrFramesDef) in
    {|
      CohFrameTypesDef := mkCohFrameTypesStep prev;
      RestrFramesDef Q :=
        (restrFrames Q.1; fun q Hq ε => totalMap (mkRestrLayer restrPaintings Q q Hq ε)):
          mkRestrFrameTypes (mkPaintings extraDeps)
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

Definition mkRestrFrames `{depsCohs: DepsCohs p k} :=
  (mkCohFrameTypesAndRestrFrames depsCohs.(_restrPaintings)).(RestrFramesDef)
    depsCohs.(_cohs).

Definition mkDepsRestr `{depsCohs: DepsCohs p k} :=
  toDepsRestr mkRestrFrames.

Definition mkRestrFrame `{depsCohs: DepsCohs p k}:
  forall q (Hq: q <= k) (ε: arity), Functor (mkFrame mkDepsRestr.(1)) (mkFrame depsCohs.(_deps)) :=
  mkRestrFrames.2.

Inductive DepsCohsExtension p: forall k (depsCohs: DepsCohs p k), Type :=
| TopCohDep `{depsCohs: DepsCohs p 0}
  (E: Family (mkFrame mkDepsRestr)):
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
  - now apply (AddRestrDep mkDepsRestr
    (mkExtraDeps p.+1 k depsCohs extraDepsCohs)).
Defined.

Fixpoint mkRestrPainting `(extraDepsCohs: DepsCohsExtension p k depsCohs)
  q {struct q}: forall (Hq: q <= k) (ε: arity),
    Map (mkPainting (mkDepsRestr; mkExtraDeps extraDepsCohs))
      mkDepsRestr.(_paintings).2 (mkDepsRestr.(_restrFrames).2 q Hq ε) :=
  match q with
  | 0 => fun _ ε => layerHead _ (fun ω => mkDepsRestr.(_restrFrames).2 0 leR_O ω)
      (mkPainting (mkExtraDeps extraDepsCohs)) ε
  | q.+1 =>
    match extraDepsCohs with
    | TopCohDep E => fun Hq _ => match leR_O_contra Hq with end
    | AddCohDep depsCohs extraDepsCohs => fun Hq ε =>
      sigmaMap (mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) q (⇓ Hq) ε)
        (mkRestrPainting extraDepsCohs q (⇓ Hq) ε)
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

Definition mkCohPaintingType `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs) :=
  forall q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity),
    MapEq (depsCohs.(_cohs).2 q Hq r Hr ε ω)
      (compMap (mkRestrPainting (depsCohs; extraDepsCohs) r (Hr ↕ (↑ Hq)) ω)
        (depsCohs.(_restrPaintings).2 q Hq ε))
      (compMap (mkRestrPainting (depsCohs; extraDepsCohs) q.+1 (⇑ Hq) ε)
        (depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) ω)).

Fixpoint mkCohPaintingTypes {p}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k depsCohs extraDepsCohs =>
    { R: mkCohPaintingTypes (depsCohs; extraDepsCohs) &T
         mkCohPaintingType extraDepsCohs }
  end.

(** Layer coherence lies over the recursively constructed frame coherence. *)
Definition mkCohLayer `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity):
  MapEq (prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω)
    (compMap
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1 prevCohFrames r (Hr ↕ ↑ Hq) ω)
      (mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) q Hq ε))
    (compMap
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1 prevCohFrames q.+1 (⇑ Hq) ε)
      (mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) r (Hr ↕ Hq) ω)).
Proof.
  eapply layerMapEq.
  now exact (cohPaintings.2 q Hq r Hr ε ω).
Defined.

(** A frame-coherence pair consists of recursive frame and layer coherence. *)
Fixpoint mkCohFrames `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs) {struct p}:
  mkCohFrameTypes (mkRestrPaintings extraDepsCohs).
Proof.
  destruct p.
  - unshelve esplit. now exact tt. intros. now apply feqRefl.
  - pose (h := mkCohFrames p k.+1 depsCohs.(1)%depscohs
      (depsCohs; extraDepsCohs)%extradepscohs cohPaintings.1).
    unshelve esplit. now exact h.
    intros q Hq r Hr ε ω.
    now exact (totalMapEq (h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω)
      (mkCohLayer cohPaintings (prevCohFrames := h) q Hq r Hr ε ω)).
Defined.

(** This package adds painting coherence to the frame coherence in
    [DepsCohs]. Equality between object paths follows from h-set UIP. *)
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
  (E: Family (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs depsCohs2))))
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

(** Painting coherence pairs layer coherence with the recursive painting step. *)
Fixpoint mkCohPainting `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingType (mkExtraCohs extraDepsCohs2).
Proof.
  intros q Hq r Hr ε ω. destruct r.
  - apply mapEqOfTotal.
    change (totalMap (mkRestrPainting (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)
        0 (Hr ↕ ↑ Hq) ω) ⨟ᶠ
      totalMap ((mkDepsCohs depsCohs2).(_restrPaintings).2 q Hq ε) ≐
      totalMap (mkRestrPainting (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)
        q.+1 (⇑ Hq) ε) ⨟ᶠ
      totalMap ((mkDepsCohs depsCohs2).(_restrPaintings).2 0 (Hr ↕ Hq) ω)).
    apply feqSym. now apply sigmaLayerHead.
  - destruct q.
    { exfalso; now apply leR_O_contra in Hr. }
    destruct extraDepsCohs2.
    { exfalso; now apply leR_O_contra in Hq. }
    unshelve eapply sigmaCompositeMapEq.
    + now exact (mkCohLayer depsCohs2.(_cohPaintings) q (⇓ Hq) r (⇓ Hr) ε ω).
    + now exact (mkCohPainting p.+1 k depsCohs2 extraDepsCohs2
        q (⇓ Hq) r (⇓ Hr) ε ω).
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

Class νStrictGpdData p := {
  frames: mkFrameTypes p 0;
  paintings: mkPaintingTypes p 0 frames;
  restrFrames: mkRestrFrameTypes paintings;
  restrPaintings E: mkRestrPaintingTypes (TopRestrDep E);
  cohFrames E: mkCohFrameTypes (restrPaintings E);
  cohPaintings E E': mkCohPaintingTypes
    (depsCohs := toDepsCohs (deps := toDepsRestr restrFrames) (cohFrames E))
    (TopCohDep E');
}.

Section νStrictGpdData.
Variable p: nat.
Variable C: νStrictGpdData p.
Variable E: Family (mkFrame (toDepsRestr C.(restrFrames))).

#[local]
Instance mkνStrictGpdData: νStrictGpdData p.+1 :=
{|
  frames := mkFrames _;
  paintings := mkPaintings _;
  restrFrames := mkRestrFrames;
  restrPaintings E' := mkRestrPaintings (TopCohDep E');
  cohFrames E' := mkCohFrames (C.(cohPaintings) E E');
  cohPaintings E' E'' :=
    mkCohPaintings (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(cohPaintings) E E')) E'');
|}.
End νStrictGpdData.

Class νStrictGpd p := {
  prefix: Type;
  data: prefix -> νStrictGpdData p;
}.

Definition mkPrefix p {C: νStrictGpd p}: Type :=
  { D: C.(prefix) &T Family (mkFrame (toDepsRestr (C.(data) D).(restrFrames))) }.

#[local]
Instance mkνStrictGpd0: νStrictGpd 0.
Proof.
  unshelve esplit.
  - now exact hunit.
  - unshelve esplit; try now trivial.
Defined.

#[local]
Instance mkνStrictGpd {p} (C: νStrictGpd p): νStrictGpd p.+1 :=
{|
  prefix := mkPrefix p;
  data := fun D: mkPrefix p => mkνStrictGpdData p (C.(data) D.1) D.2;
|}.

Fixpoint νStrictGpdAt n: νStrictGpd n :=
  match n with
  | O => mkνStrictGpd0
  | n.+1 => mkνStrictGpd (νStrictGpdAt n)
  end.

Definition mkExtensionType {p} {C: νStrictGpd p} (D: C.(prefix)): Type :=
  Family (mkFrame (toDepsRestr (C.(data) D).(restrFrames))).

Definition νStrictGpdTel: Telescope := {|
  stage l := (νStrictGpdAt l).(prefix);
  datum l X := mkExtensionType X;
  extend l X E := ((X; E): (νStrictGpdAt l.+1).(prefix));
  bond l Y := Y.1;
  head l Y := Y.2;
  bondExtend l X E := eq_refl;
  extendHead l Y := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

Definition νStrictGpdFrom n (X: (νStrictGpdAt n).(prefix)): Type := Limit νStrictGpdTel n X.

Definition νStrictGpds := νStrictGpdFrom 0 tt.

End νStrictGpd.

(** Share the generated dependency types between constructions over one layer. *)
Module Type νStrictGpdSig (A: LayerSig).
Include νStrictGpd A.
End νStrictGpdSig.

(** Concrete layer instances. *)
Module νStrictGpdSimplicial := νStrictGpd SimplicialLayer.
Module νStrictGpdCubical := νStrictGpd CubicalLayer.

Definition AugmentedSemiSimplicialStrictGroupoids := νStrictGpdSimplicial.νStrictGpds.
Definition SemiSimplicialStrictGroupoids :=
  νStrictGpdSimplicial.νStrictGpdFrom 1 (tt; const unitGroupoid unitGroupoid).
Definition SemiCubicalStrictGroupoids := νStrictGpdCubical.νStrictGpds.

Local Open Scope displayed_gpd_scope.

(** Retain named groupoid constructions and coherence operations when
    displaying the prefix. *)
Example SemiSimplicial3 := Eval lazy -[unitGroupoid total reindex sigma terminalFunctor
  totalMap reindexMap sigmaMap compFunctor feqRefl
  νStrictGpdSimplicial.LT.layerMap νStrictGpdSimplicial.LT.layerHead
  νStrictGpdSimplicial.LT.layerMapEq νStrictGpdSimplicial.LT.sigmaLayerHead
  totalMapEq sigmaMapEq sigmaCompositeMapEq feqSym feqTrans feqWhiskerL
  feqWhiskerR feqAssoc composeSquares] in
  (νStrictGpdSimplicial.νStrictGpdAt 3).(νStrictGpdSimplicial.prefix).
Print SemiSimplicial3.
