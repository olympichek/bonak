(** The coherent diagram of a fixed number of indexed frame layers. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation LeSProp RewLemmas Limit.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor.
From Bonak.Equiv.Gpd Require Import Face PresheafOfνGpd Boundary PathAlgebra.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** The functor of each file in this development includes the functor of
    the file it builds on and adds its own submodules. A definition then
    has a single instance, whichever file refers to it. *)
Module PartialDiagramOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (Extraction: ExtractionSig A Core Faces).
Include BoundaryOn A Core Faces.

Module Partial.
Import A.
Module Export Indexed := Faces.
Import Extraction.

(** The endpoint retains [p] layers while each step moves one layer from
    the frame into its painting. The tower supplies the remaining fillers. *)
Definition PartialState (p k: nat): Type :=
  {m: nat &T {X: (νGpdAt m).(prefix) &T {L: νGpdFrom m X &T
    {dc: DepsCohs3 p k &T DepsCohs3Chain (νDepsCohs3At L) dc}}}}.

Definition stateCohs {p k} (z: PartialState p k): DepsCohs3 p k := z.2.2.2.1.

Definition stateNext {p k} (z: PartialState p k): PartialState p k.+1 :=
  (z.1.+1; ((z.2.1; this z.2.2.1); (next z.2.2.1;
    (proj1DepsCohs3 (mkDepsCohs3 (stateCohs z)
      (chain3Ext (νExt3At z.2.2.1) z.2.2.2.2));
     chainUp1 (νExt3At z.2.2.1) z.2.2.2.2)))).

Definition stateUp {p k} (z: PartialState p k): PartialState p.+1 k :=
  (z.1.+1; ((z.2.1; this z.2.2.1); (next z.2.2.1;
    (mkDepsCohs3 (stateCohs z) (chain3Ext (νExt3At z.2.2.1) z.2.2.2.2);
      cohs3ChainUp (νExt3At z.2.2.1) z.2.2.2.2)))).

Lemma stateNextUp {p k} (z: PartialState p k):
  stateNext (stateUp z) = stateUp (stateNext z).
Proof. now reflexivity. Defined.

Definition stateDrop {p k} (z: PartialState p.+1 k): PartialState p k.+1 :=
  (z.1; (z.2.1; (z.2.2.1;
    (proj1DepsCohs3 (stateCohs z); DepsCohs3ChainCons z.2.2.2.2)))).

Lemma stateNextDrop {p k} (z: PartialState p.+1 k):
  stateNext (stateDrop z) = stateDrop (stateNext z).
Proof. now reflexivity. Defined.

Definition stateFrame {p k} (z: PartialState p k): HGpd :=
  mkFrame (stateCohs z).(_depsCohs2).(_depsCohs).(_deps).

Lemma stateUpFrame {p k} (z: PartialState p k):
  stateFrame (stateUp z) =
    mkFrame (mkDepsRestr (depsCohs := (stateCohs z).(_depsCohs2).(_depsCohs))).
Proof. now reflexivity. Defined.

Definition stateRestrict {p k} (z: PartialState p k)
  q (Hq: q <= k) a: stateFrame (stateNext z) -> stateFrame z :=
  mkRestrFrame (depsCohs := (stateCohs z).(_depsCohs2).(_depsCohs)) q Hq a.

Definition stateRestrictCoh {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b (x: stateFrame (stateNext (stateNext z))):
  stateRestrict z q Hq a (stateRestrict (stateNext z) r (Hr ↕ ↑ Hq) b x) =
    stateRestrict z r (Hr ↕ Hq) b (stateRestrict (stateNext z) q.+1 (⇑ Hq) a x) :=
  (mkDepsCohs (stateCohs z).(_depsCohs2)).(_cohs).2 q Hq r Hr a b x.

Definition stateRestrictHex {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) a b c
  (x: stateFrame (stateNext (stateNext (stateNext z)))):
  CohShapes.hexagonal_coherence
    (stateRestrict z q Hq a) (stateRestrict z s (Hs ↕ (Hr ↕ Hq)) c)
    (stateRestrict z r (Hr ↕ Hq) b)
    (stateRestrictCoh (stateNext z) r (Hr ↕ ↑ Hq) s Hs b c x)
    (stateRestrictCoh (stateNext z) q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b x)
    (stateRestrictCoh (stateNext z) q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) a c x)
    (stateRestrictCoh z q Hq s (Hs ↕ Hr) a c
      (stateRestrict (stateNext (stateNext z)) r.+1 (⇑ (Hr ↕ ↑ Hq)) b x))
    (stateRestrictCoh z q Hq r Hr a b
      (stateRestrict (stateNext (stateNext z)) s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) c x))
    (stateRestrictCoh z r (Hr ↕ Hq) s Hs b c
      (stateRestrict (stateNext (stateNext z)) q.+2 (⇑ (⇑ Hq)) a x)) :=
  (mkDepsCohs2 (stateCohs z)).(_coh2Frames).2 q Hq r Hr s Hs a b c x.

Definition stateTotal {p k} (z: PartialState p k): HGpd := νTotal z.2.2.1.

Definition stateTotalFace {p k} (z: PartialState p k)
  q (Hq: q <= k) a: stateTotal (stateNext z) -> stateTotal z :=
  gFaceC z.2.2.1 z.2.2.2.2 0 q Hq a.

Definition stateTotalCoh {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b (x: stateTotal (stateNext (stateNext z))):
  stateTotalFace z q Hq a (stateTotalFace (stateNext z) r (Hr ↕ ↑ Hq) b x) =
    stateTotalFace z r (Hr ↕ Hq) b (stateTotalFace (stateNext z) q.+1 (⇑ Hq) a x) :=
  gFaceCohC z.2.2.1 z.2.2.2.2 0 q Hq r Hr a b x.

Definition stateTotalHex {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) a b c
  (x: stateTotal (stateNext (stateNext (stateNext z)))):
  CohShapes.hexagonal_coherence
    (stateTotalFace z q Hq a) (stateTotalFace z s (Hs ↕ (Hr ↕ Hq)) c)
    (stateTotalFace z r (Hr ↕ Hq) b)
    (stateTotalCoh (stateNext z) r (Hr ↕ ↑ Hq) s Hs b c x)
    (stateTotalCoh (stateNext z) q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b x)
    (stateTotalCoh (stateNext z) q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) a c x)
    (stateTotalCoh z q Hq s (Hs ↕ Hr) a c
      (stateTotalFace (stateNext (stateNext z)) r.+1 (⇑ (Hr ↕ ↑ Hq)) b x))
    (stateTotalCoh z q Hq r Hr a b
      (stateTotalFace (stateNext (stateNext z)) s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) c x))
    (stateTotalCoh z r (Hr ↕ Hq) s Hs b c
      (stateTotalFace (stateNext (stateNext z)) q.+2 (⇑ (⇑ Hq)) a x)) :=
  gFaceCoh2C z.2.2.1 z.2.2.2.2 0 q Hq r Hr s Hs a b c x.

Definition stateProjection {p k} (z: PartialState p k) (t: stateTotal z): stateFrame z :=
  getFrame (cohsChainDeps (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 z.2.2.2.2))) t.1.

Local Lemma extChainDepsCohs {P K} {dcTop: DepsCohs P K}
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc):
  extChainDeps (cohsChainExt c) = cohsChainDeps c.
Proof. induction c; cbn; [now reflexivity|now rewrite IHc]. Defined.

Local Lemma nextProjectionChain {P K} {dcTop: DepsCohs3 P K}
  (e: DepsCohs3Extension P K dcTop) {p k} {dc: DepsCohs3 p k}
  (c: DepsCohs3Chain dcTop dc):
  cohsChainDeps (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (chainUp1 e c))) =
    DepsChainCons (cohsChainNext (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 c))).
Proof. induction c; cbn; [now reflexivity|now exact (f_equal (fun c => DepsChainCons c) IHc)]. Defined.

Lemma stateProjectionFace {p k} (z: PartialState p k)
  q (Hq: q <= k) a (t: stateTotal (stateNext z)):
  stateProjection z (stateTotalFace z q Hq a t) =
    stateRestrict z q Hq a (stateProjection (stateNext z) t).
Proof.
  unfold stateProjection, stateTotalFace, stateRestrict.
  cbn [gFaceC]. unfold faceDeep, faceAt, restrCell.
  rewrite <- extChainDepsCohs, getFrameGetPainting.
  unfold stateNext; cbn [projT1 projT2].
  apply f_equal.
  now exact (eq_sym (f_equal (fun c => getFrame c t.1)
    (nextProjectionChain (νExt3At z.2.2.1) z.2.2.2.2))).
Defined.

(** Whole cells decoded at the endpoint of the indexed projection chain. *)
Definition stateLocalCell {p k} (z: PartialState p k): HGpd :=
  {d: stateFrame z & mkPainting (stateCohs z).(_depsCohs2).(_depsCohs).(_extraDeps) d}.

Definition stateLocalFace {p k} (z: PartialState p k)
  q (Hq: q <= k) a: stateLocalCell (stateNext z) -> stateLocalCell z :=
  fun t => restrCell (stateCohs z).(_depsCohs2).(_extraDepsCohs) q Hq a t.1 t.2.

Definition stateLocalCoh {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b (x: stateLocalCell (stateNext (stateNext z))):
  stateLocalFace z q Hq a (stateLocalFace (stateNext z) r (Hr ↕ ↑ Hq) b x) =
    stateLocalFace z r (Hr ↕ Hq) b (stateLocalFace (stateNext z) q.+1 (⇑ Hq) a x) :=
  restrCellCoh (stateCohs z) q Hq r Hr a b x.1 x.2.

Definition stateLocalHex {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) a b c
  (x: stateLocalCell (stateNext (stateNext (stateNext z)))):
  CohShapes.hexagonal_coherence
    (stateLocalFace z q Hq a) (stateLocalFace z s (Hs ↕ (Hr ↕ Hq)) c)
    (stateLocalFace z r (Hr ↕ Hq) b)
    (stateLocalCoh (stateNext z) r (Hr ↕ ↑ Hq) s Hs b c x)
    (stateLocalCoh (stateNext z) q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b x)
    (stateLocalCoh (stateNext z) q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) a c x)
    (stateLocalCoh z q Hq s (Hs ↕ Hr) a c
      (stateLocalFace (stateNext (stateNext z)) r.+1 (⇑ (Hr ↕ ↑ Hq)) b x))
    (stateLocalCoh z q Hq r Hr a b
      (stateLocalFace (stateNext (stateNext z)) s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) c x))
    (stateLocalCoh z r (Hr ↕ Hq) s Hs b c
      (stateLocalFace (stateNext (stateNext z)) q.+2 (⇑ (⇑ Hq)) a x)) :=
  restrCellCoh2 (stateCohs z) (chain3Ext (νExt3At z.2.2.1) z.2.2.2.2)
    q Hq r Hr s Hs a b c x.1 x.2.

Local Lemma pairPathBase {T: Type} {P: T -> Type} {x y: T}
  {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  projT1_eq (= p; q) = p.
Proof. now destruct q, p. Defined.

Lemma stateLocalProjectionFace {p k} (z: PartialState p k)
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z)):
  (stateLocalFace z q Hq a t).1 = stateRestrict z q Hq a t.1.
Proof. now reflexivity. Defined.

Lemma stateLocalProjectionCoh {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b (t: stateLocalCell (stateNext (stateNext z))):
  f_equal (fun t: stateLocalCell z => t.1) (stateLocalCoh z q Hq r Hr a b t) =
    stateRestrictCoh z q Hq r Hr a b t.1.
Proof. unfold stateLocalCoh, restrCellCoh, stateRestrictCoh. now apply pairPathBase. Defined.

Definition stateCellEquiv {p k} (z: PartialState p k):
  Equiv (stateLocalCell z) (stateTotal z) :=
  Paths.paintingChainEquiv
    (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 z.2.2.2.2))).

Lemma stateCellProjection {p k} (z: PartialState p k) (t: stateLocalCell z):
  stateProjection z (stateCellEquiv z t) = t.1.
Proof.
  unfold stateProjection.
  rewrite <- extChainDepsCohs.
  now apply getFrameGetPainting.
Defined.

Definition stateCellFace {p k} (z: PartialState p k)
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z)):
  stateTotalFace z q Hq a (stateCellEquiv (stateNext z) t) =
    stateCellEquiv z (stateLocalFace z q Hq a t) :=
  f_equal (fun u: stateLocalCell (stateNext z) => stateCellEquiv z (stateLocalFace z q Hq a u))
    (deepCellRebuildUp (νExt3At z.2.2.1) z.2.2.2.2 t).

Local Lemma reconstructedFaceSquare {C0 C1 C2 G0 G1: Type}
  (e0: C0 -> G0) (e1: C1 -> G1) (r1: G1 -> C1)
  (h1: forall t, r1 (e1 t) = t)
  (f g: C1 -> C0) (u v: C2 -> C1) (h: forall t, f (u t) = g (v t))
  {s x: C2} (p: s = x):
  (f_equal (fun z => e0 (f (r1 z))) (f_equal (fun z => e1 (u z)) p)
    • f_equal (fun z => e0 (f z)) (h1 (u x))) • f_equal e0 (h x) =
  (f_equal (fun z => e0 (f z)) (h1 (u s))
    • (f_equal e0 (h s) • eq_sym (f_equal (fun z => e0 (g z)) (h1 (v s)))))
    • (f_equal (fun z => e0 (g (r1 z))) (f_equal (fun z => e1 (v z)) p)
      • f_equal (fun z => e0 (g z)) (h1 (v x))).
Proof.
  destruct p; cbn [f_equal]. rewrite 2 eq_trans_refl_l.
  now rewrite eqTransAssoc, transSymCancelR2.
Defined.

Lemma stateCellFaceCoh {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (t: stateLocalCell (stateNext (stateNext z))):
  (f_equal (stateTotalFace z q Hq a)
      (stateCellFace (stateNext z) r (Hr ↕ ↑ Hq) b t)
    • stateCellFace z q Hq a (stateLocalFace (stateNext z) r (Hr ↕ ↑ Hq) b t))
    • f_equal (stateCellEquiv z) (stateLocalCoh z q Hq r Hr a b t) =
  stateTotalCoh z q Hq r Hr a b (stateCellEquiv (stateNext (stateNext z)) t)
    • (f_equal (stateTotalFace z r (Hr ↕ Hq) b)
        (stateCellFace (stateNext z) q.+1 (⇑ Hq) a t)
      • stateCellFace z r (Hr ↕ Hq) b (stateLocalFace (stateNext z) q.+1 (⇑ Hq) a t)).
Proof.
  unfold stateTotalCoh; cbn [gFaceCohC].
  rewrite faceAtCohUpConj.
  now exact (reconstructedFaceSquare
    (stateCellEquiv z) (stateCellEquiv (stateNext z))
    (fun u => deepCell (cohs3ChainDepsCohs2 z.2.2.2.2) u)
    (deepCellRebuildUp (νExt3At z.2.2.1) z.2.2.2.2)
    (stateLocalFace z q Hq a) (stateLocalFace z r (Hr ↕ Hq) b)
    (stateLocalFace (stateNext z) r (Hr ↕ ↑ Hq) b)
    (stateLocalFace (stateNext z) q.+1 (⇑ Hq) a)
    (stateLocalCoh z q Hq r Hr a b)
    (deepCellRebuildUp (νExt3At (next z.2.2.1))
      (chainUp1 (νExt3At z.2.2.1) z.2.2.2.2) t)).
Defined.

Section Start.
Context {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X).

Fixpoint partialState (k: nat): PartialState p k :=
  match k with
  | 0 => (p; (X; (L; (νDepsCohs3At L; DepsCohs3ChainNil))))
  | S k => stateNext (partialState k)
  end.

Definition partialFramePresentation: νGpdPresentation arity := {|
  G0 k := stateFrame (partialState k);
  GFace k q Hq a := stateRestrict (partialState k) q Hq a;
  GFaceCoh k q Hq r Hr a b := stateRestrictCoh (partialState k) q Hq r Hr a b;
  GFaceCoh2 k q Hq r Hr s Hs a b c := stateRestrictHex (partialState k) q Hq r Hr s Hs a b c;
|}.

Definition partialCellPresentation: νGpdPresentation arity := {|
  G0 k := stateTotal (partialState k);
  GFace k q Hq a := stateTotalFace (partialState k) q Hq a;
  GFaceCoh k q Hq r Hr a b := stateTotalCoh (partialState k) q Hq r Hr a b;
  GFaceCoh2 k q Hq r Hr s Hs a b c := stateTotalHex (partialState k) q Hq r Hr s Hs a b c;
|}.

Definition partialLocalCellPresentation: νGpdPresentation arity := {|
  G0 k := stateLocalCell (partialState k);
  GFace k q Hq a := stateLocalFace (partialState k) q Hq a;
  GFaceCoh k q Hq r Hr a b := stateLocalCoh (partialState k) q Hq r Hr a b;
  GFaceCoh2 k q Hq r Hr s Hs a b c := stateLocalHex (partialState k) q Hq r Hr s Hs a b c;
|}.

Definition partialFrameDiagram := toPsfTot arity partialFramePresentation.
Definition partialCellDiagram := toPsfTot arity partialCellPresentation.
Definition partialLocalCellDiagram := toPsfTot arity partialLocalCellPresentation.

End Start.

Lemma partialStateDrop {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X) (k: nat):
  partialState L k.+1 = stateDrop (partialState (next L) k).
Proof.
  induction k as [|k IH].
  - now reflexivity.
  - change (stateNext (partialState L k.+1) = stateDrop (stateNext (partialState (next L) k))).
    rewrite <- stateNextDrop. now exact (f_equal (@stateNext p k.+1) IH).
Defined.

Lemma partialStateUp {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X) (k: nat):
  partialState (next L) k = stateUp (partialState L k).
Proof.
  induction k as [|k IH].
  - now reflexivity.
  - change (stateNext (partialState (next L) k) = stateUp (stateNext (partialState L k))).
    rewrite <- stateNextUp. now exact (f_equal (@stateNext p.+1 k) IH).
Defined.

(** The two ways of moving the newly retained layer agree with the
    original successor state, including the chosen endpoint paths. *)
Lemma partialStateDropUp {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X) (k: nat):
  partialStateDrop L k • f_equal (@stateDrop p k) (partialStateUp L k) = eq_refl.
Proof.
  induction k as [|k IH]; [now reflexivity|].
  change (f_equal (@stateNext p k.+1) (partialStateDrop L k)
    • f_equal (@stateDrop p k.+1)
      (f_equal (@stateNext p.+1 k) (partialStateUp L k)) = eq_refl).
  rewrite (f_equal_compose (@stateNext p.+1 k) (@stateDrop p k.+1) (partialStateUp L k)).
  change (f_equal (@stateNext p k.+1) (partialStateDrop L k)
    • f_equal (fun z => stateNext (stateDrop z)) (partialStateUp L k) = eq_refl).
  rewrite <- (f_equal_compose (@stateDrop p k) (@stateNext p k.+1) (partialStateUp L k)).
  rewrite <- eq_trans_map_distr, IH. now reflexivity.
Defined.

End Partial.

(** Moving a frame layer into its painting preserves faces and their selected
    exchange paths after shifting both face indices. *)
Module Shift.
Export Partial.
Import A Extraction.

Lemma restrCellCohShift {p k} (dc3: DepsCohs3 p.+1 k)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 (proj1DepsCohs3 dc3))).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 (proj1DepsCohs3 dc3))).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 (proj1DepsCohs3 dc3))).(_extraDepsCohs))).2 D):
  restrCellCoh (proj1DepsCohs3 dc3) Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D C
  = f_equal unassoc (restrCellCoh dc3 Q HQ R HR ε ω (D; C.1) C.2).
Proof.
  unfold restrCellCoh.
  now refine (eq_sym (f_equal_unassoc_curried
    ((mkDepsCohs (proj1DepsCohs2 dc3.(_depsCohs2))).(_cohs).2 Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D)
    (mkCohLayer dc3.(_depsCohs2).(_cohPaintings).2 dc3.(_depsCohs2).(_coh2Frames).2 Q HQ R HR ε ω D C.1)
    (mkCohPainting dc3.(_extraDepsCohs2) Q HQ R HR ε ω (D; C.1) C.2))).
Defined.

(** The cell a stage sees, one stage below its extension. *)
Definition CellBelow {p k} (dc3: DepsCohs3 p k): Type :=
  { D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1) &T
    (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D }.

Definition assocC {p k} {dc3: DepsCohs3 p.+1 k}
  (w: CellBelow (proj1DepsCohs3 dc3)): CellBelow dc3 :=
  ((w.1; w.2.1); w.2.2).

Lemma faceAtCohUpShift {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p.+1 k}
  (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (w: CellBelow (proj1DepsCohs3 dc3)):
  faceAtCohUp e0 (DepsCohs3ChainCons a) Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω w.1 w.2
  = faceAtCohUp e0 a Q HQ R HR ε ω (assocC w).1 (assocC w).2.
Proof.
  rewrite 2 faceAtCohUpConj.
  apply conjShiftM.
  - now exact (f_equal_compose unassoc
      (fun w0 => faceAt (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)) Q.+1 (⇑ HQ) ε w0.1 w0.2)
      (deepCellFaceAtUp e0 a R (HR ↕ ↑ HQ) ω (assocC w).1 (assocC w).2)).
  - refine (eq_trans (f_equal (fun z => f_equal (faceRebuild (DepsCohs3ChainCons a)) z)
      (restrCellCohShift dc3 Q HQ R HR ε ω w.1 w.2)) _).
    now exact (f_equal_compose unassoc (faceRebuild (DepsCohs3ChainCons a))
      (restrCellCoh dc3 Q HQ R HR ε ω (assocC w).1 (assocC w).2)).
  - now exact (f_equal_compose unassoc
      (fun w0 => faceAt (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)) R.+1 (⇑ HR ↕ ⇑ HQ) ω w0.1 w0.2)
      (deepCellFaceAtUp e0 a Q.+1 (⇑ HQ) ε (assocC w).1 (assocC w).2)).
Defined.


(** Cancelling a descent step shifts the residual face index by one. *)
Lemma gFaceCCons (n: nat):
  forall {m} {X: (νGpdAt m).(prefix)} (L: νGpdFrom m X)
    {p k} {dc: DepsCohs3 p.+1 k} (c: DepsCohs3Chain (νDepsCohs3At L) dc)
    q (Hq: q <= n + k) (HqFull: q.+1 <= n + k.+1) a (t: gF0 L n.+1),
  gFaceC L (DepsCohs3ChainCons c) n q.+1 HqFull a t =
    gFaceC L c n q Hq a t.
Proof.
  induction n as [|n IH]; intros m X L p k dc c q Hq HqFull a t.
  - now reflexivity.
  - cbn [gFaceC]. now apply IH.
Defined.

Lemma gFaceCohCCons (n: nat):
  forall {m} {X: (νGpdAt m).(prefix)} (L: νGpdFrom m X)
    {p k} {dc: DepsCohs3 p.+1 k} (c: DepsCohs3Chain (νDepsCohs3At L) dc)
    q (Hq: q <= n + k) (HqFull: q.+1 <= n + k.+1)
    r (Hr: r <= q) a b (t: gF0 L n.+2),
  gFaceCohC L (DepsCohs3ChainCons c) n q.+1 HqFull r.+1 (⇑ Hr) a b t
    • (gFaceCCons n L c r (Hr ↕ Hq) (⇑ Hr ↕ HqFull) b
        (gFaceC L (DepsCohs3ChainCons c) n.+1 q.+2 (⇑ HqFull) a t)
      • f_equal (gFaceC L c n r (Hr ↕ Hq) b)
        (gFaceCCons n.+1 L c q.+1 (⇑ Hq) (⇑ HqFull) a t)) =
  (gFaceCCons n L c q Hq HqFull a
      (gFaceC L (DepsCohs3ChainCons c) n.+1 r.+1 (⇑ Hr ↕ ↑ HqFull) b t)
    • f_equal (gFaceC L c n q Hq a)
      (gFaceCCons n.+1 L c r (Hr ↕ ↑ Hq) (⇑ Hr ↕ ↑ HqFull) b t))
    • gFaceCohC L c n q Hq r Hr a b t.
Proof.
  induction n as [|n IH]; intros m X L p k dc c q Hq HqFull r Hr a b t.
  - cbn [gFaceCohC gFaceCCons f_equal].
    rewrite (faceAtCohUpShift (νExt3At L) c q Hq r Hr a b
      (deepCell (cohs3ChainDepsCohs2
        (chainUp1 (νExt3At L) (DepsCohs3ChainCons c))) t)).
    now rewrite 2 eq_trans_refl_l, eq_trans_refl_r.
  - now exact (IH _ _ (next L) p k.+1 _ (chainUp1 (νExt3At L) c) q
      (leR_eq_r (plus_n_Sm n k) Hq)
      (leR_eq_r (plus_n_Sm n k.+1) HqFull) r Hr a b t).
Defined.

Lemma stateTotalFaceDrop {p k} (z: PartialState p.+1 k)
  q (Hq: q <= k) a (t: stateTotal (stateNext z)):
  stateTotalFace (stateDrop z) q.+1 (⇑ Hq) a t = stateTotalFace z q Hq a t.
Proof. now reflexivity. Defined.

Lemma stateTotalCohDrop {p k} (z: PartialState p.+1 k)
  q (Hq: q <= k) r (Hr: r <= q) a b (t: stateTotal (stateNext (stateNext z))):
  stateTotalCoh (stateDrop z) q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b t =
    stateTotalCoh z q Hq r Hr a b t.
Proof.
  now exact (faceAtCohUpShift (νExt3At z.2.2.1) z.2.2.2.2 q Hq r Hr a b
    (deepCell (cohs3ChainDepsCohs2
      (chainUp1 (νExt3At z.2.2.1) (DepsCohs3ChainCons z.2.2.2.2))) t)).
Defined.

End Shift.

End PartialDiagramOn.
