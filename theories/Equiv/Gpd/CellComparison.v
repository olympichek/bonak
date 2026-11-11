(** Coherent cell readout at a processed indexed prefix. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation LeSProp RewLemmas Limit PathSquares
  Funext NatLemmas.
From Bonak.νGpd Require Import Layer νGpd Lemmas Pasting.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor Comparison Model.
From Bonak.Equiv.Gpd Require Import Face PresheafOfνGpd PartialDiagram
  PositionExtraction Boundary.
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

Module CellComparisonOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (Extraction: ExtractionSig A Core Faces).
Include PositionExtractionOn A Core Faces Extraction.

(** The whole-cell comparison for the indexed partial-frame diagrams. *)
Module Cells.
Export Partial.
Import A.
Import Extraction.

Definition composeFaceSquare := @PathSquares.composeFaceSquare.
Arguments composeFaceSquare {A0 A1 A2 B0 B1 B2 C0 C1 C2}.

(** Reading the global total space from the current relative position. *)
Definition partialCellPositionEquiv {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) k:
  Equiv ((partialCellPresentation L).(G0) k) ((Relative.positionPresentation L).(G0) k) :=
  rewEquiv GDom (eq_sym (Relative.descTotal L (Relative.descPartial L k))).

Definition partialCellPositionFace {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) k q (Hq: q <= k) a
  (t: (partialCellPresentation L).(G0) k.+1):
  (Relative.positionPresentation L).(GFace) k q Hq a
      (partialCellPositionEquiv L k.+1 t) =
    partialCellPositionEquiv L k ((partialCellPresentation L).(GFace) k q Hq a t) :=
  Relative.descFaceG L (Relative.descPartial L k) 0 q Hq Hq a t.

Lemma partialCellPositionFaceCoh {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) k q (Hq: q <= k) r (Hr: r <= q) a b
  (t: (partialCellPresentation L).(G0) k.+2):
  (f_equal ((Relative.positionPresentation L).(GFace) k q Hq a)
      (partialCellPositionFace L k.+1 r (Hr ↕ ↑ Hq) b t)
    • partialCellPositionFace L k q Hq a
      ((partialCellPresentation L).(GFace) k.+1 r (Hr ↕ ↑ Hq) b t))
    • f_equal (partialCellPositionEquiv L k)
      ((partialCellPresentation L).(GFaceCoh) k q Hq r Hr a b t) =
  (Relative.positionPresentation L).(GFaceCoh) k q Hq r Hr a b
      (partialCellPositionEquiv L k.+2 t)
    • (f_equal ((Relative.positionPresentation L).(GFace) k r (Hr ↕ Hq) b)
        (partialCellPositionFace L k.+1 q.+1 (⇑ Hq) a t)
      • partialCellPositionFace L k r (Hr ↕ Hq) b
        ((partialCellPresentation L).(GFace) k.+1 q.+1 (⇑ Hq) a t)).
Proof.
  now exact (Relative.descFaceGCoh L (Relative.descPartial L k) 0 q Hq r Hr a b t).
Defined.

Definition localCellPositionEquiv {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) k:
  Equiv ((partialLocalCellPresentation L).(G0) k) ((Relative.positionPresentation L).(G0) k) :=
  compEquiv (stateCellEquiv (partialState L k)) (partialCellPositionEquiv L k).

Definition localCellPositionFace {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) k q (Hq: q <= k) a
  (t: (partialLocalCellPresentation L).(G0) k.+1):
  (Relative.positionPresentation L).(GFace) k q Hq a
      (localCellPositionEquiv L k.+1 t) =
    localCellPositionEquiv L k ((partialLocalCellPresentation L).(GFace) k q Hq a t) :=
  partialCellPositionFace L k q Hq a (stateCellEquiv (partialState L k.+1) t)
    • f_equal (partialCellPositionEquiv L k) (stateCellFace (partialState L k) q Hq a t).

Lemma localCellPositionFaceCoh {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) k q (Hq: q <= k) r (Hr: r <= q) a b
  (t: (partialLocalCellPresentation L).(G0) k.+2):
  (f_equal ((Relative.positionPresentation L).(GFace) k q Hq a)
      (localCellPositionFace L k.+1 r (Hr ↕ ↑ Hq) b t)
    • localCellPositionFace L k q Hq a
      ((partialLocalCellPresentation L).(GFace) k.+1 r (Hr ↕ ↑ Hq) b t))
    • f_equal (localCellPositionEquiv L k)
      ((partialLocalCellPresentation L).(GFaceCoh) k q Hq r Hr a b t) =
  (Relative.positionPresentation L).(GFaceCoh) k q Hq r Hr a b
      (localCellPositionEquiv L k.+2 t)
    • (f_equal ((Relative.positionPresentation L).(GFace) k r (Hr ↕ Hq) b)
        (localCellPositionFace L k.+1 q.+1 (⇑ Hq) a t)
      • localCellPositionFace L k r (Hr ↕ Hq) b
        ((partialLocalCellPresentation L).(GFace) k.+1 q.+1 (⇑ Hq) a t)).
Proof.
  now exact (composeFaceSquare
    (stateCellEquiv (partialState L k)) (stateCellEquiv (partialState L k.+1))
    (stateCellEquiv (partialState L k.+2))
    (partialCellPositionEquiv L k) (partialCellPositionEquiv L k.+1)
    (partialCellPositionEquiv L k.+2)
    (stateLocalFace (partialState L k) q Hq a)
    (stateLocalFace (partialState L k) r (Hr ↕ Hq) b)
    (stateLocalFace (partialState L k.+1) r (Hr ↕ ↑ Hq) b)
    (stateLocalFace (partialState L k.+1) q.+1 (⇑ Hq) a)
    (stateTotalFace (partialState L k) q Hq a)
    (stateTotalFace (partialState L k) r (Hr ↕ Hq) b)
    (stateTotalFace (partialState L k.+1) r (Hr ↕ ↑ Hq) b)
    (stateTotalFace (partialState L k.+1) q.+1 (⇑ Hq) a)
    ((Relative.positionPresentation L).(GFace) k q Hq a)
    ((Relative.positionPresentation L).(GFace) k r (Hr ↕ Hq) b)
    ((Relative.positionPresentation L).(GFace) k.+1 r (Hr ↕ ↑ Hq) b)
    ((Relative.positionPresentation L).(GFace) k.+1 q.+1 (⇑ Hq) a)
    (stateCellFace (partialState L k) q Hq a)
    (stateCellFace (partialState L k) r (Hr ↕ Hq) b)
    (stateCellFace (partialState L k.+1) r (Hr ↕ ↑ Hq) b)
    (stateCellFace (partialState L k.+1) q.+1 (⇑ Hq) a)
    (partialCellPositionFace L k q Hq a)
    (partialCellPositionFace L k r (Hr ↕ Hq) b)
    (partialCellPositionFace L k.+1 r (Hr ↕ ↑ Hq) b)
    (partialCellPositionFace L k.+1 q.+1 (⇑ Hq) a)
    (stateLocalCoh (partialState L k) q Hq r Hr a b)
    (stateTotalCoh (partialState L k) q Hq r Hr a b)
    ((Relative.positionPresentation L).(GFaceCoh) k q Hq r Hr a b) t
    (stateCellFaceCoh (partialState L k) q Hq r Hr a b t)
    (partialCellPositionFaceCoh L k q Hq r Hr a b
      (stateCellEquiv (partialState L k.+2) t))).
Defined.

Definition localCellDrop {p k} (z: PartialState p.+1 k)
  (t: stateLocalCell z): stateLocalCell (stateDrop z) :=
  (t.1.1; (t.1.2; t.2)).

End Cells.

(** The selected exchange square for one newly attached indexed face. *)
Module Coh.
Import A Faces.
Import Partial.

Definition attachedFace {p k} (z: PartialState p k) (c: arity):
  stateFrame (stateUp z) -> stateLocalCell z :=
  @νFace p k (stateCohs z).(_depsCohs2).(_depsCohs)
    p k (stateCohs z).(_depsCohs2).(_depsCohs) DepsCohsChainNil c.

Definition attachedFaceNatural {p k} (z: PartialState p k)
  q (Hq: q <= k) a c (d: stateFrame (stateUp (stateNext z))):
  attachedFace z c (stateRestrict (stateUp z) q Hq a d)
    = stateLocalFace z q Hq a (attachedFace (stateNext z) c d) :=
  eq_sym (@Attach.restrictionLayerFace p k (stateCohs z).(_depsCohs2)
    p k (stateCohs z).(_depsCohs2).(_depsCohs).(_deps)
    (stateCohs z).(_depsCohs2).(_depsCohs).(_extraDeps) ExtChainNil q Hq a c d).

Local Lemma hexNaturality {T: Type} {x0 x1 x2 x3 x4 x5: T}
  (u: x0 = x1) (v: x1 = x2) (w: x2 = x3)
  (a: x0 = x4) (b: x4 = x5) (c: x5 = x3)
  (H: (u • v) • w = a • (b • c)):
  w • (eq_sym c • eq_sym b) = (eq_sym v • eq_sym u) • a.
Proof.
  destruct u, v, w, a, b. cbn in H |- *.
  rewrite 2 eq_trans_refl_l in H. rewrite <- H. now reflexivity.
Defined.

Definition attachedFaceComparison {p k} (z: PartialState p k)
  q (Hq: q <= k) a c (d: stateFrame (stateUp (stateNext z))):
  stateLocalFace z q Hq a (attachedFace (stateNext z) c d)
    = attachedFace z c (stateRestrict (stateUp z) q Hq a d) :=
  @Attach.restrictionLayerFace p k (stateCohs z).(_depsCohs2)
    p k (stateCohs z).(_depsCohs2).(_depsCohs).(_deps)
    (stateCohs z).(_depsCohs2).(_depsCohs).(_extraDeps) ExtChainNil q Hq a c d.


Local Lemma pairPathBase {T: Type} {P: T -> Type} {x y: T}
  {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  projT1_eq (= p; q) = p.
Proof. now destruct q, p. Defined.

Lemma stateUpExchangeBase {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (d: stateFrame (stateUp (stateNext (stateNext z)))):
  projT1_eq (stateRestrictCoh (stateUp z) q Hq r Hr a b d)
    = stateRestrictCoh (stateNext z) (S q) (⇑ Hq) (S r) (⇑ Hr) a b d.1.
Proof.
  unfold stateRestrictCoh.
  now apply pairPathBase.
Defined.

Lemma attachedFaceHex {p k} (z: PartialState p k)
  q (Hq: q <= k) r (Hr: r <= q) a b c
  (d: stateFrame (stateUp (stateNext (stateNext z)))):
  hexagonal_coherence (stateLocalFace z q Hq a) (attachedFace z c)
    (stateLocalFace z r (Hr ↕ Hq) b)
    (attachedFaceComparison (stateNext z) r (Hr ↕ ↑ Hq) b c d)
    (stateRestrictCoh (stateUp z) q Hq r Hr a b d)
    (attachedFaceComparison (stateNext z) (S q) (⇑ Hq) a c d)
    (attachedFaceComparison z q Hq a c
      (stateRestrict (stateUp (stateNext z)) r (Hr ↕ ↑ Hq) b d))
    (stateLocalCoh z q Hq r Hr a b (attachedFace (stateNext (stateNext z)) c d))
    (attachedFaceComparison z r (Hr ↕ Hq) b c
      (stateRestrict (stateUp (stateNext z)) (S q) (⇑ Hq) a d)).
Proof.
  unfold attachedFaceComparison, Attach.restrictionLayerFace, attachedFace,
    stateLocalFace, stateLocalCoh, stateRestrictCoh, restrCell, restrCellCoh.
  unfold νFace.
  cbn [cohsChainExt cohsChainNext getFrame getPainting].
  rewrite 4 f_equal_id.
  unshelve eapply (eq_existT_curried_hex
    (stateRestrict z q Hq a)
    (@mkRestrPainting p k (stateCohs z).(_depsCohs2).(_depsCohs)
      (stateCohs z).(_depsCohs2).(_extraDepsCohs) q Hq a)
    (stateRestrict z r (Hr ↕ Hq) b)
    (@mkRestrPainting p k (stateCohs z).(_depsCohs2).(_depsCohs)
      (stateCohs z).(_depsCohs2).(_extraDepsCohs) r (Hr ↕ Hq) b)
    (stateRestrict z 0 leR_O c)
    (fun d (l: Layer (fun u =>
      mkPainting (stateCohs z).(_depsCohs2).(_depsCohs).(_extraDeps)
        (stateRestrict z 0 leR_O u d))) => nth l c)).
  - now exact (((mkDepsCohs2 (stateCohs z)).(_coh2Frames)).2
      q Hq r Hr 0 leR_O a b c d.1).
  - unfold mkCohLayer.
    eapply (lmap2_triangle_rew_eq
      (P := fun x => mkPainting
        (stateCohs z).(_depsCohs2).(_depsCohs).(_extraDeps) x)
      (S := fun x => mkPainting
        (stateCohs (stateNext z)).(_depsCohs2).(_depsCohs).(_extraDeps) x)
      (rf0 := fun t => stateRestrict z 0 leR_O t)
      (θ := c) (l := d.2)
      (e2 := fun t => stateRestrictCoh (stateNext z)
        r (Hr ↕ ↑ Hq) 0 leR_O b t d.1)
      (e5 := fun t => stateRestrictCoh (stateNext z)
        (S q) (⇑ Hq) 0 leR_O a t d.1)
      (pQ := fun t => stateRestrictCoh z q Hq 0 leR_O a t
        (stateRestrict (stateNext (stateNext z)) (S r) (⇑ (Hr ↕ ↑ Hq)) b d.1))
      (pR := fun t => stateRestrictCoh z r (Hr ↕ Hq) 0 leR_O b t
        (stateRestrict (stateNext (stateNext z)) (S (S q)) (⇑ (⇑ Hq)) a d.1))
      (aL := fun t => @mkRestrPainting p (S k)
        (stateCohs (stateNext z)).(_depsCohs2).(_depsCohs)
        (stateCohs (stateNext z)).(_depsCohs2).(_extraDepsCohs)
        r (Hr ↕ ↑ Hq) b (stateRestrict (stateNext (stateNext z)) 0 leR_O t d.1))
      (aR := fun t => @mkRestrPainting p (S k)
        (stateCohs (stateNext z)).(_depsCohs2).(_depsCohs)
        (stateCohs (stateNext z)).(_depsCohs2).(_extraDepsCohs)
        (S q) (⇑ Hq) a (stateRestrict (stateNext (stateNext z)) 0 leR_O t d.1))
      (F := @mkRestrPainting p k (stateCohs z).(_depsCohs2).(_depsCohs)
        (stateCohs z).(_depsCohs2).(_extraDepsCohs) q Hq a)
      (G := @mkRestrPainting p k (stateCohs z).(_depsCohs2).(_depsCohs)
        (stateCohs z).(_depsCohs2).(_extraDepsCohs) r (Hr ↕ Hq) b)).
    now apply (layer_square
      (P := fun x => GDom (mkPainting
        (stateCohs z).(_depsCohs2).(_depsCohs).(_extraDeps) x))
      (S := fun x => GDom (mkPainting
        (stateCohs (stateNext z)).(_depsCohs2).(_depsCohs).(_extraDeps) x))
      (S' := fun x => GDom (mkPainting
        (stateCohs (stateNext z)).(_depsCohs2).(_depsCohs).(_extraDeps) x))).
Defined.

Lemma attachedFaceCoh:
  forall p k (z: PartialState p k) q (Hq: q <= k) r (Hr: r <= q)
    a b c (d: stateFrame (stateUp (stateNext (stateNext z)))),
  f_equal (attachedFace z c) (stateRestrictCoh (stateUp z) q Hq r Hr a b d)
    • (attachedFaceNatural z r (Hr ↕ Hq) b c
        (stateRestrict (stateUp (stateNext z)) (S q) (⇑ Hq) a d)
      • f_equal (stateLocalFace z r (Hr ↕ Hq) b)
          (attachedFaceNatural (stateNext z) (S q) (⇑ Hq) a c d))
  = (attachedFaceNatural z q Hq a c
        (stateRestrict (stateUp (stateNext z)) r (Hr ↕ ↑ Hq) b d)
      • f_equal (stateLocalFace z q Hq a)
          (attachedFaceNatural (stateNext z) r (Hr ↕ ↑ Hq) b c d))
    • stateLocalCoh z q Hq r Hr a b (attachedFace (stateNext (stateNext z)) c d).

Proof.
  intros p k z q Hq r Hr a b c d.
  unfold attachedFaceNatural. rewrite 2 fEqualSym.
  now exact (hexNaturality _ _ _ _ _ _ (attachedFaceHex z q Hq r Hr a b c d)).
Defined.

End Coh.

Module Readout.
Export Cells.
Import A Extraction.
Include GpdComparison A.

Definition localPositionComparison {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X):
  FaceComparison (partialLocalCellPresentation L).(G0) (Relative.positionPresentation L).(G0)
    (partialLocalCellPresentation L).(GFace) (Relative.positionPresentation L).(GFace)
    (partialLocalCellPresentation L).(GFaceCoh) (Relative.positionPresentation L).(GFaceCoh) :=
  @Build_FaceComparison _ _ _ _ _ _ (localCellPositionEquiv L)
    (localCellPositionFace L) (localCellPositionFaceCoh L).

Definition presentationComparison {P Q: νGpdPresentation arity}
  (e: PresentationEquiv P Q):
  FaceComparison P.(G0) Q.(G0) P.(GFace) Q.(GFace) P.(GFaceCoh) Q.(GFaceCoh) :=
  comparisonOfForward e.(presentationCell) e.(presentationFace)
    e.(presentationFaceCoh).

Definition presentationOfComparison {P Q: νGpdPresentation arity}
  (u: FaceComparison P.(G0) Q.(G0) P.(GFace) Q.(GFace) P.(GFaceCoh) Q.(GFaceCoh)):
  PresentationEquiv P Q :=
  @Build_PresentationEquiv arity P Q u.(comparisonCell)
    (fun k q Hq a t => eq_sym (u.(comparisonFace) k q Hq a t))
    (comparisonForwardCoh u).

Definition localCellDropEquiv {p k} (z: PartialState (S p) k):
  Equiv (stateLocalCell z) (stateLocalCell (stateDrop z)) :=
  qinvEquiv (localCellDrop z) (fun t => ((t.1; t.2.1); t.2.2))
    (fun _ => eq_refl) (fun _ => eq_refl).

Lemma localCellDropFace {p k} (z: PartialState (S p) k)
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z)):
  stateLocalFace (stateDrop z) (S q) (⇑ Hq) a (localCellDrop (stateNext z) t) =
    localCellDrop z (stateLocalFace z q Hq a t).
Proof. now reflexivity. Defined.

Lemma localCellDropCoh {p k} (z: PartialState (S p) k)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (t: stateLocalCell (stateNext (stateNext z))):
  stateLocalCoh (stateDrop z) (S q) (⇑ Hq) (S r) (⇑ Hr) a b
    (localCellDrop (stateNext (stateNext z)) t) =
    f_equal (localCellDrop z) (stateLocalCoh z q Hq r Hr a b t).
Proof.
  now exact (Shift.restrCellCohShift (stateCohs z) q Hq r Hr a b t.1.1 (t.1.2; t.2)).
Defined.

Definition reindexedDrop {p k} (z: PartialState (S p) k)
  {w: PartialState p (S k)} (e: w = stateDrop z)
  (t: stateLocalCell z): stateLocalCell w :=
  rew [fun w => stateLocalCell w] eq_sym e in localCellDrop z t.

Definition reindexedDropFace {p k} (z: PartialState (S p) k)
  {w: PartialState p (S k)} (e: w = stateDrop z)
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z)):
  stateLocalFace w (S q) (⇑ Hq) a
    (reindexedDrop (stateNext z) (f_equal (@stateNext p (S k)) e) t) =
    reindexedDrop z e (stateLocalFace z q Hq a t).
Proof.
  pattern w, e. apply eqIndL. now apply localCellDropFace.
Defined.

Lemma reindexedDropCoh {p k} (z: PartialState (S p) k)
  {w: PartialState p (S k)} (e: w = stateDrop z)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (t: stateLocalCell (stateNext (stateNext z))):
  (f_equal (stateLocalFace w (S q) (⇑ Hq) a)
      (reindexedDropFace (stateNext z) (f_equal (@stateNext p (S k)) e)
        r (Hr ↕ ↑ Hq) b t)
    • reindexedDropFace z e q Hq a (stateLocalFace (stateNext z) r (Hr ↕ ↑ Hq) b t))
    • f_equal (reindexedDrop z e) (stateLocalCoh z q Hq r Hr a b t)
  = stateLocalCoh w (S q) (⇑ Hq) (S r) (⇑ Hr) a b
      (reindexedDrop (stateNext (stateNext z))
        (f_equal (@stateNext p (S (S k))) (f_equal (@stateNext p (S k)) e)) t)
    • (f_equal (stateLocalFace w (S r) (⇑ (Hr ↕ Hq)) b)
        (reindexedDropFace (stateNext z) (f_equal (@stateNext p (S k)) e)
          (S q) (⇑ Hq) a t)
      • reindexedDropFace z e r (Hr ↕ Hq) b
        (stateLocalFace (stateNext z) (S q) (⇑ Hq) a t)).
Proof.
  pattern w, e. apply eqIndL.
  cbn [reindexedDrop reindexedDropFace eqIndL localCellDropFace f_equal].
  rewrite eq_trans_refl_l, eq_trans_refl_r.
  now exact (eq_sym (localCellDropCoh z q Hq r Hr a b t)).
Defined.

Definition localSuccessorEquiv {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X) k:
  Equiv ((partialLocalCellPresentation (next L)).(G0) k)
    ((partialLocalCellPresentation L).(G0) (S k)) :=
  compEquiv (localCellDropEquiv (partialState (next L) k))
    (rewEquiv (fun w => stateLocalCell w) (eq_sym (partialStateDrop L k))).

Definition localSuccessorFace {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X)
  k q (Hq: q <= k) a (t: (partialLocalCellPresentation (next L)).(G0) (S k)):
  (partialLocalCellPresentation L).(GFace) (S k) (S q) (⇑ Hq) a
    (localSuccessorEquiv L (S k) t) =
    localSuccessorEquiv L k ((partialLocalCellPresentation (next L)).(GFace) k q Hq a t) :=
  reindexedDropFace (partialState (next L) k) (partialStateDrop L k) q Hq a t.

Definition localSuccessorCoh {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X)
  k q (Hq: q <= k) r (Hr: r <= q) a b
  (t: (partialLocalCellPresentation (next L)).(G0) (S (S k))):
  (f_equal ((partialLocalCellPresentation L).(GFace) (S k) (S q) (⇑ Hq) a)
      (localSuccessorFace L (S k) r (Hr ↕ ↑ Hq) b t)
    • localSuccessorFace L k q Hq a
      ((partialLocalCellPresentation (next L)).(GFace) (S k) r (Hr ↕ ↑ Hq) b t))
    • f_equal (localSuccessorEquiv L k)
      ((partialLocalCellPresentation (next L)).(GFaceCoh) k q Hq r Hr a b t)
  = (partialLocalCellPresentation L).(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b
      (localSuccessorEquiv L (S (S k)) t)
    • (f_equal ((partialLocalCellPresentation L).(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) b)
        (localSuccessorFace L (S k) (S q) (⇑ Hq) a t)
      • localSuccessorFace L k r (Hr ↕ Hq) b
        ((partialLocalCellPresentation (next L)).(GFace) (S k) (S q) (⇑ Hq) a t)) :=
  reindexedDropCoh (partialState (next L) k) (partialStateDrop L k) q Hq r Hr a b t.

Definition backwardStateCell {p k} {z z': PartialState p k} (h: z = z'):
  Equiv (stateLocalCell z') (stateLocalCell z) :=
  rewEquiv (fun z => stateLocalCell z) (eq_sym h).

Definition backwardStateCellFace {p k} {z z': PartialState p k} (h: z = z')
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z')):
  stateLocalFace z q Hq a (backwardStateCell (f_equal (@stateNext p k) h) t) =
    backwardStateCell h (stateLocalFace z' q Hq a t).
Proof. now destruct h. Defined.

Lemma backwardStateCellCoh {p k} {z z': PartialState p k} (h: z = z')
  q (Hq: q <= k) r (Hr: r <= q) a b
  (t: stateLocalCell (stateNext (stateNext z'))):
  (f_equal (stateLocalFace z q Hq a)
      (backwardStateCellFace (f_equal (@stateNext p k) h) r (Hr ↕ ↑ Hq) b t)
    • backwardStateCellFace h q Hq a (stateLocalFace (stateNext z') r (Hr ↕ ↑ Hq) b t))
    • f_equal (backwardStateCell h) (stateLocalCoh z' q Hq r Hr a b t)
  = stateLocalCoh z q Hq r Hr a b
      (backwardStateCell (f_equal (@stateNext p (S k)) (f_equal (@stateNext p k) h)) t)
    • (f_equal (stateLocalFace z r (Hr ↕ Hq) b)
        (backwardStateCellFace (f_equal (@stateNext p k) h) (S q) (⇑ Hq) a t)
      • backwardStateCellFace h r (Hr ↕ Hq) b
        (stateLocalFace (stateNext z') (S q) (⇑ Hq) a t)).
Proof.
  destruct h. cbn [backwardStateCellFace backwardStateCell rewEquiv qinvEquiv eqvFun f_equal].
  rewrite f_equal_id. now apply eq_trans_refl_l.
Defined.

Definition rawUpLocalPresentation {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X):
  νGpdPresentation arity := {|
  G0 k := stateLocalCell (stateUp (partialState L k));
  GFace k q Hq a := stateLocalFace (stateUp (partialState L k)) q Hq a;
  GFaceCoh k q Hq r Hr a b := stateLocalCoh (stateUp (partialState L k)) q Hq r Hr a b;
  GFaceCoh2 k q Hq r Hr s Hs a b c :=
    stateLocalHex (stateUp (partialState L k)) q Hq r Hr s Hs a b c;
|}.

Definition rawUpToNextEquiv {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X) k:
  Equiv ((rawUpLocalPresentation L).(G0) k) ((partialLocalCellPresentation (next L)).(G0) k) :=
  backwardStateCell (partialStateUp L k).

Definition rawUpToNextFace {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X)
  k q (Hq: q <= k) a (t: (rawUpLocalPresentation L).(G0) (S k)):
  (partialLocalCellPresentation (next L)).(GFace) k q Hq a (rawUpToNextEquiv L (S k) t) =
    rawUpToNextEquiv L k ((rawUpLocalPresentation L).(GFace) k q Hq a t) :=
  backwardStateCellFace (partialStateUp L k) q Hq a t.

Definition rawUpToNextCoh {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X)
  k q (Hq: q <= k) r (Hr: r <= q) a b
  (t: (rawUpLocalPresentation L).(G0) (S (S k))):
  (f_equal ((partialLocalCellPresentation (next L)).(GFace) k q Hq a)
      (rawUpToNextFace L (S k) r (Hr ↕ ↑ Hq) b t)
    • rawUpToNextFace L k q Hq a ((rawUpLocalPresentation L).(GFace) (S k) r (Hr ↕ ↑ Hq) b t))
    • f_equal (rawUpToNextEquiv L k) ((rawUpLocalPresentation L).(GFaceCoh) k q Hq r Hr a b t)
  = (partialLocalCellPresentation (next L)).(GFaceCoh) k q Hq r Hr a b
      (rawUpToNextEquiv L (S (S k)) t)
    • (f_equal ((partialLocalCellPresentation (next L)).(GFace) k r (Hr ↕ Hq) b)
        (rawUpToNextFace L (S k) (S q) (⇑ Hq) a t)
      • rawUpToNextFace L k r (Hr ↕ Hq) b
        ((rawUpLocalPresentation L).(GFace) (S k) (S q) (⇑ Hq) a t)) :=
  backwardStateCellCoh (partialStateUp L k) q Hq r Hr a b t.

Definition dropTriangleNext {p k} {z z': PartialState (S p) k}
  (h: z = z') (e: stateDrop z' = stateDrop z)
  (triangle: e • f_equal (@stateDrop p k) h = eq_refl):
  f_equal (@stateNext p (S k)) e
    • f_equal (@stateDrop p (S k)) (f_equal (@stateNext (S p) k) h) = eq_refl.
Proof.
  destruct h. change (e = eq_refl) in triangle. subst e. now reflexivity.
Defined.

Definition dropTransportTriangle {p k} {z z': PartialState (S p) k}
  (h: z = z') (e: stateDrop z' = stateDrop z)
  (triangle: e • f_equal (@stateDrop p k) h = eq_refl) (t: stateLocalCell z'):
  reindexedDrop z e (backwardStateCell h t) = localCellDrop z' t.
Proof.
  destruct h. change (e = eq_refl) in triangle. subst e. now reflexivity.
Defined.

Lemma dropTransportTriangleFace {p k} {z z': PartialState (S p) k}
  (h: z = z') (e: stateDrop z' = stateDrop z)
  (triangle: e • f_equal (@stateDrop p k) h = eq_refl)
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z')):
  f_equal (stateLocalFace (stateDrop z') (S q) (⇑ Hq) a)
    (dropTransportTriangle (f_equal (@stateNext (S p) k) h)
      (f_equal (@stateNext p (S k)) e) (dropTriangleNext h e triangle) t)
  = (reindexedDropFace z e q Hq a
        (backwardStateCell (f_equal (@stateNext (S p) k) h) t)
      • f_equal (reindexedDrop z e) (backwardStateCellFace h q Hq a t))
    • dropTransportTriangle h e triangle (stateLocalFace z' q Hq a t).
Proof.
  destruct h. change (e = eq_refl) in triangle. subst e. now reflexivity.
Defined.

Fixpoint localSuccessorTriangle {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X) (k: nat):
  partialStateDrop L k • f_equal (@stateDrop p k) (partialStateUp L k) = eq_refl :=
  match k with
  | 0 => eq_refl
  | S j => dropTriangleNext (partialStateUp L j) (partialStateDrop L j)
      (localSuccessorTriangle L j)
  end.

Definition localSuccessorUp {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X) k
  (t: (rawUpLocalPresentation L).(G0) k):
  localSuccessorEquiv L k (rawUpToNextEquiv L k t) = localCellDrop (stateUp (partialState L k)) t :=
  dropTransportTriangle (partialStateUp L k) (partialStateDrop L k)
    (localSuccessorTriangle L k) t.

Lemma localSuccessorUpFace {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X)
  k q (Hq: q <= k) a (t: (rawUpLocalPresentation L).(G0) (S k)):
  f_equal ((partialLocalCellPresentation L).(GFace) (S k) (S q) (⇑ Hq) a)
    (localSuccessorUp L (S k) t)
  = (localSuccessorFace L k q Hq a (rawUpToNextEquiv L (S k) t)
      • f_equal (localSuccessorEquiv L k) (rawUpToNextFace L k q Hq a t))
    • localSuccessorUp L k ((rawUpLocalPresentation L).(GFace) k q Hq a t).
Proof.
  now exact (dropTransportTriangleFace (partialStateUp L k) (partialStateDrop L k)
    (localSuccessorTriangle L k) q Hq a t).
Defined.


Definition localSuccessorComparison {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X):
  FaceComparison (partialLocalCellPresentation (next L)).(G0)
    (fun k => (partialLocalCellPresentation L).(G0) (S k))
    (partialLocalCellPresentation (next L)).(GFace)
    (fun k q Hq a => (partialLocalCellPresentation L).(GFace) (S k) (S q) (⇑ Hq) a)
    (partialLocalCellPresentation (next L)).(GFaceCoh)
    (fun k q Hq r Hr a b => (partialLocalCellPresentation L).(GFaceCoh)
      (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b) :=
  @Build_FaceComparison _ _ _ _ _ _ (localSuccessorEquiv L)
    (localSuccessorFace L) (localSuccessorCoh L).

Definition rawUpToNextComparison {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X):
  FaceComparison (rawUpLocalPresentation L).(G0) (partialLocalCellPresentation (next L)).(G0)
    (rawUpLocalPresentation L).(GFace) (partialLocalCellPresentation (next L)).(GFace)
    (rawUpLocalPresentation L).(GFaceCoh) (partialLocalCellPresentation (next L)).(GFaceCoh) :=
  @Build_FaceComparison _ _ _ _ _ _ (rawUpToNextEquiv L)
    (rawUpToNextFace L) (rawUpToNextCoh L).

Definition rawUpDropComparison {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X):
  FaceComparison (rawUpLocalPresentation L).(G0)
    (fun k => (partialLocalCellPresentation L).(G0) (S k))
    (rawUpLocalPresentation L).(GFace)
    (fun k q Hq a => (partialLocalCellPresentation L).(GFace) (S k) (S q) (⇑ Hq) a)
    (rawUpLocalPresentation L).(GFaceCoh)
    (fun k q Hq r Hr a b => (partialLocalCellPresentation L).(GFaceCoh)
      (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b).
Proof.
  refine (@Build_FaceComparison _ _ _ _ _ _
    (fun k => localCellDropEquiv (stateUp (partialState L k)))
    (fun k => localCellDropFace (stateUp (partialState L k))) _).
  intros k q Hq r Hr a b t.
  cbn [localCellDropFace f_equal].
  rewrite eq_trans_refl_l, eq_trans_refl_r.
  now exact (eq_sym (localCellDropCoh (stateUp (partialState L k)) q Hq r Hr a b t)).
Defined.

Definition LocalReadout (Y: νGpds) (T: ResidualTarget (g Y)) (p: nat) :=
  FaceComparison (partialLocalCellPresentation (νGpdPack p Y).2).(G0)
    (T.(targetCells) p).(G0)
    (partialLocalCellPresentation (νGpdPack p Y).2).(GFace)
    (T.(targetCells) p).(GFace)
    (partialLocalCellPresentation (νGpdPack p Y).2).(GFaceCoh)
    (T.(targetCells) p).(GFaceCoh).

Definition zeroLocalReadout (Y: νGpds) (T: ResidualTarget (g Y)): LocalReadout Y T 0 :=
  composeComparison (localPositionComparison Y)
    (presentationComparison T.(targetZero)).

Section RecursiveLocalReadout.
Context (Y: νGpds) (Tgt: ResidualTarget (g Y)).

Definition shiftReadout (p: nat):
  FaceComparison (Tgt.(targetCells) (S p)).(G0)
    (fun k => (Tgt.(targetCells) p).(G0) (S k))
    (Tgt.(targetCells) (S p)).(GFace)
    (fun k q Hq a => (Tgt.(targetCells) p).(GFace) (S k) (S q) (⇑ Hq) a)
    (Tgt.(targetCells) (S p)).(GFaceCoh)
    (fun k q Hq r Hr a b => (Tgt.(targetCells) p).(GFaceCoh)
      (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b) :=
  presentationComparison (Tgt.(targetShift) p).

Local Abbreviation shift := shiftReadout.

Fixpoint buildLocalReadouts (p: nat): LocalReadout Y Tgt p :=
  match p with
  | 0 => zeroLocalReadout Y Tgt
  | S p => composeComparison (localSuccessorComparison (νGpdPack p Y).2)
      (composeComparison (shiftComparison (buildLocalReadouts p))
        (inverseComparison (shift p)))
  end.

Definition oldUpReadout p :=
  composeComparison (rawUpDropComparison (νGpdPack p Y).2)
    (shiftComparison (buildLocalReadouts p)).

Definition newUpReadout p :=
  composeComparison (rawUpToNextComparison (νGpdPack p Y).2)
    (composeComparison (buildLocalReadouts (S p)) (shift p)).

Definition localReadoutUp p k
  (t: (rawUpLocalPresentation (νGpdPack p Y).2).(G0) k):
  (oldUpReadout p).(comparisonCell) k t = (newUpReadout p).(comparisonCell) k t :=
  eq_sym (f_equal ((buildLocalReadouts p).(comparisonCell) (S k))
    (localSuccessorUp (νGpdPack p Y).2 k t))
  • eq_sym ((toIsHAE ((shift p).(comparisonCell) k)).(haeSec)
      ((buildLocalReadouts p).(comparisonCell) (S k)
        (localSuccessorEquiv (νGpdPack p Y).2 k
          (rawUpToNextEquiv (νGpdPack p Y).2 k t)))).

Local Lemma cancelPathUnit {T: Type} {x y z: T}
  (u: x = y) (v: y = z) (w: x = z) (h: u • v = w):
  eq_sym w • u = eq_sym v.
Proof. destruct u, v; cbn in h. now destruct h. Defined.

Local Lemma inverseUnitFace {D0 D1: Type} (d: D1 -> D0)
  (u0: D0 -> D0) (u1: D1 -> D1)
  (s0: forall z, u0 z = z) (s1: forall y, u1 y = y)
  (face: forall y, d (u1 y) = u0 (d y))
  (unit: forall y, face y • s0 (d y) = f_equal d (s1 y))
  (y: D1) {z: D0} (p: d y = z):
  f_equal d (eq_sym (s1 y)) • (face y • f_equal u0 p) = p • eq_sym (s0 z).
Proof.
  destruct p; cbn [f_equal].
  rewrite eq_trans_refl_r, eq_trans_refl_l, <- eq_sym_map_distr.
  now exact (cancelPathUnit (face y) (s0 (d y)) (f_equal d (s1 y)) (unit y)).
Defined.

(** A comparison of source maps, followed by a comparison and the inverse
    unit, gives a comparison with the same selected face paths. *)
Local Lemma readoutUpFaceKernel {C0 C1 D0 D1: Type}
  (r0: C0 -> D0) (r1: C1 -> D1) (c: C1 -> C0) (d: D1 -> D0)
  (phi: forall x, d (r1 x) = r0 (c x))
  (u0: D0 -> D0) (u1: D1 -> D1)
  (s0: forall z, u0 z = z) (s1: forall y, u1 y = y)
  (face: forall y, d (u1 y) = u0 (d y))
  (unit: forall y, face y • s0 (d y) = f_equal d (s1 y))
  {x z: C1} (theta1: x = z) {a: C0}
  (alpha: c x = a) (theta0: a = c z)
  (square: f_equal c theta1 = alpha • theta0):
  f_equal d (eq_sym (f_equal r1 theta1) • eq_sym (s1 (r1 x)))
    • (face (r1 x) • f_equal u0 (phi x • f_equal r0 alpha)) =
  phi z • (eq_sym (f_equal r0 theta0) • eq_sym (s0 (r0 a))).
Proof.
  destruct theta1, alpha; cbn [f_equal] in square.
  rewrite eq_trans_refl_l in square. destruct square.
  cbn [f_equal eq_sym].
  rewrite 2 eq_trans_refl_l, eq_trans_refl_r.
  now apply inverseUnitFace.
Defined.

Local Lemma normalizeReadoutFace {B C D E: Type}
  (s: B -> C) (r: C -> D) (i: D -> E) (e: E -> D)
  {b b': B} (u: b = b') {c: C} (v: c = s b)
  {d: D} (w: d = r c) {z: E} (a: z = i d) {x: D} (t: x = e z):
  (t • f_equal e ((a • f_equal i w) • f_equal (fun c => i (r c)) v))
    • f_equal (fun b => e (i (r (s b)))) u =
  (t • f_equal e a) • f_equal (fun d => e (i d))
    (w • f_equal r (v • f_equal s u)).
Proof.
  destruct u; subst c; subst d; subst z; subst x. now reflexivity.
Defined.

Lemma localReadoutUpFace p k q (Hq: q <= k) a
  (t: (rawUpLocalPresentation (νGpdPack p Y).2).(G0) (S k)):
  f_equal ((Tgt.(targetCells) p).(GFace) (S k) (S q) (⇑ Hq) a)
      (localReadoutUp p (S k) t)
    • (newUpReadout p).(comparisonFace) k q Hq a t =
  (oldUpReadout p).(comparisonFace) k q Hq a t
    • localReadoutUp p k
      ((rawUpLocalPresentation (νGpdPack p Y).2).(GFace) k q Hq a t).
Proof.
  unfold oldUpReadout, newUpReadout, localReadoutUp.
  cbn [buildLocalReadouts composeComparison shiftComparison inverseComparison
    comparisonCell comparisonFace compEquiv symEquiv qinvEquiv eqvFun rawUpDropComparison
    rawUpToNextComparison localSuccessorComparison localCellDropFace f_equal].
  rewrite (normalizeReadoutFace
    (localSuccessorEquiv (νGpdPack p Y).2 k)
    ((buildLocalReadouts p).(comparisonCell) (S k))
    (invEq ((shift p).(comparisonCell) k)) ((shift p).(comparisonCell) k)
    (rawUpToNextFace (νGpdPack p Y).2 k q Hq a t)
    (localSuccessorFace (νGpdPack p Y).2 k q Hq a
      (rawUpToNextEquiv (νGpdPack p Y).2 (S k) t))
    ((buildLocalReadouts p).(comparisonFace) (S k) (S q) (⇑ Hq) a
      (localSuccessorEquiv (νGpdPack p Y).2 (S k)
        (rawUpToNextEquiv (νGpdPack p Y).2 (S k) t)))
    (inverseComparisonFace (shift p).(comparisonCell) (shift p).(comparisonFace)
      k q Hq a ((buildLocalReadouts p).(comparisonCell) (S (S k))
        (localSuccessorEquiv (νGpdPack p Y).2 (S k)
          (rawUpToNextEquiv (νGpdPack p Y).2 (S k) t))))
    ((shift p).(comparisonFace) k q Hq a
      (invEq ((shift p).(comparisonCell) (S k))
        ((buildLocalReadouts p).(comparisonCell) (S (S k))
          (localSuccessorEquiv (νGpdPack p Y).2 (S k)
            (rawUpToNextEquiv (νGpdPack p Y).2 (S k) t)))))).
  now exact (readoutUpFaceKernel
    ((buildLocalReadouts p).(comparisonCell) (S k))
    ((buildLocalReadouts p).(comparisonCell) (S (S k)))
    ((partialLocalCellPresentation (νGpdPack p Y).2).(GFace)
      (S k) (S q) (⇑ Hq) a)
    ((Tgt.(targetCells) p).(GFace) (S k) (S q) (⇑ Hq) a)
    ((buildLocalReadouts p).(comparisonFace) (S k) (S q) (⇑ Hq) a)
    (fun z => (shift p).(comparisonCell) k (invEq ((shift p).(comparisonCell) k) z))
    (fun z => (shift p).(comparisonCell) (S k)
      (invEq ((shift p).(comparisonCell) (S k)) z))
    ((toIsHAE ((shift p).(comparisonCell) k)).(haeSec))
    ((toIsHAE ((shift p).(comparisonCell) (S k))).(haeSec))
    (fun y => (shift p).(comparisonFace) k q Hq a
        (invEq ((shift p).(comparisonCell) (S k)) y)
      • f_equal ((shift p).(comparisonCell) k)
        (inverseComparisonFace (shift p).(comparisonCell) (shift p).(comparisonFace)
          k q Hq a y))
    (inverseComparisonUnit (shift p).(comparisonCell) (shift p).(comparisonFace)
      k q Hq a)
    (localSuccessorUp (νGpdPack p Y).2 (S k) t)
    (localSuccessorFace (νGpdPack p Y).2 k q Hq a
        (rawUpToNextEquiv (νGpdPack p Y).2 (S k) t)
      • f_equal (localSuccessorEquiv (νGpdPack p Y).2 k)
        (rawUpToNextFace (νGpdPack p Y).2 k q Hq a t))
    (localSuccessorUp (νGpdPack p Y).2 k
      ((rawUpLocalPresentation (νGpdPack p Y).2).(GFace) k q Hq a t))
    (localSuccessorUpFace (νGpdPack p Y).2 k q Hq a t)).
Defined.

End RecursiveLocalReadout.

End Readout.

End CellComparisonOn.
