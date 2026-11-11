(** Indexed partial frames compared with a residual target. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Contractible Notation LeSProp FinitePrefix
  RewLemmas Funext Limit PathSquares HomotopyPullback.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Presheaf.Gpd Require Import Presentation Cone Model.
From Bonak.Equiv.Gpd Require Import Face Boundary PresheafOfνGpd PartialDiagram
  CellComparison.
Import GpdCone.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

Module IndexedMatchingEquivOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (Extraction: ExtractionSig A Core Faces).
Include CellComparisonOn A Core Faces Extraction.

Module PartialModel.
Export Partial.
Import A Faces.

Section SourceModel.
Context {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X).
Context (Q: νGpdPresentation arity).
Context (b: forall k, (partialLocalCellPresentation L).(G0) k -> Q.(G0) k).
Context (bFace: forall k q (Hq: q <= k) a x,
  b k ((partialLocalCellPresentation L).(GFace) k q Hq a x)
    = Q.(GFace) k q Hq a (b (S k) x)).

Definition Model: Type :=
  PartialDiagramModel (partialFramePresentation L) Q (partialLocalCellPresentation L)
    (fun k (x: stateLocalCell (partialState L k)) => x.1) b
    (fun k => stateLocalProjectionFace (partialState L k)) bFace.

End SourceModel.

Definition zeroModel {X: (νGpdAt 0).(prefix)} (L: νGpdFrom 0 X)
  (Q: νGpdPresentation arity)
  (b: forall k, (partialLocalCellPresentation L).(G0) k -> Q.(G0) k)
  (bFace: forall k q (Hq: q <= k) a x,
    b k ((partialLocalCellPresentation L).(GFace) k q Hq a x)
      = Q.(GFace) k q Hq a (b (S k) x))
  (c: forall k, Contr (Q.(G0) k)): Model L Q b bFace :=
  contractiblePartialDiagramModel (partialFramePresentation L) Q (partialLocalCellPresentation L)
    (fun k (x: stateLocalCell (partialState L k)) => x.1) b
    (fun k => stateLocalProjectionFace (partialState L k)) bFace
    (fun _ => (tt; fun x => hunit_ext tt x)) c.

End PartialModel.


Module Models.
Import A Faces.
Import Partial.

Section IndexedModel.
Context {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X).
Context (Q C: νGpdPresentation arity).
Context (boundary: forall k, C.(G0) k -> Q.(G0) k).
Context (boundaryFace: forall k q (Hq: q <= k) a t,
  Q.(GFace) k q Hq a (boundary (S k) t) = boundary k (C.(GFace) k q Hq a t)).

Local Abbreviation CellComparison :=
  (PresentationEquiv (partialLocalCellPresentation L) C).

Definition boundaryFor (e: CellComparison) k
  (x: (partialLocalCellPresentation L).(G0) k):
  Q.(G0) k :=
  boundary k (e.(presentationCell) k x).

Definition boundaryForFace (e: CellComparison) k q (Hq: q <= k) a x:
  boundaryFor e k ((partialLocalCellPresentation L).(GFace) k q Hq a x)
    = Q.(GFace) k q Hq a
        (boundaryFor e (S k) x) :=
  f_equal (boundary k) (e.(presentationFace) k q Hq a x)
    • eq_sym (boundaryFace k q Hq a (e.(presentationCell) (S k) x)).

Definition Model (e: CellComparison): Type :=
  PartialModel.Model L Q (boundaryFor e) (boundaryForFace e).

(** The attachment is normalized to the residual presentation. In this
    form its new coordinate is face zero, and all old coordinates shift. *)
Local Abbreviation StepCone := (coneObject Q C boundary).
Local Abbreviation stepConeFace := (coneFace Q C boundary boundaryFace).

Definition stepConeEquiv (e: CellComparison) (M: Model e) k:
  Equiv (stateFrame (stateUp (partialState L k))) (StepCone k) :=
  @Attach.frameConeStepEquiv p k (stateCohs (partialState L k)).(_depsCohs2).(_depsCohs)
    (Q.(G0) (S k))
    (Q.(G0) k)
    (C.(G0) k)
    (fun a => Q.(GFace) k 0 leR_O a)
    (boundary k)
    (M.(modelEquiv) (S k)) (M.(modelEquiv) k) (e.(presentationCell) k)
    (fun a w => eq_sym (M.(modelFace) k 0 leR_O a w))
    (M.(modelBoundary) k).

Lemma stepConePath (e: CellComparison) (M: Model e) k
  (d: stateFrame (stateUp (partialState L k))) a:
  ((stepConeEquiv e M k d).2 a).2 =
    eq_sym (M.(modelFace) k 0 leR_O a d.1)
      • M.(modelBoundary) k (νFace DepsCohsChainNil a d).
Proof. now apply Attach.frameConeStepPath. Defined.

Definition stepSourceCellFace k q (Hq: q <= k) a c
  (d: stateFrame (stateUp (partialState L (S k)))):
  stateLocalFace (partialState L k) q Hq a (νFace DepsCohsChainNil c d)
    = νFace DepsCohsChainNil c
        (stateRestrict (stateUp (partialState L k)) q Hq a d) :=
  @Attach.restrictionLayerFace p k (stateCohs (partialState L k)).(_depsCohs2)
    p k (stateCohs (partialState L k)).(_depsCohs2).(_depsCohs).(_deps)
    (stateCohs (partialState L k)).(_depsCohs2).(_depsCohs).(_extraDeps)
    ExtChainNil q Hq a c d.

Definition stepCellFace (e: CellComparison) k q (Hq: q <= k) a c
  (d: stateFrame (stateUp (partialState L (S k)))):
  e.(presentationCell) k
      (νFace DepsCohsChainNil c
        (stateRestrict (stateUp (partialState L k)) q Hq a d))
    = C.(GFace) k q Hq a
        (e.(presentationCell) (S k) (νFace DepsCohsChainNil c d)) :=
  eq_sym (f_equal (e.(presentationCell) k) (stepSourceCellFace k q Hq a c d))
    • e.(presentationFace) k q Hq a (νFace DepsCohsChainNil c d).

Lemma stepCellFaceCoh (e: CellComparison) k q (Hq: q <= k) r (Hr: r <= q) a b c
  (d: stateFrame (stateUp (partialState L (S (S k))))):
  (stepCellFace e k q Hq a c
      (stateRestrict (stateUp (partialState L (S k))) r (Hr ↕ ↑ Hq) b d)
    • f_equal (C.(GFace) k q Hq a)
        (stepCellFace e (S k) r (Hr ↕ ↑ Hq) b c d))
    • C.(GFaceCoh) k q Hq r Hr a b
        (e.(presentationCell) (S (S k))
          (Coh.attachedFace (partialState L (S (S k))) c d))
  = f_equal (fun w => e.(presentationCell) k
        (Coh.attachedFace (partialState L k) c w))
      (stateRestrictCoh (stateUp (partialState L k)) q Hq r Hr a b d)
    • (stepCellFace e k r (Hr ↕ Hq) b c
        (stateRestrict (stateUp (partialState L (S k))) (S q) (⇑ Hq) a d)
      • f_equal (C.(GFace) k r (Hr ↕ Hq) b)
          (stepCellFace e (S k) (S q) (⇑ Hq) a c d)).
Proof.
  unfold stepCellFace.
  rewrite <- 4 fEqualSym.
  exact (composeForwardFaceSquare
    (Coh.attachedFace (partialState L k) c)
    (Coh.attachedFace (partialState L (S k)) c)
    (Coh.attachedFace (partialState L (S (S k))) c)
    (e.(presentationCell) k) (e.(presentationCell) (S k))
    (e.(presentationCell) (S (S k)))
    (stateRestrict (stateUp (partialState L k)) q Hq a)
    (stateRestrict (stateUp (partialState L k)) r (Hr ↕ Hq) b)
    (stateRestrict (stateUp (partialState L (S k))) r (Hr ↕ ↑ Hq) b)
    (stateRestrict (stateUp (partialState L (S k))) (S q) (⇑ Hq) a)
    (stateLocalFace (partialState L k) q Hq a)
    (stateLocalFace (partialState L k) r (Hr ↕ Hq) b)
    (stateLocalFace (partialState L (S k)) r (Hr ↕ ↑ Hq) b)
    (stateLocalFace (partialState L (S k)) (S q) (⇑ Hq) a)
    (C.(GFace) k q Hq a) (C.(GFace) k r (Hr ↕ Hq) b)
    (C.(GFace) (S k) r (Hr ↕ ↑ Hq) b) (C.(GFace) (S k) (S q) (⇑ Hq) a)
    (Coh.attachedFaceNatural (partialState L k) q Hq a c)
    (Coh.attachedFaceNatural (partialState L k) r (Hr ↕ Hq) b c)
    (Coh.attachedFaceNatural (partialState L (S k)) r (Hr ↕ ↑ Hq) b c)
    (Coh.attachedFaceNatural (partialState L (S k)) (S q) (⇑ Hq) a c)
    (e.(presentationFace) k q Hq a) (e.(presentationFace) k r (Hr ↕ Hq) b)
    (e.(presentationFace) (S k) r (Hr ↕ ↑ Hq) b)
    (e.(presentationFace) (S k) (S q) (⇑ Hq) a)
    (stateRestrictCoh (stateUp (partialState L k)) q Hq r Hr a b)
    (stateLocalCoh (partialState L k) q Hq r Hr a b)
    (C.(GFaceCoh) k q Hq r Hr a b) d
    (eq_sym (Coh.attachedFaceCoh p k (partialState L k) q Hq r Hr a b c d))
    (e.(presentationFaceCoh) k q Hq r Hr a b
      (Coh.attachedFace (partialState L (S (S k))) c d))).
Defined.



Lemma stepBoundaryNaturality (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) a c
  (d: stateFrame (stateUp (partialState L (S k)))):
  f_equal (M.(modelEquiv) k)
      (stateRestrictCoh (partialState L k) q Hq 0 leR_O a c d.1)
    • M.(modelBoundary) k
        (νFace DepsCohsChainNil c
          (stateRestrict (stateUp (partialState L k)) q Hq a d))
  = M.(modelBoundary) k
      (stateLocalFace (partialState L k) q Hq a (νFace DepsCohsChainNil c d))
    • f_equal (boundary k)
        (f_equal (e.(presentationCell) k) (stepSourceCellFace k q Hq a c d)).
Proof.
  pose proof (homotopyNat
    (fun t: stateLocalCell (partialState L k) => M.(modelEquiv) k t.1)
    (boundaryFor e k) (M.(modelBoundary) k)
    (stepSourceCellFace k q Hq a c d)) as H.
  rewrite <- (f_equal_compose (fun t: stateLocalCell (partialState L k) => t.1)
    (M.(modelEquiv) k) (stepSourceCellFace k q Hq a c d)) in H.
  unfold stepSourceCellFace in H.
  pose proof (@Attach.restrictionLayerFaceBase p k
    (stateCohs (partialState L k)).(_depsCohs2) q Hq a c d) as base.
  unfold projT1_eq in base. rewrite base in H.
  unfold boundaryFor in H.
  rewrite <- (f_equal_compose (e.(presentationCell) k)
    (boundary k)) in H.
  now exact H.
Defined.

Lemma stepConeFaceSquare (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) a c
  (d: stateFrame (stateUp (partialState L (S k)))):
  f_equal (Q.(GFace) k 0 leR_O c)
      (M.(modelFace) (S k) (S q) (⇑ Hq) a d.1)
    • ((stepConeFace k q Hq a (stepConeEquiv e M (S k) d)).2 c).2
  = ((stepConeEquiv e M k
        (stateRestrict (stateUp (partialState L k)) q Hq a d)).2 c).2
    • f_equal (boundary k) (stepCellFace e k q Hq a c d).
Proof.
  cbn [stepConeFace projT1 projT2].
  rewrite (stepConePath e M (S k) d c),
    (stepConePath e M k (stateRestrict (stateUp (partialState L k)) q Hq a d) c).
  unfold stepCellFace.
  rewrite 2 eq_trans_map_distr, 2 fEqualSym.
  rewrite <- (eq_sym_involutive (boundaryFace k q Hq a
    (e.(presentationCell) (S k) (νFace DepsCohsChainNil c d)))) at 1.
  refine (Attach.coneFaceAlgebra _ _ _ _ _ _ _ _ _ _
    (eq_sym (boundaryFace k q Hq a
      (e.(presentationCell) (S k) (νFace DepsCohsChainNil c d)))) _ _ _ _).
  - now exact (M.(modelFaceCoh) k q Hq 0 leR_O a c d.1).
  - pose proof (M.(modelBoundaryFace) k q Hq a (νFace DepsCohsChainNil c d)) as H.
    cbn [stateLocalProjectionFace f_equal] in H.
    rewrite eq_trans_refl_l in H. now exact H.
  - now apply stepBoundaryNaturality.
Defined.

Definition stepConeNaturality (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) a
  (d: stateFrame (stateUp (partialState L (S k)))):
  stepConeEquiv e M k (stateRestrict (stateUp (partialState L k)) q Hq a d)
    = stepConeFace k q Hq a (stepConeEquiv e M (S k) d) :=
  attachmentEq
    (fun c => Q.(GFace) k 0 leR_O c)
    (boundary k)
    (stepConeEquiv e M k (stateRestrict (stateUp (partialState L k)) q Hq a d))
    (stepConeFace k q Hq a (stepConeEquiv e M (S k) d))
    (M.(modelFace) (S k) (S q) (⇑ Hq) a d.1)
    (fun c => stepCellFace e k q Hq a c d)
    (fun c => stepConeFaceSquare e M k q Hq a c d).

Lemma stepConeNaturalityBase (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) a
  (d: stateFrame (stateUp (partialState L (S k)))):
  f_equal (fun z: StepCone k => z.1) (stepConeNaturality e M k q Hq a d) =
    M.(modelFace) (S k) (S q) (⇑ Hq) a d.1.
Proof. now apply attachmentEqBase. Defined.

Lemma stepConeNaturalityCell (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) a c
  (d: stateFrame (stateUp (partialState L (S k)))):
  f_equal (fun z: StepCone k => (z.2 c).1)
      (stepConeNaturality e M k q Hq a d)
    = stepCellFace e k q Hq a c d.
Proof.
  now exact (attachmentEqTop
    (fun c => Q.(GFace) k 0 leR_O c) (boundary k)
    (stepConeEquiv e M k (stateRestrict (stateUp (partialState L k)) q Hq a d))
    (stepConeFace k q Hq a (stepConeEquiv e M (S k) d))
    (M.(modelFace) (S k) (S q) (⇑ Hq) a d.1)
    (fun c => stepCellFace e k q Hq a c d)
    (fun c => stepConeFaceSquare e M k q Hq a c d) c).
Defined.

Definition stepConeBoundary k
  (t: C.(G0) (S k)): StepCone k :=
  (boundary (S k) t;
    fun a => (C.(GFace) k 0 leR_O a t;
      boundaryFace k 0 leR_O a t)).

(** Reassociation retains the whole cell while moving its last frame
    layer into the painting of the preceding partial frame. *)
Definition stepCellBelow k (t: stateLocalCell (stateUp (partialState L k))):
  stateLocalCell (partialState L (S k)) :=
  Cells.localCellDrop (stateUp (partialState L k)) t.

Definition stepBoundaryCell (e: CellComparison) k a
  (t: stateLocalCell (stateUp (partialState L k))):
  e.(presentationCell) k (νFace DepsCohsChainNil a t.1) =
    C.(GFace) k 0 leR_O a
      (e.(presentationCell) (S k) (stepCellBelow k t)) :=
  e.(presentationFace) k 0 leR_O a (stepCellBelow k t).

Lemma stepConeBoundarySquare (e: CellComparison) (M: Model e) k a
  (t: stateLocalCell (stateUp (partialState L k))):
  f_equal (Q.(GFace) k 0 leR_O a)
      (M.(modelBoundary) (S k) (stepCellBelow k t))
    • ((stepConeBoundary k (e.(presentationCell) (S k) (stepCellBelow k t))).2 a).2
  = ((stepConeEquiv e M k t.1).2 a).2
    • f_equal (boundary k) (stepBoundaryCell e k a t).
Proof.
  cbn [stepConeBoundary projT1 projT2]. rewrite (stepConePath e M k t.1 a).
  apply Attach.coneBoundaryAlgebra.
  pose proof (M.(modelBoundaryFace) k 0 leR_O a (stepCellBelow k t)) as H.
  cbn [stateLocalProjectionFace f_equal] in H.
  rewrite eq_trans_refl_l in H. now exact H.
Defined.

Definition stepConeBoundaryPath (e: CellComparison) (M: Model e) k
  (t: stateLocalCell (stateUp (partialState L k))):
  stepConeEquiv e M k t.1 =
    stepConeBoundary k (e.(presentationCell) (S k) (stepCellBelow k t)) :=
  attachmentEq
    (fun a => Q.(GFace) k 0 leR_O a)
    (boundary k)
    (stepConeEquiv e M k t.1)
    (stepConeBoundary k (e.(presentationCell) (S k) (stepCellBelow k t)))
    (M.(modelBoundary) (S k) (stepCellBelow k t))
    (fun a => stepBoundaryCell e k a t)
    (fun a => stepConeBoundarySquare e M k a t).

(** At a unit-filled position, projection to the indexed partial frame is
    an equivalence. The model's boundary square then proves the same for
    the categorical matching map. *)
Definition targetBoundaryEquiv (e: CellComparison) (M: Model e) k
  (projection: Equiv ((partialLocalCellPresentation L).(G0) k)
    ((partialFramePresentation L).(G0) k))
  (projectionRule: forall x, projection x = x.1):
  Equiv (C.(G0) k) (Q.(G0) k) :=
  equivOfSquare (e.(presentationCell) k) projection (M.(modelEquiv) k)
    (boundary k)
    (fun x => f_equal (M.(modelEquiv) k) (projectionRule x) • M.(modelBoundary) k x).


(** Exchange and boundary coherence make the attachment a model of the
    next indexed frame layer. *)
Context (boundaryCoh: forall k q (Hq: q <= k) r (Hr: r <= q) a c t,
  (f_equal (Q.(GFace) k q Hq a) (boundaryFace (S k) r (Hr ↕ ↑ Hq) c t)
    • boundaryFace k q Hq a (C.(GFace) (S k) r (Hr ↕ ↑ Hq) c t))
    • f_equal (boundary k) (C.(GFaceCoh) k q Hq r Hr a c t)
  = Q.(GFaceCoh) k q Hq r Hr a c (boundary (S (S k)) t)
    • (f_equal (Q.(GFace) k r (Hr ↕ Hq) c)
        (boundaryFace (S k) (S q) (⇑ Hq) a t)
      • boundaryFace k r (Hr ↕ Hq) c (C.(GFace) (S k) (S q) (⇑ Hq) a t))).

Lemma stepConeEquivBaseAp (e: CellComparison) (M: Model e) k
  {d d': stateFrame (stateUp (partialState L k))} (h: d = d'):
  f_equal (fun z: StepCone k => z.1) (f_equal (stepConeEquiv e M k) h)
    = f_equal (M.(modelEquiv) (S k)) (projT1_eq h).
Proof. now destruct h. Defined.

Lemma stepConeEquivCellAp (e: CellComparison) (M: Model e) k
  {d d': stateFrame (stateUp (partialState L k))} (h: d = d') c:
  f_equal (fun z: StepCone k => (z.2 c).1) (f_equal (stepConeEquiv e M k) h)
    = f_equal (fun w => e.(presentationCell) k (Coh.attachedFace (partialState L k) c w)) h.
Proof. now destruct h. Defined.

Lemma stepConeFaceCoh (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) r (Hr: r <= q) a b
  (d: stateFrame (stateUp (partialState L (S (S k))))):
  (stepConeNaturality e M k q Hq a
      (stateRestrict (stateUp (partialState L (S k))) r (Hr ↕ ↑ Hq) b d)
    • f_equal (stepConeFace k q Hq a)
        (stepConeNaturality e M (S k) r (Hr ↕ ↑ Hq) b d))
    • coneExchange Q C boundary boundaryFace boundaryCoh k q Hq r Hr a b
        (stepConeEquiv e M (S (S k)) d)
  = f_equal (stepConeEquiv e M k)
      (stateRestrictCoh (stateUp (partialState L k)) q Hq r Hr a b d)
    • (stepConeNaturality e M k r (Hr ↕ Hq) b
        (stateRestrict (stateUp (partialState L (S k))) (S q) (⇑ Hq) a d)
      • f_equal (stepConeFace k r (Hr ↕ Hq) b)
          (stepConeNaturality e M (S k) (S q) (⇑ Hq) a d)).
Proof.
  apply (attachmentPathExt (fun c => Q.(GFace) k 0 leR_O c) (boundary k)).
  - unfold projT1_eq at 1 2. rewrite 4 eq_trans_map_distr.
    rewrite 2 coneFaceBaseAp, stepConeEquivBaseAp,
      4 stepConeNaturalityBase,
      (coneExchangeBase Q C boundary boundaryFace boundaryCoh k q Hq r Hr a b
        (stepConeEquiv e M (S (S k)) d)),
      (Coh.stateUpExchangeBase (partialState L k) q Hq r Hr a b d).
    now exact (M.(modelFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b d.1).
  - intro c. rewrite 4 eq_trans_map_distr.
    rewrite 2 coneFaceCellAp, stepConeEquivCellAp,
      (stepConeNaturalityCell e M k q Hq a c
        (stateRestrict (stateUp (partialState L (S k))) r (Hr ↕ ↑ Hq) b d)),
      (stepConeNaturalityCell e M (S k) r (Hr ↕ ↑ Hq) b c d),
      (stepConeNaturalityCell e M k r (Hr ↕ Hq) b c
        (stateRestrict (stateUp (partialState L (S k))) (S q) (⇑ Hq) a d)),
      (stepConeNaturalityCell e M (S k) (S q) (⇑ Hq) a c d),
      (coneExchangeCell Q C boundary boundaryFace boundaryCoh k q Hq r Hr a b
        (stepConeEquiv e M (S (S k)) d) c).
    now apply stepCellFaceCoh.
Defined.

Lemma stepConeBoundaryPathBase (e: CellComparison) (M: Model e) k
  (t: stateLocalCell (stateUp (partialState L k))):
  f_equal (fun z: StepCone k => z.1) (stepConeBoundaryPath e M k t)
    = M.(modelBoundary) (S k) (stepCellBelow k t).
Proof. now apply attachmentEqBase. Defined.

Lemma stepConeBoundaryPathCell (e: CellComparison) (M: Model e) k
  (t: stateLocalCell (stateUp (partialState L k))) c:
  f_equal (fun z: StepCone k => (z.2 c).1) (stepConeBoundaryPath e M k t)
    = stepBoundaryCell e k c t.
Proof.
  now exact (attachmentEqTop
    (fun a => Q.(GFace) k 0 leR_O a) (boundary k)
    (stepConeEquiv e M k t.1)
    (stepConeBoundary k (e.(presentationCell) (S k) (stepCellBelow k t)))
    (M.(modelBoundary) (S k) (stepCellBelow k t))
    (fun a => stepBoundaryCell e k a t)
    (fun a => stepConeBoundarySquare e M k a t) c).
Defined.

Local Lemma boundaryCellAlgebra {T: Type} {x0 x1 x2 x3 x4 x5: T}
  (a: x0 = x1) (b: x0 = x2) (c: x2 = x3) (d: x3 = x4)
  (e: x1 = x5) (f: x5 = x4)
  (square: (b • c) • d = a • (e • f)):
  (eq_sym a • b) • c = e • (f • eq_sym d).
Proof.
  destruct a, b, c, e, f; cbn in square |- *.
  rewrite eq_trans_refl_l in square. now rewrite square.
Defined.

Definition stepConeBoundaryFace (e: CellComparison) k q (Hq: q <= k) a
  (t: stateLocalCell (stateUp (partialState L (S k)))):
  stepConeBoundary k (e.(presentationCell) (S k)
      (stepCellBelow k (stateLocalFace (stateUp (partialState L k)) q Hq a t)))
  = stepConeFace k q Hq a
      (stepConeBoundary (S k) (e.(presentationCell) (S (S k)) (stepCellBelow (S k) t))) :=
  f_equal (stepConeBoundary k)
      (e.(presentationFace) (S k) (S q) (⇑ Hq) a (stepCellBelow (S k) t))
    • coneBoundaryFace Q C boundary boundaryFace boundaryCoh k q Hq a
        (e.(presentationCell) (S (S k)) (stepCellBelow (S k) t)).

Lemma stepConeBoundaryModification (e: CellComparison) (M: Model e)
  k q (Hq: q <= k) a
  (t: stateLocalCell (stateUp (partialState L (S k)))):
  stepConeNaturality e M k q Hq a t.1
    • f_equal (stepConeFace k q Hq a) (stepConeBoundaryPath e M (S k) t)
  = stepConeBoundaryPath e M k (stateLocalFace (stateUp (partialState L k)) q Hq a t)
    • stepConeBoundaryFace e k q Hq a t.
Proof.
  apply (attachmentPathExt (fun c => Q.(GFace) k 0 leR_O c) (boundary k)).
  - unfold projT1_eq at 1 2. unfold stepConeBoundaryFace.
    rewrite 3 eq_trans_map_distr.
    rewrite coneFaceBaseAp, coneBoundaryBaseAp,
      2 stepConeBoundaryPathBase, stepConeNaturalityBase,
      (coneBoundaryFaceBase Q C boundary boundaryFace boundaryCoh k q Hq a
        (e.(presentationCell) (S (S k)) (stepCellBelow (S k) t))).
    pose proof (M.(modelBoundaryFace) (S k) (S q) (⇑ Hq) a
      (stepCellBelow (S k) t)) as h.
    cbn [stateLocalProjectionFace f_equal] in h.
    rewrite eq_trans_refl_l in h. now exact h.
  - intro c. unfold stepConeBoundaryFace.
    rewrite 3 eq_trans_map_distr.
    rewrite coneFaceCellAp, coneBoundaryCellAp,
      (stepConeBoundaryPathCell e M (S k) t c),
      (stepConeBoundaryPathCell e M k
        (stateLocalFace (stateUp (partialState L k)) q Hq a t) c),
      (stepConeNaturalityCell e M k q Hq a c t.1),
      (coneBoundaryFaceCell Q C boundary boundaryFace boundaryCoh k q Hq a
        (e.(presentationCell) (S (S k)) (stepCellBelow (S k) t)) c).
    unfold stepBoundaryCell, stepCellFace.
    apply boundaryCellAlgebra.
    pose proof (Attach.restrictionLayerFaceCoh (stateCohs (partialState L k))
      q Hq a c t.1.1 (t.1.2; t.2)) as indexedPath.
    change (stateLocalCoh (partialState L k) q Hq 0 leR_O a c
      (stepCellBelow (S k) t) = stepSourceCellFace k q Hq a c t.1) in indexedPath.
    rewrite <- indexedPath.
    now exact (e.(presentationFaceCoh) k q Hq 0 leR_O a c (stepCellBelow (S k) t)).
Defined.

Definition rawUpFramePresentation: νGpdPresentation arity := {|
  G0 k := stateFrame (stateUp (partialState L k));
  GFace k q Hq a := stateRestrict (stateUp (partialState L k)) q Hq a;
  GFaceCoh k q Hq r Hr a b := stateRestrictCoh (stateUp (partialState L k)) q Hq r Hr a b;
  GFaceCoh2 k q Hq r Hr s Hs a b c :=
    stateRestrictHex (stateUp (partialState L k)) q Hq r Hr s Hs a b c;
|}.

Definition sourceConeModel (e: CellComparison) (M: Model e):
  PartialDiagramModel rawUpFramePresentation
    (conePresentation Q C boundary boundaryFace boundaryCoh) (Readout.rawUpLocalPresentation L)
    (fun k t => t.1)
    (fun k t => stepConeBoundary k (e.(presentationCell) (S k) (stepCellBelow k t)))
    (fun k q Hq a t => eq_refl) (stepConeBoundaryFace e).
Proof.
  refine (@Build_PartialDiagramModel arity rawUpFramePresentation
    (conePresentation Q C boundary boundaryFace boundaryCoh) (Readout.rawUpLocalPresentation L)
    (fun k t => t.1)
    (fun k t => stepConeBoundary k (e.(presentationCell) (S k) (stepCellBelow k t)))
    (fun k q Hq a t => eq_refl) (stepConeBoundaryFace e)
    (stepConeEquiv e M) (stepConeNaturality e M)
    (stepConeFaceCoh e M) (stepConeBoundaryPath e M) _).
  intros k q Hq a t. cbn [f_equal]. rewrite eq_trans_refl_l.
  now apply stepConeBoundaryModification.
Defined.

End IndexedModel.

End Models.

(** State transport relates the raw attachment to the next indexed
    position and preserves projection to each partial frame. *)
Module Frames.
Import A Readout.

Definition backwardStateFrame {p k} {z z': PartialState p k} (h: z = z'):
  Equiv (stateFrame z') (stateFrame z) :=
  rewEquiv (fun z => stateFrame z) (eq_sym h).

Definition backwardStateFrameFace {p k} {z z': PartialState p k} (h: z = z')
  q (Hq: q <= k) a (d: stateFrame (stateNext z')):
  backwardStateFrame h (stateRestrict z' q Hq a d) =
    stateRestrict z q Hq a (backwardStateFrame (f_equal (@stateNext p k) h) d).
Proof. now destruct h. Defined.

Lemma backwardStateFrameCoh {p k} {z z': PartialState p k} (h: z = z')
  q (Hq: q <= k) r (Hr: r <= q) a b
  (d: stateFrame (stateNext (stateNext z'))):
  (backwardStateFrameFace h q Hq a (stateRestrict (stateNext z') r (Hr ↕ ↑ Hq) b d)
    • f_equal (stateRestrict z q Hq a)
        (backwardStateFrameFace (f_equal (@stateNext p k) h) r (Hr ↕ ↑ Hq) b d))
    • stateRestrictCoh z q Hq r Hr a b
        (backwardStateFrame (f_equal (@stateNext p (S k)) (f_equal (@stateNext p k) h)) d)
  = f_equal (backwardStateFrame h) (stateRestrictCoh z' q Hq r Hr a b d)
    • (backwardStateFrameFace h r (Hr ↕ Hq) b
        (stateRestrict (stateNext z') (S q) (⇑ Hq) a d)
      • f_equal (stateRestrict z r (Hr ↕ Hq) b)
        (backwardStateFrameFace (f_equal (@stateNext p k) h) (S q) (⇑ Hq) a d)).
Proof.
  destruct h.
  cbn [backwardStateFrameFace backwardStateFrame rewEquiv qinvEquiv eqvFun f_equal].
  rewrite f_equal_id, eq_trans_refl_l, eq_trans_refl_r. now reflexivity.
Defined.

Definition backwardStateProjection {p k} {z z': PartialState p k} (h: z = z')
  (t: stateLocalCell z'):
  backwardStateFrame h t.1 = (backwardStateCell h t).1.
Proof. now destruct h. Defined.

Lemma backwardStateProjectionFace {p k} {z z': PartialState p k} (h: z = z')
  q (Hq: q <= k) a (t: stateLocalCell (stateNext z')):
  backwardStateFrameFace h q Hq a t.1
    • f_equal (stateRestrict z q Hq a)
        (backwardStateProjection (f_equal (@stateNext p k) h) t)
  = backwardStateProjection h (stateLocalFace z' q Hq a t)
    • (f_equal (fun u: stateLocalCell z => u.1)
        (eq_sym (backwardStateCellFace h q Hq a t)) • eq_refl).
Proof. now destruct h. Defined.

Section Reindex.
Context {p} {X: (νGpdAt p).(prefix)} (L: νGpdFrom p X).

Definition frameReindexModel:
  PartialDiagramModel (Models.rawUpFramePresentation L) (partialFramePresentation (next L))
    (rawUpLocalPresentation L) (fun k t => t.1)
    (fun k t => (rawUpToNextEquiv L k t).1)
    (fun k q Hq a t => eq_refl)
    (fun k q Hq a t =>
      f_equal (fun t: (partialLocalCellPresentation (next L)).(G0) k => t.1)
        (eq_sym (rawUpToNextFace L k q Hq a t)) • eq_refl).
Proof.
  refine (@Build_PartialDiagramModel arity (Models.rawUpFramePresentation L)
    (partialFramePresentation (next L)) (rawUpLocalPresentation L)
    (fun k t => t.1) (fun k t => (rawUpToNextEquiv L k t).1)
    (fun k q Hq a t => eq_refl)
    (fun k q Hq a t =>
      f_equal (fun t: (partialLocalCellPresentation (next L)).(G0) k => t.1)
        (eq_sym (rawUpToNextFace L k q Hq a t)) • eq_refl)
    (fun k => backwardStateFrame (partialStateUp L k))
    (fun k q Hq a => backwardStateFrameFace (partialStateUp L k) q Hq a)
    (fun k q Hq r Hr a b =>
      backwardStateFrameCoh (partialStateUp L k) q Hq r Hr a b)
    (fun k => backwardStateProjection (partialStateUp L k)) _).
  intros k q Hq a t. cbn [f_equal]. rewrite eq_trans_refl_l.
  now exact (backwardStateProjectionFace (partialStateUp L k) q Hq a t).
Defined.
End Reindex.
End Frames.

(** The recursive indexed cell readout retains its selected face paths
    while passing from a raw attachment to the next indexed position. *)
Module Actions.
Import A Extraction Readout GpdCone.

Definition actionOfComparison {P Q: νGpdPresentation arity}
  (e: FaceComparison P.(G0) Q.(G0) P.(GFace) Q.(GFace) P.(GFaceCoh) Q.(GFaceCoh)):
  CellActionData P Q :=
  (fun k x => e.(comparisonCell) k x; e.(comparisonFace)).

Section Readouts.
Context (Y: νGpds) (T: ResidualTarget (g Y)).
Local Definition cells p := T.(targetCells) p.
Local Definition readout p := buildLocalReadouts Y T p.

Definition indexedReadoutAction p:
  CellActionData (partialLocalCellPresentation (νGpdPack p Y).2) (cells p) :=
  @actionOfComparison (partialLocalCellPresentation (νGpdPack p Y).2)
    (cells p) (readout p).

Definition indexedReindexAction p:
  CellActionData (rawUpLocalPresentation (νGpdPack p Y).2)
    (partialLocalCellPresentation (νGpdPack (S p) Y).2) :=
  @actionOfComparison (rawUpLocalPresentation (νGpdPack p Y).2)
    (partialLocalCellPresentation (νGpdPack (S p) Y).2)
    (rawUpToNextComparison (νGpdPack p Y).2).

Definition indexedShiftAction p:
  CellActionData (cells (S p)) (residualShift (cells p)) :=
  targetShiftAction T p.

Definition indexedOldAction p:
  CellActionData (rawUpLocalPresentation (νGpdPack p Y).2)
    (residualShift (cells p)) :=
  (fun k t => (readout p).(comparisonCell) (S k)
      (localCellDrop (stateUp (partialState (νGpdPack p Y).2 k)) t);
    fun k q Hq a t => (readout p).(comparisonFace) (S k) (S q) (⇑ Hq) a
      (localCellDrop (stateUp (partialState (νGpdPack p Y).2 (S k))) t)).

Lemma oldActionFace p k q (Hq: q <= k) a
  (t: (rawUpLocalPresentation (νGpdPack p Y).2).(G0) (S k)):
  (oldUpReadout Y T p).(comparisonFace) k q Hq a t =
    (indexedOldAction p).2 k q Hq a t.
Proof.
  change ((readout p).(comparisonFace) (S k) (S q) (⇑ Hq) a
      (localCellDrop (stateUp (partialState (νGpdPack p Y).2 (S k))) t)
    • eq_refl = (readout p).(comparisonFace) (S k) (S q) (⇑ Hq) a
      (localCellDrop (stateUp (partialState (νGpdPack p Y).2 (S k))) t)).
  now apply eq_trans_refl_r.
Defined.

Definition indexedReadoutCompatibility p:
  indexedOldAction p = composeCellAction (indexedReindexAction p)
    (composeCellAction (indexedReadoutAction (S p)) (indexedShiftAction p)).
Proof.
  apply (cellActionDataEq
    (C := rawUpLocalPresentation (νGpdPack p Y).2)
    (D := residualShift (cells p))
    (cell1 := (indexedOldAction p).1)
    (cell2 := (composeCellAction (indexedReindexAction p)
      (composeCellAction (indexedReadoutAction (S p)) (indexedShiftAction p))).1)
    (face1 := (indexedOldAction p).2)
    (face2 := (composeCellAction (indexedReindexAction p)
      (composeCellAction (indexedReadoutAction (S p)) (indexedShiftAction p))).2)
    (localReadoutUp Y T p)).
  intros k q Hq a t.
  pose proof (localReadoutUpFace Y T p k q Hq a t) as h.
  rewrite (oldActionFace p k q Hq a t) in h.
  now exact h.
Defined.

Definition indexedFrameData p:
  ModelTargetData (partialLocalCellPresentation (νGpdPack p Y).2) :=
  (partialFramePresentation (νGpdPack p Y).2;
    (fun k t => t.1; fun k q Hq a t => eq_refl)).

Definition indexedRawFrameData p:
  ModelTargetData (rawUpLocalPresentation (νGpdPack p Y).2) :=
  (Models.rawUpFramePresentation (νGpdPack p Y).2;
    (fun k t => t.1; fun k q Hq a t => eq_refl)).

Definition indexedFrameReindexEquality p:
  indexedRawFrameData p =
    precomposeCellAction (indexedReindexAction p) (indexedFrameData (S p)) :=
  modelTargetEquality (Frames.frameReindexModel (νGpdPack p Y).2).

End Readouts.
End Actions.

(** Indexed partial frames compared with a residual target. *)
Module Comparison.
Import A Extraction Readout GpdCone.

(** The empty level is handled with an abstract target so that its
    boundary does not enter the contractibility proof. *)
Definition emptyFrameEquality {X: (νGpdAt 0).(prefix)} (L: νGpdFrom 0 X)
  (target: ModelTargetData (partialLocalCellPresentation L))
  (contractible: forall k, Contr (target.1.(G0) k)):
  ((partialFramePresentation L;
    (fun k t => t.1; fun k q Hq a t => eq_refl)):
      ModelTargetData (partialLocalCellPresentation L)) = target :=
  modelTargetEquality
    (PartialModel.zeroModel L target.1 target.2.1 target.2.2 contractible).

Section Matching.
Context (Y: νGpds) (T: ResidualTarget (g Y)).

Definition canonicalCellComparison p:
  PresentationEquiv (partialLocalCellPresentation (νGpdPack p Y).2)
    (T.(targetCells) p) :=
  presentationOfComparison (buildLocalReadouts Y T p).

Definition TargetModel p: Type :=
  Models.Model (νGpdPack p Y).2 (T.(targetMatching) p) (T.(targetCells) p)
    (T.(targetBoundary) p) (T.(targetBoundaryNatural) p)
    (canonicalCellComparison p).

Definition readoutData p :=
  precomposeCellAction (Actions.indexedReadoutAction Y T p) (targetData T p).

(** Fieldwise reconstruction limits conversion to the maps and chosen
    paths needed for the comparison. *)
Definition modelFromEquality p
  (h: Actions.indexedFrameData Y p = readoutData p):
  TargetModel p.
Proof.
  let source := constr:(Actions.indexedFrameData Y p) in
  let target := constr:(readoutData p) in
  let t := type of source in
  lazymatch t with
  | @ModelTargetData ?aa ?cc =>
    pose proof (@modelOfTargetEquality aa source.1 target.1 cc
      source.2.1 target.2.1 source.2.2 target.2.2 h) as m
  end.
  cbv beta delta [TargetModel Models.Model PartialModel.Model].
  unshelve refine {| modelEquiv := _; modelFace := _; modelFaceCoh := _;
    modelBoundary := _; modelBoundaryFace := _ |}.
  - intro n. now exact (m.(modelEquiv) n).
  - intros n q Hq a x. now exact (m.(modelFace) n q Hq a x).
  - intros n x. now exact (m.(modelBoundary) n x).
  - intros n q Hq r Hr a b x. now exact (m.(modelFaceCoh) n q Hq r Hr a b x).
  - intros n q Hq a x. now exact (m.(modelBoundaryFace) n q Hq a x).
Defined.

Definition sourceStepEquality p
  (M: TargetModel p):
  Actions.indexedRawFrameData Y p =
    precomposeCellAction (Actions.indexedOldAction Y T p) (targetCone T p) :=
  modelTargetEquality
    (Models.sourceConeModel (νGpdPack p Y).2
      (T.(targetMatching) p) (T.(targetCells) p) (T.(targetBoundary) p)
      (T.(targetBoundaryNatural) p) (T.(targetBoundaryCoh) p)
      (canonicalCellComparison p) M).

Definition canonicalZeroEquality:
  Actions.indexedFrameData Y 0 = readoutData 0 :=
  emptyFrameEquality Y (readoutData 0) (fun k => T.(targetMatchingZero) k).

Fixpoint indexedMatchingEquality (p: nat) {struct p}:
  Actions.indexedFrameData Y p = readoutData p.
Proof.
  destruct p as [|p].
  - now exact canonicalZeroEquality.
  - refine (assembleAugmentedStep
      (Actions.indexedReindexAction Y p)
      (fun k => (rawUpToNextEquiv (νGpdPack p Y).2 k).(eqvIsEquiv))
      (Actions.indexedReadoutAction Y T (S p))
      (Actions.indexedShiftAction Y T p)
      (Actions.indexedOldAction Y T p)
      (Actions.indexedRawFrameData Y p) (Actions.indexedFrameData Y (S p))
      (targetData T (S p)) (targetCone T p)
      (Actions.indexedFrameReindexEquality Y p) _ (targetSplitEquality T p)
      (Actions.indexedReadoutCompatibility Y T p)).
    now exact (sourceStepEquality p (modelFromEquality p (indexedMatchingEquality p))).
Defined.

Definition indexedModel p:
  TargetModel p :=
  modelFromEquality p (indexedMatchingEquality p).

(** Where projection to the partial frame at residual position [0] is an
    equivalence, the boundary map of the target is one as well. *)
Definition indexedTargetComplete p
  (projection: Equiv ((partialLocalCellPresentation (νGpdPack p Y).2).(G0) 0)
    ((partialFramePresentation (νGpdPack p Y).2).(G0) 0))
  (projectionRule: forall x, projection x = x.1): T.(targetComplete) p :=
  T.(targetCompleteOf) p
    (Models.targetBoundaryEquiv (νGpdPack p Y).2 (T.(targetMatching) p)
      (T.(targetCells) p) (T.(targetBoundary) p) (T.(targetBoundaryNatural) p)
      (canonicalCellComparison p) (indexedModel p) 0 projection projectionRule)
    (fun x => eq_refl).

End Matching.
End Comparison.

End IndexedMatchingEquivOn.
