(** Indexed ν-sets with degeneracies are matching sequences of diagrams on
    the ν-shape category. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet Equiv Notation FinitePrefix HSetFamily
  Univalence Contractible SequentialLimit TelescopeLimit.
From Bonak.νSet Require Import Layer νDgnSet νSet.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.
From Bonak.Presheaf.Dgn Require Import Generators νShape.
From Bonak.Reedy.Dgn Require Import Reedy Matching Extension.
From Bonak.Equiv Require Import Boundary Matching.
From Bonak.Equiv.Dgn Require Import Layer.
From Bonak.Reedy Require Reedy.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

(** Indexed frames classify the full lower boundaries of diagrams with
    degeneracies. Face-word values determine the remaining boundary values. *)

Module SemiReedy := Bonak.Reedy.Reedy.

Module DgnMatchingOn (A: LayerSig) (S: νDgnSetSig A)
  (N: IndexedMatchingSig A S.νSet).
Import A.
Module Export DgnSet := S.
Module Export Indexed := N.

Definition zeroFrameMatchingEquiv (X: DgnPrefix 0) (D: Diagram arity 0):
  Equiv (νFrame X.1) (MatchingObject arity D).
Proof.
  refine (qinvEquiv (fun _ => (fun i: Index 0 => match i with end;
    fun i: Index 0 => match i with end)) (fun _ => tt) _ _).
  - now intros [].
  - intro b. apply matchingExt. now intros [].
Defined.

Section First.
Context (X: DgnPrefix 1) (D: Diagram arity 1).
Context (upper: Equiv (prefixCell X.1) (cells D None)).
Definition firstWordMatchingEquiv:
  Equiv (νFrame X.1) (SemiReedy.MatchingObject arity (faceDiagram arity D)) :=
  zeroIndexedMatchingEquiv (prefixDepsCohs X.1) (faceDiagram arity D) upper.

Definition firstFrameMatchingEquiv:
  Equiv (νFrame X.1) (MatchingObject arity D) :=
  compEquiv firstWordMatchingEquiv (symEquiv (matchingEquivFace arity D)).

Lemma firstFrameMatchingFace d i a:
  (firstFrameMatchingEquiv d).1 None (shapeFace (depthFaceWord arity 0 i a))
    = upper (faceAtDepth (prefixDepsCohs X.1) (depth i) a d).
Proof.
  change ((matchingExtend arity D (firstWordMatchingEquiv d)).1 None
    (shapeFace (depthFaceWord arity 0 i a))
    = upper (faceAtDepth (prefixDepsCohs X.1) (depth i) a d)).
  rewrite matchingExtendFace.
  now exact (zeroIndexedMatchingFace (prefixDepsCohs X.1) (faceDiagram arity D) upper d i a).
Qed.
End First.

Section Higher.
Context {n} (X: DgnPrefix n.+2) (D: Diagram arity n.+2).
Context (upper: Equiv (prefixCell X.1) (cells D None)).
Context (lower: Equiv (prefixCell X.1.1) (cells D (Some None))).
Context (compatible: forall (i: FaceDepth n) a (x: prefixCell X.1),
  lower (faceAtDepth (prefixDepsCohs X.1.1) (depth i) a x.1) =
    act D (i := Some None) (j := None)
      (shapeFace (depthFaceWord arity n i a)) (upper x)).
Definition higherWordMatchingEquiv:
  Equiv (νFrame X.1) (SemiReedy.MatchingObject arity (faceDiagram arity D)) :=
  prefixMatchingEquiv X.1 (faceDiagram arity D) upper lower compatible.

Definition higherFrameMatchingEquiv:
  Equiv (νFrame X.1) (MatchingObject arity D) :=
  compEquiv higherWordMatchingEquiv (symEquiv (matchingEquivFace arity D)).

Lemma higherFrameMatchingFace d i a:
  (higherFrameMatchingEquiv d).1 None (shapeFace (depthFaceWord arity n.+1 i a))
    = upper (faceAtDepth (prefixDepsCohs X.1) (depth i) a d).
Proof.
  change ((matchingExtend arity D (higherWordMatchingEquiv d)).1 None
    (shapeFace (depthFaceWord arity n.+1 i a))
    = upper (faceAtDepth (prefixDepsCohs X.1) (depth i) a d)).
  rewrite matchingExtendFace.
  now exact (prefixMatchingFace X.1 (faceDiagram arity D) upper lower compatible d i a).
Qed.
End Higher.
End DgnMatchingOn.


(** Finite indexed degeneracy prefixes and their Reedy diagrams. *)

Module IndexedReedyDgnOn (A: LayerSig) (S: νDgnSetSig A).
Import A.
Module Export Indexed := DgnLayerOn A S.
Module Frames := DgnMatchingOn A S Indexed.Step.Faces.Faces.

Fixpoint indexedCells (n: nat): DgnPrefix n -> Index n -> HSet :=
  match n as n return DgnPrefix n -> Index n -> HSet with
  | 0 => fun _ i => match i with end
  | S n => fun X i =>
      match i with
      | Some i => indexedCells n (dgnBond X) i
      | None => prefixCell X.1
      end
  end.

(** The finite comparison records the actions needed by the next layer. *)
Definition FrameProjection n
  (D: DgnPrefix n -> Diagram arity n)
  (c: forall X i, Equiv (indexedCells n X i) (cells (D X) i))
  (b: forall X, νFrame X.1 -> MatchingObject arity (D X)): Type :=
  match n as n return forall (D: DgnPrefix n -> Diagram arity n),
    (forall X i, Equiv (indexedCells n X i) (cells (D X) i)) ->
    (forall X, νFrame X.1 -> MatchingObject arity (D X)) -> Type with
  | 0 => fun _ _ _ => unit
  | S n => fun D c b => forall X d (i: FaceDepth n) a,
      (b X d).1 None (shapeFace (depthFaceWord arity n i a))
        = c X None (faceAtDepth (prefixDepsCohs X.1) (depth i) a d)
  end D c b.

Definition FaceProjection n
  (D: DgnPrefix n -> Diagram arity n)
  (c: forall X i, Equiv (indexedCells n X i) (cells (D X) i)): Type :=
  match n as n return forall (D: DgnPrefix n -> Diagram arity n),
    (forall X i, Equiv (indexedCells n X i) (cells (D X) i)) -> Type with
  | 0 => fun _ _ => unit
  | S 0 => fun _ _ => unit
  | S (S n) => fun D c => forall X (i: FaceDepth n) a (x: prefixCell X.1),
      c X (Some None) (faceAtDepth (prefixDepsCohs X.1.1) (depth i) a x.1) =
      act (D X) (i := Some None) (j := None)
        (shapeFace (depthFaceWord arity n i a)) (c X None x)
  end D c.

Definition DegeneracyProjection n
  (D: DgnPrefix n -> Diagram arity n)
  (c: forall X i, Equiv (indexedCells n X i) (cells (D X) i)): Type :=
  match n as n return forall (D: DgnPrefix n -> Diagram arity n),
    (forall X i, Equiv (indexedCells n X i) (cells (D X) i)) -> Type with
  | 0 => fun _ _ => unit
  | S 0 => fun _ _ => unit
  | S (S n) => fun D c => forall X (i: FaceDepth n) x,
      c X None (prefixGenerator X i x) =
      act (D X) (i := None) (j := Some None)
        (shapeMask (depthFaceWord hunit n i tt)) (c X (Some None) x)
  end D c.

Record IndexedStage {n: nat} := {
  stageDiagram: Equiv (DgnPrefix n) (Diagram arity n);
  stageCells: forall X i, Equiv (indexedCells n X i) (cells (stageDiagram X) i);
  stageBoundary: forall X, Equiv (νFrame X.1) (MatchingObject arity (stageDiagram X));
  stageFrames: FrameProjection n stageDiagram stageCells (fun X => stageBoundary X);
  stageFaces: FaceProjection n stageDiagram stageCells;
  stageDegeneracies: DegeneracyProjection n stageDiagram stageCells;
}.
Arguments IndexedStage n : clear implicits.

Definition indexedStageZero: IndexedStage 0.
Proof.
  unshelve refine {| stageDiagram := qinvEquiv (fun _ => emptyDiagram arity)
      (fun _ => (tt; tt)) _ _;
    stageCells := _;
    stageBoundary := fun X => Frames.zeroFrameMatchingEquiv X (emptyDiagram arity);
    stageFrames := tt; stageFaces := tt; stageDegeneracies := tt |}.
  - now intros [[] []].
  - now exact (emptyPartialEq _ (dgnLaws arity)).
  - now intros X [].
Defined.

Definition indexedExtensionEquiv n:
  Equiv (DgnPrefix n.+1) {X: DgnPrefix n &T dgnIncrType X} :=
  qinvEquiv (fun X => (dgnBond X; dgnHead X))
    (fun X => dgnExtend X.1 X.2) (fun _ => eq_refl) (fun _ => eq_refl).

(** A local classification of the degeneracy layer extends a prefix
    classification while retaining its original total cell space. *)
Definition extendIndexedDiagramEquiv n
  (d: Equiv (DgnPrefix n) (Diagram arity n))
  (b: forall X, Equiv (νFrame X.1) (MatchingObject arity (d X)))
  (e: forall (X: DgnPrefix n) (E: νFrame X.1 -> HSet),
    Equiv ((νDgnSetAt n).(dgnStepType) X.1 X.2 E)
      (LatchingLifts arity (d X) (hsigT E) (fun x => b X x.1))):
  Equiv (DgnPrefix n.+1) (Diagram arity n.+1) :=
  compEquiv (indexedExtensionEquiv n)
    (compEquiv (sigTEquiv d (fun X =>
      compEquiv (sigTEquivSnd (e X))
        (sigTEquivFst (B := fun m: {T: HSet &T T -> MatchingObject arity (d X)} =>
          LatchingLifts arity (d X) m.1 m.2)
          (hsetFamilyMapEquivAlong (b X)))))
      (extensionEquivDiagram arity n)).

Definition LayerEquivalence {n} (R: IndexedStage n): Type :=
  forall (X: DgnPrefix n) (E: νFrame X.1 -> HSet),
    Equiv ((νDgnSetAt n).(dgnStepType) X.1 X.2 E)
      (LatchingLifts arity (stageDiagram R X) (hsigT E)
        (fun x => stageBoundary R X x.1)).

Definition zeroLayerEquiv (R: IndexedStage 0): LayerEquivalence R.
Proof.
  intros X E.
  refine (qinvEquiv (fun _ => @Build_LatchingLifts arity 0 (stageDiagram R X)
    (hsigT E) (fun x => stageBoundary R X x.1)
    (fun (i: Index 0) d x => match i return hsigT E with end)
    (fun (i: Index 0) d x => False_rect _ (match i return False with end))
    (fun (i j: Index 0) d f x => False_rect _ (match i return False with end)))
    (fun _ => tt) _ _).
  - now intros [].
  - intro L. apply latchingLiftsEq. intros i d x. exfalso. now destruct i.
Defined.

Definition LayerProjection {n} (R: IndexedStage n) (e: LayerEquivalence R): Type :=
  match n as n return forall R: IndexedStage n, LayerEquivalence R -> Type with
  | 0 => fun _ _ => unit
  | S n => fun R e => forall X E L (i: FaceDepth n) x,
      (e X E L).(lift) None (shapeMask (depthFaceWord hunit n i tt))
        (stageCells R X None x) = layerAbove X E L (depth i) (depthBound i) x
  end R e.

Section Step.
Context {n} (R: IndexedStage n).
Context (e: forall (X: DgnPrefix n) (E: νFrame X.1 -> HSet),
  Equiv ((νDgnSetAt n).(dgnStepType) X.1 X.2 E)
    (LatchingLifts arity (stageDiagram R X) (hsigT E)
      (fun x => stageBoundary R X x.1))).

Definition nextIndexedDiagram: Equiv (DgnPrefix n.+1) (Diagram arity n.+1) :=
  extendIndexedDiagramEquiv n (stageDiagram R) (stageBoundary R) e.

Definition nextIndexedCells (X: DgnPrefix n.+1) (i: Index n.+1):
  Equiv (indexedCells n.+1 X i) (cells (nextIndexedDiagram X) i).
Proof.
  destruct i as [i|].
  - now exact (stageCells R (dgnBond X) i).
  - now exact idEquiv.
Defined.

End Step.

Definition nextIndexedFaces {n} (R: IndexedStage n) (e: LayerEquivalence R):
  FaceProjection n.+1 (nextIndexedDiagram R e) (nextIndexedCells R e).
Proof.
  destruct n as [|k].
  - now exact tt.
  - intros X i a x. symmetry.
    now exact (stageFrames R (dgnBond X) x.1 i a).
Defined.

Definition nextIndexedBoundary {n} (R: IndexedStage n) (e: LayerEquivalence R)
  (X: DgnPrefix n.+1):
  Equiv (νFrame X.1) (MatchingObject arity (nextIndexedDiagram R e X)).
Proof.
  destruct n as [|k].
  - now exact (Frames.firstFrameMatchingEquiv X (nextIndexedDiagram R e X)
      (nextIndexedCells R e X None)).
  - now exact (Frames.higherFrameMatchingEquiv X (nextIndexedDiagram R e X)
      (nextIndexedCells R e X None) (nextIndexedCells R e X (Some None))
      (nextIndexedFaces R e X)).
Defined.

Definition nextIndexedFrames {n} (R: IndexedStage n) (e: LayerEquivalence R):
  FrameProjection n.+1 (nextIndexedDiagram R e) (nextIndexedCells R e)
    (nextIndexedBoundary R e).
Proof.
  destruct n as [|k].
  - now exact (fun X => Frames.firstFrameMatchingFace X (nextIndexedDiagram R e X)
      (nextIndexedCells R e X None)).
  - now exact (fun X => Frames.higherFrameMatchingFace X (nextIndexedDiagram R e X)
      (nextIndexedCells R e X None) (nextIndexedCells R e X (Some None))
      (nextIndexedFaces R e X)).
Defined.

Definition nextIndexedDegeneracies {n} (R: IndexedStage n) (e: LayerEquivalence R)
  (h: LayerProjection R e):
  DegeneracyProjection n.+1 (nextIndexedDiagram R e) (nextIndexedCells R e).
Proof.
  destruct n as [|k].
  - now exact tt.
  - intros X i x. symmetry.
    now exact (h (dgnBond X) X.1.2 X.2.2 i x).
Defined.

Definition nextIndexedStage {n} (R: IndexedStage n) (e: LayerEquivalence R)
  (h: LayerProjection R e): IndexedStage n.+1 := {|
  stageDiagram := nextIndexedDiagram R e;
  stageCells := nextIndexedCells R e;
  stageBoundary := nextIndexedBoundary R e;
  stageFrames := nextIndexedFrames R e;
  stageFaces := nextIndexedFaces R e;
  stageDegeneracies := nextIndexedDegeneracies R e h;
|}.


Definition positiveLayerModel {n} (R: IndexedStage n.+1) (X: DgnPrefix n.+1):
  LowerModel n X (stageDiagram R X) (stageCells R X None).
Proof.
  destruct n as [|k].
  - now exact tt.
  - exists (stageCells R X (Some None)). split.
    + now exact (stageFaces R X).
    + now exact (stageDegeneracies R X).
Defined.

Definition positiveLayerEquiv {n} (R: IndexedStage n.+1): LayerEquivalence R :=
  fun X E => indexedLayerLiftsEquiv X (stageDiagram R X) (stageCells R X None)
    (positiveLayerModel R X) (stageBoundary R X) (stageFrames R X) E.

Definition positiveLayerProjection {n} (R: IndexedStage n.+1):
  LayerProjection R (positiveLayerEquiv R) :=
  fun X E L i x => indexedLayerLiftsFace X (stageDiagram R X) (stageCells R X None)
    (positiveLayerModel R X) (stageBoundary R X) (stageFrames R X) E L i x.

Definition layerClassification {n} (R: IndexedStage n):
  {e: LayerEquivalence R &T LayerProjection R e}.
Proof.
  destruct n as [|k].
  - now exact (zeroLayerEquiv R; tt).
  - now exact (positiveLayerEquiv R; positiveLayerProjection R).
Defined.

Definition advanceIndexedStage {n} (R: IndexedStage n): IndexedStage n.+1 :=
  nextIndexedStage R (layerClassification R).1 (layerClassification R).2.

Fixpoint indexedStageAt n: IndexedStage n :=
  match n with 0 => indexedStageZero | S n => advanceIndexedStage (indexedStageAt n) end.

Definition indexedPrefixDiagramEquiv n: Equiv (DgnPrefix n) (Diagram arity n) :=
  stageDiagram (indexedStageAt n).

Lemma indexedPrefixDiagramBond n (X: DgnPrefix n.+1):
  indexedPrefixDiagramEquiv n (dgnBond X) =
    truncateDiagram (indexedPrefixDiagramEquiv n.+1 X).
Proof. now reflexivity. Defined.

End IndexedReedyDgnOn.

Module IndexedReedyDgn (A: LayerSig).
Module Base := νDgnSet.νDgnSet A.
Include IndexedReedyDgnOn A Base.
End IndexedReedyDgn.

Module IndexedReedyDgnSimplicial := IndexedReedyDgnOn SimplicialLayer νDgnSetSimplicial.
Module IndexedReedyDgnCubical := IndexedReedyDgnOn CubicalLayer νDgnSetCubical.


(** Indexed ν-sets with degeneracies are matching sequences of diagrams on
    the ν-shape category. Each indexed prefix is identified with a finite
    diagram, compatibly with truncation. *)

Module ReedyCorrespondenceOn (A: LayerSig) (S: νDgnSetSig A).
Import A.
Module Export PrefixComparison := IndexedReedyDgnOn A S.

Definition initialPrefixContr: Contr (DgnPrefix 0).
Proof. exists (tt; tt). now intros [[] []]. Defined.

Definition νDgnSetsEquivDiagramLimit:
  Equiv νDgnSets (SequentialLimit (Diagram arity) (fun n => @truncateDiagram arity n)) :=
  compEquiv (telescopeLimitEquiv νDgnSetTel (tt; tt) initialPrefixContr)
    (sequentialLimitEquiv (fun n => @dgnBond n) (fun n => @truncateDiagram arity n)
      indexedPrefixDiagramEquiv indexedPrefixDiagramBond).

Definition νDgnSetsEquivMatchingSeq: Equiv νDgnSets (MatchingSeq (dgnSystem arity)) :=
  compEquiv νDgnSetsEquivDiagramLimit
    (symEquiv (matchingSeqEquivDiagramLimit (dgnSystem arity) (dgnLaws arity))).

Definition νDgnSetsEqMatchingSeq: νDgnSets = MatchingSeq (dgnSystem arity) :=
  ua νDgnSetsEquivMatchingSeq.

End ReedyCorrespondenceOn.

Module ReedyCorrespondence (A: LayerSig).
Module Base := νDgnSet.νDgnSet A.
Include ReedyCorrespondenceOn A Base.
End ReedyCorrespondence.

Module ReedyCorrespondenceSimplicial := ReedyCorrespondenceOn SimplicialLayer νDgnSetSimplicial.
Module ReedyCorrespondenceCubical := ReedyCorrespondenceOn CubicalLayer νDgnSetCubical.
