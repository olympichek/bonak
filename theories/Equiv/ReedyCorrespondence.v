(** Indexed ν-sets are matching sequences of h-set diagrams on the
    semi-shape category. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Equiv HSetFamily Notation FinitePrefix
  Univalence SequentialLimit TelescopeLimit.
From Bonak.νSet Require Import Layer νSet.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.
From Bonak.Reedy Require Import Reedy Extension.
From Bonak.Equiv Require Import Boundary Matching.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

(** Finite indexed prefixes compared directly with Reedy diagrams. *)

Module IndexedReedyOn (A: LayerSig) (V: νSetSig A).
Import A FinitePrefix.
Module Export Indexed := IndexedMatching A V.

(** Each stage retains both the classification and its face evaluation.
    The latter identifies the next matching object with its indexed frame. *)
Definition StageProjections n
  (D: (νSetAt n).(prefix) -> Diagram arity n)
  (b: forall X, νFrame X -> MatchingObject arity (D X)): Type :=
  match n as n return forall
    (D: (νSetAt n).(prefix) -> Diagram arity n),
    (forall X, νFrame X -> MatchingObject arity (D X)) -> Type with
  | 0 => fun _ _ => unit
  | S n => fun D b =>
      {cells: forall X, Equiv (prefixCell X) ((D X).(cells) None) &T
       forall X d i a, (b X d).1 None (depthFaceWord arity n i a)
         = cells X (faceAtDepth (prefixDepsCohs X) (depth i) a d)}
  end D b.

Record IndexedStage {n: nat} := {
  stageDiagram: Equiv (νSetAt n).(prefix) (Diagram arity n);
  stageBoundary: forall X, Equiv (νFrame X) (MatchingObject arity (stageDiagram X));
  stageProjections: StageProjections n stageDiagram (fun X => stageBoundary X);
}.
Arguments IndexedStage n : clear implicits.

Definition indexedStageZero: IndexedStage 0.
Proof.
  refine (@Build_IndexedStage 0 (qinvEquiv (fun _ => emptyDiagram arity)
    (fun _ => tt) (fun x => match x with tt => eq_refl end)
    (matchingEmptyEq _ (hsetLaws arity))) _ tt).
  intro X. refine (qinvEquiv (fun _: νFrame X =>
    ((fun i: Index 0 => match i with end; fun i: Index 0 => match i with end)
      : MatchingObject arity (emptyDiagram arity))) (fun _ => tt) _ _).
  - now intros [].
  - intro b. apply matchingExt. now intros [].
Defined.

Section Step.
Context {n} (R: IndexedStage n).

Definition nextIndexedDiagram: Equiv (νSetAt n.+1).(prefix) (Diagram arity n.+1) :=
  compEquiv (sigTEquiv (stageDiagram R)
    (fun X => hsetFamilyMapEquivAlong (stageBoundary R X)))
    {| eqvFun := joinExtension; eqvIsEquiv := joinExtensionIsEquiv _ (hsetLaws arity) n |}.

Definition nextIndexedCells (X: (νSetAt n.+1).(prefix)):
  Equiv (prefixCell X) ((nextIndexedDiagram X).(cells) None) := idEquiv.

Lemma nextIndexedFace (X: (νSetAt n.+1).(prefix)) (i: Index n)
  (u: Word arity (rank i) n) (x: prefixCell X):
  (stageBoundary R X.1 x.1).1 i u
    = (nextIndexedDiagram X).(restrict) (i := Some i) (j := None) u
        (nextIndexedCells X x).
Proof. now reflexivity. Defined.

Lemma nextIndexedBond (X: (νSetAt n.+1).(prefix)):
  stageDiagram R X.1 = truncateDiagram arity (nextIndexedDiagram X).
Proof. now reflexivity. Defined.

End Step.
Definition firstIndexedBoundary (R: IndexedStage 0) (X: (νSetAt 1).(prefix)):
  Equiv (νFrame X) (MatchingObject arity (nextIndexedDiagram R X)) :=
  zeroIndexedMatchingEquiv (prefixDepsCohs X) (nextIndexedDiagram R X) (nextIndexedCells R X).

Lemma firstIndexedBoundaryFace (R: IndexedStage 0) (X: (νSetAt 1).(prefix)) d i a:
  (firstIndexedBoundary R X d).1 None (depthFaceWord arity 0 i a)
    = nextIndexedCells R X (faceAtDepth (prefixDepsCohs X) (depth i) a d).
Proof. now apply zeroIndexedMatchingFace. Qed.

Section HigherStep.
Context {n} (R: IndexedStage n.+1) (X: (νSetAt n.+2).(prefix)).
Local Abbreviation D := (nextIndexedDiagram R X).

Lemma nextIndexedFaceCompatible (i: FaceDepth n) a (x: prefixCell X):
  (stageProjections R).1 X.1 (faceAtDepth (prefixDepsCohs X.1) (depth i) a x.1)
    = D.(restrict) (i := Some None) (j := None)
        (depthFaceWord arity n i a) (nextIndexedCells R X x).
Proof. rewrite <- (stageProjections R).2. now apply nextIndexedFace. Qed.

Definition higherIndexedBoundary: Equiv (νFrame X) (MatchingObject arity D) :=
  prefixMatchingEquiv X D (nextIndexedCells R X) ((stageProjections R).1 X.1)
    nextIndexedFaceCompatible.

Lemma higherIndexedBoundaryFace d i a:
  (higherIndexedBoundary d).1 None (depthFaceWord arity n.+1 i a)
    = nextIndexedCells R X (faceAtDepth (prefixDepsCohs X) (depth i) a d).
Proof. now apply prefixMatchingFace. Qed.
End HigherStep.

Definition nextIndexedStage {n} (R: IndexedStage n): IndexedStage n.+1.
Proof.
  destruct n as [|n].
  - refine (@Build_IndexedStage 1 (nextIndexedDiagram R) (firstIndexedBoundary R) _).
    now exact (nextIndexedCells R; firstIndexedBoundaryFace R).
  - refine (@Build_IndexedStage n.+2 (nextIndexedDiagram R) (higherIndexedBoundary R) _).
    now exact (nextIndexedCells R; higherIndexedBoundaryFace R).
Defined.

Fixpoint indexedStageAt n: IndexedStage n :=
  match n with 0 => indexedStageZero | S n => nextIndexedStage (indexedStageAt n) end.

Definition indexedPrefixDiagramEquiv n:
  Equiv (νSetAt n).(prefix) (Diagram arity n) :=
  stageDiagram (indexedStageAt n).

Lemma indexedPrefixDiagramBond n (X: (νSetAt n.+1).(prefix)):
  indexedPrefixDiagramEquiv n X.1
    = truncateDiagram arity (indexedPrefixDiagramEquiv n.+1 X).
Proof. destruct n; now apply nextIndexedBond. Defined.

End IndexedReedyOn.

Module IndexedReedy (A: LayerSig).
Module Base := νSet.νSet A.
Include IndexedReedyOn A Base.
End IndexedReedy.

Module IndexedReedySimplicial := IndexedReedyOn SimplicialLayer νSetSimplicial.
Module IndexedReedyCubical := IndexedReedyOn CubicalLayer νSetCubical.


(** Indexed ν-sets are matching sequences of h-set diagrams on the
    semi-shape category. Each indexed prefix is identified with a finite diagram,
    compatibly with truncation. *)

Module ReedyCorrespondenceOn (A: LayerSig) (V: νSetSig A).
Import A.
Module Export PrefixComparison := IndexedReedyOn A V.

Definition νSetsEquivDiagramLimit:
  Equiv νSets (SequentialLimit (Diagram arity) (fun n => @truncateDiagram arity n)) :=
  compEquiv (telescopeLimitEquiv νSetTel tt (tt; fun x => hunit_ext tt x))
    (sequentialLimitEquiv (fun n X => X.1) (fun n => @truncateDiagram arity n)
      indexedPrefixDiagramEquiv indexedPrefixDiagramBond).

Definition νSetsEquivMatchingSeq: Equiv νSets (MatchingSeq (hsetSystem arity)) :=
  compEquiv νSetsEquivDiagramLimit
    (symEquiv (matchingSeqEquivDiagramLimit (hsetSystem arity)
      (matchingExtensionLaws (hsetSystem arity) (hsetLaws arity)))).

Definition νSetsEqMatchingSeq: νSets = MatchingSeq (hsetSystem arity) :=
  ua νSetsEquivMatchingSeq.

End ReedyCorrespondenceOn.

Module ReedyCorrespondence (A: LayerSig).
Module Base := νSet.νSet A.
Include ReedyCorrespondenceOn A Base.
End ReedyCorrespondence.

Module ReedyCorrespondenceSimplicial := ReedyCorrespondenceOn SimplicialLayer νSetSimplicial.
Module ReedyCorrespondenceCubical := ReedyCorrespondenceOn CubicalLayer νSetCubical.
