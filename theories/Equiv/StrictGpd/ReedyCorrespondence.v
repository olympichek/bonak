(** Indexed strict groupoids are matching sequences of strict groupoid
    diagrams on the semi-shape category, and hence functors into strict
    groupoids and face presentations. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Notation FinitePrefix
  Univalence SequentialLimit TelescopeLimit.
From Bonak.Category.Groupoid Require Import Strict GraphFiberRoundtrip.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.
From Bonak.Presheaf.StrictGpd Require Import Presentation Correspondence.
From Bonak.Reedy.StrictGpd Require Import Reedy Extension Correspondence.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Equiv.StrictGpd Require Import Face Boundary Matching.

Set Primitive Projections.
Set Printing Projections.

(** The matching object of the empty diagram is the terminal groupoid. *)
Section Empty.
Context (A: HSet).

Definition emptyMatchingPoint: MatchingBoundary A (emptyDiagram A) :=
  (fun i: Index 0 => match i with end; fun i: Index 0 => match i with end).

Definition emptyMatchingHom (b c: MatchingBoundary A (emptyDiagram A)):
  MatchingHom A b c :=
  (fun i: Index 0 => match i with end; fun i: Index 0 => match i with end).

Definition emptyMatchingFunctor:
  Functor unitGroupoid (MatchingObject A (emptyDiagram A)).
Proof.
  refine {| fobj _ := emptyMatchingPoint;
    fhom _ _ _ := emptyMatchingHom emptyMatchingPoint emptyMatchingPoint |}.
  - intro x. apply matchingHomExt. now intros [].
  - intros x y z f g. apply matchingHomExt. now intros [].
Defined.

Lemma emptyMatchingRet:
  emptyMatchingFunctor ⨟ᶠ terminalFunctor _ = idFunctor unitGroupoid.
Proof.
  apply (functorEqPath unitGroupoid.(groupoidStrictness)).
  refine (Build_FunctorEq (fun x => match x with tt => eq_refl end) _).
  intros [] [] f. now apply hunit_ext.
Qed.

Lemma emptyMatchingSec:
  terminalFunctor _ ⨟ᶠ emptyMatchingFunctor
  = idFunctor (MatchingObject A (emptyDiagram A)).
Proof.
  apply (functorEqPath
    (MatchingObject A (emptyDiagram A)).(groupoidStrictness)).
  refine (Build_FunctorEq (fun b => matchingBoundaryExt A emptyMatchingPoint b
    (fun i => match i with end)) _).
  intros b c f. apply matchingHomExt. now intros [].
Qed.

Definition emptyMatchingIso:
  Iso StrictGroupoidCat unitGroupoid (MatchingObject A (emptyDiagram A)) :=
  @Build_Iso StrictGroupoidCat _ _ emptyMatchingFunctor
    (@Build_IsInvertible StrictGroupoidCat _ _ _ (terminalFunctor _)
      emptyMatchingRet emptyMatchingSec).
End Empty.

(** Finite indexed prefixes compared directly with Reedy diagrams. *)

Module IndexedReedyOn (A: LayerSig) (S: νStrictGpdSig A) (F: FaceSig A S).
Import A FinitePrefix.
Module Export Indexed := IndexedMatchingOn A S F.

(** Each stage retains both the classification and its face evaluation.
    The latter identifies the next matching object with its indexed frame. *)
Definition StageProjections n
  (D: (νStrictGpdAt n).(prefix) -> Diagram arity n)
  (b: forall X, Iso StrictGroupoidCat (νFrame X) (MatchingObject arity (D X))):
  Type :=
  match n as n return forall
    (D: (νStrictGpdAt n).(prefix) -> Diagram arity n),
    (forall X, Iso StrictGroupoidCat (νFrame X) (MatchingObject arity (D X))) ->
    Type with
  | 0 => fun _ _ => unit
  | S n => fun D b =>
      {cells: forall X,
         Iso StrictGroupoidCat (prefixCell X) ((D X).(cells) None) &T
       forall X i a, (b X).(isoHom)
         ⨟ᶠ matchingProjection arity (D X) None (depthFaceWord arity n i a)
         = faceAtDepth (prefixDepsCohs X) (depth i) a ⨟ᶠ (cells X).(isoHom)}
  end D b.

Record IndexedStage {n: nat} := {
  stageDiagram: Equiv (νStrictGpdAt n).(prefix) (Diagram arity n);
  stageBoundary: forall X,
    Iso StrictGroupoidCat (νFrame X) (MatchingObject arity (stageDiagram X));
  stageProjections: StageProjections n stageDiagram (fun X => stageBoundary X);
}.
Arguments IndexedStage n : clear implicits.

Definition indexedStageZero: IndexedStage 0.
Proof.
  refine (@Build_IndexedStage 0 (qinvEquiv (fun _ => emptyDiagram arity)
    (fun _ => tt) (fun x => match x with tt => eq_refl end)
    (matchingEmptyEq _ (strictGpdLaws arity))) _ tt).
  intro X. now exact (emptyMatchingIso arity).
Defined.

Section Step.
Context {n} (R: IndexedStage n).

Definition nextIndexedDiagram:
  Equiv (νStrictGpdAt n.+1).(prefix) (Diagram arity n.+1) :=
  compEquiv (sigTEquiv (stageDiagram R)
    (fun X => familyMapEquivAlong (stageBoundary R X)))
    {| eqvFun := joinExtension;
       eqvIsEquiv := joinExtensionIsEquiv _ (strictGpdLaws arity) n |}.

Definition nextIndexedCells (X: (νStrictGpdAt n.+1).(prefix)):
  Iso StrictGroupoidCat (prefixCell X) ((nextIndexedDiagram X).(cells) None) :=
  idToIso (C := StrictGroupoidCat) eq_refl.

Lemma nextIndexedFace (X: (νStrictGpdAt n.+1).(prefix)) (i: Index n)
  (u: Word arity (rank i) n):
  proj X.2 ⨟ᶠ (stageBoundary R X.1).(isoHom)
    ⨟ᶠ matchingProjection arity (stageDiagram R X.1) i u
  = (nextIndexedDiagram X).(restrict) (i := Some i) (j := None) u.
Proof. now reflexivity. Defined.

Lemma nextIndexedBond (X: (νStrictGpdAt n.+1).(prefix)):
  stageDiagram R X.1 = truncateDiagram arity (nextIndexedDiagram X).
Proof. now reflexivity. Defined.
End Step.

Definition firstIndexedBoundary (R: IndexedStage 0)
  (X: (νStrictGpdAt 1).(prefix)):
  Iso StrictGroupoidCat (νFrame X)
    (MatchingObject arity (nextIndexedDiagram R X)) :=
  zeroIndexedMatchingIso (prefixDepsCohs X) (nextIndexedDiagram R X)
    (nextIndexedCells R X).

Lemma firstIndexedBoundaryFace (R: IndexedStage 0)
  (X: (νStrictGpdAt 1).(prefix)) i a:
  (firstIndexedBoundary R X).(isoHom)
    ⨟ᶠ matchingProjection arity (nextIndexedDiagram R X) None
      (depthFaceWord arity 0 i a)
  = faceAtDepth (prefixDepsCohs X) (depth i) a
    ⨟ᶠ (nextIndexedCells R X).(isoHom).
Proof. now apply zeroIndexedMatchingFace. Qed.

Section HigherStep.
Context {n} (R: IndexedStage n.+1) (X: (νStrictGpdAt n.+2).(prefix)).
Local Abbreviation D := (nextIndexedDiagram R X).

Lemma nextIndexedFaceCompatible (i: FaceDepth n) a:
  proj X.2 ⨟ᶠ faceAtDepth (prefixDepsCohs X.1) (depth i) a
    ⨟ᶠ ((stageProjections R).1 X.1).(isoHom)
  = (nextIndexedCells R X).(isoHom)
    ⨟ᶠ D.(restrict) (i := Some None) (j := None) (depthFaceWord arity n i a).
Proof.
  now exact (functorAssocEq _ _ _
    • f_equal (compFunctor (proj X.2)) (eq_sym ((stageProjections R).2 X.1 i a))
    • eq_sym (functorAssocEq _ _ _) • eq_sym (functorIdL _)).
Qed.

Definition higherIndexedBoundary:
  Iso StrictGroupoidCat (νFrame X) (MatchingObject arity D) :=
  prefixMatchingIso X D (nextIndexedCells R X) ((stageProjections R).1 X.1)
    nextIndexedFaceCompatible.

Lemma higherIndexedBoundaryFace i a:
  higherIndexedBoundary.(isoHom)
    ⨟ᶠ matchingProjection arity D None (depthFaceWord arity n.+1 i a)
  = faceAtDepth (prefixDepsCohs X) (depth i) a
    ⨟ᶠ (nextIndexedCells R X).(isoHom).
Proof. now apply prefixMatchingFace. Qed.
End HigherStep.

Definition nextIndexedStage {n} (R: IndexedStage n): IndexedStage n.+1.
Proof.
  destruct n as [|n].
  - refine (@Build_IndexedStage 1 (nextIndexedDiagram R)
      (firstIndexedBoundary R) _).
    now exact (nextIndexedCells R; firstIndexedBoundaryFace R).
  - refine (@Build_IndexedStage n.+2 (nextIndexedDiagram R)
      (higherIndexedBoundary R) _).
    now exact (nextIndexedCells R; higherIndexedBoundaryFace R).
Defined.

Fixpoint indexedStageAt n: IndexedStage n :=
  match n with
  | 0 => indexedStageZero
  | S n => nextIndexedStage (indexedStageAt n)
  end.

Definition indexedPrefixDiagramEquiv n:
  Equiv (νStrictGpdAt n).(prefix) (Diagram arity n) :=
  stageDiagram (indexedStageAt n).

Lemma indexedPrefixDiagramBond n (X: (νStrictGpdAt n.+1).(prefix)):
  indexedPrefixDiagramEquiv n X.1
    = truncateDiagram arity (indexedPrefixDiagramEquiv n.+1 X).
Proof. destruct n; now apply nextIndexedBond. Defined.

End IndexedReedyOn.

(** Indexed strict groupoids are matching sequences, functors into strict
    groupoids and face presentations. *)

Module ReedyCorrespondenceOn (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S).
Import A.
Module Export PrefixComparison := IndexedReedyOn A S F.

Definition νStrictGpdsEquivDiagramLimit:
  Equiv νStrictGpds
    (SequentialLimit (Diagram arity) (fun n => @truncateDiagram arity n)) :=
  compEquiv (telescopeLimitEquiv νStrictGpdTel tt (tt; fun x => hunit_ext tt x))
    (sequentialLimitEquiv (fun n X => X.1) (fun n => @truncateDiagram arity n)
      indexedPrefixDiagramEquiv indexedPrefixDiagramBond).

Definition νStrictGpdsEquivMatchingSeq:
  Equiv νStrictGpds (MatchingSeq (strictGpdSystem arity)) :=
  compEquiv νStrictGpdsEquivDiagramLimit
    (symEquiv (matchingSeqEquivDiagramLimit (strictGpdSystem arity)
      (matchingExtensionLaws (strictGpdSystem arity) (strictGpdLaws arity)))).

Definition νStrictGpdsEqMatchingSeq:
  νStrictGpds = MatchingSeq (strictGpdSystem arity) :=
  ua νStrictGpdsEquivMatchingSeq.

Definition νStrictGpdsEquivFunctor:
  Equiv νStrictGpds (Functor (Op (νSemiShape arity)) StrictGroupoidCat) :=
  compEquiv νStrictGpdsEquivMatchingSeq (matchingSeqEquivFunctor arity).

Definition νStrictGpdsEqFunctor:
  νStrictGpds = Functor (Op (νSemiShape arity)) StrictGroupoidCat :=
  ua νStrictGpdsEquivFunctor.

Definition νStrictGpdsEquivPresentation:
  Equiv νStrictGpds (νStrictGpdPresentation arity) :=
  compEquiv νStrictGpdsEquivFunctor (symEquiv (pshEquivFunctor arity)).

Definition νStrictGpdsEqPresentation:
  νStrictGpds = νStrictGpdPresentation arity :=
  ua νStrictGpdsEquivPresentation.

End ReedyCorrespondenceOn.

Module ReedyCorrespondence (A: LayerSig).
Module Core := νStrictGpd.νStrictGpd A.
Module Faces := FaceOn A Core.
Include ReedyCorrespondenceOn A Core Faces.
End ReedyCorrespondence.

Module ReedyCorrespondenceSimplicial :=
  ReedyCorrespondenceOn SimplicialLayer νStrictGpdSimplicial FaceSimplicial.
Module ReedyCorrespondenceCubical :=
  ReedyCorrespondenceOn CubicalLayer νStrictGpdCubical FaceCubical.
