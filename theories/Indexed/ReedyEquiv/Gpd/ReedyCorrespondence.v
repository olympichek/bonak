(** Indexed ν-groupoids are matching sequences of diagrams of homotopy
    groupoids on the semi-shape category. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation Univalence
  FinitePrefix SequentialLimit TelescopeLimit.
From Bonak.Indexed.Gpd Require Import Layer νGpd.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Pseudofunctor LocallyDiscrete
  HGpdBicat.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Reedy.Gpd Require Import Reedy Extension Bounded.
From Bonak.Indexed.ReedyEquiv.Gpd.Target Require Import Target.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Face Diagram StoredDiagram
  Matching.
From Bonak.Indexed.ReedyEquiv.Gpd Require Tower.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

(** A readout of finite diagrams from indexed prefixes is an equivalence as
    soon as it sends filler families to extensions by matching maps along an
    equivalence of frames with matching objects. *)

Module ReadoutClassifierOn (A: LayerGpdSig) (Core: νGpdSig A).
Import A.
Module Export Indexed := Tower.TowerOn A Core.

Local Definition replaceForward {S T: Type} (e: Equiv S T)
  (f: S -> T) (h: forall x, e x = f x): Equiv S T := {|
  eqvFun := f;
  eqvIsEquiv := {|
    linv := e.(eqvIsEquiv).(linv);
    linvEq x := f_equal e.(eqvIsEquiv).(linv) (eq_sym (h x))
      • e.(eqvIsEquiv).(linvEq) x;
    rinv := e.(eqvIsEquiv).(rinv);
    rinvEq y := eq_sym (h (e.(eqvIsEquiv).(rinv) y))
      • e.(eqvIsEquiv).(rinvEq) y;
  |};
|}.

(** Changing the base of a map along an equivalence keeps its total space. *)
Local Definition baseChangeEquiv {M N: HGpd} (e: Equiv M N):
  Equiv {T: HGpd &T T -> M} {T: HGpd &T T -> N} :=
  sigTEquivSnd (fun T: HGpd => @piEquiv T (fun _ => M) (fun _ => N) (fun _ => e)).

Section Readout.
Context (readout: forall n, (νGpdAt n).(prefix) -> Diagram arity n).
Context (frameMatchingMap: forall n (X: (νGpdAt n).(prefix)),
  νFrame X -> MatchingObject (readout n X)).
Context (frameMatchingMapIsEquiv: forall n (X: (νGpdAt n).(prefix)),
  IsEquiv (frameMatchingMap n X)).
Context (readoutExtension: forall n (X: (νGpdAt (S n)).(prefix)),
  extendByMatchingMap arity (readout n X.1) {d: νFrame X.1 & X.2 d}
    (fun t => frameMatchingMap n X.1 t.1) = readout (S n) X).

Definition readoutFrameEquiv n (X: (νGpdAt n).(prefix)):
  Equiv (νFrame X) (MatchingObject (readout n X)) :=
  {| eqvFun := frameMatchingMap n X; eqvIsEquiv := frameMatchingMapIsEquiv n X |}.

(** A filler family over a frame is a map into the matching object, and
    extension by such maps classifies the next diagram. *)
Fixpoint readoutIsEquiv (n: nat): IsEquiv (readout n).
Proof.
  destruct n as [|n].
  - refine ((qinvEquiv (readout 0) (fun _ => tt) _ _).(eqvIsEquiv)).
    + now intros [].
    + intro Y. now exact (eq_sym (emptyDiagramEq arity (readout 0 tt))
        • emptyDiagramEq arity Y).
  - pose (previous := {| eqvFun := readout n; eqvIsEquiv := readoutIsEquiv n |}).
    pose (step := compEquiv (sigTEquiv previous (fun X =>
        compEquiv (hgpdFamilyMapEquiv (νFrame X))
          (baseChangeEquiv (readoutFrameEquiv n X))))
      {| eqvFun := joinExtension (M := gpdSystem arity) (n := n);
        eqvIsEquiv := joinExtensionIsEquiv _ (gpdLaws arity) n |}).
    now exact (replaceForward step (readout (S n)) (readoutExtension n)).(eqvIsEquiv).
Defined.

Definition readoutEquiv n: Equiv (νGpdAt n).(prefix) (Diagram arity n) :=
  {| eqvFun := readout n; eqvIsEquiv := readoutIsEquiv n |}.

Lemma readoutBond n (X: (νGpdAt (S n)).(prefix)):
  readoutEquiv n X.1 = truncateDiagram (readoutEquiv (S n) X).
Proof.
  now exact (f_equal (@truncateDiagram arity n) (readoutExtension n X)).
Defined.

End Readout.
End ReadoutClassifierOn.


(** Indexed ν-groupoids are matching sequences of diagrams of homotopy
    groupoids on the semi-shape category. Each indexed prefix is identified
    with the finite diagram read off from it, compatibly with truncation. *)

Module ReedyCorrespondenceOn (A: LayerGpdSig) (Core: νGpdSig A).
Module Faces := FaceOn A Core.
Module Diagrams := IndexedDiagramOn A Core Faces.
Module Stored := StoredDiagramOn A Core Faces Diagrams.
Module IndexedModel := IndexedMatchingEquivOn A Core Faces Diagrams.Extraction.
Module Classifier := ReadoutClassifierOn A Core.
Import A Stored.Prefix.

Definition completedMatchingMapIsEquiv {n} (X: (νGpdAt n).(prefix)):
  IsEquiv (matchingMap
    (restrictDiagram (S n) (indexedDiagram (completePrefix X)))) :=
  IndexedModel.Comparison.indexedTargetComplete (completePrefix X)
    (reedyTarget (Diagrams.Extraction.g (completePrefix X))) n
    (packedCellProjectionEquiv X) (fun t => eq_refl).

Definition indexedMatchingMapIsEquiv n (X: (νGpdAt n).(prefix)):
  IsEquiv (Stored.storedBoundary X) :=
  Stored.boundaryIsEquiv X (completedMatchingMapIsEquiv X).

Definition indexedReadout n (X: (νGpdAt n).(prefix)): Diagram arity n :=
  Stored.storedDiagram X.
Definition indexedMatchingMap n (X: (νGpdAt n).(prefix)):
  νFrame X -> MatchingObject (indexedReadout n X) := Stored.storedBoundary X.

Definition indexedExtension n (X: (νGpdAt (S n)).(prefix)):
  extendByMatchingMap arity (indexedReadout n X.1) {d: νFrame X.1 & X.2 d}
    (fun t => indexedMatchingMap n X.1 t.1) = indexedReadout (S n) X :=
  Stored.storedDiagramExtension X.1 X.2.

Definition indexedPrefixDiagramEquiv n:
  Equiv (νGpdAt n).(prefix) (Diagram arity n) :=
  Classifier.readoutEquiv indexedReadout indexedMatchingMap indexedMatchingMapIsEquiv
    indexedExtension n.

Definition indexedPrefixDiagramBond n (X: (νGpdAt (S n)).(prefix)):
  indexedPrefixDiagramEquiv n X.1 = truncateDiagram (indexedPrefixDiagramEquiv (S n) X) :=
  Classifier.readoutBond indexedReadout indexedMatchingMap indexedMatchingMapIsEquiv
    indexedExtension n X.

Definition νGpdsEquivDiagramLimit:
  Equiv νGpds (SequentialLimit (Diagram arity) (fun n => @truncateDiagram arity n)) :=
  compEquiv (telescopeLimitEquiv νGpdTel tt (tt; fun x => hunit_ext tt x))
    (sequentialLimitEquiv (fun n X => X.1) (fun n => @truncateDiagram arity n)
      indexedPrefixDiagramEquiv indexedPrefixDiagramBond).

Definition νGpdsEquivMatchingSeq: Equiv νGpds (MatchingSeq (gpdSystem arity)) :=
  compEquiv νGpdsEquivDiagramLimit
    (symEquiv (matchingSeqEquivDiagramLimit (gpdSystem arity)
      (matchingExtensionLaws (gpdSystem arity) (gpdLaws arity)))).

Definition νGpdsEqMatchingSeq: νGpds = MatchingSeq (gpdSystem arity) :=
  ua νGpdsEquivMatchingSeq.

End ReedyCorrespondenceOn.

Module ReedyCorrespondence (A: LayerGpdSig).
Module Core := νGpd.νGpd A.
Include ReedyCorrespondenceOn A Core.
End ReedyCorrespondence.

Module ReedyCorrespondenceSimplicial :=
  ReedyCorrespondenceOn SimplicialGpdLayer νGpdSimplicial.
Module ReedyCorrespondenceCubical :=
  ReedyCorrespondenceOn CubicalGpdLayer νGpdCubical.
