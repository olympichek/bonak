(** Sequences of filler data over partial diagrams

    A diagram on a category graded by rank can be built one rank at a time:
    [FillerData] over the levels below a rank determines the next level. An
    [ExtensionSystem] records this for a chosen kind of diagram, and a
    [MatchingSeq] is a choice of filler data at every rank. [ExtensionLaws]
    state that extension loses no information. From them, finite prefixes
    classify partial diagrams compatibly with truncation, and the sequence
    classifies their sequential limit.

    On a direct category latching objects are trivial, so filler data is only a
    family over the matching object. A [MatchingSystem] presents this case. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Limit LeSProp SequentialLimit.

Set Primitive Projections.
Set Printing Projections.

Record DiagramStages := {
  PartialDiagram: nat -> Type;
  truncate {n}: PartialDiagram (S n) -> PartialDiagram n;
  emptyPartial: PartialDiagram 0;
}.

Arguments PartialDiagram : clear implicits.
Arguments truncate {_ _} _.
Arguments emptyPartial : clear implicits.

Record ExtensionSystem := {
  stages :> DiagramStages;
  FillerData {n}: PartialDiagram stages n -> Type;
  extendDiagram {n} (X: PartialDiagram stages n):
    FillerData X -> PartialDiagram stages (S n);
}.

Arguments FillerData {_ _} _.
Arguments extendDiagram {_ _} _ _.

Section Sequence.
Context (Sys: ExtensionSystem).

(** The recursive package keeps each prefix together with its diagram. *)
Fixpoint prefixPackage (n: nat): {R: Type &T R -> PartialDiagram Sys n} :=
  match n as k return {R: Type &T R -> PartialDiagram Sys k} with
  | 0 => ((unit: Type); fun _: unit => emptyPartial Sys)
  | S n =>
      let P := prefixPackage n in
      ({X: P.1 &T FillerData (P.2 X)};
       fun X: {X: P.1 &T FillerData (P.2 X)} => extendDiagram (P.2 X.1) X.2)
  end.

Definition Prefix n: Type := (prefixPackage n).1.
Definition prefixDiagram {n} (X: Prefix n): PartialDiagram Sys n :=
  (prefixPackage n).2 X.

Definition prefixTelescope: Telescope := {|
  stage := Prefix;
  datum n X := FillerData (prefixDiagram X);
  extend n X E := (X; E);
  bond n X := X.1;
  head n X := X.2;
  bondExtend n X E := eq_refl;
  headExtend _ _ _ := eq_refl;
  extendHead n X := eq_refl;
  bondExtendHead n X := eq_refl;
|}.

(** Compatible filler prefixes at every rank, starting at rank zero. *)
Definition MatchingSeq: Type := Limit prefixTelescope 0 tt.

Definition extendPacked {n} (z: {X: PartialDiagram Sys n &T FillerData X}):
  PartialDiagram Sys (S n) := extendDiagram z.1 z.2.

Record ExtensionLaws := {
  emptyPartialEq (X: PartialDiagram Sys 0): emptyPartial Sys = X;
  extendIsEquiv n: IsEquiv (@extendPacked n);
  truncateExtend {n} (X: PartialDiagram Sys n) (E: FillerData X):
    truncate (extendDiagram X E) = X;
}.

Section Classification.
Context (L: ExtensionLaws).

Fixpoint prefixDiagramIsEquiv (n: nat): IsEquiv (@prefixDiagram n).
Proof.
  destruct n as [|n].
  - now exact (qinvEquiv (fun _: unit => emptyPartial Sys) (fun _ => tt)
      (fun x => match x with tt => eq_refl end) L.(emptyPartialEq)).(eqvIsEquiv).
  - pose (e := {| eqvFun := @prefixDiagram n;
      eqvIsEquiv := prefixDiagramIsEquiv n |}).
    now exact (compEquiv (sigTEquivFst (B := fun X => FillerData X) e)
      {| eqvFun := @extendPacked n;
        eqvIsEquiv := L.(extendIsEquiv) n |}).(eqvIsEquiv).
Defined.

Definition prefixEquivDiagram n: Equiv (Prefix n) (PartialDiagram Sys n) :=
  {| eqvFun := @prefixDiagram n; eqvIsEquiv := prefixDiagramIsEquiv n |}.

Definition PrefixLimit := SequentialLimit Prefix (fun n X => X.1).

Definition toPrefixLimit (L': MatchingSeq): PrefixLimit :=
  (fun n => L'.(approx) n leR_O; fun n => L'.(approxS) n leR_O leR_O).

Definition ofPrefixLimit (X: PrefixLimit): MatchingSeq :=
  @limit prefixTelescope 0 tt (fun n Hn => X.1 n)
    (hunit_ext (X.1 0) tt) (fun n Hn HSn => X.2 n).

Lemma ofToPrefixLimit (L': MatchingSeq): ofPrefixLimit (toPrefixLimit L') = L'.
Proof.
  destruct L' as [a o s]. unfold ofPrefixLimit, toPrefixLimit; cbn.
  assert (H: hunit_ext (a 0 leR_O) tt = o) by now apply unit_UIP.
  now destruct H.
Defined.

Lemma toOfPrefixLimit (X: PrefixLimit): toPrefixLimit (ofPrefixLimit X) = X.
Proof. now reflexivity. Defined.

(** The sequence classifies the sequential limit of partial diagrams. *)
Definition matchingSeqEquivDiagramLimit:
  Equiv MatchingSeq
    (SequentialLimit (PartialDiagram Sys) (fun n => @truncate Sys n)) :=
  compEquiv
    (qinvEquiv toPrefixLimit ofPrefixLimit ofToPrefixLimit toOfPrefixLimit)
    (sequentialLimitEquiv (fun n X => X.1) (fun n => @truncate Sys n)
      prefixEquivDiagram
      (fun n X => eq_sym (L.(truncateExtend) _ _))).

End Classification.
End Sequence.

Arguments MatchingSeq : clear implicits.
Arguments ExtensionLaws : clear implicits.
Arguments matchingSeqEquivDiagramLimit : clear implicits.

Record MatchingSystem := {
  matchingStages :> DiagramStages;
  Cell: Type;
  CellMap: Cell -> Cell -> Type;
  CellFamily: Cell -> Type;
  familyTotal {B}: CellFamily B -> {T: Cell &T CellMap T B};
  Matching {n}: PartialDiagram matchingStages n -> Cell;
  extendByMap {n} (X: PartialDiagram matchingStages n) (T: Cell):
    CellMap T (Matching X) -> PartialDiagram matchingStages (S n);
}.

Arguments Cell : clear implicits.
Arguments CellMap : clear implicits.
Arguments CellFamily : clear implicits.
Arguments familyTotal {_ _} _.
Arguments Matching {_ _} _.
Arguments extendByMap {_ _} _ _ _.

Section MatchingSystems.
Context (M: MatchingSystem).

Definition matchingExtensionSystem: ExtensionSystem := {|
  stages := M;
  FillerData n X := CellFamily M (Matching X);
  extendDiagram n X E := let m := familyTotal E in extendByMap X m.1 m.2;
|}.

(** A diagram below [n] with a candidate next level and its matching map. *)
Definition ExtensionData n: Type :=
  {X: PartialDiagram M n &T {T: Cell M &T CellMap M T (Matching X)}}.

Definition joinExtension {n} (z: ExtensionData n): PartialDiagram M (S n) :=
  extendByMap z.1 z.2.1 z.2.2.

Record MatchingSystemLaws := {
  familyTotalIsEquiv B: IsEquiv (@familyTotal M B);
  matchingEmptyEq (X: PartialDiagram M 0): emptyPartial M = X;
  joinExtensionIsEquiv n: IsEquiv (@joinExtension n);
  matchingTruncateExtend {n} (X: PartialDiagram M n) T (b: CellMap M T (Matching X)):
    truncate (extendByMap X T b) = X;
}.

Definition matchingExtensionLaws (L: MatchingSystemLaws):
  ExtensionLaws matchingExtensionSystem.
Proof.
  refine (Build_ExtensionLaws matchingExtensionSystem L.(matchingEmptyEq) _
    (fun n X E => L.(matchingTruncateExtend) X _ _)).
  intro n.
  now exact (compEquiv
    (sigTEquivSnd (fun X: PartialDiagram M n =>
      {| eqvFun := @familyTotal M (Matching X);
        eqvIsEquiv := L.(familyTotalIsEquiv) _ |}))
    {| eqvFun := @joinExtension n;
      eqvIsEquiv := L.(joinExtensionIsEquiv) n |}).(eqvIsEquiv).
Defined.

End MatchingSystems.

Coercion matchingExtensionSystem: MatchingSystem >-> ExtensionSystem.

Arguments joinExtension {_ _} _.
Arguments MatchingSystemLaws : clear implicits.
