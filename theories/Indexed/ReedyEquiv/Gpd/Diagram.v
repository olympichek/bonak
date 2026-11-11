(** Completing an indexed prefix by unit fillers and extracting its coherent diagram. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation LeSProp Limit
  TelescopeLimit TelescopeCompletion FinitePrefix NatLemmas RewLemmas.
From Bonak.νGpd Require Import Layer νGpd Pasting.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagram.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presentation Require Import WordAction GeneratorCoherence.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Pseudofunctor.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Face PresheafOfνGpd
  PathAlgebra.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** Canonical coherent diagrams extracted from finite indexed prefixes. *)

Module IndexedDiagramOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Import A.
Module Export Indexed := Faces.
Module Extraction := PresheafOfνGpdOn A Core Faces.

Definition completePrefix {n} (X: (νGpdAt n).(prefix)): νGpds :=
  sequentialToLimit νGpdTel tt (tt; fun x => hunit_ext tt x)
    (completePrefixChain n νGpdTel (fun _ _ _ => gunit) X).

Lemma completionAt {n} (X: (νGpdAt n).(prefix)):
  (completePrefix X).(approx) n leR_O = X.
Proof. now apply completePrefixAt. Defined.

Lemma completionPack {n} (X: (νGpdAt n).(prefix)):
  (νGpdPack n (completePrefix X)).1 = X.
Proof.
  now exact (limitPackPath n (completePrefix X) • completionAt X).
Defined.

Definition prefixCell {n} (X: (νGpdAt (S n)).(prefix)): HGpd :=
  {d: νFrame X.1 & X.2 d}.

Section Diagrams.

Definition indexedDiagram (X: νGpds): PathDiagramFamily (Op (νSemiShape arity)) :=
  toPsfTot arity (Extraction.g X).

Definition unitExtension {n} (X: (νGpdAt n).(prefix)):
  (νGpdAt (S n)).(prefix) := (X; fun _ => gunit).

Lemma completePrefixUnitExtension {n} (X: (νGpdAt n).(prefix)):
  completePrefix (unitExtension X) = completePrefix X.
Proof.
  unfold completePrefix, unitExtension.
  apply f_equal.
  now exact (completePrefixExtend n νGpdTel (fun _ _ _ => gunit) X).
Defined.

Definition unitPrefixProjectionEquiv {n} (X: (νGpdAt n).(prefix)):
  Equiv (prefixCell (unitExtension X)) (νFrame X).
Proof.
  refine (qinvEquiv (fun z => z.1) (fun d => (d; tt)) _ _).
  - now intros [d []].
  - now intro d.
Defined.

Lemma unitProjectionIsEquiv {n} (Y: (νGpdAt (S n)).(prefix))
  (X: (νGpdAt n).(prefix)) (e: Y = unitExtension X):
  IsEquiv (fun z: prefixCell Y => z.1).
Proof. destruct (eq_sym e). now exact (unitPrefixProjectionEquiv X).(eqvIsEquiv). Defined.

Lemma packedUnitPrefix {n} (X: (νGpdAt n).(prefix)):
  (νGpdPack (S n) (completePrefix X)).1 = unitExtension X.
Proof.
  now exact (f_equal (fun Y: νGpds => (νGpdPack (S n) Y).1)
      (eq_sym (completePrefixUnitExtension X))
    • completionPack (unitExtension X)).
Defined.

Definition packedCellProjectionEquiv {n} (X: (νGpdAt n).(prefix)):
  Equiv (prefixCell (νGpdPack (S n) (completePrefix X)).1)
    (νFrame (νGpdPack n (completePrefix X)).1) :=
  {| eqvFun z := z.1;
    eqvIsEquiv := unitProjectionIsEquiv
      (νGpdPack (S n) (completePrefix X)).1 X (packedUnitPrefix X) |}.

End Diagrams.
End IndexedDiagramOn.

Module Type IndexedDiagramSig (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Include IndexedDiagramOn A Core Faces.
End IndexedDiagramSig.
