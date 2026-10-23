(** The correspondence between presheaf groupoids and ν-groupoids

    [f] and [g] are mutually inverse up to the two levelwise equivalences
    [gf] and [fg]; each is converted into an equality of the two structures
    ([presheafEquivEq], [νGpdsEquivEq]), and univalence turns the
    resulting quasi-inverse pair into an equality of the two types. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation νGpd.Layer νGpd Univalence.
From Bonak.Lib Require Import Equiv.
From Bonak.Presheaf.Gpd Require Import Presentation.
From Bonak Require Equiv.Gpd.νGpdRoundtrip.
From Bonak.Equiv.Gpd Require Constructions νGpdEquiv PresheafRoundtrip
  Extensionality.

Set Primitive Projections.
Set Keyed Unification.

(** The correspondence fixes the reconstruction and extraction maps. *)
Module Type CorrespondenceSig (A: LayerGpdSig) (S: νGpdSig A)
  (Base: Constructions.ConstructionsSig A S).
  Parameter presentationRoundtrip: forall P,
    Base.Extraction.g (Base.Reconstruction.f P) = P.
  Parameter indexedRoundtrip: forall X,
    Base.Reconstruction.f (Base.Extraction.g X) = X.
  Definition presheafνGpdsEquiv: Equiv (νGpdPresentation A.arity) S.νGpds :=
    qinvEquiv Base.Reconstruction.f Base.Extraction.g
      presentationRoundtrip indexedRoundtrip.
End CorrespondenceSig.

Module CorrespondenceOn (A: LayerGpdSig) (S: νGpdSig A)
  (Base: Constructions.ConstructionsSig A S) <: CorrespondenceSig A S Base.
Import A.

Import S Base.Faces Base.Reconstruction Base.Extraction.
Module Translations := νGpdEquiv.νGpdEquiv A S.
Module Export PresheafRoundtrip := PresheafRoundtrip.PresheafRoundtrip A S Base.
Module Extensionality := Extensionality.Extensionality A S Translations.
Module Export IndexedRoundtrip := νGpdRoundtrip.νGpdRoundtrip A S Base Translations.

Definition presentationRoundtrip (P: νGpdPresentation arity): g (f P) = P :=
  presheafEquivEq (PresheafRoundtrip.gf P).

Definition indexedRoundtrip (X: νGpds): f (g X) = X :=
  Extensionality.νGpdsEquivEq (IndexedRoundtrip.fg X).

Definition presheafνGpdsEquiv: Equiv (νGpdPresentation arity) νGpds :=
  qinvEquiv f g presentationRoundtrip indexedRoundtrip.

Definition presheafEqνGpds: νGpdPresentation arity = νGpds := ua presheafνGpdsEquiv.

End CorrespondenceOn.

Module Correspondence (A: LayerGpdSig).
Module Maps := Constructions.Constructions A.
Include CorrespondenceOn A Maps.Core Maps.
End Correspondence.

Module CorrespondenceSimplicial :=
  CorrespondenceOn SimplicialGpdLayer νGpdSimplicial Constructions.ConstructionsSimplicial.
Module CorrespondenceCubical :=
  CorrespondenceOn CubicalGpdLayer νGpdCubical Constructions.ConstructionsCubical.

