(** The correspondence between presheaf groupoids and ν-groupoids

    [f] and [g] are mutually inverse up to the two levelwise equivalences
    [gf] and [fg]; each is converted into an equality of the two structures
    ([presheafEquivEq], [νGpdsEquivEq]), and univalence turns the
    resulting quasi-inverse pair into an equality of the two types. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation νGpd.Layer Univalence.
From Bonak.Lib Require Import Equiv.
From Bonak.Presheaf.Gpd Require Import Presentation.
From Bonak Require Equiv.Gpd.νGpdRoundtrip.
From Bonak.Equiv.Gpd Require PresheafOfνGpd νGpdEquiv PresheafRoundtrip
  Extensionality.

Set Primitive Projections.
Set Keyed Unification.

Module Correspondence (A: LayerGpdSig).
Import A.

Module Export Base := PresheafOfνGpd.PresheafOfνGpd A.
Module Translations := νGpdEquiv.νGpdEquiv A Base.
Module Export PresheafRoundtrip := PresheafRoundtrip.PresheafRoundtrip A Base.
Module Extensionality := Extensionality.Extensionality A Base Translations.
Module Export IndexedRoundtrip := νGpdRoundtrip.νGpdRoundtrip A Base Translations.

Definition presheafνGpdsEquiv: Equiv (νGpdPresentation arity) νGpds :=
  qinvEquiv f g
    (fun psh => presheafEquivEq (PresheafRoundtrip.gf psh))
    (fun X => Extensionality.νGpdsEquivEq (IndexedRoundtrip.fg X)).

Definition presheafEqνGpds: νGpdPresentation arity = νGpds := ua presheafνGpdsEquiv.

End Correspondence.

Module CorrespondenceSimplicial := Correspondence SimplicialGpdLayer.
Module CorrespondenceCubical := Correspondence CubicalGpdLayer.
