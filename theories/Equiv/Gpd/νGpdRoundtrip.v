(** The backward round trip of the presheaf groupoid correspondence.

    [fg] compares [f (g X)] with [X] through the levelwise translation
    relation. Its construction is parameterized by the layer structure. *)

From Bonak Require Import νGpd.Layer.
From Bonak.Equiv.Gpd Require PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Positive.

Module νGpdRoundtrip (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Module Export Positive := Positive.Positive A Base Translations.

Definition fg (X: νGpds): νGpdsEquiv (f (g X)) X := Positive.fg X.

End νGpdRoundtrip.
