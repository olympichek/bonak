(** The backward round trip of the presheaf groupoid correspondence.

    [fg] compares [f (g X)] with [X] through the levelwise translation
    relation. Its construction is parameterized by the layer structure. *)

From Bonak Require Import νGpd.Layer νGpd.
From Bonak.Equiv.Gpd Require Constructions νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Positive.

Module νGpdRoundtrip (A: LayerGpdSig) (S: νGpdSig A)
  (Base: Constructions.ConstructionsSig A S)
  (Translations: νGpdEquiv.TranslationSig A S).
Module Export Positive := Positive.Positive A S Base Translations.

Definition fg (X: νGpds): νGpdsEquiv (f (g X)) X := Positive.fg X.

End νGpdRoundtrip.
