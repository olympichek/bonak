(** Indexed strict groupoids and face presentations.

    The two round trips identify strict graph fibers and their total
    groupoids by structure isomorphisms. Univalence turns those
    isomorphisms into paths and the resulting equivalences into equalities
    of the two types. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Equiv Univalence.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Presheaf.StrictGpd Require Import Presentation.
From Bonak.Equiv.StrictGpd Require Import Constructions PresheafEquiv
  νStrictGpdRoundtrip PresheafRoundtrip.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

(** The correspondence fixes the reconstruction and extraction maps. *)
Module Type CorrespondenceSig (A: LayerSig) (S: νStrictGpdSig A)
  (Base: ConstructionsSig A S).
  Parameter presentationRoundtrip: forall P,
    Base.Extraction.g (Base.Reconstruction.f P) = P.
  Parameter indexedRoundtrip: forall X,
    Base.Reconstruction.f (Base.Extraction.g X) = X.
  Definition presheafνStrictGpdsEquiv: Equiv (νStrictGpdPresentation A.arity) S.νStrictGpds :=
    qinvEquiv Base.Reconstruction.f Base.Extraction.g
      presentationRoundtrip indexedRoundtrip.
End CorrespondenceSig.

Module CorrespondenceOn (A: LayerSig) (S: νStrictGpdSig A)
  (Base: ConstructionsSig A S) <: CorrespondenceSig A S Base.
Import A.
Import S Base.Faces Base.Reconstruction Base.Extraction.
Module Export IndexedRoundtrip := νStrictGpdRoundtripOn A S Base.
Module Export PresentationRoundtrip := PresheafRoundtripOn A S Base.

Definition presentationRoundtrip (P: νStrictGpdPresentation arity): g (f P) = P :=
  eq_sym (presheafIsoEq (gf P)).

Definition indexedRoundtrip (X: νStrictGpds): f (g X) = X := νStrictGpdsEquivEq (fg X).

Definition presheafνStrictGpdsEquiv: Equiv (νStrictGpdPresentation arity) νStrictGpds :=
  qinvEquiv f g presentationRoundtrip indexedRoundtrip.

Definition presheafEqνStrictGpds: νStrictGpdPresentation arity = νStrictGpds :=
  ua presheafνStrictGpdsEquiv.

End CorrespondenceOn.

Module Correspondence (A: LayerSig).
Module Maps := Constructions A.
Include CorrespondenceOn A Maps.Core Maps.
End Correspondence.

Module CorrespondenceSimplicial :=
  CorrespondenceOn SimplicialLayer νStrictGpdSimplicial ConstructionsSimplicial.
Module CorrespondenceCubical :=
  CorrespondenceOn CubicalLayer νStrictGpdCubical ConstructionsCubical.
