(** Shared face operations and the two presentation translations.
    The module fields fix the same inductive chain types for both maps. *)
Set Warnings "-notation-overridden".
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Equiv.StrictGpd Require Import
  Face νStrictGpdOfPresheaf PresheafOfνStrictGpd.

Module Type ConstructionsSig (A: LayerSig) (S: νStrictGpdSig A).
Module Core := S.
Declare Module Faces: FaceSig A S.
Declare Module Reconstruction: ReconstructionSig A S Faces.
Declare Module Extraction: ExtractionSig A S Faces.
Export Core Faces Reconstruction Extraction.
End ConstructionsSig.

Module ConstructionsOn (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S) (R: ReconstructionSig A S F) (E: ExtractionSig A S F).
Module Export Core := S.
Module Export Faces := F.
Module Export Reconstruction := R.
Module Export Extraction := E.
End ConstructionsOn.

Module Constructions (A: LayerSig).
Module Instance := νStrictGpd.νStrictGpd A.
Module FaceOperations := FaceOn A Instance.
Module Reconstruct := νStrictGpdOfPresheafOn A Instance FaceOperations.
Module Extract := PresheafOfνStrictGpdOn A Instance FaceOperations.
Include ConstructionsOn A Instance FaceOperations Reconstruct Extract.
End Constructions.

Module ConstructionsSimplicial :=
  ConstructionsOn SimplicialLayer νStrictGpdSimplicial FaceSimplicial
    νStrictGpdOfPresheafSimplicial PresheafOfνStrictGpdSimplicial.
Module ConstructionsCubical :=
  ConstructionsOn CubicalLayer νStrictGpdCubical FaceCubical
    νStrictGpdOfPresheafCubical PresheafOfνStrictGpdCubical.
