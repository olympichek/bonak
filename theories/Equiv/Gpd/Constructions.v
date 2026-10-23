(** Shared face operations and the two presentation translations. *)

From Bonak Require Import νGpd.Layer νGpd.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd.

Module Type ConstructionsSig (A: LayerGpdSig) (S: νGpdSig A).
Module Core := S.
Declare Module Faces: FaceSig A S.
Declare Module Reconstruction: ReconstructionSig A S Faces.
Declare Module Extraction: ExtractionSig A S Faces.
Export Core Faces Reconstruction Extraction.
End ConstructionsSig.

Module ConstructionsOn (A: LayerGpdSig) (S: νGpdSig A)
  (F: FaceSig A S) (R: ReconstructionSig A S F)
  (E: ExtractionSig A S F).
Module Export Core := S.
Module Export Faces := F.
Module Export Reconstruction := R.
Module Export Extraction := E.
End ConstructionsOn.

Module Constructions (A: LayerGpdSig).
Module Source := νGpd.νGpd A.
Module FaceOperations := FaceOn A Source.
Module Reconstruct := νGpdOfPresheafOn A Source FaceOperations.
Module Extract := PresheafOfνGpdOn A Source FaceOperations.
Include ConstructionsOn A Source FaceOperations Reconstruct Extract.
End Constructions.

Module ConstructionsSimplicial :=
  ConstructionsOn SimplicialGpdLayer νGpdSimplicial FaceSimplicial
    νGpdOfPresheafSimplicial PresheafOfνGpdSimplicial.
Module ConstructionsCubical :=
  ConstructionsOn CubicalGpdLayer νGpdCubical FaceCubical
    νGpdOfPresheafCubical PresheafOfνGpdCubical.
