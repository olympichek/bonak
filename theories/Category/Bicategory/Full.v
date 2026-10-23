(** Reindexing objects leaves the hom-categories and all their operations
    unchanged. The inclusion acts identically on arrows and cells. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Bicategory Require Import Bicategory BicategoryEq.
Set Primitive Projections.
Set Universe Polymorphism.

Definition fullBicategory (B: Bicategory) {A: Type} (o: A -> B.(BObj)):
  Bicategory := {|
  BObj := A;
  BHom a b := B.(BHom) (o a) (o b);
  bid a := B.(bid) (o a);
  bcomp a b c f g := B.(bcomp) f g;
  bwhiskerL a b c f g h α := B.(bwhiskerL) f α;
  bwhiskerR a b c f g α h := B.(bwhiskerR) α h;
  bunitL a b f := B.(bunitL) f;
  bunitR a b f := B.(bunitR) f;
  bassoc a b c d f g h := B.(bassoc) f g h;
  bwhiskerLId a b c f g := B.(bwhiskerLId) f g;
  bwhiskerRId a b c f g := B.(bwhiskerRId) f g;
  bwhiskerLComp a b c f g h i α β := B.(bwhiskerLComp) f α β;
  bwhiskerRComp a b c f g h α β i := B.(bwhiskerRComp) α β i;
  binterchange a b c f g h i α β := B.(binterchange) α β;
  bunitLNat a b f g α := B.(bunitLNat) α;
  bunitRNat a b f g α := B.(bunitRNat) α;
  bassocNatL a b c d f g h i α := B.(bassocNatL) f g α;
  bassocNatR a b c d f g α h i := B.(bassocNatR) α h i;
  bassocNatM a b c d f g h α i := B.(bassocNatM) f α i;
  btriangle a b c f g := B.(btriangle) f g;
  bpentagon a b c d e f g h i := B.(bpentagon) f g h i;
|}.

Definition fullInclusion (B: Bicategory) {A: Type} (o: A -> B.(BObj)):
  BicategoryStructureMap (fullBicategory B o) B.
Proof.
  refine (@Build_BicategoryStructureMap (fullBicategory B o) B o
    (fun a b f => f) (fun a => eq_refl) (fun a b c f g => eq_refl)
    (fun a b f g α => α) _ _ _ _ _ _ _); now reflexivity.
Defined.
