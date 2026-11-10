(** Isomorphisms of filler families of indexed strict groupoids over a
    prefix path, and the filler paths that structure identity turns them
    into. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT RewLemmas HSet LeSProp Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category.Groupoid Require Import FamilyIdentity.
From Bonak.Equiv.StrictGpd Require Import Tower.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νStrictGpdEquivOn (A: LayerSig) (S: νStrictGpdSig A).
Import A.
Module Export Tower := TowerOn A S.

Definition νFillerEqvType {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA) (EB: νFillerType XB): Type :=
  FamilyIso (rew [νFillerType] e in EA) EB.

Definition νFillerEq {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (iso: νFillerEqvType e EA EB): rew [νFillerType] e in EA = EB := familyEq iso.

End νStrictGpdEquivOn.

Module νStrictGpdEquiv (A: LayerSig).
Module Base := νStrictGpd.νStrictGpd A.
Include νStrictGpdEquivOn A Base.
End νStrictGpdEquiv.

Module νStrictGpdEquivSimplicial := νStrictGpdEquivOn SimplicialLayer νStrictGpdSimplicial.
Module νStrictGpdEquivCubical := νStrictGpdEquivOn CubicalLayer νStrictGpdCubical.
