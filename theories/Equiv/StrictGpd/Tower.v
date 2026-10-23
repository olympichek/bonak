(** Finite tower data of indexed strict groupoids. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module TowerOn (A: LayerSig) (S: νStrictGpdSig A).
Import A.
Module Export Core := S.

Definition νDataAt {m} (Xpre: (νStrictGpdAt m).(prefix)): νStrictGpdData m :=
  (νStrictGpdAt m).(data) Xpre.

Definition νTowerDeps {n} (Xpre: (νStrictGpdAt n).(prefix)): DepsRestr n 0 :=
  toDepsRestr (νDataAt Xpre).(restrFrames).

Definition νFrame {n} (Xpre: (νStrictGpdAt n).(prefix)): HSetGroupoid :=
  mkFrame (νTowerDeps Xpre).

Definition νFillerType {n} (Xpre: (νStrictGpdAt n).(prefix)): Type := Family (νFrame Xpre).

Definition prefixDepsCohs {n} (Xp: (νStrictGpdAt n.+1).(prefix)): DepsCohs n 0 := {|
  _deps := νTowerDeps Xp.1;
  _extraDeps := TopRestrDep Xp.2;
  _restrPaintings := (νDataAt Xp.1).(restrPaintings) Xp.2;
  _cohs := (νDataAt Xp.1).(cohFrames) Xp.2;
|}.

Definition νTotalGpd {n} (Xp: (νStrictGpdAt n.+1).(prefix)): HSetGroupoid := total Xp.2.

Definition νStrictGpdPack (m: nat) (X: νStrictGpds):
  {Xp: (νStrictGpdAt m).(prefix) &T νStrictGpdFrom m Xp} := limitPack m X.

End TowerOn.

Module Tower (A: LayerSig).
Module Source := νStrictGpd.νStrictGpd A.
Include TowerOn A Source.
End Tower.

Module TowerSimplicial := TowerOn SimplicialLayer νStrictGpdSimplicial.
Module TowerCubical := TowerOn CubicalLayer νStrictGpdCubical.
