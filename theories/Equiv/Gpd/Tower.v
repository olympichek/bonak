(** Finite prefixes, filler families, and unfoldings of ν-groupoids. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp Notation Limit νGpd.HGpd νGpd.Layer νGpd.

Set Primitive Projections.
Set Keyed Unification.

Module Tower (A: LayerGpdSig).
Import A.

Module Export νGpd := νGpd.νGpd A.

Definition νDataAt {m} (Xpre: (νGpdAt m).(prefix)): νGpdData m :=
  (νGpdAt m).(data) Xpre.

Definition νTowerDeps {n} (Xpre: (νGpdAt n).(prefix)): DepsRestr n 0 :=
  toDepsRestr (νDataAt Xpre).(restrFrames).

(** The full frame at a prefix, and the filler-family type over it. The
    [this] field of [νGpdFrom n Xpre] has type [νFillerType Xpre], and the
    prefix one level up is [{Xpre &T νFillerType Xpre}], both definitionally.
    [νFrameDom] is the [Type]-valued version used as a transport motive. *)

Definition νFrame {n} (Xpre: (νGpdAt n).(prefix)): HGpd :=
  mkFrame (νTowerDeps Xpre).

Definition νFrameDom {n} (Xpre: (νGpdAt n).(prefix)): Type := νFrame Xpre.

Definition νFillerType {n} (Xpre: (νGpdAt n).(prefix)): Type :=
  νFrame Xpre -> HGpd.

(** Finite unfoldings of a tower

    The [m]-step unfolding of a νGpd: the reached prefix, packed with the
    remaining tower so the recursion needs no arithmetic. *)

Fixpoint νGpdPack (m: nat) (S: νGpds):
  {Xp: (νGpdAt m).(prefix) &T νGpdFrom m Xp} :=
  match m with
  | 0 => (tt; S)
  | S m => (((νGpdPack m S).1; this ((νGpdPack m S).2));
            next ((νGpdPack m S).2))
  end.

End Tower.
