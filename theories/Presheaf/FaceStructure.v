(** Face maps on arbitrary type families indexed by dimension, with the
    exchange law. No truncation of the levels is assumed. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
Set Primitive Projections.
Set Printing Projections.

Section FaceStructure.

Record FaceStr := {
  S0: nat -> Type;
  SFace n q (Hq: q <= n): S0 (S n) -> S0 n;
}.

Definition shiftStr (Q: FaceStr): FaceStr := {|
  S0 n := Q.(S0) (S n);
  SFace n q Hq := Q.(SFace) (S n) q (↑ Hq);
|}.

(** The top face at level [n]: the one deleting position [n]. *)

Definition sTop (Q: FaceStr) (n: nat): Q.(S0) (S n) -> Q.(S0) n :=
  Q.(SFace) n n leR_refl.

End FaceStructure.

Definition CohOf (Q: FaceStr): Type :=
  forall n q (Hq: q <= n) r (Hr: r <= q) (X: Q.(S0) (S (S n))),
    Q.(SFace) n q Hq (Q.(SFace) (S n) r (Hr ↕ (↑ Hq)) X) =
    Q.(SFace) n r (Hr ↕ Hq) (Q.(SFace) (S n) (S q) (⇑ Hq) X).

Definition cohShift {Q: FaceStr} (H: CohOf Q): CohOf (shiftStr Q) :=
  fun n q Hq r Hr X => H (S n) q (↑ Hq) r Hr X.

(** Exchanging a face with the top face preserves the index of the other
    face. *)

Definition topCoh {Q: FaceStr} (H: CohOf Q):
  forall k q (Hq: q <= k) (X: Q.(S0) (S (S k))),
    sTop Q k (Q.(SFace) (S k) q (↑ Hq) X)
    = Q.(SFace) k q Hq (sTop Q (S k) X) :=
  fun k q Hq X => H k k leR_refl q Hq X.
