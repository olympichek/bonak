(** Generating faces of the semi-shape category, indexed by their depth:
    the number of positions a face keeps before the one it skips. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Presheaf Require Import νSemiShape.

Set Primitive Projections.
Set Printing Projections.

Record FaceDepth {P: nat} := { depth: nat; depthBound: depth <= P }.
Arguments FaceDepth P : clear implicits.

Lemma depthEq {P} (i j: FaceDepth P): depth i = depth j -> i = j.
Proof. destruct i,j; cbn; intro e; destruct e; now reflexivity. Qed.
Definition firstDepth P: FaceDepth P := {| depth := 0; depthBound := leR_O |}.
Definition nextDepth {P} (i: FaceDepth P): FaceDepth P.+1 :=
  {| depth := (depth i).+1; depthBound := ⇑ (depthBound i) |}.
Definition weakenDepth {n} (i: FaceDepth n): FaceDepth n.+1 :=
  {| depth := depth i; depthBound := ↑ (depthBound i) |}.

Section FaceWords.
Context (A: HSet).

Fixpoint depthFaceWord n: FaceDepth n -> A -> Word A n n.+1.
Proof.
  destruct n as [|n]; intros [j h] a.
  - now exact (wskip a wnil).
  - destruct j as [|j].
    + now exact (wskip a (wid n.+1)).
    + now exact (wkeep (depthFaceWord n {| depth := j; depthBound := ⇓ h |} a)).
Defined.

Lemma depthFaceFirst n a:
  depthFaceWord n (firstDepth n) a = wskip a (wid n).
Proof. destruct n; now reflexivity. Qed.

Lemma depthFaceNext n i a:
  depthFaceWord n.+1 (nextDepth i) a = wkeep (depthFaceWord n i a).
Proof. destruct i; now reflexivity. Qed.

End FaceWords.
