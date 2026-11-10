(** Full ν-shape boundaries are determined by their face-word values. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.PeanoNat.
From Bonak.Lib Require Import HSet SigT Equiv Notation FinitePrefix.
From Bonak.Presheaf.Dgn Require Import Generators.
From Bonak.Reedy Require Reedy.
From Bonak.Reedy.Dgn Require Import Reedy ShapeAction.

Set Primitive Projections.
Set Printing Projections.

Module SemiReedy := Bonak.Reedy.Reedy.

Section Matching.
Context (A: HSet) {n} (X: Diagram A n).

Definition faceDiagram: SemiReedy.Diagram A n := {|
  SemiReedy.cells i := cells X i;
  SemiReedy.restrict i j f := act X (i := i) (j := j) (shapeFace f);
  SemiReedy.restrictId i := actId X i;
  SemiReedy.restrictComp i j k f g x :=
    actComp X (shapeFace f) (shapeFace g) x
    • f_equal (fun s => act X (i := i) (j := k) s x) (shapeFaceComp f g);
|}.

Definition matchingForget (b: MatchingObject A X):
  SemiReedy.MatchingObject A faceDiagram.
Proof.
  exists (fun i f => b.1 i (shapeFace f)).
  intros i j f g. cbn.
  refine (b.2 i j (shapeFace f) (shapeFace g) • _).
  now rewrite shapeFaceComp.
Defined.

Definition fullValue (b: SemiReedy.MatchingObject A faceDiagram)
  (i: Index n) (s: Shape A (rank i) n): cells X i :=
  boundedShapeFold (fun m r f => act X (i := i) (j := m) (shapeMask r) (b.1 m f)) s
    (Nat.le_lt_trans _ _ _ (wordBound (fst s.2)) (rankLt i)).

Lemma fullValueFactor (b: SemiReedy.MatchingObject A faceDiagram)
  (i m: Index n) (r: Word hunit (rank m) (rank i)) (f: Word A (rank m) n):
  fullValue b i (rank m; (r, f)) =
    act X (i := i) (j := m) (shapeMask r) (b.1 m f).
Proof. unfold fullValue. now rewrite boundedShapeFoldFactor. Defined.

Lemma fullValueComp (b: SemiReedy.MatchingObject A faceDiagram)
  (i j: Index n) (s: Shape A (rank i) (rank j)) (t: Shape A (rank j) n):
  act X s (fullValue b j t) = fullValue b i (shapeComp s t).
Proof.
  destruct s as [p [r f]], t as [q [d g]].
  destruct (atRank n p (Nat.le_lt_trans _ _ _ (wordBound r) (rankLt i))) as [m em].
  destruct em.
  destruct (atRank n q (Nat.le_lt_trans _ _ _ (wordBound d) (rankLt j))) as [l el].
  destruct el.
  rewrite fullValueFactor.
  rewrite <- (shapeFactor r f) at 1.
  rewrite <- (actComp X (shapeMask r) (shapeFace f)).
  rewrite (actComp X (shapeFace f) (shapeMask d)), shapeCross.
  change (act X (i := i) (j := m) (shapeMask r)
    (act X (i := m) (j := l) (cross f d) (b.1 l g)) =
    fullValue b i (shapeSandwich r g (cross f d))).
  destruct (cross f d) as [p [u v]].
  destruct (atRank n p (Nat.le_lt_trans _ _ _ (wordBound u) (rankLt m))) as [o eo].
  destruct eo.
  change (act X (i := i) (j := m) (shapeMask r)
    (act X (i := m) (j := l) (rank o; (u, v)) (b.1 l g)) =
    fullValue b i (rank o; (wcomp r u, wcomp g v))).
  rewrite fullValueFactor.
  rewrite <- (shapeFactor u v), <- actComp.
  change (act X (shapeMask r)
    (act X (shapeMask u)
      ((faceDiagram.(SemiReedy.restrict) v) (b.1 l g))) =
    act X (shapeMask (wcomp r u)) (b.1 o (wcomp g v))).
  rewrite b.2, actComp, shapeMaskComp.
  now reflexivity.
Defined.

Definition matchingExtend (b: SemiReedy.MatchingObject A faceDiagram):
  MatchingObject A X :=
  (fullValue b; fullValueComp b).

Lemma forgetExtend (b: SemiReedy.MatchingObject A faceDiagram):
  matchingForget (matchingExtend b) = b.
Proof.
  apply SemiReedy.matchingExt; intros i f.
  change (fullValue b i (rank i; (wid (rank i), f)) = b.1 i f).
  rewrite fullValueFactor. now apply actId.
Defined.

Lemma extendForget (b: MatchingObject A X):
  matchingExtend (matchingForget b) = b.
Proof.
  apply matchingExt; intros i [k [r f]].
  destruct (atRank n k (Nat.le_lt_trans _ _ _ (wordBound r) (rankLt i))) as [m em].
  destruct em.
  change (fullValue (matchingForget b) i (rank m; (r, f)) = b.1 i (rank m; (r, f))).
  rewrite fullValueFactor.
  change (act X (shapeMask r) (b.1 m (shapeFace f)) = b.1 i (rank m; (r, f))).
  rewrite b.2, shapeFactor. now reflexivity.
Defined.

Definition matchingEquivFace:
  Equiv (MatchingObject A X) (SemiReedy.MatchingObject A faceDiagram) :=
  qinvEquiv matchingForget matchingExtend extendForget forgetExtend.

Lemma matchingExtendFace (b: SemiReedy.MatchingObject A faceDiagram)
  (i: Index n) (f: Word A (rank i) n):
  (matchingExtend b).1 i (shapeFace f) = b.1 i f.
Proof.
  change (fullValue b i (rank i; (wid (rank i), f)) = b.1 i f).
  rewrite fullValueFactor. now apply actId.
Defined.

End Matching.
