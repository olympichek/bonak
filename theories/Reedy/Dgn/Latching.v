(** Latching cocones are determined by their coordinate-selection maps. *)
Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat.
From Bonak.Lib Require Import HSet SigT Equiv FinitePrefix Notation.
From Bonak.Reedy.Set Require Reedy.
From Bonak.Reedy.Dgn Require Import Reedy ShapeAction.
From Bonak.Presheaf.Dgn Require Import Generators.
Set Primitive Projections.
Set Printing Projections.

Module SemiReedy := Bonak.Reedy.Set.Reedy.

Section Cocones.
Context {A: HSet} {n: nat} (X: Diagram A n) (T: HSet).

Definition maskHomDiagram: SemiReedy.Diagram hunit n.
Proof.
  refine {| SemiReedy.cells i := hpiT (fun _: cells X i => T);
    SemiReedy.restrict i j r h x := h (act X (i := j) (j := i) (shapeMask r) x) |}.
  - intros i h. apply functional_extensionality_dep; intro x.
    change (h (act X (i := i) (j := i) (shapeId (rank i)) x) = h x).
    now rewrite (actId X i x).
  - intros i j k r s h. apply functional_extensionality_dep; intro x.
    change (h (act X (shapeMask s) (act X (shapeMask r) x)) =
      h (act X (shapeMask (wcomp s r)) x)).
    rewrite actComp, shapeMaskComp. now reflexivity.
Defined.

Definition MaskCocone: HSet := SemiReedy.MatchingObject hunit maskHomDiagram.

Definition coconeAction (B: MaskCocone) (i: Index n)
  (d: Shape A n (rank i)): cells X i -> T :=
  boundedShapeFold (fun m r f x => B.1 m r (act X (i := m) (j := i) (shapeFace f) x)) d
    (Nat.le_lt_trans _ _ _ (wordBound (snd d.2)) (rankLt i)).

Lemma coconeActionFactor (B: MaskCocone) (i m: Index n)
  (r: Word hunit (rank m) n) (f: Word A (rank m) (rank i)) (x: cells X i):
  coconeAction B i (rank m; (r, f)) x = B.1 m r (act X (shapeFace f) x).
Proof. unfold coconeAction. now rewrite boundedShapeFoldFactor. Defined.

Lemma coconeActionMask (B: MaskCocone) (i: Index n)
  (r: Word hunit (rank i) n) (x: cells X i):
  coconeAction B i (shapeMask r) x = B.1 i r x.
Proof.
  unfold shapeMask. rewrite coconeActionFactor.
  change (B.1 i r (act X (i := i) (j := i) (shapeId (rank i)) x) = B.1 i r x).
  now rewrite actId.
Defined.

Lemma coconeActionComp (B: MaskCocone) (i j: Index n)
  (d: Shape A n (rank i)) (f: Shape A (rank i) (rank j)) (x: cells X j):
  coconeAction B i d (act X f x) = coconeAction B j (shapeComp d f) x.
Proof.
  destruct d as [p [r u]], f as [q [s v]].
  destruct (atRank n p (Nat.le_lt_trans _ _ _ (wordBound u) (rankLt i))) as [m em].
  destruct em.
  destruct (atRank n q (Nat.le_lt_trans _ _ _ (wordBound s) (rankLt i))) as [l el].
  destruct el.
  rewrite coconeActionFactor.
  rewrite <- (shapeFactor s v) at 1.
  rewrite <- actComp.
  change (B.1 m r (act X (i := m) (j := i) (shapeFace u)
      (act X (i := i) (j := l) (shapeMask s)
        (act X (i := l) (j := j) (shapeFace v) x))) =
    coconeAction B j (shapeComp (rank m; (r, u)) (rank l; (s, v))) x).
  rewrite actComp, shapeCross.
  unfold shapeComp; cbn.
  destruct (cross u s) as [p [a b]].
  destruct (atRank n p (Nat.le_lt_trans _ _ _ (wordBound a) (rankLt m))) as [o eo].
  destruct eo.
  change (B.1 m r (act X (i := m) (j := l) (rank o; (a, b))
      (act X (i := l) (j := j) (shapeFace v) x)) =
    coconeAction B j (rank o; (wcomp r a, wcomp v b)) x).
  rewrite coconeActionFactor.
  rewrite <- (shapeFactor a b), <- actComp.
  change (B.1 m r (act X (i := m) (j := o) (shapeMask a)
      (act X (i := o) (j := l) (shapeFace b)
        (act X (i := l) (j := j) (shapeFace v) x))) =
    B.1 o (wcomp r a) (act X (i := o) (j := j) (shapeFace (wcomp v b)) x)).
  refine (f_equal (fun h => h (act X (shapeFace b) (act X (shapeFace v) x)))
    (B.2 o m a r) • _).
  now rewrite actComp, shapeFaceComp.
Defined.

Definition coconeOfLifts {b: T -> MatchingObject A X}
  (L: LatchingLifts A X T b): MaskCocone.
Proof.
  exists (fun i r => L.(lift) i (shapeMask r)).
  intros i j f g. apply functional_extensionality_dep; intro x.
  change (L.(lift) j (shapeMask g) (act X (shapeMask f) x)
    = L.(lift) i (shapeMask (wcomp g f)) x).
  now rewrite L.(liftComp), shapeMaskComp.
Defined.

Lemma coconeOfLiftsAction {b: T -> MatchingObject A X}
  (L: LatchingLifts A X T b) (i: Index n) (d: Shape A n (rank i)) (x: cells X i):
  coconeAction (coconeOfLifts L) i d x = L.(lift) i d x.
Proof.
  destruct d as [p [r f]].
  destruct (atRank n p (Nat.le_lt_trans _ _ _ (wordBound f) (rankLt i))) as [m em].
  destruct em. rewrite coconeActionFactor.
  change (L.(lift) m (shapeMask r) (act X (shapeFace f) x) = L.(lift) i (rank m; (r, f)) x).
  now rewrite L.(liftComp), shapeFactor.
Defined.

Context (b: T -> MatchingObject A X).
Definition MaskBoundary (B: MaskCocone): Type :=
  forall (i: Index n) (r: Word hunit (rank i) n) (x: cells X i),
    b (B.1 i r x) = latchingBoundary A X (shapeMask r) x.
Definition MaskLifts: Type := {B: MaskCocone &T MaskBoundary B}.

Lemma latchingBoundaryComp (i j: Index n)
  (d: Shape A n (rank i)) (f: Shape A (rank i) (rank j)) (x: cells X j):
  latchingBoundary A X d (act X f x) = latchingBoundary A X (shapeComp d f) x.
Proof.
  apply matchingExt; intros k g.
  change (act X (i := k) (j := i) (shapeComp g d) (act X f x) =
    act X (i := k) (j := j) (shapeComp g (shapeComp d f)) x).
  now rewrite actComp, shapeAssoc.
Defined.

Definition liftsOfMask (B: MaskLifts): LatchingLifts A X T b.
Proof.
  refine {| lift := coconeAction B.1; liftComp := coconeActionComp B.1 |}.
  intros i d x. destruct d as [p [r f]].
  destruct (atRank n p (Nat.le_lt_trans _ _ _ (wordBound f) (rankLt i))) as [m em].
  destruct em. rewrite coconeActionFactor, B.2, latchingBoundaryComp, shapeFactor.
  now reflexivity.
Defined.

Definition maskOfLifts (L: LatchingLifts A X T b): MaskLifts :=
  (coconeOfLifts L; fun i r x => L.(liftBoundary) i (shapeMask r) x).


Definition latchingEquivMask: Equiv (LatchingLifts A X T b) MaskLifts.
Proof.
  refine (qinvEquiv maskOfLifts liftsOfMask _ _).
  - intro L. apply latchingLiftsEq. intros i d x. now apply coconeOfLiftsAction.
  - intros [B h]. unshelve refine (eq_existT_curried _ _).
    + apply SemiReedy.matchingExt; intros i r. apply functional_extensionality_dep; intro x.
      now apply coconeActionMask.
    + repeat (apply functional_extensionality_dep; intro). now apply UIP.
Defined.
End Cocones.
