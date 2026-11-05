(** Extension of ν-shape diagrams by a matching map with latching lifts loses
    no information. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat.
From Bonak.Lib Require Import HSet SigT Equiv RewLemmas Univalence FinitePrefix.
From Bonak.Category Require Import CategoryEq.
From Bonak.Presheaf.Dgn Require Import Generators.
From Bonak.Reedy.Dgn Require Import Reedy ShapeAction.

Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.

Section Classification.
Context (A: HSet).

Local Lemma rewArrow {n} {C D: Index n -> HSet} (p: C = D)
  (i j: Index n) (r: C j -> C i) (x: D j):
  (rew [fun C: Index n -> HSet => C j -> C i] p in r) x =
  rew [fun C => (C i).(Dom)] p in
    r (rew [fun C => (C j).(Dom)] (eq_sym p) in x).
Proof. now destruct p. Defined.

Lemma diagramEqPointwise {n} (X Y: Diagram A n)
  (p: forall i, cells X i = cells Y i)
  (q: forall i j (f: Shape A (rank i) (rank j)) (x: cells Y j),
    rew [Dom] (p i) in act X f (rew [Dom] (eq_sym (p j)) in x) = act Y f x): X = Y.
Proof.
  apply (functorEq X Y (functional_extensionality_dep_good _ _ p)).
  intros j i f.
  change ((rew [fun C: Index n -> HSet => C j -> C i]
    (functional_extensionality_dep_good _ _ p) in @act A n X i j f) = @act A n Y i j f).
  apply functional_extensionality; intro x.
  rewrite rewArrow.
  rewrite (rew_map Dom (fun C: Index n -> HSet => C i)).
  rewrite (rew_map Dom (fun C: Index n -> HSet => C j)).
  rewrite <- eq_sym_f_equal.
  rewrite (f_equal__functional_extensionality_dep_good p i).
  rewrite (f_equal__functional_extensionality_dep_good p j).
  now apply q.
Defined.

Definition matchingMap {n} (X: Diagram A (S n)) (x: cells X None):
  MatchingObject A (truncateDiagram X).
Proof.
  exists (fun i f => act X (i := Some i) (j := None) f x).
  intros i j f g.
  now exact (actComp X (i := Some i) (j := Some j) (k := None) f g x).
Defined.

Definition matchingLifts {n} (X: Diagram A (S n)):
  LatchingLifts A (truncateDiagram X) (cells X None) (matchingMap X).
Proof.
  refine (@Build_LatchingLifts A n (truncateDiagram X) (cells X None) (matchingMap X)
    (fun i d x => act X (i := None) (j := Some i) d x) _ _).
  - intros i d x. apply matchingExt. intros j f.
    now exact (actComp X (i := Some j) (j := None) (k := Some i) f d x).
  - intros i j d f x.
    now exact (actComp X (i := None) (j := Some i) (k := Some j) d f x).
Defined.

Definition LiftedExtension {n} (X: Diagram A n): Type :=
  {m: {T: HSet &T T -> MatchingObject A X} &T LatchingLifts A X m.1 m.2}.

Local Lemma extensionDataEq {n} {X: Diagram A n} {T: HSet}
  {b c: T -> MatchingObject A X} (L: LatchingLifts A X T b)
  (K: LatchingLifts A X T c) (p: b = c)
  (e: forall i d x, L.(lift) i d x = K.(lift) i d x):
  (((T; b); L): LiftedExtension X) = ((T; c); K).
Proof.
  destruct p. apply f_equal. now apply latchingLiftsEq.
Defined.

Definition splitLifted {n} (X: Diagram A (S n)):
  {Y: Diagram A n &T LiftedExtension Y} :=
  (truncateDiagram X; ((cells X None; matchingMap X); matchingLifts X)).

Definition joinLifted {n} (X: {Y: Diagram A n &T LiftedExtension Y}):
  Diagram A (S n) :=
  extendByMatchingMap A X.1 X.2.1.1 X.2.1.2 X.2.2.

Lemma joinSplitExtension {n} (X: Diagram A (S n)):
  joinLifted (splitLifted X) = X.
Proof.
  apply (diagramEqPointwise (joinLifted (splitLifted X)) X
    (fun i => match i with Some _ => eq_refl | None => eq_refl end)).
  intros [i|] [j|] s x.
  - now reflexivity.
  - now reflexivity.
  - now reflexivity.
  - change (extensionNormal A (truncateDiagram X) (matchingLifts X)
      (i := None) (j := None) s x = act X (i := None) (j := None) s x).
    destruct s as [k [r f]].
    destruct (atRank (S n) k (Nat.le_lt_trans _ _ _
      (wordBound r) (@rankLt (S n) None))) as [m em].
    destruct em. unfold extensionNormal.
    rewrite (normalActionFactor (matchingMapCells A (truncateDiagram X) (cells X None))
      (extensionFace A (truncateDiagram X) (matchingMap X))
      (fun i j => extensionMask A (truncateDiagram X) (matchingLifts X) j i) None None m).
    destruct m as [m|].
    + change (act X (i := None) (j := Some m) (shapeMask r)
        (act X (i := Some m) (j := None) (shapeFace f) x) =
        act X (i := None) (j := None) (rank m; (r, f)) x).
      rewrite actComp, shapeFactor. now reflexivity.
    + change (x = act X (i := None) (j := None) (n; (r, f)) x).
      rewrite (wordEndId n r), (wordEndId n f).
      now exact (eq_sym (actId X None x)).
Defined.

Lemma splitJoinExtension {n} (X: {Y: Diagram A n &T LiftedExtension Y}):
  splitLifted (joinLifted X) = X.
Proof.
  destruct X as [X [[T b] L]].
  refine (eq_existT_curried eq_refl _).
  apply extensionDataEq.
  - apply functional_extensionality; intro x.
    apply matchingExt. now intros i f.
  - now intros i d x.
Defined.

Definition extensionEquivDiagram n:
  Equiv {X: Diagram A n &T LiftedExtension X} (Diagram A (S n)) :=
  qinvEquiv joinLifted splitLifted splitJoinExtension joinSplitExtension.

Definition liftedFamilyEquiv {n} (X: Diagram A n):
  Equiv (LiftedFamily A X) (LiftedExtension X) :=
  sigTEquivFst (B := fun m: {T: HSet &T T -> MatchingObject A X} =>
    LatchingLifts A X m.1 m.2) (hsetFamilyMapEquiv (MatchingObject A X)).

Definition dgnLaws: ExtensionLaws (dgnSystem A) :=
  Build_ExtensionLaws (dgnSystem A)
    (fun X => diagramEqPointwise (emptyDiagram A) X
      (fun i => match i with end) (fun i => match i with end))
    (fun n => (compEquiv
      (sigTEquivSnd (fun X: Diagram A n => liftedFamilyEquiv X))
      (extensionEquivDiagram n)).(eqvIsEquiv))
    (fun n X E => eq_refl).

End Classification.
