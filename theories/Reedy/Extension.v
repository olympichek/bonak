(** Extension of h-set diagrams by a matching map loses no information. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Equiv RewLemmas Univalence FinitePrefix.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy Require Import Reedy.

Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.

Section Classification.
Context (A: HSet).

Local Definition Restriction {n} (C: Index n -> HSet) :=
  forall i j, Word A (rank i) (rank j) -> C j -> C i.

Lemma diagramEq {n} (X Y: Diagram A n) (p: X.(cells) = Y.(cells))
  (q: rew [@Restriction n] p in @restrict A n X = @restrict A n Y): X = Y.
Proof.
  destruct X as [C r u v], Y as [C' r' u' v']; cbn in p, q.
  destruct p, q.
  assert (eu: u = u').
  { repeat (apply functional_extensionality_dep; intro).
    now apply UIP. }
  destruct eu.
  assert (ev: v = v').
  { repeat (apply functional_extensionality_dep; intro).
    now apply UIP. }
  now destruct ev.
Defined.

Local Lemma rewRestriction {n} {C D: Index n -> HSet} (p: C = D)
  (r: Restriction C) (i j: Index n) (f: Word A (rank i) (rank j)) (x: D j):
  (rew [@Restriction n] p in r) i j f x =
  rew [fun C => (C i).(Dom)] p in
    r i j f (rew [fun C => (C j).(Dom)] (eq_sym p) in x).
Proof. now destruct p. Defined.

Lemma diagramEqPointwise {n} (X Y: Diagram A n)
  (p: forall i, X.(cells) i = Y.(cells) i)
  (q: forall i j (f: Word A (rank i) (rank j)) (x: Y.(cells) j),
    rew [Dom] (p i) in
      X.(restrict) f (rew [Dom] (eq_sym (p j)) in x) = Y.(restrict) f x): X = Y.
Proof.
  apply (diagramEq X Y (functional_extensionality_dep_good _ _ p)).
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply functional_extensionality_dep; intro f.
  apply functional_extensionality_dep; intro x.
  rewrite rewRestriction.
  rewrite (rew_map Dom (fun C: Index n -> HSet => C i)).
  rewrite (rew_map Dom (fun C: Index n -> HSet => C j)).
  rewrite <- eq_sym_f_equal.
  rewrite (f_equal__functional_extensionality_dep_good p i).
  rewrite (f_equal__functional_extensionality_dep_good p j).
  now apply q.
Defined.

Definition matchingMap {n} (X: Diagram A (S n)) (x: X.(cells) None):
  MatchingObject A (truncateDiagram A X).
Proof.
  exists (fun i f => X.(restrict) (i := Some i) (j := None) f x).
  intros i j f g.
  now exact (X.(restrictComp) (i := Some i) (j := Some j) (k := None) f g x).
Defined.

Definition splitExtension {n} (X: Diagram A (S n)): ExtensionData (hsetSystem A) n :=
  (truncateDiagram A X; (X.(cells) None; matchingMap X)).

Lemma joinSplitExtension {n} (X: Diagram A (S n)):
  extendByMatchingMap A (truncateDiagram A X) (X.(cells) None) (matchingMap X) = X.
Proof.
  apply (diagramEqPointwise
    (extendByMatchingMap A (truncateDiagram A X) (X.(cells) None) (matchingMap X)) X
    (fun i => match i with Some _ => eq_refl | None => eq_refl end)).
  intros [i|] [j|] f x; cbn [extendByMatchingMap matchingMapCells
    matchingMapRestrict matchingMap truncateDiagram].
  - now reflexivity.
  - now reflexivity.
  - now wordAboveAbsurd.
  - rewrite (wordEndId n f). now symmetry; apply X.(restrictId).
Defined.

Lemma splitJoinExtension {n} (X: ExtensionData (hsetSystem A) n):
  splitExtension (joinExtension X) = X.
Proof.
  destruct X as [X [T b]].
  refine (eq_existT_curried eq_refl _).
  refine (eq_existT_curried eq_refl _).
  apply functional_extensionality; intro x.
  apply matchingExt. now intros i f.
Defined.

Definition hsetLaws: MatchingSystemLaws (hsetSystem A) :=
  Build_MatchingSystemLaws (hsetSystem A)
    (fun B: HSet => (hsetFamilyMapEquiv B).(eqvIsEquiv))
    (fun X => diagramEqPointwise (emptyDiagram A) X
      (fun i => match i with end) (fun i => match i with end))
    (fun n => (qinvEquiv (joinExtension (M := hsetSystem A) (n := n))
      splitExtension splitJoinExtension joinSplitExtension).(eqvIsEquiv))
    (fun n X T b => eq_refl).

End Classification.
