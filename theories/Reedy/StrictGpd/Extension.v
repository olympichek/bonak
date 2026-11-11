(** Extension of strict groupoid diagrams by a matching functor loses no
    information. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Equiv FinitePrefix.
From Bonak.Category.Groupoid Require Import GraphFiberRoundtrip FamilyIdentity.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.StrictGpd Require Import Reedy.

Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.

Section Classification.
Context (A: HSet).

Local Definition Restriction {n} (C: Index n -> StrictGroupoid) :=
  forall i j, Word A (rank i) (rank j) -> Functor (C j) (C i).

Lemma diagramEq {n} (X Y: Diagram A n) (p: X.(cells) = Y.(cells))
  (q: rew [@Restriction n] p in @restrict A n X = @restrict A n Y): X = Y.
Proof.
  destruct X as [C r u v], Y as [C' r' u' v']; cbn in p, q.
  destruct p, q.
  assert (eu: u = u').
  { apply functional_extensionality_dep; intro i.
    now apply (strictGroupoidFunctorSet (C i) (C i)).(UIP). }
  destruct eu.
  assert (ev: v = v').
  { repeat (apply functional_extensionality_dep; intro).
    now apply (strictGroupoidFunctorSet _ _).(UIP). }
  now destruct ev.
Defined.

Local Lemma rewRestriction {n} {C D: Index n -> StrictGroupoid} (p: C = D)
  (r: Restriction C) (i j: Index n) (f: Word A (rank i) (rank j)):
  (rew [@Restriction n] p in r) i j f =
    transportGroupoidFunctor (eq_sym (f_equal (fun C => C j) p)) ⨟ᶠ
    r i j f ⨟ᶠ transportGroupoidFunctor (f_equal (fun C => C i) p).
Proof.
  destruct p. apply (functorEqPath (C i).(groupoidStrictness)).
  unshelve econstructor; now intros.
Defined.

Lemma diagramEqPointwise {n} (X Y: Diagram A n)
  (p: forall i, X.(cells) i = Y.(cells) i)
  (q: forall i j (f: Word A (rank i) (rank j)),
    transportGroupoidFunctor (eq_sym (p j)) ⨟ᶠ X.(restrict) f ⨟ᶠ
      transportGroupoidFunctor (p i) = Y.(restrict) f): X = Y.
Proof.
  apply (diagramEq X Y (functional_extensionality_dep_good _ _ p)).
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply functional_extensionality_dep; intro f.
  rewrite rewRestriction.
  rewrite (f_equal__functional_extensionality_dep_good p i).
  rewrite (f_equal__functional_extensionality_dep_good p j).
  now apply q.
Defined.

Definition matchingMapObj {n} (X: Diagram A (S n)) (x: X.(cells) None):
  MatchingBoundary A (truncateDiagram A X).
Proof.
  exists (fun i f => (X.(restrict) (i := Some i) (j := None) f).(fobj) x).
  intros i j f g.
  now exact ((pathFunctorEq
    (X.(restrictComp) (i := Some i) (j := Some j) (k := None) f g)).(objEq) x).
Defined.

Definition matchingMapHom {n} (X: Diagram A (S n)) {x y: X.(cells) None}
  (h: (X.(cells) None).(CHom) x y):
  MatchingHom A (matchingMapObj X x) (matchingMapObj X y).
Proof.
  exists (fun i f => (X.(restrict) (i := Some i) (j := None) f).(fhom) h).
  intros i j f g.
  now exact ((pathFunctorEq
    (X.(restrictComp) (i := Some i) (j := Some j) (k := None) f g)).(homEq) x y h).
Defined.

Definition matchingMap {n} (X: Diagram A (S n)):
  Functor (X.(cells) None) (MatchingObject A (truncateDiagram A X)).
Proof.
  refine {| fobj := matchingMapObj X; fhom x y := matchingMapHom X |}.
  - intro x. apply matchingHomExt. intros i f.
    now apply ((X.(restrict) (i := Some i) (j := None) f).(fid)).
  - intros x y z h k. apply matchingHomExt. intros i f.
    now apply ((X.(restrict) (i := Some i) (j := None) f).(fcomp)).
Defined.

Definition splitExtension {n} (X: Diagram A (S n)): ExtensionData (strictGpdSystem A) n :=
  (truncateDiagram A X; (X.(cells) None; matchingMap X)).

Lemma joinSplitExtension {n} (X: Diagram A (S n)):
  joinExtension (splitExtension X) = X.
Proof.
  apply (diagramEqPointwise (joinExtension (splitExtension X)) X
    (fun i => match i with Some _ => eq_refl | None => eq_refl end)).
  intros [i|] [j|] f; cbn [transportGroupoidFunctor].
  - apply (functorEqPath (X.(cells) (Some i)).(groupoidStrictness)).
    unshelve econstructor; now intros.
  - apply (functorEqPath (X.(cells) (Some i)).(groupoidStrictness)).
    unshelve econstructor; now intros.
  - now wordAboveAbsurd.
  - change (idFunctor (X.(cells) None) = X.(restrict) (i := None) (j := None) f).
    rewrite (wordEndId n f). now symmetry; apply X.(restrictId).
Defined.

Lemma matchingFunctorEq {n} {X: Diagram A n} {G: StrictGroupoid}
  (p q: Functor G (MatchingObject A X))
  (h: forall i f, p ⨟ᶠ matchingProjection A X i f = q ⨟ᶠ matchingProjection A X i f):
  p = q.
Proof.
  apply (functorEqPath (MatchingObject A X).(groupoidStrictness)).
  pose (e := fun x => matchingBoundaryExt A (p.(fobj) x) (q.(fobj) x)
    (fun i f => (pathFunctorEq (h i f)).(objEq) x)).
  refine (Build_FunctorEq e _).
  intros x y a. apply matchingHomExt. intros i f.
  change ((matchingProjection A X i f).(fhom)
    (a := q.(fobj) x) (b := q.(fobj) y)
    (castArrow (G := MatchingObject A X) (e x) (e y) (p.(fhom) a)) =
    (q.(fhom) a).1 i f).
  rewrite mapCastArrow.
  match goal with |- castArrow ?e ?d _ = _ =>
    rewrite ((X.(cells) i).(groupoidStrictness) _ _ e ((pathFunctorEq (h i f)).(objEq) x));
    rewrite ((X.(cells) i).(groupoidStrictness) _ _ d ((pathFunctorEq (h i f)).(objEq) y))
  end.
  now exact ((pathFunctorEq (h i f)).(homEq) x y a).
Defined.

Lemma splitJoinExtension {n} (X: ExtensionData (strictGpdSystem A) n):
  splitExtension (joinExtension X) = X.
Proof.
  destruct X as [X [G p]].
  refine (eq_existT_curried eq_refl _).
  refine (eq_existT_curried eq_refl _).
  apply matchingFunctorEq. intros i f.
  apply (functorEqPath (X.(cells) i).(groupoidStrictness)).
  unshelve econstructor; now intros.
Defined.

Definition strictGpdLaws: MatchingSystemLaws (strictGpdSystem A) :=
  Build_MatchingSystemLaws (strictGpdSystem A)
    (fun B: StrictGroupoid => (familyEquivFunctor B).(eqvIsEquiv))
    (fun X => diagramEqPointwise (emptyDiagram A) X
      (fun i => match i with end) (fun i => match i with end))
    (fun n => (qinvEquiv (joinExtension (M := strictGpdSystem A) (n := n))
      splitExtension splitJoinExtension joinSplitExtension).(eqvIsEquiv))
    (fun n X T b => eq_refl).

End Classification.
