(** Strict groupoid diagrams on the semi-shape category and their matching
    objects, with displayed groupoids as fillers. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT FinitePrefix.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Category.Groupoid Require Import Family.
From Bonak.Reedy Require Export MatchingSystem.

Set Primitive Projections.
Set Printing Projections.

Record Diagram {A: HSet} {n: nat} := {
  cells: Index n -> HSetGroupoid;
  restrict {i j}: Word A (rank i) (rank j) -> Functor (cells j) (cells i);
  restrictId i: restrict (wid (rank i)) = idFunctor (cells i);
  restrictComp {i j k} (f: Word A (rank i) (rank j))
    (g: Word A (rank j) (rank k)):
    restrict g ⨟ᶠ restrict f = restrict (wcomp g f);
}.

Arguments Diagram A n : clear implicits.

Section Construction.
Context (A: HSet).

Definition matchingData {n} (X: Diagram A n): HSet :=
  hforall (i: Index n) (f: Word A (rank i) n), X.(cells) i.

Definition MatchingBoundary {n} (X: Diagram A n): HSet :=
  {b: matchingData X &
    hforall (i j: Index n) (f: Word A (rank i) (rank j))
      (g: Word A (rank j) n),
      @hEq (hsetGroupoidObjects (X.(cells) i))
        ((X.(restrict) f).(fobj) (b j g)) (b i (wcomp g f))}.

Lemma matchingBoundaryExt {n} {X: Diagram A n} (b c: MatchingBoundary X)
  (h: forall i f, b.1 i f = c.1 i f): b = c.
Proof.
  destruct b as [b hb], c as [c hc]; cbn in h.
  assert (e: b = c).
  { repeat (apply functional_extensionality_dep; intro). now apply h. }
  destruct e. apply f_equal.
  repeat (apply functional_extensionality_dep; intro). now apply UIP.
Defined.

Definition MatchingHom {n} {X: Diagram A n} (b c: MatchingBoundary X): HSet :=
  {h: hforall (i: Index n) (f: Word A (rank i) n),
      (X.(cells) i).(CHom) (b.1 i f) (c.1 i f) &
    hforall (i j: Index n) (f: Word A (rank i) (rank j))
      (g: Word A (rank j) n),
      hEq (castArrow (b.2 i j f g) (c.2 i j f g)
        ((X.(restrict) f).(fhom) (h j g))) (h i (wcomp g f))}.

Lemma matchingHomExt {n} {X: Diagram A n} {b c: MatchingBoundary X}
  (h k: MatchingHom b c) (e: forall i f, h.1 i f = k.1 i f): h = k.
Proof.
  destruct h as [h hh], k as [k hk]; cbn in e.
  assert (p: h = k).
  { repeat (apply functional_extensionality_dep; intro). now apply e. }
  destruct p. apply f_equal.
  repeat (apply functional_extensionality_dep; intro). now apply UIP.
Defined.

Definition matchingId {n} {X: Diagram A n} (b: MatchingBoundary X): MatchingHom b b.
Proof.
  exists (fun i f => cid (b.1 i f)). intros i j f g.
  rewrite (X.(restrict) f).(fid). now apply castArrowId.
Defined.

Definition matchingComp {n} {X: Diagram A n} {a b c: MatchingBoundary X}
  (h: MatchingHom a b) (k: MatchingHom b c): MatchingHom a c.
Proof.
  exists (fun i f => h.1 i f ⨟ k.1 i f). intros i j f g.
  rewrite (X.(restrict) f).(fcomp).
  rewrite (castArrowComp (a.2 i j f g) (b.2 i j f g) (c.2 i j f g)).
  now rewrite h.2, k.2.
Defined.

Local Lemma castArrowInv {G: Groupoid} {x x' y y': G.(CObj)}
  (p: x = x') (q: y = y') (f: G.(CHom) x y):
  castArrow q p (ginv f) = ginv (castArrow p q f).
Proof. now destruct p, q. Defined.

Definition matchingInv {n} {X: Diagram A n} {b c: MatchingBoundary X}
  (h: MatchingHom b c): MatchingHom c b.
Proof.
  exists (fun i f => ginv (h.1 i f)). intros i j f g.
  rewrite functorInv, castArrowInv. now rewrite h.2.
Defined.

(** Objects and arrows both satisfy strict compatibility with every face. *)
Definition matchingCategory {n} (X: Diagram A n): Category.
Proof.
  refine {| CObj := MatchingBoundary X; CHom := MatchingHom; cid := matchingId;
    ccomp a b c := matchingComp |}.
  - intros a b h. apply matchingHomExt. intros i f. now apply cidl.
  - intros a b h. apply matchingHomExt. intros i f. now apply cidr.
  - intros a b c d h k l. apply matchingHomExt. intros i f. now apply cassoc.
Defined.

Definition MatchingObject {n} (X: Diagram A n): HSetGroupoid.
Proof.
  refine {| hsetGroupoid := {| gcat := matchingCategory X |};
    hsetGroupoidUIP := @UIP (MatchingBoundary X) |}.
  intros a b h. refine (@Build_IsInvertible _ a b h (matchingInv h) _ _).
  - apply matchingHomExt. intros i f. now apply ginvR.
  - apply matchingHomExt. intros i f. now apply ginvL.
Defined.

Definition matchingProjection {n} (X: Diagram A n) (i: Index n)
  (f: Word A (rank i) n): Functor (MatchingObject X) (X.(cells) i) := {|
  fobj b := b.1 i f; fhom b c h := h.1 i f;
  fid b := eq_refl; fcomp b c d h k := eq_refl;
|}.

Lemma matchingProjectionComp {n} (X: Diagram A n) (i j: Index n)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  matchingProjection X j g ⨟ᶠ X.(restrict) f = matchingProjection X i (wcomp g f).
Proof.
  apply (functorEqPath (X.(cells) i).(hsetGroupoidUIP)).
  refine (Build_FunctorEq (fun b => b.2 i j f g) _).
  intros b c h. now exact (h.2 i j f g).
Defined.

Definition emptyDiagram: Diagram A 0.
Proof.
  refine {| cells := fun i: Index 0 => match i with end;
    restrict := fun (i j: Index 0) => match i with end |}; now intros [].
Defined.

Definition matchingMapCells {n} (X: Diagram A n) (G: HSetGroupoid)
  (i: Index (S n)): HSetGroupoid :=
  match i with Some i => X.(cells) i | None => G end.

Definition matchingMapRestrict {n} (X: Diagram A n) {G: HSetGroupoid}
  (p: Functor G (MatchingObject X)) (i j: Index (S n)):
  Word A (rank i) (rank j) -> Functor (matchingMapCells X G j) (matchingMapCells X G i).
Proof.
  destruct i as [i|], j as [j|]; cbn.
  - now exact (X.(restrict) (i := i) (j := j)).
  - now exact (fun f => p ⨟ᶠ matchingProjection X i f).
  - intro f. now wordAboveAbsurd.
  - now exact (fun _ => idFunctor G).
Defined.

Definition extendByMatchingMap {n} (X: Diagram A n) {G: HSetGroupoid}
  (p: Functor G (MatchingObject X)): Diagram A (S n).
Proof.
  refine {| cells := matchingMapCells X G; restrict := matchingMapRestrict X p |}.
  - intros [i|]; cbn [matchingMapRestrict].
    + now apply X.(restrictId).
    + now reflexivity.
  - intros [i|] [j|] [k|] f g; cbn [matchingMapRestrict]; try now wordAboveAbsurd.
    + now apply X.(restrictComp).
    + change ((p ⨟ᶠ matchingProjection X j g) ⨟ᶠ X.(restrict) f =
        p ⨟ᶠ matchingProjection X i (wcomp g f)).
      rewrite functorAssocEq, matchingProjectionComp. now reflexivity.
    + rewrite (wordEndId n g), wcompIdl. now apply functorIdL.
    + now apply functorIdL.
Defined.

Definition truncateDiagram {n} (X: Diagram A (S n)): Diagram A n := {|
  cells i := X.(cells) (Some i);
  restrict i j f := X.(restrict) (i := Some i) (j := Some j) f;
  restrictId i := X.(restrictId) (Some i);
  restrictComp i j k f g :=
    X.(restrictComp) (i := Some i) (j := Some j) (k := Some k) f g;
|}.

Definition strictGpdSystem: MatchingSystem := {|
  matchingStages := {|
    PartialDiagram := Diagram A;
    truncate n := truncateDiagram;
    emptyPartial := emptyDiagram;
  |};
  Cell := HSetGroupoid;
  CellMap T B := Functor T B;
  CellFamily B := Family B;
  familyTotal B E := (total E; proj E);
  Matching n X := MatchingObject X;
  extendByMap n X T b := extendByMatchingMap X b;
|}.

End Construction.

Definition AugmentedSemiSimplicialStrictGpdMatchingSeq :=
  MatchingSeq (strictGpdSystem hunit).
Definition SemiCubicalStrictGpdMatchingSeq :=
  MatchingSeq (strictGpdSystem hbool).
