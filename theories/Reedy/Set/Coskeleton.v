(** Extending finite h-set diagrams by their compatible restriction cones. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Equiv Notation FinitePrefix.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Set Require Import Reedy.

Set Primitive Projections.
Set Printing Projections.


Section Coskeleton.
Context (A: HSet) (n: nat) (X: Diagram A n).

Definition Cone (k: nat): HSet :=
  {b: hforall (i: Index n) (f: Word A (rank i) k), X.(cells) i &
   hforall (i j: Index n) (f: Word A (rank i) (rank j))
     (g: Word A (rank j) k),
     hEq (X.(restrict) f (b j g)) (b i (wcomp g f))}.

Lemma coneExt {k} (b c: Cone k)
  (h: forall i f, b.1 i f = c.1 i f): b = c.
Proof.
  destruct b as [b hb], c as [c hc]; cbn in h.
  assert (e: b = c).
  { apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro f. now apply h. }
  destruct e. apply f_equal.
  repeat (apply functional_extensionality_dep; intro).
  now apply UIP.
Defined.

Definition coneRestrict {j k} (f: Word A j k) (b: Cone k): Cone j.
Proof.
  exists (fun i g => b.1 i (wcomp f g)).
  intros i l g h. rewrite wcompAssoc. now apply b.2.
Defined.

Lemma coneRestrictId k (b: Cone k): coneRestrict (wid k) b = b.
Proof. apply coneExt; intros i f; cbn. now rewrite wcompIdl. Defined.

Lemma coneRestrictComp {i j k} (f: Word A i j) (g: Word A j k) (b: Cone k):
  coneRestrict f (coneRestrict g b) = coneRestrict (wcomp g f) b.
Proof. apply coneExt; intros l h; cbn. now rewrite wcompAssoc. Defined.

Definition coskeleton: Functor (Op (νSemiShape A)) HSetCat := {|
  fobj := Cone;
  fhom i j f := coneRestrict f;
  fid i := functional_extensionality_dep _ _ (coneRestrictId i);
  fcomp i j k f g := functional_extensionality_dep _ _
    (fun b => eq_sym (coneRestrictComp g f b));
|}.

Definition yoneda (i: Index n) (x: X.(cells) i): Cone (rank i).
Proof.
  exists (fun j f => X.(restrict) (i := j) (j := i) f x).
  intros j k f g. now exact (X.(restrictComp) f g x).
Defined.

Lemma yonedaRet (i: Index n) (b: Cone (rank i)):
  yoneda i (b.1 i (wid (rank i))) = b.
Proof.
  apply coneExt; intros j f; cbn.
  refine (b.2 j i f (wid (rank i)) • _). now rewrite wcompIdl.
Defined.

Definition coskeletonCells (i: Index n):
  Equiv (coskeleton.(fobj) (rank i)) (X.(cells) i) :=
  qinvEquiv (fun b: Cone (rank i) => b.1 i (wid (rank i))) (yoneda i)
    (yonedaRet i) (X.(restrictId) i).

Lemma coskeletonCellsNatural (i j: Index n) (f: Word A (rank i) (rank j))
  (b: coskeleton.(fobj) (rank j)):
  coskeletonCells i (coskeleton.(fhom) f b) = X.(restrict) f (coskeletonCells j b).
Proof.
  cbn. rewrite wcompIdr. symmetry.
  refine (b.2 i j f (wid (rank j)) • _). now rewrite wcompIdl.
Defined.

Definition coskeletonDiagram: Diagram A n := {|
  cells i := Cone (rank i);
  restrict i j f := coneRestrict f;
  restrictId i := coneRestrictId (rank i);
  restrictComp i j k f g := coneRestrictComp f g;
|}.

Definition matchingEvaluate (b: MatchingObject A coskeletonDiagram): MatchingObject A X.
Proof.
  exists (fun i f => coskeletonCells i (b.1 i f)).
  intros i j f g.
  refine (eq_sym (coskeletonCellsNatural i j f (b.1 j g)) • _).
  now exact (f_equal (coskeletonCells i) (b.2 i j f g)).
Defined.

Definition matchingYoneda (b: MatchingObject A X): MatchingObject A coskeletonDiagram.
Proof.
  exists (fun i f => yoneda i (b.1 i f)).
  intros i j f g. apply coneExt; intros k h; cbn.
  refine (eq_sym (X.(restrictComp) h f (b.1 j g)) • _).
  now exact (f_equal (X.(restrict) h) (b.2 i j f g)).
Defined.

Lemma matchingEvaluateYoneda (b: MatchingObject A X):
  matchingEvaluate (matchingYoneda b) = b.
Proof. apply matchingExt; intros i f. now apply X.(restrictId). Defined.

Lemma matchingYonedaEvaluate (b: MatchingObject A coskeletonDiagram):
  matchingYoneda (matchingEvaluate b) = b.
Proof. apply matchingExt; intros i f. now apply yonedaRet. Defined.

Definition coskeletonMatching:
  Equiv (MatchingObject A coskeletonDiagram) (MatchingObject A X) :=
  qinvEquiv matchingEvaluate matchingYoneda matchingYonedaEvaluate matchingEvaluateYoneda.

End Coskeleton.
