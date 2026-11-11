(** Functors into the matching object of a finite strict groupoid diagram
    are the points of the matching object of the h-set diagram of functors
    out of their domain. Through this correspondence, such a functor is
    determined by its projections to the generating faces, and compatible
    generating projections assemble into a functor. As a consequence, the
    indexed frame of strict groupoids is isomorphic to the matching object
    of any diagram whose top two cell groupoids are identified with those
    of the frame compatibly with the faces between them. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Notation FinitePrefix.
From Bonak.Category.Groupoid Require Import Strict GraphFiberRoundtrip.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.
From Bonak.Reedy.Set Require Reedy.
From Bonak.Reedy.Set Require Import GeneratorBoundary.
From Bonak.Reedy.StrictGpd Require Import Reedy Extension.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Indexed.ReedyEquiv.StrictGpd Require Import Face Boundary.

Set Primitive Projections.
Set Printing Projections.

Module HSetReedy := Bonak.Reedy.Set.Reedy.

Section Matching.
Context (A: HSet).

(** The h-set diagram of functors from [X] into the cells of [D]. *)
Definition homDiagram (X: StrictGroupoid) {n} (D: Diagram A n):
  HSetReedy.Diagram A n.
Proof.
  refine {| HSetReedy.cells i := strictGroupoidFunctorSet X (D.(cells) i);
    HSetReedy.restrict i j f c := c ⨟ᶠ D.(restrict) f |}.
  - intros i c. cbn. rewrite D.(restrictId). now apply functorIdR.
  - intros i j k f g c. cbn. rewrite functorAssocEq, D.(restrictComp).
    now reflexivity.
Defined.

(** The projections of a functor into the matching object. *)
Definition matchingCone {X: StrictGroupoid} {n} (D: Diagram A n)
  (p: Functor X (MatchingObject A D)):
  HSetReedy.MatchingObject A (homDiagram X D).
Proof.
  exists (fun i f => p ⨟ᶠ matchingProjection A D i f).
  intros i j f g.
  now exact (functorAssocEq p (matchingProjection A D j g) (D.(restrict) f)
    • f_equal (compFunctor p) (matchingProjectionComp A D i j f g)).
Defined.

(** The functor into the matching object with prescribed projections. *)
Definition coneFunctorObj {X: StrictGroupoid} {n} (D: Diagram A n)
  (b: HSetReedy.MatchingObject A (homDiagram X D)) (x: X):
  MatchingBoundary A D.
Proof.
  exists (fun i f => (b.1 i f).(fobj) x).
  intros i j f g. now exact ((pathFunctorEq (b.2 i j f g)).(objEq) x).
Defined.

Definition coneFunctorHom {X: StrictGroupoid} {n} (D: Diagram A n)
  (b: HSetReedy.MatchingObject A (homDiagram X D)) {x y: X}
  (h: X.(CHom) x y):
  MatchingHom A (coneFunctorObj D b x) (coneFunctorObj D b y).
Proof.
  exists (fun i f => (b.1 i f).(fhom) h).
  intros i j f g. now exact ((pathFunctorEq (b.2 i j f g)).(homEq) x y h).
Defined.

Definition coneFunctor {X: StrictGroupoid} {n} (D: Diagram A n)
  (b: HSetReedy.MatchingObject A (homDiagram X D)):
  Functor X (MatchingObject A D).
Proof.
  refine {| fobj := coneFunctorObj D b; fhom x y := coneFunctorHom D b |}.
  - intro x. apply matchingHomExt. intros i f. now apply (b.1 i f).(fid).
  - intros x y z h k. apply matchingHomExt. intros i f.
    now apply (b.1 i f).(fcomp).
Defined.

Lemma coneFunctorProjection {X: StrictGroupoid} {n} (D: Diagram A n) b i f:
  coneFunctor (X := X) D b ⨟ᶠ matchingProjection A D i f = b.1 i f.
Proof.
  apply (functorEqPath (D.(cells) i).(groupoidStrictness)).
  unshelve econstructor; now intros.
Qed.

(** Generating faces suffice. *)
Lemma matchingFacesExt {X: StrictGroupoid} {n} (D: Diagram A n.+1)
  (p q: Functor X (MatchingObject A D))
  (h: forall i a,
    p ⨟ᶠ matchingProjection A D None (depthFaceWord A n i a)
    = q ⨟ᶠ matchingProjection A D None (depthFaceWord A n i a)): p = q.
Proof.
  apply matchingFunctorEq. intros i f.
  pose proof (finiteMatchingFacesExt A n (homDiagram X D)
    (matchingCone D p) (matchingCone D q) h) as e.
  now exact (f_equal (fun b => b.1 i f) e).
Qed.

Definition matchingOfFaces {X: StrictGroupoid} {n} (D: Diagram A n.+1)
  (b: FinitePairwiseBoundary A n.+1 (homDiagram X D)):
  Functor X (MatchingObject A D) :=
  coneFunctor D (finitePairwiseMatchingEquiv A n.+1 (homDiagram X D) b).

Lemma matchingOfFacesFace {X: StrictGroupoid} {n} (D: Diagram A n.+1) b i a:
  matchingOfFaces (X := X) D b
    ⨟ᶠ matchingProjection A D None (depthFaceWord A n i a)
  = b.1 i a.
Proof.
  now exact (coneFunctorProjection D _ None (depthFaceWord A n i a)
    • finitePairwiseMatchingFace A n (homDiagram X D) b i a).
Qed.

(** The generating projections of a functor are pairwise compatible. *)
Lemma matchingFacesPairwise {X: StrictGroupoid} {n} (D: Diagram A n.+1)
  (p: Functor X (MatchingObject A D)):
  FinitePairwiseBoundaryLaw A n.+1 (homDiagram X D)
    (fun i a => p ⨟ᶠ matchingProjection A D None (depthFaceWord A n i a)).
Proof.
  destruct n as [|n]; [now exact tt|].
  intros i j hij a c.
  pose (b := matchingCone D p).
  pose proof (b.2 (Some None) None (depthFaceWord A n i a)
    (depthFaceWord A n.+1 (nextDepth j) c)) as h1.
  pose proof (b.2 (Some None) None (depthFaceWord A n j c)
    (depthFaceWord A n.+1 (weakenDepth i) a)) as h2.
  now exact (h1 • f_equal (fun w => b.1 (Some None) w)
    (depthFaceExchange A n i j hij a c) • eq_sym h2).
Qed.

End Matching.

(** Cancelling an isomorphism of strict groupoids after a functor. *)
Section IsoCancel.
Context {G H: StrictGroupoid} (e: Iso StrictGroupoidCat G H).

Lemma isoHomInverseAfter {X: Category} (F: Functor X G):
  F ⨟ᶠ e.(isoHom) ⨟ᶠ inverse e.(isoInvertible) = F.
Proof.
  now exact (functorAssocEq F e.(isoHom) (inverse e.(isoInvertible))
    • f_equal (compFunctor F) (strictGroupoidIsoInverseR e) • functorIdR F).
Qed.

Lemma inverseIsoHomAfter {X: Category} (F: Functor X H):
  F ⨟ᶠ inverse e.(isoInvertible) ⨟ᶠ e.(isoHom) = F.
Proof.
  now exact (functorAssocEq F (inverse e.(isoInvertible)) e.(isoHom)
    • f_equal (compFunctor F) (strictGroupoidIsoInverseL e) • functorIdR F).
Qed.

Lemma isoHomCancel {X: Category} (F L: Functor X G)
  (h: F ⨟ᶠ e.(isoHom) = L ⨟ᶠ e.(isoHom)): F = L.
Proof.
  now exact (eq_sym (isoHomInverseAfter F)
    • f_equal (fun T => T ⨟ᶠ inverse e.(isoInvertible)) h
    • isoHomInverseAfter L).
Qed.
End IsoCancel.

Module IndexedMatchingOn (A: LayerSig) (S: νStrictGpdSig A) (F: FaceSig A S).
Import A.
Module Export Boundaries := BoundaryOn A S F.

(** The cells at the top of a prefix: the total groupoid of its filler. *)
Definition prefixCell {n} (X: (νStrictGpdAt n.+1).(prefix)): StrictGroupoid :=
  total X.2.

Section Zero.
Context {K} (dc: DepsCohs 0 K) (D: Diagram arity 1)
  (e: Iso StrictGroupoidCat (Cell dc.(_extraDeps)) (D.(cells) None)).

Local Abbreviation Frame := (mkFrame (mkDepsRestr (depsCohs := dc))).

Definition zeroFrameFaces:
  FinitePairwiseBoundary arity 1 (homDiagram arity Frame D) :=
  (fun i a => faceAtDepth dc (depth i) a ⨟ᶠ e.(isoHom); tt).

Definition zeroMatchingFaces: FaceTuple (MatchingObject arity D) dc :=
  fun i a => matchingProjection arity D None (depthFaceWord arity 0 i a)
    ⨟ᶠ inverse e.(isoInvertible).

Lemma zeroFrameRet:
  matchingOfFaces arity D zeroFrameFaces
    ⨟ᶠ zeroFrameOfFaces dc zeroMatchingFaces
  = idFunctor Frame.
Proof.
  apply frameFacesExt; intros i a.
  rewrite functorAssocEq, zeroFrameOfFacesFace, functorIdL.
  unfold zeroMatchingFaces. rewrite <- functorAssocEq, matchingOfFacesFace.
  now apply isoHomInverseAfter.
Qed.

Lemma zeroFrameSec:
  zeroFrameOfFaces dc zeroMatchingFaces
    ⨟ᶠ matchingOfFaces arity D zeroFrameFaces
  = idFunctor (MatchingObject arity D).
Proof.
  apply matchingFacesExt; intros i a.
  rewrite functorAssocEq, matchingOfFacesFace, functorIdL.
  change (zeroFrameOfFaces dc zeroMatchingFaces
    ⨟ᶠ (faceAtDepth dc (depth i) a ⨟ᶠ e.(isoHom))
    = matchingProjection arity D None (depthFaceWord arity 0 i a)).
  rewrite <- functorAssocEq, zeroFrameOfFacesFace.
  now apply inverseIsoHomAfter.
Qed.

Definition zeroIndexedMatchingIso:
  Iso StrictGroupoidCat Frame (MatchingObject arity D) :=
  @Build_Iso StrictGroupoidCat _ _ (matchingOfFaces arity D zeroFrameFaces)
    (@Build_IsInvertible StrictGroupoidCat _ _ _
      (zeroFrameOfFaces dc zeroMatchingFaces) zeroFrameRet zeroFrameSec).

Lemma zeroIndexedMatchingFace i a:
  zeroIndexedMatchingIso.(isoHom)
    ⨟ᶠ matchingProjection arity D None (depthFaceWord arity 0 i a)
  = faceAtDepth dc (depth i) a ⨟ᶠ e.(isoHom).
Proof. now apply matchingOfFacesFace. Qed.
End Zero.

(** Isomorphisms of the top two cell groupoids with those of a diagram,
    compatible with the faces between them. *)
Record IndexedDiagramModel {P K} {dc: DepsCohs2 P K}
  {D: Diagram arity P.+2} := {
  modelUpper: Iso StrictGroupoidCat
    (Cell (mkDepsCohs dc).(_extraDeps)) (D.(cells) None);
  modelLower: Iso StrictGroupoidCat
    (Cell dc.(_depsCohs).(_extraDeps)) (D.(cells) (Some None));
  modelFace (i: FaceDepth P) a:
    proj _ ⨟ᶠ faceAtDepth dc.(_depsCohs) (depth i) a ⨟ᶠ modelLower.(isoHom)
    = modelUpper.(isoHom)
      ⨟ᶠ D.(restrict) (i := Some None) (j := None) (depthFaceWord arity P i a);
}.
Arguments IndexedDiagramModel {P K} dc D.

Section Compare.
Context {P K} (dc: DepsCohs2 P K) (D: Diagram arity P.+2)
  (M: IndexedDiagramModel dc D).

Local Abbreviation Frame :=
  (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc))).

(** The face law of the model, after any functor into the upper cells. *)
Lemma modelFaceAfter {X: Category}
  (G: Functor X (Cell (mkDepsCohs dc).(_extraDeps))) (i: FaceDepth P) a:
  G ⨟ᶠ proj _ ⨟ᶠ faceAtDepth dc.(_depsCohs) (depth i) a
    ⨟ᶠ (modelLower M).(isoHom)
  = G ⨟ᶠ (modelUpper M).(isoHom)
    ⨟ᶠ D.(restrict) (i := Some None) (j := None) (depthFaceWord arity P i a).
Proof.
  now exact (functorAssocEq _ _ _ • functorAssocEq _ _ _
    • f_equal (compFunctor G) (eq_sym (functorAssocEq _ _ _) • modelFace M i a)
    • eq_sym (functorAssocEq _ _ _)).
Qed.

Lemma frameFacesPairwise:
  FinitePairwiseBoundaryLaw arity P.+2 (homDiagram arity Frame D)
    (fun i a => faceAtDepth (mkDepsCohs dc) (depth i) a
      ⨟ᶠ (modelUpper M).(isoHom)).
Proof.
  intros i j hij a c.
  pose proof (frameFacesDepthLaw dc (idFunctor _) i j hij a c) as h.
  unfold frameFaces in h. rewrite 2 functorIdL in h.
  now exact (eq_sym (modelFaceAfter _ i a)
    • f_equal (fun T => T ⨟ᶠ (modelLower M).(isoHom)) h
    • modelFaceAfter _ j c).
Qed.

Definition frameFacesBoundary:
  FinitePairwiseBoundary arity P.+2 (homDiagram arity Frame D) :=
  (fun i a => faceAtDepth (mkDepsCohs dc) (depth i) a
    ⨟ᶠ (modelUpper M).(isoHom); frameFacesPairwise).

Definition matchingFaces: FaceTuple (MatchingObject arity D) (mkDepsCohs dc) :=
  fun i a => matchingProjection arity D None (depthFaceWord arity P.+1 i a)
    ⨟ᶠ inverse (modelUpper M).(isoInvertible).

Lemma matchingFacesDepthLaw: DepthLaw dc matchingFaces.
Proof.
  intros i j hij a c. apply (isoHomCancel (modelLower M)).
  pose proof (matchingFacesPairwise arity D (idFunctor _) i j hij a c) as h.
  change ((idFunctor _ ⨟ᶠ matchingProjection arity D None
      (depthFaceWord arity P.+1 (nextDepth j) c))
      ⨟ᶠ D.(restrict) (i := Some None) (j := None) (depthFaceWord arity P i a)
    = (idFunctor _ ⨟ᶠ matchingProjection arity D None
      (depthFaceWord arity P.+1 (weakenDepth i) a))
      ⨟ᶠ D.(restrict) (i := Some None) (j := None) (depthFaceWord arity P j c))
    in h.
  rewrite 2 functorIdL in h.
  now exact (modelFaceAfter _ i a
    • f_equal (fun T => T ⨟ᶠ D.(restrict) (i := Some None) (j := None)
        (depthFaceWord arity P i a))
      (inverseIsoHomAfter (modelUpper M) _)
    • h
    • eq_sym (f_equal (fun T => T ⨟ᶠ D.(restrict) (i := Some None) (j := None)
        (depthFaceWord arity P j c))
      (inverseIsoHomAfter (modelUpper M) _))
    • eq_sym (modelFaceAfter _ j c)).
Qed.

Definition matchingFrame: Functor (MatchingObject arity D) Frame :=
  frameOfFaces dc matchingFaces matchingFacesDepthLaw.

Lemma indexedFrameRet:
  matchingOfFaces arity D frameFacesBoundary ⨟ᶠ matchingFrame = idFunctor Frame.
Proof.
  apply frameFacesExt; intros i a. unfold matchingFrame.
  rewrite functorAssocEq, frameOfFacesFace, functorIdL.
  unfold matchingFaces. rewrite <- functorAssocEq, matchingOfFacesFace.
  now apply isoHomInverseAfter.
Qed.

Lemma indexedFrameSec:
  matchingFrame ⨟ᶠ matchingOfFaces arity D frameFacesBoundary
  = idFunctor (MatchingObject arity D).
Proof.
  apply matchingFacesExt; intros i a.
  rewrite functorAssocEq, matchingOfFacesFace, functorIdL.
  change (matchingFrame
    ⨟ᶠ (faceAtDepth (mkDepsCohs dc) (depth i) a ⨟ᶠ (modelUpper M).(isoHom))
    = matchingProjection arity D None (depthFaceWord arity P.+1 i a)).
  rewrite <- functorAssocEq. unfold matchingFrame. rewrite frameOfFacesFace.
  now apply inverseIsoHomAfter.
Qed.

Definition indexedFrameMatchingIso:
  Iso StrictGroupoidCat Frame (MatchingObject arity D) :=
  @Build_Iso StrictGroupoidCat _ _ (matchingOfFaces arity D frameFacesBoundary)
    (@Build_IsInvertible StrictGroupoidCat _ _ _ matchingFrame
      indexedFrameRet indexedFrameSec).

Lemma indexedFrameMatchingFace i a:
  indexedFrameMatchingIso.(isoHom)
    ⨟ᶠ matchingProjection arity D None (depthFaceWord arity P.+1 i a)
  = faceAtDepth (mkDepsCohs dc) (depth i) a ⨟ᶠ (modelUpper M).(isoHom).
Proof. now apply matchingOfFacesFace. Qed.
End Compare.

(** The top two cell groupoids of a prefix, identified with those of a
    diagram compatibly with the faces between them, model the diagram. *)
Section PrefixModel.
Context {n} (X: (νStrictGpdAt n.+2).(prefix)) (D: Diagram arity n.+2)
  (upper: Iso StrictGroupoidCat (prefixCell X) (D.(cells) None))
  (lower: Iso StrictGroupoidCat (prefixCell X.1) (D.(cells) (Some None)))
  (compatible: forall (i: FaceDepth n) a,
    proj X.2 ⨟ᶠ faceAtDepth (prefixDepsCohs X.1) (depth i) a ⨟ᶠ lower.(isoHom)
    = upper.(isoHom)
      ⨟ᶠ D.(restrict) (i := Some None) (j := None) (depthFaceWord arity n i a)).

Definition prefixModel: IndexedDiagramModel (prefixDepsCohs2 X) D :=
  @Build_IndexedDiagramModel n 0 (prefixDepsCohs2 X) D upper lower compatible.

Definition prefixMatchingIso:
  Iso StrictGroupoidCat (νFrame X) (MatchingObject arity D) :=
  indexedFrameMatchingIso (prefixDepsCohs2 X) D prefixModel.

Lemma prefixMatchingFace i a:
  prefixMatchingIso.(isoHom)
    ⨟ᶠ matchingProjection arity D None (depthFaceWord arity n.+1 i a)
  = faceAtDepth (prefixDepsCohs X) (depth i) a ⨟ᶠ upper.(isoHom).
Proof.
  now exact (indexedFrameMatchingFace (prefixDepsCohs2 X) D prefixModel i a).
Qed.
End PrefixModel.
End IndexedMatchingOn.
