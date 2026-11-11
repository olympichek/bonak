(** Indexed frame boundaries interpreted in a diagram with the same
    adjacent cell spaces and face maps. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet Notation LeSProp Equiv Funext.
From Bonak.νSet Require Import Layer νSet.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.
From Bonak.Reedy.Set Require Import Reedy GeneratorBoundary.
From Bonak.Indexed.ReedyEquiv.Set Require Import Boundary.
From Bonak.Indexed.ReedyEquiv Require ChainDepth.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module IndexedMatching (A: LayerSig) (V: νSetSig A).
Import A.
Module Export Chains := ChainPairs A V.

(** The cells at the top of a prefix: frames with a filler. *)
Definition prefixCell {n} (X: (νSetAt n.+1).(prefix)): HSet :=
  {d: νFrame X.1 & X.2 d}.

Section Zero.
Context {K} (dc: DepsCohs 0 K) (D: Diagram arity 1)
  (e: Equiv (Cell dc.(_extraDeps)) (D.(cells) None)).

Definition zeroPairwise (d: mkFrame (mkDepsRestr (depsCohs := dc))):
  FinitePairwiseBoundary arity 1 D :=
  ((fun i a => e (frameFaces dc d i a)); tt).

Definition zeroPairwiseFrame (b: FinitePairwiseBoundary arity 1 D):
  mkFrame (mkDepsRestr (depsCohs := dc)) :=
  (zeroRealization dc (fun i a => invEq e (b.1 i a))).1.

Lemma zeroPairwiseRet d: zeroPairwiseFrame (zeroPairwise d) = d.
Proof.
  apply νFaceEq; intros p k dc' c a. rewrite <- 2 faceAtChain.
  refine ((zeroRealization dc (fun i a => invEq e (e (frameFaces dc d i a)))).2
    (chainDepth c) a • _).
  now apply retEq.
Qed.

Lemma zeroPairwiseSec b: zeroPairwise (zeroPairwiseFrame b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro a.
    refine (f_equal e ((zeroRealization dc (fun i a => invEq e (b.1 i a))).2 i a) • _).
    now apply secEq.
  - now apply finitePairwiseBoundaryLawProp.
Qed.

Definition zeroIndexedMatchingEquiv:
  Equiv (mkFrame (mkDepsRestr (depsCohs := dc)))
    (MatchingObject arity D) :=
  compEquiv (qinvEquiv zeroPairwise zeroPairwiseFrame zeroPairwiseRet zeroPairwiseSec)
    (finitePairwiseMatchingEquiv arity 1 D).

Lemma zeroIndexedMatchingFace d i a:
  (zeroIndexedMatchingEquiv d).1 None (depthFaceWord arity 0 i a)
    = e (faceAtDepth dc (depth i) a d).
Proof. now apply finitePairwiseMatchingFace. Qed.
End Zero.

Lemma upperChainDepth {P K} {dc: DepsCohs2 P K}
  {p k} {d: DepsCohs2 p k} (c: DepsCohs2Chain dc d):
  chainDepth (cohs2ChainCohs c) = weakenDepth (chainDepth (cohs2ChainDepsCohs c)).
Proof. apply depthEq. now apply cohs2ChainLenEq. Qed.
Lemma earlierChainDepth {P K} {dc: DepsCohs2 P K}
  {p k} {d: DepsCohs2 p k} (c: DepsCohs2Chain dc d):
  chainDepth (DepsCohsChainCons (cohs2ChainCohs c)) = nextDepth (chainDepth (cohs2ChainDepsCohs c)).
Proof. apply depthEq; cbn. now rewrite cohs2ChainLenEq. Qed.

Definition IndexedDepthLaw {P K} (dc: DepsCohs2 P K) (f: FaceTuple (mkDepsCohs dc)): Type :=
  forall (i j: FaceDepth P), depth i <= depth j -> forall a c,
    faceAtDepth dc.(_depsCohs) (depth i) a (f (nextDepth j) c).1
      = faceAtDepth dc.(_depsCohs) (depth j) c (f (weakenDepth i) a).1.
Lemma indexedCompatibleDepth {P K} (dc: DepsCohs2 P K) f (H: FaceCompatible dc f): IndexedDepthLaw dc f.
Proof.
  intros i j hij a c.
  destruct (ChainDepth.pairAtDepth depthChains P K dc i j hij)
    as [[[p [k [d c1]]] [p' [k' [d' c2]]]] [hi hj]].
  pose proof (H p k d c1 p' k' d' c2 a c) as h.
  rewrite earlierChainDepth, upperChainDepth, <- 2 faceAtChain in h.
  assert (ei: chainDepth (cohs2ChainDepsCohs c1) = i).
  { apply depthEq. now exact hi. }
  assert (ej: chainDepth (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)) = j).
  { apply depthEq. now exact hj. }
  change (faceAtDepth dc.(_depsCohs) (depth (chainDepth (cohs2ChainDepsCohs c1))) a
    (f (nextDepth (chainDepth (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)))) c).1
    = faceAtDepth dc.(_depsCohs)
      (depth (chainDepth (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)))) c
      (f (weakenDepth (chainDepth (cohs2ChainDepsCohs c1))) a).1) in h.
  now rewrite ei, ej in h.
Qed.
Lemma indexedDepthCompatible {P K} (dc: DepsCohs2 P K) f (H: IndexedDepthLaw dc f): FaceCompatible dc f.
Proof.
  intros p k d c p' k' d' c' a b.
  rewrite earlierChainDepth, upperChainDepth, <- 2 faceAtChain.
  now exact (H (chainDepth (cohs2ChainDepsCohs c))
    (chainDepth (cohs2ChainDepsCohs (cohs2ChainCompose c c')))
    (indexedChainComposeLe c c') a b).
Qed.

Record IndexedDiagramModel {P K} {dc: DepsCohs2 P K}
  {D: Diagram arity P.+2} := {
  modelUpper: Equiv (Cell (mkDepsCohs dc).(_extraDeps)) (D.(cells) None);
  modelLower: Equiv (Cell dc.(_depsCohs).(_extraDeps)) (D.(cells) (Some None));
  modelFace (i: FaceDepth P) a (x: Cell (mkDepsCohs dc).(_extraDeps)):
    modelLower (faceAtDepth dc.(_depsCohs) (depth i) a x.1)
      = D.(restrict) (i := Some None) (j := None) (depthFaceWord arity P i a) (modelUpper x);
}.
Arguments IndexedDiagramModel {P K} dc D.

Section Compare.
Context {P K} (dc: DepsCohs2 P K) (D: Diagram arity P.+2)
  (M: IndexedDiagramModel dc D).
Definition modelFaces (f: FaceTuple (mkDepsCohs dc)): FiniteRawBoundary arity P.+2 D :=
  fun i a => modelUpper M (f i a).
Definition unmodelFaces (f: FiniteRawBoundary arity P.+2 D): FaceTuple (mkDepsCohs dc) :=
  fun i a => invEq (modelUpper M) (f i a).
Lemma modelFacesCompatible f (H: FaceCompatible dc f):
  FinitePairwiseBoundaryLaw arity P.+2 D (modelFaces f).
Proof.
  intros i j hij a c. unfold modelFaces. rewrite <- 2 modelFace.
  now exact (f_equal (modelLower M) (indexedCompatibleDepth dc f H i j hij a c)).
Qed.
Lemma unmodelFacesCompatible f (H: FinitePairwiseBoundaryLaw arity P.+2 D f):
  FaceCompatible dc (unmodelFaces f).
Proof.
  apply indexedDepthCompatible. intros i j hij a c.
  apply (eqvInj (modelLower M)). rewrite 2 modelFace.
  unfold unmodelFaces. rewrite 2 secEq. now exact (H i j hij a c).
Qed.
Definition indexedToPairwise (b: IndexedFaceBoundary dc): FinitePairwiseBoundary arity P.+2 D :=
  (modelFaces b.1; modelFacesCompatible b.1 b.2).
Definition pairwiseToIndexed (b: FinitePairwiseBoundary arity P.+2 D): IndexedFaceBoundary dc :=
  (unmodelFaces b.1; unmodelFacesCompatible b.1 b.2).
Lemma indexedPairwiseRet b: pairwiseToIndexed (indexedToPairwise b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro a. now apply retEq.
  - now apply faceCompatibleProp.
Qed.
Lemma indexedPairwiseSec b: indexedToPairwise (pairwiseToIndexed b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro a. now apply secEq.
  - now apply finitePairwiseBoundaryLawProp.
Qed.
Definition indexedPairwiseEquiv: Equiv (IndexedFaceBoundary dc) (FinitePairwiseBoundary arity P.+2 D) :=
  qinvEquiv indexedToPairwise pairwiseToIndexed indexedPairwiseRet indexedPairwiseSec.
Definition indexedFrameMatchingEquiv:
  Equiv (mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc)))
    (MatchingObject arity D) :=
  compEquiv (indexedFaceBoundaryEquiv dc)
    (compEquiv indexedPairwiseEquiv (finitePairwiseMatchingEquiv arity P.+2 D)).
Lemma indexedFrameMatchingFace d i a:
  (indexedFrameMatchingEquiv d).1 None (depthFaceWord arity P.+1 i a)
    = modelUpper M (faceAtDepth (mkDepsCohs dc) (depth i) a d).
Proof. now apply finitePairwiseMatchingFace. Qed.
End Compare.

(** The top two cell spaces of a prefix, identified with those of a diagram
    compatibly with the faces between them, model the diagram. *)
Section PrefixModel.
Context {n} (X: (νSetAt n.+2).(prefix)) (D: Diagram arity n.+2)
  (upper: Equiv (prefixCell X) (D.(cells) None))
  (lower: Equiv (prefixCell X.1) (D.(cells) (Some None)))
  (compatible: forall (i: FaceDepth n) a (x: prefixCell X),
    lower (faceAtDepth (prefixDepsCohs X.1) (depth i) a x.1)
      = D.(restrict) (i := Some None) (j := None) (depthFaceWord arity n i a) (upper x)).

Definition prefixModel: IndexedDiagramModel (prefixDepsCohs2 X) D :=
  @Build_IndexedDiagramModel n 0 (prefixDepsCohs2 X) D upper lower compatible.

Definition prefixMatchingEquiv: Equiv (νFrame X) (MatchingObject arity D) :=
  indexedFrameMatchingEquiv (prefixDepsCohs2 X) D prefixModel.

Lemma prefixMatchingFace d i a:
  (prefixMatchingEquiv d).1 None (depthFaceWord arity n.+1 i a)
    = upper (faceAtDepth (prefixDepsCohs X) (depth i) a d).
Proof. now exact (indexedFrameMatchingFace (prefixDepsCohs2 X) D prefixModel d i a). Qed.
End PrefixModel.
End IndexedMatching.

(** A shared instance keeps the indexed chain types used by face evaluation. *)
Module Type IndexedMatchingSig (A: LayerSig) (V: νSetSig A).
Include IndexedMatching A V.
End IndexedMatchingSig.
