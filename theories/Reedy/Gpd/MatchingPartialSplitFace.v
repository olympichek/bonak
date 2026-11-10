(** Faces of the partial matching split equivalence and their coherence: the
    split commutes with the face maps of the partial matching presentation and
    of the matching-step presentation. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation RewLemmas
  FinitePrefix LeSProp PathSquares.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape WordTensor.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor Cone.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift Pullback
  ShiftedPrefix PullbackReindex MatchingSplit MatchingPartialSplit.

Set Primitive Projections.
Set Printing Projections.
Import FinitePrefix WordTensor.

(** Naturality of the top face of a shifted matching object after flattening
    the residual map. *)
Set Keyed Unification.

Lemma paddedTopResidual {A: HSet} (p: nat) {k l: nat}
  (u: Word A k l) (a: A):
  compNatTrans (whiskerLNat (shiftFunctor A p) (residualNat (S p) u)) (paddedTopNat p k a) =
    compNatTrans (paddedTopNat p l a) (residualNat p u).
Proof.
  apply natTransEq; intro i.
  now exact (eq_sym ((residualNat (S p) u).(nnat)
    (a := raiseIndex i) (b := Some i) (topFaceWord i a))).
Defined.

Section ResidualTopFace.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A)))
  {k l: nat} (u: Word A k l) (a: A).
Local Abbreviation Gamma := (residualMap (S p) F u).
Local Abbreviation shiftedResidual := (whiskerLNat (shiftFunctor A p) (residualNat (S p) u)).
Local Abbreviation oldShift := (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) l)).
Local Abbreviation newShift := (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k)).

Definition residualTopFaceMapNatural
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) l F))) :=
  topFaceMapNatural Gamma a b
    • truncatedResidualComparison p F u
        (topFaceMatching (shiftedPrefix (S p) l F) a b).

Lemma topFaceMapNaturalityFlatten
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) l F))):
  residualTopFaceMapNatural b
    • f_equal (residualMatching p F u) (topFaceFlatten p l F a b)
  = topFaceFlatten p k F a (mapMatching (shiftMap Gamma) b)
    • (f_equal (matchingAction p (Op (νSemiShape A)) F newShift
          (shiftPrefixFunctor A p k) (paddedTopNat p k a))
        (matchingCompositeNatural (shiftFunctor A p)
          (shiftPrefixFunctor A (S p) l) (shiftPrefixFunctor A (S p) k) F
          (residualNat (S p) u) b)
      • diagramSquare (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F)
          shiftedResidual (paddedTopNat p k a) (paddedTopNat p l a) (residualNat p u)
          (paddedTopResidual p u a)
          (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) l) F b)).
Proof.
  apply (matchingPathExt (shiftedPrefix p k F)); intros i g.
  unfold residualTopFaceMapNatural.
  lazymatch goal with
  | |- context [f_equal ?h (?left • ?right)] =>
      rewrite (eq_trans_map_distr h left right)
  end.
  lazymatch goal with
  | |- context [f_equal ?h (?left • ?right)] =>
      rewrite (eq_trans_map_distr h left right)
  end.
  lazymatch goal with
  | |- context [f_equal ?h (?left • ?right)] =>
      rewrite (eq_trans_map_distr h left right)
  end.
  lazymatch goal with
  | |- context [f_equal ?h (?left • ?right)] =>
      rewrite (eq_trans_map_distr h left right)
  end.
  rewrite (truncatedResidualComparisonValue p F u
    (topFaceMatching (shiftedPrefix (S p) l F) a b) i g).
  rewrite (topFaceMapNaturalValue Gamma a b i g),
    (residualMatchingMapPath p F u (topFaceFlatten p l F a b) i g),
    (topFaceFlattenValue p l F a b i g),
    (topFaceFlattenValue p k F a (mapMatching (shiftMap Gamma) b) i g).
  rewrite (matchingActionMapPath p (Op (νSemiShape A)) F newShift
    (shiftPrefixFunctor A p k) (paddedTopNat p k a)
    (matchingCompositeNatural (shiftFunctor A p)
      (shiftPrefixFunctor A (S p) l) (shiftPrefixFunctor A (S p) k) F
      (residualNat (S p) u) b) i g).
  rewrite (matchingCompositeNaturalValue (shiftFunctor A p)
    (shiftPrefixFunctor A (S p) l) (shiftPrefixFunctor A (S p) k) F
    (residualNat (S p) u) b i g).
  cbn [f_equal].
  lazymatch goal with
  | |- @eq ?P ?lhsExpr ?rhsExpr =>
      lazymatch rhsExpr with
      | @eq_trans ?C ?x _ ?y (@eq_refl _ _) ?tail =>
          refine (@eq_trans P lhsExpr tail rhsExpr _
            (@eq_sym P rhsExpr tail (@eq_trans_refl_l C x y tail)))
      end
  end.
  pose proof (matchingRelationValue p (Op (νSemiShape A)) F
    shiftedResidual (paddedTopNat p k a) (paddedTopNat p l a) (residualNat p u)
    (paddedTopResidual p u a)
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) l) F b) i g
    (eq_sym ((residualNat (S p) u).(nnat)
      (a := raiseIndex i) (b := Some i) (topFaceWord i a)))) as cubeReadout.
  assert (finishUnit : forall (T: Type) (x y: T) (p0 q0: x = y),
    q0 = p0 -> (eq_sym (eq_sym p0) • eq_refl) • eq_refl = eq_refl • q0).
  { intros T x y p0 q0 h0. destruct h0. now destruct q0. }
  cbn [residualMap pullbackMap mapNatural].
  cbv beta iota zeta delta [diagramSquare diagramRelation pullbackNaturality]
    in cubeReadout |- *.
  cbn [shiftedPrefix] in cubeReadout |- *.
  cbn [whiskerLNat shiftFunctor paddedTopNat residualNat shiftPrefixFunctor
    ncomp fobj fhom] in cubeReadout |- *.
  cbn [matchingValue matchingCompEquiv qinvEquiv eqvFun matchingComposite]
    in cubeReadout |- *.
  cbv beta iota zeta delta [matchingValue matchingComposite SigT.projT1]
    in cubeReadout |- *.
  cbv beta iota zeta delta [shiftedPrefix] in cubeReadout |- *.
  lazymatch type of cubeReadout with
  | @eq ?P ?lhsPath ?rhsPath =>
      lazymatch P with
      | @eq ?C ?x ?y => now exact (finishUnit C x y rhsPath lhsPath cubeReadout)
      end
  end.
Defined.
End ResidualTopFace.

(** The shifted matching bridge commutes with the normalized residual faces.
    *)

Local Lemma reverseRelationAlgebra {T: Type} {a b c d: T}
  (p: a = b) (q: b = c) (r: d = c):
  p • (q • eq_sym r) = eq_sym (r • (eq_sym q • eq_sym p)).
Proof. now destruct p, q, r. Defined.

Local Lemma factorCubeAlgebra {T: Type} {x0 x1 x2 x3 x4 x5 x6 x7 x8: T}
  (j: x0 = x1) (f0: x2 = x1) (u: x2 = x3) (f1: x3 = x4)
  (v: x1 = x4) (s: x3 = x5) (q: x5 = x6) (g: x6 = x7)
  (r: x4 = x7) (m: x0 = x8) (j0: x8 = x7)
  (natural: u • f1 = f0 • v)
  (cube: s • (q • g) = f1 • r)
  (flatten: m • j0 = j • (v • r)):
  (j • eq_sym f0) • ((u • s) • q) = m • (j0 • eq_sym g).
Proof.
  destruct j, f0, u, s, q, g, m, f1.
  cbn in natural, cube, flatten |- *.
  rewrite eq_trans_refl_l in natural, cube, flatten.
  rewrite <- natural, <- cube in flatten. cbn in flatten.
  now rewrite flatten.
Defined.

Local Lemma attachmentBridgeAlgebra {T: Type} {x0 x1 x2 x3 x4 x5 x6: T}
  (n: x0 = x1) (a: x1 = x2) (q: x2 = x3) (m: x0 = x4)
  (g: x4 = x3) (r: x4 = x5) (s: x5 = x6)
  (square: n • (a • q) = m • g):
  a • (q • ((eq_sym g • r) • s)) = eq_sym n • (m • (r • s)).
Proof.
  destruct n, a, q, m, r, s. cbn in square |- *.
  rewrite eq_trans_refl_l in square. now rewrite <- square.
Defined.

Local Lemma comparisonPathPaste {S T: Type} (f g: S -> T)
  (h: forall x, f x = g x) {x y: S} (p: x = y)
  {z w: T} (before: z = f x) (after: f y = w) (after': g y = w)
  (boundary: h y • after' = after):
  before • (f_equal f p • after) =
    (before • h x) • (f_equal g p • after').
Proof.
  destruct p; cbn [f_equal]. rewrite 2 eq_trans_refl_l.
  rewrite <- boundary. now apply eq_sym, eqTransAssoc.
Defined.

Definition shiftPrefixResidualFace {A: HSet} (p k q: nat) (Hq: q <= k) (a: A):
  compNatTrans (whiskerLNat (shiftFunctor A p) (residualNat (S p) (wgen k q a)))
    (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _ (shiftPrefixFunctorEq (A := A) p k)) =
  compNatTrans (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _ (shiftPrefixFunctorEq (A := A) p (S k)))
    (residualNat p (wgen (S k) (S q) a)) :=
  shiftPrefixResidualNat p (wgen k q a)
    • f_equal (fun w => compNatTrans
        (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _ (shiftPrefixFunctorEq (A := A) p (S k)))
        (residualNat p w)) (residualOneGen k q Hq a).

Definition residualNatExchange {A: HSet} (p k q: nat) (Hq: q <= k) (a c: A):
  compNatTrans (residualNat p (wgen (S k) (S q) a)) (residualNat p (wgen k 0 c)) =
    compNatTrans (residualNat p (wgen (S k) 0 c)) (residualNat p (wgen k q a)) :=
  residualNatComp p (wgen k 0 c) (wgen (S k) (S q) a)
    • (f_equal (fun w => residualNat p w) (eq_sym (wgenExchange k q Hq 0 leR_O a c))
      • eq_sym (residualNatComp p (wgen k q a) (wgen (S k) 0 c))).

Section BridgeFace.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation MD := (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F).
Local Abbreviation Q := (MatchingPartialPresentation p F).
Local Abbreviation CS n := (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) n)).

Definition shiftPrefixBridgeFace k q (Hq: q <= k) a
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) (S k) F))):
  shiftPrefixBridge p k F (mapMatching (shiftMap (residualMap (S p) F (wgen k q a))) b) =
    Q.(GFace) (S k) (S q) (⇑ Hq) a (shiftPrefixBridge p (S k) F b) :=
  f_equal (matchingAction p (Op (νSemiShape A)) F (CS k) (shiftPrefixFunctor A p (S k))
      (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A)))
        (CS k) (shiftPrefixFunctor A p (S k)) (shiftPrefixFunctorEq (A := A) p k)))
    (matchingCompositeNatural (shiftFunctor A p)
      (shiftPrefixFunctor A (S p) (S k)) (shiftPrefixFunctor A (S p) k) F
      (residualNat (S p) (wgen k q a)) b)
  • diagramSquare MD (whiskerLNat (shiftFunctor A p) (residualNat (S p) (wgen k q a)))
      (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A)))
        (CS k) (shiftPrefixFunctor A p (S k)) (shiftPrefixFunctorEq (A := A) p k))
      (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A)))
        (CS (S k)) (shiftPrefixFunctor A p (S (S k)))
        (shiftPrefixFunctorEq (A := A) p (S k)))
      (residualNat p (wgen (S k) (S q) a)) (shiftPrefixResidualFace p k q Hq a)
      (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) (S k)) F b).

Definition matchingTopFactor k a (b: MatchingObject (pullbackDiagram (CS k) F)) :=
  diagramFactor MD (shiftPrefixFunctorEq (A := A) p k) (residualNat p (wgen k 0 a))
    (paddedTopNat p k a) (shiftTopNatComp p k a) b.

Lemma shiftPrefixTopFaceFactor k a
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F))):
  shiftPrefixTopFace p k F a b = topFaceFlatten p k F a b
    • eq_sym (matchingTopFactor k a
        (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b)).
Proof. now reflexivity. Defined.

Lemma matchingMixedReverse k q (Hq: q <= k) a c
  (b: Q.(G0) (S (S k))):
  diagramSquare MD (residualNat p (wgen (S k) (S q) a)) (residualNat p (wgen k 0 c))
    (residualNat p (wgen (S k) 0 c)) (residualNat p (wgen k q a))
    (residualNatExchange p k q Hq a c) b = eq_sym (Q.(GFaceCoh) k q Hq 0 leR_O a c b).
Proof.
  change (diagramRelation (pathData _ _ MD.(pfStr))
    (residualNat p (wgen (S k) (S q) a)) (residualNat p (wgen k 0 c))
    (residualNat p (wgen (S k) 0 c)) (residualNat p (wgen k q a))
    (residualNatExchange p k q Hq a c) b =
    eq_sym (diagramRelation (pathData _ _ (MatchingPartialDiagram p F).(pfStr))
      (wgen (S k) 0 c) (wgen k q a) (wgen (S k) (S q) a) (wgen k 0 c)
      (wgenExchange k q Hq 0 leR_O a c) b)).
  refine (_ • f_equal (@eq_sym _ _ _) (eq_sym
    (pullbackDiagramRelation (residualFunctor A p) MD
      (wgen (S k) 0 c) (wgen k q a) (wgen (S k) (S q) a) (wgen k 0 c)
      (wgenExchange k q Hq 0 leR_O a c) (eq_sym (residualNatExchange p k q Hq a c)) b))).
  unfold diagramRelation, phomEq. rewrite fEqualSym.
  now apply reverseRelationAlgebra.
Defined.

Lemma shiftPrefixTopFaceFace k q (Hq: q <= k) a c
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) (S k) F))):
  shiftPrefixTopFace p k F c
      (mapMatching (shiftMap (residualMap (S p) F (wgen k q a))) b)
    • (f_equal (Q.(GFace) k 0 leR_O c) (shiftPrefixBridgeFace k q Hq a b)
      • eq_sym (Q.(GFaceCoh) k q Hq 0 leR_O a c (shiftPrefixBridge p (S k) F b))) =
  @residualTopFaceMapNatural A p F k (S k) (wgen k q a) c b
    • f_equal (@residualMatching A p F k (S k) (wgen k q a))
        (@shiftPrefixTopFace A p (S k) F c b).
Proof.
  refine (transCongR (shiftPrefixTopFaceFactor k c
    (mapMatching (shiftMap (residualMap (S p) F (wgen k q a))) b)) _ • _).
  refine (_ • eq_sym (transCongL
    (residualTopFaceMapNatural p F (wgen k q a) c b)
    (f_equal (fun e => f_equal (residualMatching p F (wgen k q a)) e)
      (shiftPrefixTopFaceFactor (S k) c b)))).
  refine (transCongL _ (transCongL _
    (eq_sym (matchingMixedReverse k q Hq a c (shiftPrefixBridge p (S k) F b)))) • _).
  unfold shiftPrefixBridgeFace.
  lazymatch goal with
  | |- context [f_equal ?h (?first • ?second)] =>
      rewrite (eq_trans_map_distr h first second)
  end.
  lazymatch goal with
  | |- context [f_equal ?h (?first • ?second)] =>
      rewrite (eq_trans_map_distr h first second)
  end.
  lazymatch goal with
  | |- context [f_equal ?h (eq_sym ?path)] =>
      rewrite (fEqualSym h path)
  end.
  eapply factorCubeAlgebra.
  - rewrite f_equal_compose.
    now exact (homotopyNat _ _ (matchingTopFactor k c)
      (matchingCompositeNatural (shiftFunctor A p)
        (shiftPrefixFunctor A (S p) (S k)) (shiftPrefixFunctor A (S p) k) F
        (residualNat (S p) (wgen k q a)) b)).
  - now exact (diagramIsoCube MD (shiftPrefixFunctorEq (A := A) p (S k)) (shiftPrefixFunctorEq (A := A) p k)
      (whiskerLNat (shiftFunctor A p) (residualNat (S p) (wgen k q a)))
      (residualNat p (wgen (S k) (S q) a)) (residualNat p (wgen k q a))
      (paddedTopNat p (S k) c) (paddedTopNat p k c)
      (residualNat p (wgen (S k) 0 c)) (residualNat p (wgen k 0 c))
      (shiftPrefixResidualFace p k q Hq a)
      (shiftTopNatComp p (S k) c) (shiftTopNatComp p k c)
      (paddedTopResidual p (wgen k q a) c) (residualNatExchange p k q Hq a c)
      (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) (S k)) F b)).
  - now exact (topFaceMapNaturalityFlatten p F (wgen k q a) c b).
Defined.

Lemma residualMapBoundary k q (Hq: q <= k) a
  (t: (wholeCellDiagram p F).(pfObj) (S k)):
  truncatedResidualComparison p F (wgen k q a) (partialBoundary p F (S k) t)
    • boundaryNatural p F (wgen k q a) t =
  mapBoundary (residualMap (S p) F (wgen k q a)) t.
Proof.
  apply (matchingPathExt (shiftedPrefix p k F)); intros i g.
  lazymatch goal with
  | |- context [f_equal ?read (?first • ?second)] =>
      rewrite (eq_trans_map_distr read first second)
  end.
  rewrite (truncatedResidualComparisonValue p F (wgen k q a)
    (partialBoundary p F (S k) t) i g).
  pose proof (boundaryNaturalValue p F (wgen k q a) t i g) as hb.
  lazymatch goal with
  | |- @eq ?P ?lhsExpr (f_equal ?read (@mapBoundary ?AA ?nn ?XX ?YY ?DD ?tt)) =>
      pose proof (@mapBoundaryValue AA nn XX YY DD tt i g) as hmExact
  end.
  lazymatch goal with
  | |- @eq ?P ?lhsExpr ?rhsExpr =>
      lazymatch type of hb with
      | @eq _ _ ?common =>
          assert (hmGoal : @eq P rhsExpr common) by exact hmExact
      end
  end.
  assert (unitThroughCommon : forall (T: Type) (x y: T) (u v w: x = y),
    u = w -> v = w -> eq_refl • u = v).
  { intros T x y u v w hu hv. subst u v. now destruct w. }
  cbv beta iota zeta delta
    [matchingValue mapMatching mapValues SigT.projT1 residualMatching]
    in hb, hmExact, hmGoal |- *.
  lazymatch goal with
  | |- @eq ?P (@eq_trans _ _ _ _ _ ?lhsPath) ?rhsPath =>
      lazymatch type of hmGoal with
      | @eq _ _ ?common =>
          assert (hbGoal : @eq P lhsPath common) by exact hb
      end
  end.
  lazymatch goal with
  | |- @eq (@eq ?C ?x ?y) (@eq_trans _ _ _ _ _ ?lhsPath) ?rhsPath =>
      lazymatch type of hbGoal with
      | @eq _ _ ?common =>
          now exact (unitThroughCommon C x y lhsPath rhsPath common hbGoal hmGoal)
      end
  end.
Defined.

Lemma splitMapAttachmentResidual k q (Hq: q <= k) a
  (s: SplitMatching (shiftedPrefix (S p) (S k) F)) c:
  ((splitMap (residualMap (S p) F (wgen k q a)) s).2 c).2 =
    residualTopFaceMapNatural p F (wgen k q a) c s.1
      • (f_equal (residualMatching p F (wgen k q a)) (s.2 c).2
        • boundaryNatural p F (wgen k q a) (s.2 c).1).
Proof.
  now exact (comparisonPathPaste
    (mapMatching (truncateMap (residualMap (S p) F (wgen k q a))))
    (residualMatching p F (wgen k q a))
    (truncatedResidualComparison p F (wgen k q a))
    (s.2 c).2 (topFaceMapNatural (residualMap (S p) F (wgen k q a)) c s.1)
    (mapBoundary (residualMap (S p) F (wgen k q a)) (s.2 c).1)
    (boundaryNatural p F (wgen k q a) (s.2 c).1)
    (residualMapBoundary k q Hq a (s.2 c).1)).
Defined.

Lemma matchingStepBridgeFaceSquare k q (Hq: q <= k) a
  (s: SplitMatching (shiftedPrefix (S p) (S k) F)) c:
  f_equal (Q.(GFace) k 0 leR_O c) (shiftPrefixBridgeFace k q Hq a s.1)
    • ((matchingStepFace p F k q Hq a (matchingStepBridge p F (S k) s)).2 c).2
  = ((matchingStepBridge p F k (splitMap (residualMap (S p) F (wgen k q a)) s)).2 c).2.
Proof.
  change (f_equal (Q.(GFace) k 0 leR_O c) (shiftPrefixBridgeFace k q Hq a s.1)
    • (eq_sym (Q.(GFaceCoh) k q Hq 0 leR_O a c (shiftPrefixBridge p (S k) F s.1))
      • (f_equal (residualMatching p F (wgen k q a))
          (eq_sym (shiftPrefixTopFace p (S k) F c s.1) • (s.2 c).2)
        • boundaryNatural p F (wgen k q a) (s.2 c).1)) =
    eq_sym (shiftPrefixTopFace p k F c
      (mapMatching (shiftMap (residualMap (S p) F (wgen k q a))) s.1))
      • ((splitMap (residualMap (S p) F (wgen k q a)) s).2 c).2).
  rewrite (splitMapAttachmentResidual k q Hq a s c).
  rewrite (eq_trans_map_distr (residualMatching p F (wgen k q a))
    (eq_sym (shiftPrefixTopFace p (S k) F c s.1)) (s.2 c).2).
  rewrite (fEqualSym (residualMatching p F (wgen k q a))
    (shiftPrefixTopFace p (S k) F c s.1)).
  apply attachmentBridgeAlgebra.
  now exact (shiftPrefixTopFaceFace k q Hq a c s.1).
Defined.

Definition matchingStepBridgeFace k q (Hq: q <= k) a
  (s: SplitMatching (shiftedPrefix (S p) (S k) F)):
  matchingStepBridge p F k (splitMap (residualMap (S p) F (wgen k q a)) s) =
    matchingStepFace p F k q Hq a (matchingStepBridge p F (S k) s) :=
  attachmentEq (fun c => Q.(GFace) k 0 leR_O c) (partialBoundary p F k)
    (matchingStepBridge p F k (splitMap (residualMap (S p) F (wgen k q a)) s))
    (matchingStepFace p F k q Hq a (matchingStepBridge p F (S k) s))
    (shiftPrefixBridgeFace k q Hq a s.1) (fun _ => eq_refl)
    (matchingStepBridgeFaceSquare k q Hq a s).

Lemma matchingStepBridgeFaceBase k q (Hq: q <= k) a
  (s: SplitMatching (shiftedPrefix (S p) (S k) F)):
  f_equal (fun z: MatchingStep p F k => z.1) (matchingStepBridgeFace k q Hq a s) =
    shiftPrefixBridgeFace k q Hq a s.1.
Proof. now apply attachmentEqBase. Defined.

Lemma matchingStepBridgeFaceCell k q (Hq: q <= k) a
  (s: SplitMatching (shiftedPrefix (S p) (S k) F)) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1)
    (matchingStepBridgeFace k q Hq a s) = eq_refl.
Proof.
  unfold matchingStepBridgeFace.
  now exact (attachmentEqTop (fun c => Q.(GFace) k 0 leR_O c) (partialBoundary p F k)
    (matchingStepBridge p F k (splitMap (residualMap (S p) F (wgen k q a)) s))
    (matchingStepFace p F k q Hq a (matchingStepBridge p F (S k) s))
    (shiftPrefixBridgeFace k q Hq a s.1) (fun _ => eq_refl)
    (matchingStepBridgeFaceSquare k q Hq a s) c).
Defined.
End BridgeFace.

(** The base map of the partial matching split and its face coherence. *)

Section NormalizedBase.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation MD := (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F).
Local Abbreviation U := (shiftedResidualFunctor A p).
Local Abbreviation V := (residualFunctor A p).
Local Abbreviation alpha := (shiftPrefixResidualTransformation A p).
Local Abbreviation P := (MatchingPartialPresentation (S p) F).
Local Abbreviation D := (keptResidualPresentation p F).
Local Abbreviation Q := (MatchingPartialPresentation p F).
Local Abbreviation phi := (residualShiftCell MD U V alpha).
Local Abbreviation phiFace := (residualShiftFace MD U V alpha).

Definition splitBaseMap k (m: P.(G0) k): Q.(G0) (S k) :=
  phi k (keptResidualMap p F k m).

Definition splitBaseFace k q (Hq: q <= k) a (m: P.(G0) (S k)):
  splitBaseMap k (P.(GFace) k q Hq a m) =
    Q.(GFace) (S k) (S q) (⇑ Hq) a (splitBaseMap (S k) m) :=
  f_equal (phi k) (keptResidualFace p F k q Hq a m)
    • phiFace k q Hq a (keptResidualMap p F (S k) m).

Lemma splitBaseFaceCoh k q (Hq: q <= k) r (Hr: r <= q) a b
  (m: P.(G0) (S (S k))):
  (splitBaseFace k q Hq a (P.(GFace) (S k) r (Hr ↕ ↑ Hq) b m)
    • f_equal (Q.(GFace) (S k) (S q) (⇑ Hq) a)
      (splitBaseFace (S k) r (Hr ↕ ↑ Hq) b m))
    • Q.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b
      (splitBaseMap (S (S k)) m) =
  f_equal (splitBaseMap k) (P.(GFaceCoh) k q Hq r Hr a b m)
    • (splitBaseFace k r (Hr ↕ Hq) b (P.(GFace) (S k) (S q) (⇑ Hq) a m)
      • f_equal (Q.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) b)
        (splitBaseFace (S k) (S q) (⇑ Hq) a m)).
Proof.
  now exact (composeForwardFaceSquare
    (keptResidualMap p F k) (keptResidualMap p F (S k)) (keptResidualMap p F (S (S k)))
    (phi k) (phi (S k)) (phi (S (S k)))
    (P.(GFace) k q Hq a) (P.(GFace) k r (Hr ↕ Hq) b)
    (P.(GFace) (S k) r (Hr ↕ ↑ Hq) b) (P.(GFace) (S k) (S q) (⇑ Hq) a)
    (D.(GFace) k q Hq a) (D.(GFace) k r (Hr ↕ Hq) b)
    (D.(GFace) (S k) r (Hr ↕ ↑ Hq) b) (D.(GFace) (S k) (S q) (⇑ Hq) a)
    (Q.(GFace) (S k) (S q) (⇑ Hq) a) (Q.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) b)
    (Q.(GFace) (S (S k)) (S r) (⇑ (Hr ↕ ↑ Hq)) b)
    (Q.(GFace) (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a)
    (keptResidualFace p F k q Hq a) (keptResidualFace p F k r (Hr ↕ Hq) b)
    (keptResidualFace p F (S k) r (Hr ↕ ↑ Hq) b)
    (keptResidualFace p F (S k) (S q) (⇑ Hq) a)
    (phiFace k q Hq a) (phiFace k r (Hr ↕ Hq) b)
    (phiFace (S k) r (Hr ↕ ↑ Hq) b) (phiFace (S k) (S q) (⇑ Hq) a)
    (P.(GFaceCoh) k q Hq r Hr a b)
    (D.(GFaceCoh) k q Hq r Hr a b)
    (Q.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a b) m
    (keptResidualFaceCoh p F k q Hq r Hr a b m)
    (residualShiftFaceCoh MD U V alpha k q Hq r Hr a b
      (keptResidualMap p F (S (S k)) m))).
Defined.

Local Opaque matchingCompEquiv keepMatching mapMatching.

Lemma splitBaseFaceFormula k q (Hq: q <= k) a (m: P.(G0) (S k)):
  f_equal (shiftPrefixBridge p k F)
      (eq_sym (keepMap (residualMap (S p) F (wgen k q a)) m))
    • shiftPrefixBridgeFace p F k q Hq a
      (keepMatching (shiftedPrefix (S p) (S k) F) m)
  = splitBaseFace k q Hq a m.
Proof.
  unfold splitBaseFace, keptResidualFace, shiftPrefixBridgeFace.
  rewrite eq_trans_map_distr.
  rewrite (residualShiftFaceRelation MD U V alpha k q Hq a
    (keptResidualMap p F (S k) m) (shiftPrefixResidualFace p k q Hq a)).
  change (f_equal (shiftPrefixBridge p k F)
      (eq_sym (keepMap (residualMap (S p) F (wgen k q a)) m)))
    with (f_equal (fun x => phi k
      (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F x))
      (eq_sym (keepMap (residualMap (S p) F (wgen k q a)) m))).
  rewrite <- f_equal_compose.
  now apply eq_sym, eqTransAssoc.
Defined.
Local Transparent matchingCompEquiv keepMatching mapMatching.
End NormalizedBase.

Unset Keyed Unification.

(** Faces of the partial matching split equivalence and their coherence. *)

Section NormalizedSplit.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation P := (MatchingPartialPresentation (S p) F).
Local Abbreviation Q := (MatchingStepPresentation p F).

Definition matchingPartialSplitFace k q (Hq: q <= k) a (m: P.(G0) (S k)):
  matchingPartialSplitEquiv p F k (P.(GFace) k q Hq a m) =
    Q.(GFace) k q Hq a (matchingPartialSplitEquiv p F (S k) m) :=
  f_equal (matchingStepBridge p F k)
    (splitNaturality (residualMap (S p) F (wgen k q a)) m)
    • matchingStepBridgeFace p F k q Hq a
        (splitMatching (shiftedPrefix (S p) (S k) F) m).

Local Lemma stepBridgeBaseAp k
  {s t: SplitMatching (shiftedPrefix (S p) k F)} (e: s = t):
  projT1_eq (f_equal (matchingStepBridge p F k) e) =
    f_equal (shiftPrefixBridge p k F) (projT1_eq e).
Proof. now destruct e. Defined.

Local Lemma stepBridgeCellAp k
  {s t: SplitMatching (shiftedPrefix (S p) k F)} (e: s = t) a:
  f_equal (fun z: MatchingStep p F k => (z.2 a).1)
    (f_equal (matchingStepBridge p F k) e) =
  f_equal (fun z: SplitMatching (shiftedPrefix (S p) k F) => (z.2 a).1) e.
Proof. now destruct e. Defined.

Lemma matchingPartialSplitFaceBase k q (Hq: q <= k) a (m: P.(G0) (S k)):
  f_equal (fun z: MatchingStep p F k => z.1)
    (matchingPartialSplitFace k q Hq a m) =
    f_equal (shiftPrefixBridge p k F)
      (eq_sym (keepMap (residualMap (S p) F (wgen k q a)) m))
    • shiftPrefixBridgeFace p F k q Hq a
        (keepMatching (shiftedPrefix (S p) (S k) F) m).
Proof.
  unfold matchingPartialSplitFace. rewrite eq_trans_map_distr.
  refine (transCongR
    (stepBridgeBaseAp k (splitNaturality (residualMap (S p) F (wgen k q a)) m)) _ • _).
  refine (transCongR (f_equal (fun e => f_equal (shiftPrefixBridge p k F) e)
    (splitNaturalityBase (residualMap (S p) F (wgen k q a)) m)) _ • _).
  now exact (transCongL _ (matchingStepBridgeFaceBase p F k q Hq a
    (splitMatching (shiftedPrefix (S p) (S k) F) m))).
Defined.

Lemma matchingPartialSplitFaceCell k q (Hq: q <= k) a (m: P.(G0) (S k)) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1)
    (matchingPartialSplitFace k q Hq a m) = eq_refl.
Proof.
  unfold matchingPartialSplitFace. rewrite eq_trans_map_distr.
  refine (transCongR
    (stepBridgeCellAp k (splitNaturality (residualMap (S p) F (wgen k q a)) m) c) _ • _).
  refine (transCongR
    (splitNaturalityTop (residualMap (S p) F (wgen k q a)) m c) _ • _).
  refine (transCongL _ (matchingStepBridgeFaceCell p F k q Hq a
    (splitMatching (shiftedPrefix (S p) (S k) F) m) c) • _).
  now reflexivity.
Defined.

Lemma matchingPartialSplitMapPathCell k {m n: P.(G0) k} (h: m = n) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1)
    (f_equal (matchingPartialSplitEquiv p F k) h) =
  f_equal (fun z: P.(G0) k => matchingValue z None (wskip c (wid p))) h.
Proof. now destruct h. Defined.

Lemma matchingPartialSplitExchangeCell k q (Hq: q <= k) r (Hr: r <= q) a b
  (m: P.(G0) (S (S k))) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1)
    (f_equal (matchingPartialSplitEquiv p F k) (P.(GFaceCoh) k q Hq r Hr a b m)) =
  (ofPsfTot A (wholeCellDiagram p F)).(GFaceCoh) k q Hq r Hr a b
    ((matchingPartialSplitEquiv p F (S (S k)) m).2 c).1.
Proof.
  refine (matchingPartialSplitMapPathCell k (P.(GFaceCoh) k q Hq r Hr a b m) c • _).
  now exact (matchingPartialExchangeReadout (S p) F k q Hq r Hr a b m
    None (wskip c (wid p))).
Defined.

Lemma matchingPartialSplitMapPathBase k {m n: P.(G0) k} (h: m = n):
  f_equal (fun z: MatchingStep p F k => z.1)
    (f_equal (matchingPartialSplitEquiv p F k) h) =
    f_equal (splitBaseMap p F k) h.
Proof. now destruct h. Defined.

Local Lemma matchingStepFaceBaseAp k q (Hq: q <= k) a
  {m n: Q.(G0) (S k)} (h: m = n):
  f_equal (fun z: MatchingStep p F k => z.1)
    (f_equal (Q.(GFace) k q Hq a) h) =
  f_equal ((MatchingPartialPresentation p F).(GFace) (S k) (S q) (⇑ Hq) a)
    (f_equal (fun z: MatchingStep p F (S k) => z.1) h).
Proof. now destruct h. Defined.

Local Lemma matchingStepFaceCellAp k q (Hq: q <= k) a
  {m n: Q.(G0) (S k)} (h: m = n) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1)
    (f_equal (Q.(GFace) k q Hq a) h) =
  f_equal ((ofPsfTot A (wholeCellDiagram p F)).(GFace) k q Hq a)
    (f_equal (fun z: MatchingStep p F (S k) => (z.2 c).1) h).
Proof. now destruct h. Defined.

Lemma matchingStepPathExt k {s t: MatchingStep p F k} (u v: s = t)
  (basePaths: f_equal (fun z: MatchingStep p F k => z.1) u =
    f_equal (fun z: MatchingStep p F k => z.1) v)
  (cellPaths: forall c, f_equal (fun z: MatchingStep p F k => (z.2 c).1) u =
    f_equal (fun z: MatchingStep p F k => (z.2 c).1) v): u = v.
Proof.
  now exact (GpdCone.attachmentPathExt
    (fun c => (MatchingPartialPresentation p F).(GFace) k 0 leR_O c)
    (partialBoundary p F k) u v basePaths cellPaths).
Defined.

Local Opaque matchingCompEquiv keepMatching mapMatching.
Local Lemma matchingPartialSplitFaceBaseFormula k q (Hq: q <= k) a
  (m: P.(G0) (S k)):
  f_equal (fun z: MatchingStep p F k => z.1)
    (matchingPartialSplitFace k q Hq a m) =
    splitBaseFace p F k q Hq a m.
Proof.
  refine (matchingPartialSplitFaceBase k q Hq a m • _).
  now exact (splitBaseFaceFormula p F k q Hq a m).
Defined.
Local Transparent matchingCompEquiv keepMatching mapMatching.

Local Ltac rewriteConcreteNormalizedBase :=
  multimatch goal with
  | |- context [(?ap ?dom ?cod ?read ?x ?y ?path)] =>
      lazymatch ap with
      | @f_equal =>
          lazymatch path with
          | @matchingPartialSplitFace ?level ?slot ?bound ?color ?point =>
              let actual := constr:(ap dom cod read x y path) in
              let carrier := type of actual in
              let readoutProof := constr:(matchingPartialSplitFaceBaseFormula level slot bound color point) in
              let readoutType := type of readoutProof in
              lazymatch readoutType with
              | @eq _ _ ?result =>
                  let aligned := fresh "baseReadout" in
                  assert (aligned : @eq carrier actual result) by exact readoutProof;
                  rewrite aligned;
                  clear aligned
              end
          end
      end
  end.

Local Ltac rewriteConcreteCell cell :=
  multimatch goal with
  | |- context [(?ap ?dom ?cod ?read ?x ?y ?path)] =>
      lazymatch ap with
      | @f_equal =>
          lazymatch path with
          | @matchingPartialSplitFace ?level ?slot ?bound ?color ?point =>
              let actual := constr:(ap dom cod read x y path) in
              let carrier := type of actual in
              let readoutProof := constr:(matchingPartialSplitFaceCell level slot bound color point cell) in
              let readoutType := type of readoutProof in
              lazymatch readoutType with
              | @eq _ _ ?result =>
                  let aligned := fresh "cellReadout" in
                  assert (aligned : @eq carrier actual result) by exact readoutProof;
                  rewrite aligned;
                  clear aligned
              end
          end
      end
  end.

Lemma matchingPartialSplitFaceCoh k q (Hq: q <= k) r (Hr: r <= q) a b
  (m: P.(G0) (S (S k))):
  (matchingPartialSplitFace k q Hq a (P.(GFace) (S k) r (Hr ↕ ↑ Hq) b m)
    • f_equal (Q.(GFace) k q Hq a)
      (matchingPartialSplitFace (S k) r (Hr ↕ ↑ Hq) b m))
    • Q.(GFaceCoh) k q Hq r Hr a b (matchingPartialSplitEquiv p F (S (S k)) m) =
  f_equal (matchingPartialSplitEquiv p F k) (P.(GFaceCoh) k q Hq r Hr a b m)
    • (matchingPartialSplitFace k r (Hr ↕ Hq) b (P.(GFace) (S k) (S q) (⇑ Hq) a m)
      • f_equal (Q.(GFace) k r (Hr ↕ Hq) b)
        (matchingPartialSplitFace (S k) (S q) (⇑ Hq) a m)).
Proof.
  apply (matchingStepPathExt k).
  - rewrite 4 eq_trans_map_distr.
    rewrite matchingStepFaceBaseAp.
    rewrite matchingStepFaceBaseAp.
    Local Opaque matchingCompEquiv keepMatching mapMatching.
    lazymatch goal with
    | |- @eq _ _ (@eq_trans _ _ _ _ ?actual _) =>
        lazymatch actual with
        | f_equal ?read (f_equal ?forward ?path) =>
            lazymatch forward with
            | @eqvFun _ _ (@matchingPartialSplitEquiv _ _ _ ?level) =>
                lazymatch type of forward with
                | ?domain -> _ =>
                    let composed := constr:(fun x: domain => read (forward x)) in
                    rewrite (f_equal_compose forward read path);
                    change composed with (splitBaseMap p F level)
                end
            end
        end
    end.
    Local Transparent matchingCompEquiv keepMatching mapMatching.
    do 4 rewriteConcreteNormalizedBase.
    rewrite (matchingStepExchangeBase p F k q Hq r Hr a b
      (matchingPartialSplitEquiv p F (S (S k)) m)).
    now exact (splitBaseFaceCoh p F k q Hq r Hr a b m).
  - intro c. rewrite 4 eq_trans_map_distr.
    rewrite matchingStepFaceCellAp.
    rewrite matchingStepFaceCellAp.
    rewrite matchingPartialSplitExchangeCell.
    rewrite (matchingStepExchangeCell p F k q Hq r Hr a b
      (matchingPartialSplitEquiv p F (S (S k)) m) c).
    cbn [f_equal].
    do 4 (rewriteConcreteCell c).
    cbn [f_equal]. now rewrite eq_trans_refl_l, eq_trans_refl_r.
Defined.

End NormalizedSplit.
