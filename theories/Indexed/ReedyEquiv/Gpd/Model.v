(** Comparisons of coherent presentations over a common presentation of cells. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Contractible Notation LeSProp RewLemmas Funext.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Cone.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** A comparison of partial-frame diagrams preserves restrictions and
    their chosen exchange paths. The boundary modification also preserves
    the projection of each whole cell to its partial frame. *)
Record PartialDiagramModel {A: HSet}
  {P Q C: νGpdPresentation A}
  {sourceBoundary: forall n, C.(G0) n -> P.(G0) n}
  {matchingBoundary: forall n, C.(G0) n -> Q.(G0) n}
  {sourceBoundaryFace: forall n q (Hq: q <= n) a x,
    sourceBoundary n (C.(GFace) n q Hq a x)
      = P.(GFace) n q Hq a (sourceBoundary (S n) x)}
  {matchingBoundaryFace: forall n q (Hq: q <= n) a x,
    matchingBoundary n (C.(GFace) n q Hq a x)
      = Q.(GFace) n q Hq a (matchingBoundary (S n) x)} := {
  modelEquiv n: Equiv (P.(G0) n) (Q.(G0) n);
  modelFace n q (Hq: q <= n) a x:
    modelEquiv n (P.(GFace) n q Hq a x)
      = Q.(GFace) n q Hq a (modelEquiv (S n) x);
  modelFaceCoh n q (Hq: q <= n) r (Hr: r <= q) a b x:
    (modelFace n q Hq a (P.(GFace) (S n) r (Hr ↕ ↑ Hq) b x)
      • f_equal (Q.(GFace) n q Hq a)
          (modelFace (S n) r (Hr ↕ ↑ Hq) b x))
      • Q.(GFaceCoh) n q Hq r Hr a b (modelEquiv (S (S n)) x)
    = f_equal (modelEquiv n) (P.(GFaceCoh) n q Hq r Hr a b x)
      • (modelFace n r (Hr ↕ Hq) b (P.(GFace) (S n) (S q) (⇑ Hq) a x)
        • f_equal (Q.(GFace) n r (Hr ↕ Hq) b)
            (modelFace (S n) (S q) (⇑ Hq) a x));
  modelBoundary n x:
    modelEquiv n (sourceBoundary n x) = matchingBoundary n x;
  modelBoundaryFace n q (Hq: q <= n) a x:
    f_equal (modelEquiv n) (sourceBoundaryFace n q Hq a x)
      • (modelFace n q Hq a (sourceBoundary (S n) x)
        • f_equal (Q.(GFace) n q Hq a) (modelBoundary (S n) x))
    = modelBoundary n (C.(GFace) n q Hq a x)
      • matchingBoundaryFace n q Hq a x;
}.


Arguments PartialDiagramModel {A} P Q C sourceBoundary matchingBoundary
  sourceBoundaryFace matchingBoundaryFace.

(** Equality transport for coherent augmented presentations.
    Requires the PartialDiagramModel record and Lib.Funext. *)

Definition BoundaryMap {A: HSet} (C Q: νGpdPresentation A): Type :=
  forall n, C.(G0) n -> Q.(G0) n.

Definition BoundaryFace {A: HSet} {C Q: νGpdPresentation A}
  (b: BoundaryMap C Q): Type :=
  forall n q (Hq: q <= n) a x,
    b n (C.(GFace) n q Hq a x) = Q.(GFace) n q Hq a (b (S n) x).

Definition ModelTargetData {A: HSet} (C: νGpdPresentation A): Type :=
  {Q: νGpdPresentation A &T {b: BoundaryMap C Q &T BoundaryFace b}}.

Definition ModelAtTarget {A: HSet} {P C: νGpdPresentation A}
  {source: BoundaryMap C P} (sourceFace: BoundaryFace source)
  (target: ModelTargetData C): Type :=
  PartialDiagramModel P target.1 C source target.2.1 sourceFace target.2.2.

Definition transportModelTarget {A: HSet} {P C: νGpdPresentation A}
  {source: BoundaryMap C P} {sourceFace: BoundaryFace source}
  {target1 target2: ModelTargetData C} (e: target1 = target2)
  (M: ModelAtTarget sourceFace target1): ModelAtTarget sourceFace target2 :=
  rew [ModelAtTarget sourceFace] e in M.

Definition modelTargetEquality {A: HSet} {P Q C: νGpdPresentation A}
  {bP: BoundaryMap C P} {bQ: BoundaryMap C Q}
  {faceP: BoundaryFace bP} {faceQ: BoundaryFace bQ}
  (M: PartialDiagramModel P Q C bP bQ faceP faceQ):
  ((P; (bP; faceP)): ModelTargetData C) = (Q; (bQ; faceQ)).
Proof.
  destruct P as [G Fa Ca Da], Q as [H Fb Cb Db].
  destruct M as [E phi coh theta square]. cbn in *.
  revert Fb Cb Db phi coh bQ faceQ theta square.
  pattern H, E. apply hgpdFamilyEquivInd.
  intros Fb Cb Db phi coh bQ faceQ theta square. cbn in *.
  revert Cb Db coh bQ faceQ theta square.
  pattern Fb, phi. apply (homInd5S (I1 := nat) (I2 := fun _ => nat) (I3 := fun n q => q <= n)
    (I4 := fun _ _ _ => A) (I5 := fun n _ _ _ => G (S n))
    (B := fun n _ _ _ _ => G n) Fa).
  intros Cb Db coh bQ faceQ theta square.
  assert (HC: Ca = Cb).
  { apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro r.
    apply spropFunext; intro Hr.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro x.
    pose proof (coh n q Hq r Hr a b x) as K.
    cbn [f_equal] in K. rewrite f_equal_id in K.
    rewrite eq_trans_refl_l, eq_trans_refl_r in K. now symmetry. }
  destruct HC.
  assert (HD: Da = Db).
  { apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro r.
    apply spropFunext; intro Hr.
    apply functional_extensionality_dep; intro s.
    apply spropFunext; intro Hs.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro c.
    apply functional_extensionality_dep; intro x.
    now apply (G n).(GUIP). }
  destruct HD.
  revert faceQ square.
  pattern bQ, theta. apply (homInd2 bP).
  intros faceQ square.
  assert (HF: faceP = faceQ).
  { apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro x.
    pose proof (square n q Hq a x) as K.
    cbn [f_equal] in K. rewrite f_equal_id in K.
    rewrite 2 eq_trans_refl_l, eq_trans_refl_r in K. now exact K. }
  now destruct HF.
Defined.

Definition identityPartialDiagramModel {A: HSet} {P C: νGpdPresentation A}
  (b: BoundaryMap C P) (face: BoundaryFace b):
  PartialDiagramModel P P C b b face face.
Proof.
  refine {| modelEquiv n := idEquiv;
    modelFace n q Hq a x := eq_refl;
    modelBoundary n x := eq_refl |}.
  - intros n q Hq r Hr a b' x. cbn [f_equal].
    rewrite f_equal_id, eq_trans_refl_l, eq_trans_refl_r. now reflexivity.
  - intros n q Hq a x. cbn [f_equal].
    rewrite f_equal_id, 2 eq_trans_refl_l, eq_trans_refl_r. now reflexivity.
Defined.

Definition modelOfTargetEquality {A: HSet} {P Q C: νGpdPresentation A}
  {bP: BoundaryMap C P} {bQ: BoundaryMap C Q}
  {faceP: BoundaryFace bP} {faceQ: BoundaryFace bQ}
  (e: ((P; (bP; faceP)): ModelTargetData C) = (Q; (bQ; faceQ))):
  PartialDiagramModel P Q C bP bQ faceP faceQ :=
  transportModelTarget e (identityPartialDiagramModel bP faceP).

Definition precomposeModelTarget {A: HSet} {C D: νGpdPresentation A}
  (cell: forall n, C.(G0) n -> D.(G0) n)
  (cellFace: forall n q (Hq: q <= n) a x,
    cell n (C.(GFace) n q Hq a x) = D.(GFace) n q Hq a (cell (S n) x))
  (target: ModelTargetData D): ModelTargetData C :=
  (target.1;
    (fun n x => target.2.1 n (cell n x);
      fun n q Hq a x => f_equal (target.2.1 n) (cellFace n q Hq a x)
        • target.2.2 n q Hq a (cell (S n) x))).

Definition precomposeModelTargetIsEquiv {A: HSet} {C D: νGpdPresentation A}
  (cell: forall n, Equiv (C.(G0) n) (D.(G0) n))
  (cellFace: forall n q (Hq: q <= n) a x,
    cell n (C.(GFace) n q Hq a x) = D.(GFace) n q Hq a (cell (S n) x)):
  IsEquiv (precomposeModelTarget (C := C) (D := D) (fun n => cell n) cellFace).
Proof.
  destruct C as [G f c d], D as [H g c' d'].
  cbn in cell, cellFace |- *.
  revert g c' d' cellFace.
  pattern H, cell. apply hgpdFamilyEquivInd.
  intros g c' d' cellFace. cbn in cellFace |- *.
  revert c' d'.
  pattern g, cellFace.
  apply (homInd5S (I1 := nat) (I2 := fun _ => nat) (I3 := fun n q => q <= n)
    (I4 := fun _ _ _ => A) (I5 := fun n _ _ _ => G (S n))
    (B := fun n _ _ _ _ => G n) f).
  intros c' d'.
  pose (P := @Build_νGpdPresentation A G f c d).
  assert (unit: forall t: ModelTargetData P,
    precomposeModelTarget (C := P) (D := P) (fun n (x: G n) => x)
      (fun n q Hq a x => eq_refl) t = t).
  { intros [Q [b face]].
    refine (f_equal (fun face => ((Q; (b; face)): ModelTargetData P)) _).
    apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro x.
    now apply eq_trans_refl_l. }
  now exact (qinvEquiv
    (precomposeModelTarget (C := P) (D := P) (fun n (x: G n) => x) (fun n q Hq a x => eq_refl))
    (fun t: ModelTargetData P => t) unit unit).(eqvIsEquiv).
Defined.

Definition precomposeModelTargetEquiv {A: HSet} {C D: νGpdPresentation A}
  (cell: forall n, Equiv (C.(G0) n) (D.(G0) n))
  (cellFace: forall n q (Hq: q <= n) a x,
    cell n (C.(GFace) n q Hq a x) = D.(GFace) n q Hq a (cell (S n) x)):
  Equiv (ModelTargetData D) (ModelTargetData C) :=
  {| eqvFun := precomposeModelTarget (C := C) (D := D) (fun n => cell n) cellFace;
    eqvIsEquiv := precomposeModelTargetIsEquiv (C := C) (D := D) cell cellFace |}.

Definition ReverseCellFace {A: HSet} {C D: νGpdPresentation A}
  (cell: BoundaryMap C D): Type :=
  forall n q (Hq: q <= n) a x,
    D.(GFace) n q Hq a (cell (S n) x) = cell n (C.(GFace) n q Hq a x).

Definition CellActionData {A: HSet} (C D: νGpdPresentation A): Type :=
  {cell: BoundaryMap C D &T ReverseCellFace cell}.

Definition cellActionDataEq {A: HSet} {C D: νGpdPresentation A}
  {cell1 cell2: BoundaryMap C D}
  {face1: ReverseCellFace cell1} {face2: ReverseCellFace cell2}
  (theta: forall n x, cell1 n x = cell2 n x)
  (square: forall n q (Hq: q <= n) a x,
    f_equal (D.(GFace) n q Hq a) (theta (S n) x) • face2 n q Hq a x =
      face1 n q Hq a x • theta n (C.(GFace) n q Hq a x)):
  ((cell1; face1): CellActionData C D) = (cell2; face2).
Proof.
  revert face2 square.
  pattern cell2, theta. apply (homInd2 cell1).
  intros face2 square.
  apply (f_equal (fun face => ((cell1; face): CellActionData C D))).
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro a.
  apply functional_extensionality_dep; intro x.
  pose proof (square n q Hq a x) as h. cbn [f_equal] in h.
  rewrite eq_trans_refl_l, eq_trans_refl_r in h. now symmetry.
Defined.

Definition precomposeCellAction {A: HSet} {C D: νGpdPresentation A}
  (action: CellActionData C D) (target: ModelTargetData D): ModelTargetData C :=
  precomposeModelTarget (C := C) (D := D) action.1 (fun n q Hq a x => eq_sym (action.2 n q Hq a x)) target.



Definition composeCellAction {A: HSet} {C D E: νGpdPresentation A}
  (u: CellActionData C D) (v: CellActionData D E): CellActionData C E :=
  (fun n x => v.1 n (u.1 n x);
    fun n q Hq a x => v.2 n q Hq a (u.1 (S n) x)
      • f_equal (v.1 n) (u.2 n q Hq a x)).

Local Lemma precomposeFaceComposition {X Y Z: Type} (f: X -> Y) (g: Y -> Z)
  {a b: X} {z: Y} {t: Z} (p: a = b) (q: z = f a) (r: g z = t):
  f_equal (fun x => g (f x)) (eq_sym p) • (f_equal g (eq_sym q) • r) =
    f_equal g (eq_sym (q • f_equal f p)) • r.
Proof.
  destruct p; cbn [f_equal].
  now rewrite eq_trans_refl_l, eq_trans_refl_r.
Defined.

Lemma precomposeCellActionComposition {A: HSet} {C D E: νGpdPresentation A}
  (u: CellActionData C D) (v: CellActionData D E) (target: ModelTargetData E):
  precomposeCellAction u (precomposeCellAction v target) =
    precomposeCellAction (composeCellAction u v) target.
Proof.
  destruct target as [Q [b face]].
  refine (f_equal (fun h => ((Q; ((fun n x => b n (v.1 n (u.1 n x))); h)):
    ModelTargetData C)) _).
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro a.
  apply functional_extensionality_dep; intro x.
  now exact (precomposeFaceComposition (v.1 n) (b n)
    (u.2 n q Hq a x) (v.2 n q Hq a (u.1 (S n) x))
    (face n q Hq a (v.1 (S n) (u.1 (S n) x)))).
Defined.

(** A cone comparison and its coherent change of cell readout descend
    along an equivalence of the source cells. *)
Definition assembleAugmentedStep {A: HSet}
  {R C D E: νGpdPresentation A}
  (reindex: CellActionData R C)
  (reindexIsEquiv: forall n, IsEquiv (reindex.1 n))
  (nextReadout: CellActionData C D) (shift: CellActionData D E)
  (oldReadout: CellActionData R E)
  (raw: ModelTargetData R) (actual: ModelTargetData C)
  (target: ModelTargetData D) (cone: ModelTargetData E)
  (sourceReindex: raw = precomposeCellAction reindex actual)
  (sourceCone: raw = precomposeCellAction oldReadout cone)
  (targetCone: target = precomposeCellAction shift cone)
  (readoutCompatibility: oldReadout = composeCellAction reindex
    (composeCellAction nextReadout shift)):
  actual = precomposeCellAction nextReadout target.
Proof.
  refine (@eqvInj (ModelTargetData C) (ModelTargetData R)
    (precomposeModelTargetEquiv
      (fun n => {| eqvFun := reindex.1 n; eqvIsEquiv := reindexIsEquiv n |})
      (fun n q Hq a x => eq_sym (reindex.2 n q Hq a x)))
    actual (precomposeCellAction nextReadout target) _).
  now exact (eq_sym sourceReindex • sourceCone
    • f_equal (fun action => precomposeCellAction action cone) readoutCompatibility
    • eq_sym (precomposeCellActionComposition reindex
        (composeCellAction nextReadout shift) cone)
    • f_equal (precomposeCellAction reindex)
        (eq_sym (precomposeCellActionComposition nextReadout shift cone))
    • f_equal (fun t => precomposeCellAction reindex
        (precomposeCellAction nextReadout t)) (eq_sym targetCone)).
Defined.

Definition contractiblePartialDiagramModel {A: HSet}
  (P Q C: νGpdPresentation A)
  (sourceBoundary: forall n, C.(G0) n -> P.(G0) n)
  (matchingBoundary: forall n, C.(G0) n -> Q.(G0) n)
  (sourceBoundaryFace: forall n q (Hq: q <= n) a x,
    sourceBoundary n (C.(GFace) n q Hq a x)
      = P.(GFace) n q Hq a (sourceBoundary (S n) x))
  (matchingBoundaryFace: forall n q (Hq: q <= n) a x,
    matchingBoundary n (C.(GFace) n q Hq a x)
      = Q.(GFace) n q Hq a (matchingBoundary (S n) x))
  (sourceContr: forall n, Contr (P.(G0) n))
  (targetContr: forall n, Contr (Q.(G0) n)):
  PartialDiagramModel P Q C sourceBoundary matchingBoundary
    sourceBoundaryFace matchingBoundaryFace.
Proof.
  refine {| modelEquiv n := qinvEquiv
    (fun _ => (targetContr n).1) (fun _ => (sourceContr n).1)
    (sourceContr n).2 (targetContr n).2;
    modelFace n q Hq a x := (targetContr n).2 _;
    modelBoundary n x := (targetContr n).2 _ |}.
  - intros n q Hq r Hr a b x. now apply (contrUIP (targetContr n)).
  - intros n q Hq a x. now apply (contrUIP (targetContr n)).
Defined.

(** The residual shift of a presentation, at fixed universe levels. *)
Definition residualShift {A: HSet} (C: νGpdPresentation A): νGpdPresentation A :=
  GpdCone.residualShiftPresentation C.

Section StepTarget.
Context {A: HSet} (Q C: νGpdPresentation A).
Context (boundary: forall k, C.(G0) k -> Q.(G0) k).
Context (boundaryNatural: forall k q (Hq: q <= k) a t,
  Q.(GFace) k q Hq a (boundary (S k) t) = boundary k (C.(GFace) k q Hq a t)).
Context (boundaryCoh: forall k q (Hq: q <= k) r (Hr: r <= q) a c t,
  (f_equal (Q.(GFace) k q Hq a) (boundaryNatural (S k) r (Hr ↕ ↑ Hq) c t)
    • boundaryNatural k q Hq a (C.(GFace) (S k) r (Hr ↕ ↑ Hq) c t))
    • f_equal (boundary k) (C.(GFaceCoh) k q Hq r Hr a c t)
  = Q.(GFaceCoh) k q Hq r Hr a c (boundary (S (S k)) t)
    • (f_equal (Q.(GFace) k r (Hr ↕ Hq) c)
        (boundaryNatural (S k) (S q) (⇑ Hq) a t)
      • boundaryNatural k r (Hr ↕ Hq) c (C.(GFace) (S k) (S q) (⇑ Hq) a t))).

(** The cone attachment with its boundary map, over the shifted cells. *)
Definition stepTarget: ModelTargetData (residualShift C) :=
  (GpdCone.conePresentation Q C boundary boundaryNatural boundaryCoh;
    (GpdCone.coneBoundary Q C boundary boundaryNatural;
     GpdCone.coneBoundaryFace Q C boundary boundaryNatural boundaryCoh)).

End StepTarget.

(** A levelwise equivalence of presentations preserving faces and their
    selected exchange paths. *)
Record PresentationEquiv {A: HSet} {P Q: νGpdPresentation A} := {
  presentationCell k: Equiv (P.(G0) k) (Q.(G0) k);
  presentationFace k q (Hq: q <= k) a x:
    presentationCell k (P.(GFace) k q Hq a x)
      = Q.(GFace) k q Hq a (presentationCell (S k) x);
  presentationFaceCoh k q (Hq: q <= k) r (Hr: r <= q) a b x:
    (presentationFace k q Hq a (P.(GFace) (S k) r (Hr ↕ ↑ Hq) b x)
      • f_equal (Q.(GFace) k q Hq a)
          (presentationFace (S k) r (Hr ↕ ↑ Hq) b x))
      • Q.(GFaceCoh) k q Hq r Hr a b (presentationCell (S (S k)) x)
    = f_equal (presentationCell k) (P.(GFaceCoh) k q Hq r Hr a b x)
      • (presentationFace k r (Hr ↕ Hq) b (P.(GFace) (S k) (S q) (⇑ Hq) a x)
        • f_equal (Q.(GFace) k r (Hr ↕ Hq) b)
            (presentationFace (S k) (S q) (⇑ Hq) a x));
}.

Arguments PresentationEquiv {A} P Q.

Definition presentationAction {A: HSet} {P Q: νGpdPresentation A}
  (e: PresentationEquiv P Q): CellActionData P Q :=
  (fun n x => e.(presentationCell) n x;
    fun n q Hq a x => eq_sym (e.(presentationFace) n q Hq a x)).

(** The data against which the partial frames of an indexed groupoid with
    presentation [P] are compared. Level [p] has whole cells and a partial
    boundary; the cells at level [S p] are the shifted cells at level [p],
    and the partial boundaries at level [S p] are the cone attachment over
    those at level [p]. [targetComplete p] is the statement that follows
    once the boundary map at residual position [0] is an equivalence. *)
Record ResidualTarget {A: HSet} {P: νGpdPresentation A} := {
  targetCells: nat -> νGpdPresentation A;
  targetZero: PresentationEquiv P (targetCells 0);
  targetShift p: PresentationEquiv (targetCells (S p)) (residualShift (targetCells p));
  targetMatching: nat -> νGpdPresentation A;
  targetBoundary p k: (targetCells p).(G0) k -> (targetMatching p).(G0) k;
  targetBoundaryNatural p k q (Hq: q <= k) a x:
    (targetMatching p).(GFace) k q Hq a (targetBoundary p (S k) x)
      = targetBoundary p k ((targetCells p).(GFace) k q Hq a x);
  targetBoundaryCoh p k q (Hq: q <= k) r (Hr: r <= q) a c x:
    (f_equal ((targetMatching p).(GFace) k q Hq a)
        (targetBoundaryNatural p (S k) r (Hr ↕ ↑ Hq) c x)
      • targetBoundaryNatural p k q Hq a
          ((targetCells p).(GFace) (S k) r (Hr ↕ ↑ Hq) c x))
      • f_equal (targetBoundary p k)
          ((targetCells p).(GFaceCoh) k q Hq r Hr a c x)
    = (targetMatching p).(GFaceCoh) k q Hq r Hr a c (targetBoundary p (S (S k)) x)
      • (f_equal ((targetMatching p).(GFace) k r (Hr ↕ Hq) c)
          (targetBoundaryNatural p (S k) (S q) (⇑ Hq) a x)
        • targetBoundaryNatural p k r (Hr ↕ Hq) c
            ((targetCells p).(GFace) (S k) (S q) (⇑ Hq) a x));
  targetMatchingZero k: Contr ((targetMatching 0).(G0) k);
  targetSplit p:
    PartialDiagramModel (targetMatching (S p))
      (stepTarget (targetMatching p) (targetCells p) (targetBoundary p)
        (targetBoundaryNatural p) (targetBoundaryCoh p)).1
      (targetCells (S p)) (targetBoundary (S p))
      (precomposeCellAction (presentationAction (targetShift p))
        (stepTarget (targetMatching p) (targetCells p) (targetBoundary p)
          (targetBoundaryNatural p) (targetBoundaryCoh p))).2.1
      (fun n q Hq a x => eq_sym (targetBoundaryNatural (S p) n q Hq a x))
      (precomposeCellAction (presentationAction (targetShift p))
        (stepTarget (targetMatching p) (targetCells p) (targetBoundary p)
          (targetBoundaryNatural p) (targetBoundaryCoh p))).2.2;
  targetComplete: nat -> Type;
  targetCompleteOf p
    (e: Equiv ((targetCells p).(G0) 0) ((targetMatching p).(G0) 0)):
    (forall x, e x = targetBoundary p 0 x) -> targetComplete p;
}.

Arguments ResidualTarget {A} P.

Section TargetData.
Context {A: HSet} {P: νGpdPresentation A} (T: ResidualTarget P).

Definition targetData p: ModelTargetData (T.(targetCells) p) :=
  (T.(targetMatching) p;
    (T.(targetBoundary) p;
      fun n q Hq a x => eq_sym (T.(targetBoundaryNatural) p n q Hq a x))).

Definition targetCone p: ModelTargetData (residualShift (T.(targetCells) p)) :=
  stepTarget (T.(targetMatching) p) (T.(targetCells) p) (T.(targetBoundary) p)
    (T.(targetBoundaryNatural) p) (T.(targetBoundaryCoh) p).

Definition targetShiftAction p:
  CellActionData (T.(targetCells) (S p)) (residualShift (T.(targetCells) p)) :=
  presentationAction (T.(targetShift) p).

Definition targetSplitEquality p:
  targetData (S p) = precomposeCellAction (targetShiftAction p) (targetCone p) :=
  modelTargetEquality (T.(targetSplit) p).

End TargetData.
