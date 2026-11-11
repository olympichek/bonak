(** The residual target formed by the partial matching objects of a diagram. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Contractible Notation
  RewLemmas FinitePrefix NatLemmas LeSProp Funext.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape WordTensor.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Pseudofunctor.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Cone Model.
From Bonak.Reedy.Gpd Require Import Reedy Matching Shift.
From Bonak.Indexed.ReedyEquiv.Gpd.Target Require Import ShiftedPrefix
  PullbackReindex MatchingSplit MatchingPartialSplit MatchingPartialSplitFace
  MatchingPartialSplitBoundary.

Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations FinitePrefix WordTensor.

(** Squares over pointwise identifications of face families can be
    inverted and composed. *)
Section Squares.
Context {A: HSet} {G: nat -> HGpd}.

Local Lemma gSqSym {f g: GFaceType A G} {c: GCohType A f} {d: GCohType A g}
  (h: forall n q (Hq: q <= n) a x, f n q Hq a x = g n q Hq a x)
  (sq: GSqType A c d h):
  GSqType A d c (fun n q Hq a x => eq_sym (h n q Hq a x)).
Proof.
  revert d sq. pattern g, h.
  apply (homInd5S (I1 := nat) (I2 := fun _ => nat) (I3 := fun n q => q <= n)
    (I4 := fun _ _ _ => A) (I5 := fun n _ _ _ => G (S n))
    (B := fun n _ _ _ _ => G n) f).
  intros d sq n q Hq r Hr a b x.
  pose proof (sq n q Hq r Hr a b x) as K.
  cbn [f_equal eq_sym eq_trans] in K |- *.
  rewrite eq_trans_refl_l in K |- *. now symmetry.
Defined.

Local Lemma gSqTrans {f g e: GFaceType A G} {c: GCohType A f}
  {d: GCohType A g} {c': GCohType A e}
  (h: forall n q (Hq: q <= n) a x, f n q Hq a x = g n q Hq a x)
  (h': forall n q (Hq: q <= n) a x, g n q Hq a x = e n q Hq a x)
  (sq: GSqType A c d h) (sq': GSqType A d c' h'):
  GSqType A c c' (fun n q Hq a x => h n q Hq a x • h' n q Hq a x).
Proof.
  revert c' sq'. pattern e, h'.
  apply (homInd5S (I1 := nat) (I2 := fun _ => nat) (I3 := fun n q => q <= n)
    (I4 := fun _ _ _ => A) (I5 := fun n _ _ _ => G (S n))
    (B := fun n _ _ _ _ => G n) g).
  intros c' sq' n q Hq r Hr a b x.
  pose proof (sq' n q Hq r Hr a b x) as K.
  cbn [f_equal eq_sym eq_trans] in K |- *.
  rewrite eq_trans_refl_l in K. rewrite <- K.
  now exact (sq n q Hq r Hr a b x).
Defined.

End Squares.

(** At level [0] the residual presentation has the cells of [P], and its
    faces agree with those of [P] up to the casts along [0 + S k = S (0 + k)]. *)
Section Zero.
Context {A: HSet} (P: νGpdPresentation A).

Local Definition shiftedFaceZero k q (Hq: q <= k) a (x: P.(G0) (S k)):
  shiftedFace P 0 k q Hq a x = P.(GFace) k q Hq a x :=
  f_equal (fun e: S k = S k =>
    P.(GFace) k q Hq a (rew [fun n => P.(G0) n] e in x))
    (natUIP (Nat.add_succ_r 0 k) eq_refl).

Local Lemma shiftedFaceZeroCoh:
  GSqType A (shiftedExchange P 0) P.(GFaceCoh) shiftedFaceZero.
Proof.
  intros k q Hq r Hr a c x.
  unfold shiftedFaceZero, shiftedExchange, shiftedFace.
  cbv beta iota zeta delta [FaceStructure.SFace FaceStructure.S0].
  rewrite (natUIP (Nat.add_succ_r 0 k) eq_refl),
    (natUIP (Nat.add_succ_r 0 (S k)) eq_refl),
    (natUIP (Nat.add_succ_r 0 q) eq_refl).
  change (P.(GFaceCoh) k q Hq r Hr a c x =
    eq_refl • P.(GFaceCoh) k q Hq r Hr a c x).
  now symmetry; apply eq_trans_refl_l.
Defined.

Local Definition zeroFace k q (Hq: q <= k) a (x: P.(G0) (S k)):
  P.(GFace) k q Hq a x = (residualPresentation 0 P).(GFace) k q Hq a x :=
  eq_sym (faceGen P 0 k q Hq a x • shiftedFaceZero k q Hq a x).

Local Lemma zeroFaceSq:
  GSqType A P.(GFaceCoh) (residualPresentation 0 P).(GFaceCoh) zeroFace.
Proof.
  now exact (gSqSym _ (gSqTrans _ _ (faceGenCoh P 0) shiftedFaceZeroCoh)).
Defined.

Definition zeroEquiv: PresentationEquiv P (residualPresentation 0 P).
Proof.
  refine (@Build_PresentationEquiv A P (residualPresentation 0 P)
    (fun k => idEquiv) zeroFace _).
  intros k q Hq r Hr a b x.
  change (f_equal (fun z => z) ?u) with (f_equal (fun z: P.(G0) k => z) u).
  rewrite f_equal_id. symmetry.
  now exact (zeroFaceSq k q Hq r Hr a b x).
Defined.

End Zero.

Definition emptyMatchingContr {A: HSet} (X: Diagram A 0):
  Contr (MatchingObject X).
Proof.
  assert (b0: MatchingObject X).
  { exists (fun i: Index 0 => match i with end).
    exists (fun i: Index 0 => match i with end).
    split; now intros []. }
  exists b0. intro b.
  unshelve refine (matchingExt X b0 b _ _).
  - apply functional_extensionality_dep. now intros [].
  - apply functional_extensionality_dep. now intros [].
Defined.

(** An equivalence onto the partial matching object at residual position
    [0] that agrees with the partial boundary makes the ordinary boundary
    map of the next rank an equivalence. *)
Definition ordinaryBoundaryIsEquiv {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A)))
  (e: Equiv (F.(pfObj) (p + 0)) (MatchingObject (shiftedPrefix p 0 F)))
  (rule: forall x, e x = partialBoundary p F 0 x):
  IsEquiv (matchingMap (unshiftedPrefix (S p) F)) :=
  (equivOfSquare
    (rewEquiv (fun n => GDom (F.(pfObj) n)) (Nat.add_0_r p)) idEquiv
    (compEquiv e (zeroPrefixBridge p F))
    (matchingMap (unshiftedPrefix (S p) F))
    (fun x => f_equal (zeroPrefixBridge p F) (rule x)
      • zeroPrefixBoundary p F x)).(eqvIsEquiv).

Section Target.
Context {A: HSet} (P: νGpdPresentation A).
Local Abbreviation F := (toPsfTot A P).

(** All components are given in one definition, so their universe levels
    are solved together and later uses refer to this one instance. *)
Definition reedyTarget: ResidualTarget P := {|
  targetCells p := ofPsfTot A (wholeCellDiagram p F);
  targetZero := zeroEquiv P;
  targetShift p :=
    @Build_PresentationEquiv A (ofPsfTot A (wholeCellDiagram (S p) F))
      (residualShift (ofPsfTot A (wholeCellDiagram p F)))
      (fun k => shiftPrefixCell p k F) (shiftCellFace p F) (shiftCellFaceCoh p F);
  targetMatching p := MatchingPartialPresentation p F;
  targetBoundary p k x := partialBoundary p F k x;
  targetBoundaryNatural p k q Hq a x := boundaryNatural p F (wgen k q a) x;
  targetBoundaryCoh p := matchingBoundaryForwardCoh p F;
  targetMatchingZero k := emptyMatchingContr (shiftedPrefix 0 k F);
  targetSplit p :=
    @Build_PartialDiagramModel A (MatchingPartialPresentation (S p) F)
      (MatchingStepPresentation p F) (ofPsfTot A (wholeCellDiagram (S p) F))
      (partialBoundary (S p) F)
      (fun n x => matchingStepBoundary p F n (shiftPrefixCell p n F x))
      (matchingBoundaryFace (S p) F)
      (fun n q Hq a x =>
        f_equal (matchingStepBoundary p F n)
          (eq_sym (shiftCellComparisonFace p F n q Hq a x))
        • matchingStepBoundaryFace p F n q Hq a (shiftPrefixCell p (S n) F x))
      (matchingPartialSplitEquiv p F) (matchingPartialSplitFace p F)
      (matchingPartialSplitFaceCoh p F) (matchingPartialSplitBoundary p F)
      (matchingPartialSplitBoundaryFace p F);
  targetComplete p := IsEquiv (matchingMap (unshiftedPrefix (S p) F));
  targetCompleteOf p e rule := ordinaryBoundaryIsEquiv p F e rule |}.

End Target.
