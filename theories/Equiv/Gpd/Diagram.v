(** Canonical coherent diagrams extracted from finite indexed prefixes,
    with their face and overlap computations. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation LeSProp Limit
  TelescopeLimit TelescopeCompletion FinitePrefix NatLemmas RewLemmas.
From Bonak.νGpd Require Import Layer νGpd Pasting.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagram.
From Bonak.Presheaf Require Import νSemiShape WordAction GeneratorCoherence.
From Bonak.Presheaf.Gpd Require Import Pseudofunctor Presentation.
From Bonak.Reedy.Gpd Require Import Reedy Bounded.
From Bonak.Equiv.Gpd Require Import Face PresheafOfνGpd PathAlgebra.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** Canonical coherent diagrams extracted from finite indexed prefixes. *)

Module IndexedDiagramOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Import A.
Module Export Indexed := Faces.
Module Extraction := PresheafOfνGpdOn A Core Faces.

Definition completePrefix {n} (X: (νGpdAt n).(prefix)): νGpds :=
  sequentialToLimit νGpdTel tt (tt; fun x => hunit_ext tt x)
    (completePrefixChain n νGpdTel (fun _ _ _ => gunit) X).

Lemma completionAt {n} (X: (νGpdAt n).(prefix)):
  (completePrefix X).(approx) n leR_O = X.
Proof. now apply completePrefixAt. Defined.

Lemma completionPack {n} (X: (νGpdAt n).(prefix)):
  (νGpdPack n (completePrefix X)).1 = X.
Proof.
  now exact (limitPackPath n (completePrefix X) • completionAt X).
Defined.

Definition prefixCell {n} (X: (νGpdAt (S n)).(prefix)): HGpd :=
  {d: νFrame X.1 & X.2 d}.

Section Diagrams.

Definition indexedDiagram (X: νGpds): PathDiagramFamily (Op (νSemiShape arity)) :=
  toPsfTot arity (Extraction.g X).

Definition finiteDiagram {n} (X: (νGpdAt n).(prefix)): Diagram arity n :=
  restrictDiagram n (indexedDiagram (completePrefix X)).

Definition unitExtension {n} (X: (νGpdAt n).(prefix)):
  (νGpdAt (S n)).(prefix) := (X; fun _ => gunit).

Lemma completePrefixUnitExtension {n} (X: (νGpdAt n).(prefix)):
  completePrefix (unitExtension X) = completePrefix X.
Proof.
  unfold completePrefix, unitExtension.
  apply f_equal.
  now exact (completePrefixExtend n νGpdTel (fun _ _ _ => gunit) X).
Defined.

Definition unitPrefixProjectionEquiv {n} (X: (νGpdAt n).(prefix)):
  Equiv (prefixCell (unitExtension X)) (νFrame X).
Proof.
  refine (qinvEquiv (fun z => z.1) (fun d => (d; tt)) _ _).
  - now intros [d []].
  - now intro d.
Defined.

Lemma unitProjectionIsEquiv {n} (Y: (νGpdAt (S n)).(prefix))
  (X: (νGpdAt n).(prefix)) (e: Y = unitExtension X):
  IsEquiv (fun z: prefixCell Y => z.1).
Proof. destruct (eq_sym e). now exact (unitPrefixProjectionEquiv X).(eqvIsEquiv). Defined.

Lemma packedUnitPrefix {n} (X: (νGpdAt n).(prefix)):
  (νGpdPack (S n) (completePrefix X)).1 = unitExtension X.
Proof.
  now exact (f_equal (fun Y: νGpds => (νGpdPack (S n) Y).1)
      (eq_sym (completePrefixUnitExtension X))
    • completionPack (unitExtension X)).
Defined.

Definition packedCellProjectionEquiv {n} (X: (νGpdAt n).(prefix)):
  Equiv (prefixCell (νGpdPack (S n) (completePrefix X)).1)
    (νFrame (νGpdPack n (completePrefix X)).1) :=
  {| eqvFun z := z.1;
    eqvIsEquiv := unitProjectionIsEquiv
      (νGpdPack (S n) (completePrefix X)).1 X (packedUnitPrefix X) |}.

End Diagrams.
End IndexedDiagramOn.

Module Type IndexedDiagramSig (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Include IndexedDiagramOn A Core Faces.
End IndexedDiagramSig.


(** Face and overlap computations of the canonical diagram of a prefix. *)

Module DiagramFacesOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (D: IndexedDiagramSig A Core Faces).
Import A.
Module Export Diagram := D.
Import Diagram.Extraction.

Definition νFacePackIrr {P K} {dcTop: DepsCohs P K} (s t: DCPack dcTop)
  (H: dcPackLen s = dcPackLen t) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop))):
  νFace s.2.2.2 ε d = νFace t.2.2.2 ε d :=
  f_equal (fun u: DCPack dcTop => νFace u.2.2.2 ε d) (dcPackEq s t H).

(** Erasing dimension [0] at the bottom of a [DepsCohs2]-chain is [νFace]
    along any [DepsCohs]-chain of the same length. *)

Lemma faceDeepZero {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c2: DepsCohs2Chain dc2Top dc2) {pB kB} {dcB: DepsCohs pB kB}
  (cB: DepsCohsChain dc2Top.(_depsCohs) dcB)
  (Hlen: cohsChainLen cB = cohs2ChainLen c2)
  (ε: arity) (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  faceDeep c2 0 leR_O ε d Q = νFace cB ε d.
Proof.
  refine (eq_sym (νFaceAsDeep c2 ε d Q) • _).
  now exact (νFacePackIrr (dcPackOf (cohs2ChainDepsCohs c2)) (dcPackOf cB)
    (cohs2ChainDepsCohsLen c2 • eq_sym Hlen) ε d).
Defined.

(** The general dimension: erasing dimension [j] at the bottom of a chain of
    length [l + j] is [νFace] along a chain of length [l]. *)

Lemma faceDeepAsνFace {P K} {dc2Top: DepsCohs2 P K} {p k} {dc2: DepsCohs2 p k}
  (c2: DepsCohs2Chain dc2Top dc2) (j: nat) (Hj: j <= k)
  {pB kB} {dcB: DepsCohs pB kB} (cB: DepsCohsChain dc2Top.(_depsCohs) dcB)
  (Hlen: cohs2ChainLen c2 = (cohsChainLen cB + j)%nat)
  (ε: arity) (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  faceDeep c2 j Hj ε d Q = νFace cB ε d.
Proof.
  revert j Hj pB kB dcB cB Hlen.
  induction c2 as [|p k dc2 c2 IH]; intros j Hj pB kB dcB cB Hlen.
  - destruct j as [|j].
    + refine (faceDeepZero DepsCohs2ChainNil cB _ ε d Q).
      now exact (eq_sym (addZeroR (cohsChainLen cB)) • eq_sym Hlen).
    + rewrite (addSuccR (cohsChainLen cB) j) in Hlen. now discriminate Hlen.
  - destruct j as [|j].
    + refine (faceDeepZero (DepsCohs2ChainCons c2) cB _ ε d Q).
      now exact (eq_sym (Hlen • addZeroR (cohsChainLen cB))).
    + refine (IH j (⇓ Hj) pB kB dcB cB _).
      rewrite (addSuccR (cohsChainLen cB) j) in Hlen.
      now exact (f_equal Nat.pred Hlen).
Defined.

(** The face maps of the presheaf a tower determines, read as [νFace]

    [gFaceC] at relative level [0] erases a dimension at the bottom of the
    chain the position carries; [νFace] erases dimension [0] at the bottom of
    an arbitrary chain. The two agree whenever the lengths match. *)

Lemma gFaceCAsνFace {n} {Xpre: (νGpdAt n).(prefix)} (S0: νGpdFrom n Xpre)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (dim: nat) (Hdim: dim <= 0 + k)
  {pB kB} {dcB: DepsCohs pB kB} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen a = (cohsChainLen cB + dim)%nat)
  (ε: arity) (t: gF0 S0 1):
  gFaceC S0 a 0 dim Hdim ε t = νFace cB ε t.1.
Proof.
  now exact (faceDeepAsνFace (cohs3ChainDepsCohs2 a) dim Hdim cB
    (cohs3ChainDepsCohs2Len a • Hlen) ε t.1 t.2).
Defined.

Section Descent.
Variable X: νGpds.

Inductive Desc: forall {n} {Xpre: (νGpdAt n).(prefix)},
  νGpdFrom n Xpre -> Type :=
| DescZ: Desc X
| DescS {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}:
    Desc S0 -> Desc (next S0).

(** Indexing by [k + n] makes the use sites instantiate [k := 0]. The branches
    supply the required [plus_n_O] and [plus_n_Sm] equalities. *)

Fixpoint descF0 {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0) (k: nat) {struct D}: gF0 X (k + n) = gF0 S0 k :=
  match D in @Desc n0 _ S1 return gF0 X (k + n0) = gF0 S1 k with
  | DescZ => f_equal (gF0 X) (eq_sym (plus_n_O k))
  | @DescS n1 _ S1 D' =>
      f_equal (gF0 X) (eq_sym (plus_n_Sm k n1)) • descF0 D' k.+1
  end.

(** The chain a descent reaches: the tower's own chain, lifted once per level.
    A position at level [n] carries the chain of length [n] landing at stage
    [0], which is what makes every face map of [g X] at that level readable at
    the position. *)

Fixpoint descChain {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0): {dc3: DepsCohs3 0 n &T DepsCohs3Chain (νDepsCohs3At S0) dc3} :=
  match D in @Desc n0 _ S1
    return {dc3: DepsCohs3 0 n0 &T DepsCohs3Chain (νDepsCohs3At S1) dc3} with
  | DescZ => (νDepsCohs3At X; DepsCohs3ChainNil)
  | @DescS n1 _ S1 D' => (_; chainUp1 (νExt3At S1) (descChain D').2)
  end.

Lemma descChainLen {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0): cohs3ChainLen (descChain D).2 = n.
Proof.
  induction D.
  - now reflexivity.
  - now exact (f_equal S
      (cohs3ChainUpLen (νExt3At S0) (descChain D).2 • IHD)).
Defined.

(** At [k := 0], the cells of [g X] at the position's level are the total
    space of the position — the level state's cell identification. *)

Definition descTotal {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0): gF0 X n = νTotal S0 := descF0 D 0.

(** A transparent form of the same level change, with the equality at the
    source level named separately from its successor.  Keeping the two
    equalities related explicitly makes simultaneous path induction possible
    in the coherence lemma below. *)

Lemma gFaceLevelCore {n0} {Xpre0: (νGpdAt n0).(prefix)}
  (S0: νGpdFrom n0 Xpre0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  {n1 n2: nat} (e0: n1 = n2) (e1: n1.+1 = n2.+1)
  (He: e1 = f_equal S e0) (dim: nat)
  (H1: dim <= n1 + k) (H2: dim <= n2 + k) (ε: arity)
  (d: gF0 S0 n1.+1):
  gFaceC S0 a n2 dim H2 ε
    (rew [GDom] eq_sym (f_equal (gF0 S0) (eq_sym e1)) in d) =
  rew [GDom] eq_sym (f_equal (gF0 S0) (eq_sym e0)) in
    gFaceC S0 a n1 dim H1 ε d.
Proof.
  destruct e0; cbn in He; subst e1; now reflexivity.
Defined.

(** Naturality of [gFaceLevelCore].  The three adjacent level equalities are
    eliminated together; this is the small generic core that prevents the
    three dependent transports from expanding independently. *)

Lemma gFaceLevelCohCore (Y: νGpds)
  {k1 k2: nat} (e0: k1 = k2)
  (e1: k1.+1 = k2.+1) (He1: e1 = f_equal S e0)
  (e2: k1.+2 = k2.+2) (He2: e2 = f_equal S e1)
  (q: nat) (Hq1: q <= k1 + 0) (Hq2: q <= k2 + 0)
  (r0: nat) (Hr: r0 <= q) (ε ω: arity) (t: gF0 Y k1.+2):
  (f_equal (gFaceC Y DepsCohs3ChainNil k2 q Hq2 ε)
      (gFaceLevelCore Y DepsCohs3ChainNil e1 e2 He2 r0
        (leR_eq_r (plus_n_Sm k1 0 • PeanoNat.Nat.add_1_r k1
              • plus_n_O k1.+1) (Hr ↕ (↑ Hq1)))
        (leR_eq_r (plus_n_Sm k2 0 • PeanoNat.Nat.add_1_r k2
              • plus_n_O k2.+1) (Hr ↕ (↑ Hq2))) ω t)
    • gFaceLevelCore Y DepsCohs3ChainNil e0 e1 He1 q Hq1 Hq2 ε
        (gFaceC Y DepsCohs3ChainNil k1.+1 r0
          (leR_eq_r (plus_n_Sm k1 0 • PeanoNat.Nat.add_1_r k1
              • plus_n_O k1.+1) (Hr ↕ (↑ Hq1))) ω t))
  • f_equal
      (fun w => rew [GDom]
        eq_sym (f_equal (gF0 Y) (eq_sym e0)) in w)
      (gFaceCohC Y DepsCohs3ChainNil k1 q Hq1 r0 Hr ε ω t)
  =
  gFaceCohC Y DepsCohs3ChainNil k2 q Hq2 r0 Hr ε ω
    (rew [GDom] eq_sym (f_equal (gF0 Y) (eq_sym e2)) in t)
  • (f_equal (gFaceC Y DepsCohs3ChainNil k2 r0 (Hr ↕ Hq2) ω)
      (gFaceLevelCore Y DepsCohs3ChainNil e1 e2 He2 q.+1
        (leR_eq_r (plus_n_Sm k1 0 • PeanoNat.Nat.add_1_r k1
              • plus_n_O k1.+1) (⇑ Hq1))
        (leR_eq_r (plus_n_Sm k2 0 • PeanoNat.Nat.add_1_r k2
              • plus_n_O k2.+1) (⇑ Hq2)) ε t)
    • gFaceLevelCore Y DepsCohs3ChainNil e0 e1 He1 r0
        (Hr ↕ Hq1) (Hr ↕ Hq2) ω
        (gFaceC Y DepsCohs3ChainNil k1.+1 q.+1
          (leR_eq_r (plus_n_Sm k1 0 • PeanoNat.Nat.add_1_r k1
              • plus_n_O k1.+1) (⇑ Hq1)) ε t)).
Proof.
  destruct e0; cbn in He1; subst e1; cbn in He2; subst e2.
  unfold gFaceLevelCore; cbn.
  set (HH := gFaceCohC Y DepsCohs3ChainNil k1 q Hq1 r0 Hr ε ω t) in *.
  clearbody HH.
  rewrite f_equal_id.
  now exact (eq_trans_refl_l HH).
Defined.

(** Moving a face-compatible path across a level equality retains the
    unit corrections of its two object identifications at the endpoints. *)

Lemma faceDescStepCore (Y: νGpdPresentation arity)
  {l1 l2: nat} (e0: l1 = l2) (e1: l1.+1 = l2.+1)
  (He: e1 = f_equal S e0) {A0 A1: HGpd}
  (p0: Y.(G0) l1 = A0) (p1: Y.(G0) l1.+1 = A1)
  (dim: nat) (H1: dim <= l1) (H2: dim <= l2) (ε: arity)
  (u: A1) (v: A0)
  (P: Y.(GFace) l1 dim H1 ε (rew [GDom] eq_sym p1 in u)
    = rew [GDom] eq_sym p0 in v):
  Y.(GFace) l2 dim H2 ε
    (rew [GDom]
      eq_sym (f_equal (fun z => Y.(G0) z) (eq_sym e1) • p1) in u)
  = rew [GDom]
      eq_sym (f_equal (fun z => Y.(G0) z) (eq_sym e0) • p0) in v.
Proof.
  destruct e0; cbn in He; subst e1.
  now exact (path_change
    (f_equal (Y.(GFace) l1 dim H2 ε)
      (f_equal (fun p => rew [GDom] eq_sym p in u) (eq_trans_refl_l p1))) P
    (f_equal (fun p => rew [GDom] eq_sym p in v) (eq_trans_refl_l p0))).
Defined.

(** The face square is reindexed along the three object comparisons.
    Naturality moves its coherence cell, and matching endpoint corrections
    cancel where the face paths are pasted. *)

Lemma faceDescStepCohCore (Y: νGpdPresentation arity)
  {l1 l2: nat} (e0: l1 = l2)
  (e1: l1.+1 = l2.+1) (He1: e1 = f_equal S e0)
  (e2: l1.+2 = l2.+2) (He2: e2 = f_equal S e1)
  {A0 A1 A2: HGpd}
  (p0: Y.(G0) l1 = A0) (p1: Y.(G0) l1.+1 = A1)
  (p2: Y.(G0) l1.+2 = A2)
  (q: nat) (Hq1: q <= l1) (Hq2: q <= l2)
  (r0: nat) (Hr: r0 <= q) (ε ω: arity)
  (t: A2) (ur ub uq ud: _)
  (Pr: Y.(GFace) l1.+1 r0 (Hr ↕ ↑ Hq1) ω
      (rew [GDom] eq_sym p2 in t)
    = rew [GDom] eq_sym p1 in (ur: A1))
  (Pqr: Y.(GFace) l1 q Hq1 ε (rew [GDom] eq_sym p1 in ur)
    = rew [GDom] eq_sym p0 in (ub: A0))
  (Pq: Y.(GFace) l1.+1 q.+1 (⇑ Hq1) ε
      (rew [GDom] eq_sym p2 in t)
    = rew [GDom] eq_sym p1 in (uq: A1))
  (Prq: Y.(GFace) l1 r0 (Hr ↕ Hq1) ω
      (rew [GDom] eq_sym p1 in uq)
    = rew [GDom] eq_sym p0 in (ud: A0))
  (Csrc: ub = ud)
  (IH: (f_equal (Y.(GFace) l1 q Hq1 ε) Pr • Pqr)
      • f_equal (fun w: A0 => rew [GDom] eq_sym p0 in w) Csrc
    = Y.(GFaceCoh) l1 q Hq1 r0 Hr ε ω
        (rew [GDom] eq_sym p2 in t)
      • (f_equal (Y.(GFace) l1 r0 (Hr ↕ Hq1) ω) Pq • Prq)):
  (f_equal (Y.(GFace) l2 q Hq2 ε)
      (faceDescStepCore Y e1 e2 He2 p1 p2 r0
        (Hr ↕ ↑ Hq1) (Hr ↕ ↑ Hq2) ω t ur Pr)
    • faceDescStepCore Y e0 e1 He1 p0 p1 q Hq1 Hq2 ε ur ub Pqr)
  • f_equal
      (fun w: A0 => rew [GDom]
        eq_sym (f_equal (fun z => Y.(G0) z) (eq_sym e0) • p0) in w)
      Csrc
  = Y.(GFaceCoh) l2 q Hq2 r0 Hr ε ω
      (rew [GDom]
        eq_sym (f_equal (fun z => Y.(G0) z) (eq_sym e2) • p2) in t)
    • (f_equal (Y.(GFace) l2 r0 (Hr ↕ Hq2) ω)
        (faceDescStepCore Y e1 e2 He2 p1 p2 q.+1
          (⇑ Hq1) (⇑ Hq2) ε t uq Pq)
      • faceDescStepCore Y e0 e1 He1 p0 p1 r0
          (Hr ↕ Hq1) (Hr ↕ Hq2) ω uq ud Prq).
Proof.
  destruct e0; cbn in He1; subst e1; cbn in He2; subst e2.
  unfold faceDescStepCore; cbn [eq_rect eq_rect_r eq_sym f_equal].
  now exact (face_square_reindex
    (fun u: A0 => rew [GDom] eq_sym p0 in u)
    (fun u: A0 => rew [GDom] eq_sym (eq_refl • p0) in u)
    (fun u: A1 => rew [GDom] eq_sym p1 in u)
    (fun u: A1 => rew [GDom] eq_sym (eq_refl • p1) in u)
    (fun u: A2 => rew [GDom] eq_sym p2 in u)
    (fun u: A2 => rew [GDom] eq_sym (eq_refl • p2) in u)
    (fun u => f_equal (fun p => rew [GDom] eq_sym p in u) (eq_trans_refl_l p0))
    (fun u => f_equal (fun p => rew [GDom] eq_sym p in u) (eq_trans_refl_l p1))
    (fun u => f_equal (fun p => rew [GDom] eq_sym p in u) (eq_trans_refl_l p2))
    (Y.(GFace) l1 q Hq1 ε) (Y.(GFace) l1 r0 (Hr ↕ Hq1) ω)
    (Y.(GFace) l1.+1 q.+1 (⇑ Hq1) ε) (Y.(GFace) l1.+1 r0 (Hr ↕ ↑ Hq1) ω)
    (Y.(GFaceCoh) l1 q Hq1 r0 Hr ε ω) t ur uq ub ud Pr Pqr Pq Prq Csrc IH).
Defined.

(** The faces of [g X] along a descent are the faces of the position: the
    face-compatibility of the cell identification, by induction on the witness
    with index equalities normalized by [natUIP]. *)

Lemma descFaceG {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0) (k dim: nat) (HdX: dim <= k + n) (HdS: dim <= k + n)
  (ε: arity) (t: gF0 S0 k.+1):
  (g X).(GFace) (k + n) dim HdX ε
    (rew [GDom] (eq_sym (descF0 D k.+1)) in t) =
  rew [GDom] (eq_sym (descF0 D k)) in
    gFaceC S0 (descChain D).2 k dim HdS ε t.
Proof.
  revert k dim HdX HdS ε t.
  induction D as [|n0 Xpre0 Sbase HDbase IH];
    intros k dim HdX HdS ε t.
  - cbn [descF0 descChain].
    now exact (gFaceLevelCore X DepsCohs3ChainNil
      (plus_n_O k) (plus_n_O k.+1)
      (natUIP (plus_n_O k.+1) (f_equal S (plus_n_O k)))
      dim HdS (leR_eq_r (plus_n_O (k + 0)) HdX) ε t).
  - cbn [descF0 descChain].
    now exact (faceDescStepCore (g X)
      (plus_n_Sm k n0) (plus_n_Sm k.+1 n0)
      (natUIP (plus_n_Sm k.+1 n0) (f_equal S (plus_n_Sm k n0)))
      (descF0 HDbase k.+1) (descF0 HDbase k.+2)
      dim (leR_eq_r (eq_sym (plus_n_Sm k n0)) HdX) HdX ε
      t
      (gFaceC (next Sbase)
        (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
        k dim HdS ε t)
      (IH k.+1 dim
        (leR_eq_r (eq_sym (plus_n_Sm k n0)) HdX)
        (leR_eq_r (eq_sym (plus_n_Sm k n0)) HdS)
        ε t)).
Defined.

(** The successor equation of [descFaceG], kept named so its recursive call
    stays folded when the coherence proof rewrites the four boundary paths. *)

Lemma descFaceGS {n} {Xpre: (νGpdAt n).(prefix)}
  {S0: νGpdFrom n Xpre} (D: Desc S0) (k dim: nat)
  (HdX HdS: dim <= k + n.+1) (ε: arity)
  (t: gF0 (next S0) k.+1):
  descFaceG (DescS D) k dim HdX HdS ε t
  = faceDescStepCore (g X)
      (plus_n_Sm k n) (plus_n_Sm k.+1 n)
      (natUIP (plus_n_Sm k.+1 n) (f_equal S (plus_n_Sm k n)))
      (descF0 D k.+1) (descF0 D k.+2)
      dim (leR_eq_r (eq_sym (plus_n_Sm k n)) HdX) HdX ε
      t
      (gFaceC (next S0) (chainUp1 (νExt3At S0) (descChain D).2)
        k dim HdS ε t)
      (descFaceG D k.+1 dim
        (leR_eq_r (eq_sym (plus_n_Sm k n)) HdX)
        (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS) ε t).
Proof.
  now reflexivity.
Defined.

(** Naturality of the descent face identification. *)

Lemma descFaceGCoh {n} {Xpre: (νGpdAt n).(prefix)}
  {S0: νGpdFrom n Xpre} (D: Desc S0)
  (k q: nat) (Hq: q <= k + n) (r0: nat) (Hr: r0 <= q)
  (ε ω: arity) (t: gF0 S0 k.+2):
  (f_equal ((g X).(GFace) (k + n) q Hq ε)
      (descFaceG D k.+1 r0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω t)
    • descFaceG D k q Hq Hq ε
        (gFaceC S0 (descChain D).2 k.+1 r0 (Hr ↕ ↑ Hq) ω t))
  • f_equal (fun w => rew [GDom] eq_sym (descF0 D k) in w)
      (gFaceCohC S0 (descChain D).2 k q Hq r0 Hr ε ω t)
  = (g X).(GFaceCoh) (k + n) q Hq r0 Hr ε ω
      (rew [GDom] eq_sym (descF0 D k.+2) in t)
    • (f_equal ((g X).(GFace) (k + n) r0 (Hr ↕ Hq) ω)
        (descFaceG D k.+1 q.+1 (⇑ Hq) (⇑ Hq) ε t)
      • descFaceG D k r0 (Hr ↕ Hq) (Hr ↕ Hq) ω
          (gFaceC S0 (descChain D).2 k.+1 q.+1 (⇑ Hq) ε t)).
Proof.
  revert k q Hq r0 Hr ε ω t.
  induction D as [|n0 Xpre0 Sbase HDbase IH];
    intros k q Hq r0 Hr ε ω t.
  - unfold descFaceG; cbn.
    now exact (gFaceLevelCohCore X
      (plus_n_O k) (plus_n_O k.+1)
      (natUIP (plus_n_O k.+1) (f_equal S (plus_n_O k)))
      (plus_n_O k.+2)
      (natUIP (plus_n_O k.+2) (f_equal S (plus_n_O k.+1)))
      q Hq (leR_eq_r (plus_n_O (k + 0)) Hq)
      r0 Hr ε ω t).
  - rewrite 4 descFaceGS.
    cbn [descF0 descChain].
    now exact (faceDescStepCohCore (g X)
      (plus_n_Sm k n0) (plus_n_Sm k.+1 n0)
      (natUIP (plus_n_Sm k.+1 n0) (f_equal S (plus_n_Sm k n0)))
      (plus_n_Sm k.+2 n0)
      (natUIP (plus_n_Sm k.+2 n0)
        (f_equal S (plus_n_Sm k.+1 n0)))
      (descF0 HDbase k.+1) (descF0 HDbase k.+2)
      (descF0 HDbase k.+3)
      q (leR_eq_r (eq_sym (plus_n_Sm k n0)) Hq) Hq
      r0 Hr ε ω t
      (gFaceC (next Sbase)
        (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
        k.+1 r0 (Hr ↕ ↑ Hq) ω t)
      (gFaceC (next Sbase)
        (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
        k q Hq ε
        (gFaceC (next Sbase)
          (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
          k.+1 r0 (Hr ↕ ↑ Hq) ω t))
      (gFaceC (next Sbase)
        (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
        k.+1 q.+1 (⇑ Hq) ε t)
      (gFaceC (next Sbase)
        (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
        k r0 (Hr ↕ Hq) ω
        (gFaceC (next Sbase)
          (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
          k.+1 q.+1 (⇑ Hq) ε t))
      (descFaceG HDbase k.+2 r0
        (leR_eq_r (eq_sym (plus_n_Sm k.+1 n0)) (Hr ↕ ↑ Hq))
        (leR_eq_r (eq_sym (plus_n_Sm k.+1 n0)) (Hr ↕ ↑ Hq)) ω t)
      (descFaceG HDbase k.+1 q
        (leR_eq_r (eq_sym (plus_n_Sm k n0)) Hq)
        (leR_eq_r (eq_sym (plus_n_Sm k n0)) Hq) ε
        (gFaceC (next Sbase)
          (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
          k.+1 r0 (Hr ↕ ↑ Hq) ω t))
      (descFaceG HDbase k.+2 q.+1
        (leR_eq_r (eq_sym (plus_n_Sm k.+1 n0)) (⇑ Hq))
        (leR_eq_r (eq_sym (plus_n_Sm k.+1 n0)) (⇑ Hq)) ε t)
      (descFaceG HDbase k.+1 r0
        (leR_eq_r (eq_sym (plus_n_Sm k n0)) (Hr ↕ Hq))
        (leR_eq_r (eq_sym (plus_n_Sm k n0)) (Hr ↕ Hq)) ω
        (gFaceC (next Sbase)
          (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
          k.+1 q.+1 (⇑ Hq) ε t))
      (gFaceCohC (next Sbase)
        (chainUp1 (νExt3At Sbase) (descChain HDbase).2)
        k q Hq r0 Hr ε ω t)
      (IH k.+1 q (leR_eq_r (eq_sym (plus_n_Sm k n0)) Hq)
        r0 Hr ε ω t)).
Defined.

Fixpoint descPack (n: nat): Desc (νGpdPack n X).2 :=
  match n with
  | 0 => DescZ
  | S n => DescS (descPack n)
  end.

End Descent.

End DiagramFacesOn.
