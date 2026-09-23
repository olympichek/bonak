(** The indexed side of the backward round trip [f ∘ g] of the
    correspondence between the fibred presentation ([νGpdPresentation]) and the
    indexed construction ([νGpd]), one truncation level up, over the
    translation tower of [νGpdEquiv.v].

    A level of the round trip identifies the cells of the presheaf [g X] in
    the ambient dimension with the total space of the position reached in
    [X] (the descent witness [Desc]), and contracts the candidate fillers of
    [f (g X)] over a translated frame onto the fillers of [X]
    ([fillerEquivOf]).  The frame identification the contraction consumes —
    the candidate frame of a descended cell is the frame translation of its
    frame — is carried stage by stage, in the shape of the two stage-indexed
    frame lists it compares. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νGpd.HGpd
  νGpd.Layer νGpd.Lemmas νGpd.Pasting νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Lib Require Import Equiv.

From Bonak Require Import Limit.
From Bonak.Equiv.Gpd Require Export PathAlgebra Filler.

From Bonak.Equiv.Gpd Require PathTactics.

Set Primitive Projections.
Set Keyed Unification.

Module Translation (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Import A.

Module Export Tr := Translations.

Section FG.

Variable X: νGpds.

(** The descent identification

    The level step of the round trip must identify the cells of [g X] with the
    total spaces of the carried [X]-position. Induction on [Desc] proves the
    identification, with [plus_n_Sm]-style equalities on the relative index at
    each successor step. *)

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

(** Aligning the two presentations of the next-level cell identification:
    stepping the witness, then identifying at relative index 0, is identifying
    at relative index 1. *)

Definition descTotalS {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (HD: Desc S0): descTotal (DescS HD) = descF0 HD 1 :=
  f_equal (fun w: n.+1 = n.+1 =>
      f_equal (fun x: nat => (g X).(G0) x) (eq_sym w) • descF0 HD 1)
     (natUIP (plus_n_Sm 0 n) eq_refl)
  • eq_trans_refl_l (descF0 HD 1).

(** The same one relative index up.  Both are stated as explicit terms rather
    than closed by a rewrite: the reindexing lemmas below need the exact
    correction, and an equation between two paths of [HGpd]s is not unique. *)

Definition descF0DescS1 {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (HD: Desc S0): descF0 (DescS HD) 1 = descF0 HD 2 :=
  f_equal (fun w: n.+2 = n.+2 =>
      f_equal (fun x: nat => (g X).(G0) x) (eq_sym w) • descF0 HD 2)
     (natUIP (plus_n_Sm 1 n) (f_equal S (plus_n_Sm 0 n))
      • f_equal (fun w: n.+1 = n.+1 => f_equal S w)
          (natUIP (plus_n_Sm 0 n) eq_refl))
  • eq_trans_refl_l (descF0 HD 2).

(** [faceDescStepCore] at a level equality that is reflexivity: the two level
    equalities are proofs in [nat], hence [natUIP]-trivial, and what the step
    contributes is then only the unit correction of the two carried object
    equalities. *)

Lemma faceDescStepCoreTriv (Y: νGpdPresentation arity) {l: nat}
  (e0: l = l) (E0: e0 = eq_refl) (e1: l.+1 = l.+1) (He: e1 = f_equal S e0)
  {A0 A1: HGpd} (p0: Y.(G0) l = A0) (p1: Y.(G0) l.+1 = A1)
  (dim: nat) (H1 H2: dim <= l) (ε: arity) (u: A1) (v: A0)
  (P: Y.(GFace) l dim H1 ε (rew [GDom] eq_sym p1 in u)
    = rew [GDom] eq_sym p0 in v):
  faceDescStepCore Y e0 e1 He p0 p1 dim H1 H2 ε u v P
  = f_equal (fun z: Y.(G0) l.+1 = A1 =>
       Y.(GFace) l dim H2 ε (rew [GDom] eq_sym z in u))
      (f_equal (fun w: l.+1 = l.+1 =>
          f_equal (fun x: nat => Y.(G0) x) (eq_sym w) • p1)
         (He • f_equal (fun w: l = l => f_equal S w) E0)
       • eq_trans_refl_l p1)
    • (P • f_equal (fun z: Y.(G0) l = A0 => rew [GDom] eq_sym z in v)
        (eq_sym (f_equal (fun w: l = l =>
            f_equal (fun x: nat => Y.(G0) x) (eq_sym w) • p0) E0
          • eq_trans_refl_l p0))).
Proof.
  subst e0; cbn in He; subst e1.
  unfold faceDescStepCore, path_change.
  cbn [f_equal eq_sym].
  rewrite (eq_trans_refl_l (eq_trans_refl_l p1)),
    (eq_trans_refl_l (eq_trans_refl_l p0)).
  rewrite (f_equal_compose
    (fun z: Y.(G0) l.+1 = A1 => rew [GDom] eq_sym z in u)
    (Y.(GFace) l dim H2 ε) (eq_trans_refl_l p1)).
  now rewrite (eq_sym_map_distr
    (fun z: Y.(G0) l = A0 => rew [GDom] eq_sym z in v) (eq_trans_refl_l p0)).
Qed.

(** Reindexing the descent face identification: stepping the witness and
    reading at relative index [0] is reading at relative index [1], up to the
    two corrections of [descF0].  This is [descFaceGS] with the level
    equalities discharged by [natUIP]. *)

Lemma descFaceGDescS0 {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (HD: Desc S0) (dim: nat) (HdX HdS: dim <= 0 + n.+1) (ε: arity)
  (t: gF0 (next S0) 1):
  descFaceG (DescS HD) 0 dim HdX HdS ε t
  = f_equal (fun z: gF0 X n.+2 = gF0 S0 2 =>
       (g X).(GFace) n.+1 dim HdX ε (rew [GDom] eq_sym z in t)) (descF0DescS1 HD)
    • (descFaceG HD 1 dim HdX HdS ε t
       • f_equal (fun z: gF0 X n.+1 = gF0 S0 1 =>
            rew [GDom] eq_sym z in gFaceC S0 (descChain HD).2 1 dim HdS ε t)
           (eq_sym (descTotalS HD))).
Proof.
  rewrite descFaceGS.
  now exact (faceDescStepCoreTriv (g X) (plus_n_Sm 0 n)
    (natUIP (plus_n_Sm 0 n) eq_refl)
    (plus_n_Sm 1 n) (natUIP (plus_n_Sm 1 n) (f_equal S (plus_n_Sm 0 n)))
    (descF0 HD 1) (descF0 HD 2) dim _ _ ε t _ (descFaceG HD 1 dim _ _ ε t)).
Qed.

(** A chain package is determined by its length, and the result type of
    [νFace] does not mention the chain, so a face map may be moved between
    two chains of equal length. *)

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

(** The descent's cell, frame and filler maps

    The level state reads a cell of [g X] as an element of the total space of
    the position it has reached, and the frame identification compares its
    frame component with the frame translation.  The face law of that reading
    is [descFaceG] with its transports turned around. *)

Definition descCell {m} {XpB: (νGpdAt m).(prefix)} {SB: νGpdFrom m XpB}
  (HD: Desc SB) (t: gF0 X m): νTotal SB := rew [GDom] (descTotal HD) in t.

Definition descCells {m} {XpB: (νGpdAt m).(prefix)} {SB: νGpdFrom m XpB}
  (HD: Desc SB) (t: gF0 X m): νFrame XpB := (descCell HD t).1.

(** The descent face identification at a relative index: the transposed form
    of [descFaceG], where the cell identification is applied to the face
    rather than to the cell. *)

Definition descCellFaceK {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0) (k dim: nat) (HdX HdS: dim <= k + n) (ε: arity)
  (u: gF0 X (k.+1 + n)):
  rew [GDom] (descF0 D k) in ((g X).(GFace) (k + n) dim HdX ε u)
  = gFaceC S0 (descChain D).2 k dim HdS ε (rew [GDom] (descF0 D k.+1) in u)
  := condFace (descF0 D k) (descF0 D k.+1)
       ((g X).(GFace) (k + n) dim HdX ε)
       (gFaceC S0 (descChain D).2 k dim HdS ε)
       (descFaceG D k dim HdX HdS ε) u.

(** The exchange law of the transposed identification, at every relative
    index: [descFaceGCoh] read through [condSq].  This is the descent's own
    δ-δ square, the fact the restriction ladder's layer clause rests on. *)

Lemma descCellFaceKSq {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (D: Desc S0) (k q: nat) (Hq: q <= k + n) (r: nat) (Hr: r <= q)
  (ε ω: arity) (t: gF0 X (k.+2 + n)):
  f_equal (fun z: gF0 X (k + n) => rew [GDom] (descF0 D k) in z)
     ((g X).(GFaceCoh) (k + n) q Hq r Hr ε ω t)
  • (descCellFaceK D k r (Hr ↕ Hq) (Hr ↕ Hq) ω
       ((g X).(GFace) (k + n).+1 q.+1 (⇑ Hq) ε t)
     • f_equal (gFaceC S0 (descChain D).2 k r (Hr ↕ Hq) ω)
         (descCellFaceK D k.+1 q.+1 (⇑ Hq) (⇑ Hq) ε t))
  = descCellFaceK D k q Hq Hq ε ((g X).(GFace) (k + n).+1 r (Hr ↕ ↑ Hq) ω t)
    • (f_equal (gFaceC S0 (descChain D).2 k q Hq ε)
         (descCellFaceK D k.+1 r (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω t)
       • gFaceCohC S0 (descChain D).2 k q Hq r Hr ε ω
           (rew [GDom] (descF0 D k.+2) in t)).
Proof.
  now exact (condSq (P := GDom) (descF0 D k) (descF0 D k.+1) (descF0 D k.+2)
    ((g X).(GFace) (k + n) q Hq ε) ((g X).(GFace) (k + n) r (Hr ↕ Hq) ω)
    ((g X).(GFace) (k + n).+1 q.+1 (⇑ Hq) ε)
    ((g X).(GFace) (k + n).+1 r (Hr ↕ ↑ Hq) ω)
    (gFaceC S0 (descChain D).2 k q Hq ε)
    (gFaceC S0 (descChain D).2 k r (Hr ↕ Hq) ω)
    (gFaceC S0 (descChain D).2 k.+1 q.+1 (⇑ Hq) ε)
    (gFaceC S0 (descChain D).2 k.+1 r (Hr ↕ ↑ Hq) ω)
    ((g X).(GFaceCoh) (k + n) q Hq r Hr ε ω)
    (gFaceCohC S0 (descChain D).2 k q Hq r Hr ε ω)
    (descFaceG D k q Hq Hq ε) (descFaceG D k r (Hr ↕ Hq) (Hr ↕ Hq) ω)
    (descFaceG D k.+1 q.+1 (⇑ Hq) (⇑ Hq) ε)
    (descFaceG D k.+1 r (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω)
    (descFaceGCoh D k q Hq r Hr ε ω) t).
Defined.

(** The same reindexing for the transposed identification. *)

Lemma descCellFaceKDescS0 {n} {Xpre: (νGpdAt n).(prefix)}
  {S0: νGpdFrom n Xpre} (HD: Desc S0) (dim: nat)
  (HdX HdS: dim <= 0 + n.+1) (ε: arity) (u: gF0 X (1 + n.+1)):
  descCellFaceK (DescS HD) 0 dim HdX HdS ε u
  = f_equal (fun z: gF0 X n.+1 = gF0 S0 1 =>
       rew [GDom] z in (g X).(GFace) n.+1 dim HdX ε u) (descTotalS HD)
    • (descCellFaceK HD 1 dim HdX HdS ε u
       • f_equal (fun z: gF0 X n.+2 = gF0 S0 2 =>
            gFaceC S0 (descChain HD).2 1 dim HdS ε (rew [GDom] z in u))
           (eq_sym (descF0DescS1 HD))).
Proof.
  now exact (condFaceCorr (P := GDom) (descTotalS HD) (descF0DescS1 HD)
    ((g X).(GFace) n.+1 dim HdX ε) (gFaceC S0 (descChain HD).2 1 dim HdS ε)
    (descFaceG (DescS HD) 0 dim HdX HdS ε) (descFaceG HD 1 dim HdX HdS ε)
    (fun t => descFaceGDescS0 HD dim HdX HdS ε t) u).
Defined.

(** At relative index [0] the identification of the cells one level up is the
    level state's own [descTotal], which is [descF0] at index [1] up to
    [descTotalS]. *)

Definition descCellFace {n} {XpB: (νGpdAt n).(prefix)} {SB: νGpdFrom n XpB}
  (HD: Desc SB) (dim: nat) (HdX HdS: dim <= 0 + n) (ε: arity)
  (u: gF0 X n.+1):
  descCell HD ((g X).(GFace) (0 + n) dim HdX ε u)
  = gFaceC SB (descChain HD).2 0 dim HdS ε (descCell (DescS HD) u) :=
  descCellFaceK HD 0 dim HdX HdS ε u
  • f_equal (fun e: gF0 X n.+1 = gF0 SB 1 =>
       gFaceC SB (descChain HD).2 0 dim HdS ε (rew [GDom] e in u))
      (eq_sym (descTotalS HD)).

(** The descent's δ-δ square, in the form the restriction ladder consumes:
    the identification of a doubly-faced cell computed through the two orders
    of the two faces.  It is [descCellFaceKSq] at relative index [0], with the
    level-[n.+1] leg reindexed by [descCellFaceKDescS0] and the resulting
    corrections discharged by [sqAssemble]. *)

Lemma descCellFaceSq {n} {Xpre: (νGpdAt n).(prefix)} {S0: νGpdFrom n Xpre}
  (HD: Desc S0) (q: nat) (Hq: q <= 0 + n) (r: nat) (Hr: r <= q)
  (ε ω: arity) (t: gF0 X n.+2):
  f_equal (descCell HD) ((g X).(GFaceCoh) (0 + n) q Hq r Hr ε ω t)
  • (descCellFace HD r (Hr ↕ Hq) (Hr ↕ Hq) ω
       ((g X).(GFace) (0 + n).+1 q.+1 (⇑ Hq) ε t)
     • f_equal (gFaceC S0 (descChain HD).2 0 r (Hr ↕ Hq) ω)
         (descCellFace (DescS HD) q.+1 (⇑ Hq) (⇑ Hq) ε t))
  = descCellFace HD q Hq Hq ε ((g X).(GFace) (0 + n).+1 r (Hr ↕ ↑ Hq) ω t)
    • (f_equal (gFaceC S0 (descChain HD).2 0 q Hq ε)
         (descCellFace (DescS HD) r (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω t)
       • gFaceCohC S0 (descChain HD).2 0 q Hq r Hr ε ω
           (descCell (DescS (DescS HD)) t)).
Proof.
  unfold descCellFace.
  rewrite (descCellFaceKDescS0 HD q.+1 (⇑ Hq) (⇑ Hq) ε t).
  rewrite (descCellFaceKDescS0 HD r (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω t).
  now exact (sqAssemble
    (gFaceC S0 (descChain HD).2 0 r (Hr ↕ Hq) ω)
    (gFaceC S0 (descChain HD).2 0 q Hq ε)
    (gFaceC S0 (descChain HD).2 1 q.+1 (⇑ Hq) ε)
    (gFaceC S0 (descChain HD).2 1 r (Hr ↕ ↑ Hq) ω)
    (f_equal (descCell HD) ((g X).(GFaceCoh) (0 + n) q Hq r Hr ε ω t))
    (f_equal (fun z: gF0 X n.+1 = gF0 S0 1 =>
        rew [GDom] z in (g X).(GFace) n.+1 q.+1 (⇑ Hq) ε t) (descTotalS HD))
    (f_equal (fun z: gF0 X n.+1 = gF0 S0 1 =>
        rew [GDom] z in (g X).(GFace) n.+1 r (Hr ↕ ↑ Hq) ω t) (descTotalS HD))
    (descCellFaceK HD 0 r (Hr ↕ Hq) (Hr ↕ Hq) ω
       ((g X).(GFace) (0 + n).+1 q.+1 (⇑ Hq) ε t))
    (descCellFaceK HD 0 q Hq Hq ε ((g X).(GFace) (0 + n).+1 r (Hr ↕ ↑ Hq) ω t))
    (f_equal (fun e: gF0 X n.+1 = gF0 S0 1 =>
        gFaceC S0 (descChain HD).2 0 r (Hr ↕ Hq) ω
          (rew [GDom] e in (g X).(GFace) (0 + n).+1 q.+1 (⇑ Hq) ε t))
       (eq_sym (descTotalS HD)))
    (erCancel (gFaceC S0 (descChain HD).2 0 r (Hr ↕ Hq) ω) (descTotalS HD)
       ((g X).(GFace) (0 + n).+1 q.+1 (⇑ Hq) ε t))
    (f_equal (fun e: gF0 X n.+1 = gF0 S0 1 =>
        gFaceC S0 (descChain HD).2 0 q Hq ε
          (rew [GDom] e in (g X).(GFace) (0 + n).+1 r (Hr ↕ ↑ Hq) ω t))
       (eq_sym (descTotalS HD)))
    (erCancel (gFaceC S0 (descChain HD).2 0 q Hq ε) (descTotalS HD)
       ((g X).(GFace) (0 + n).+1 r (Hr ↕ ↑ Hq) ω t))
    (f_equal (fun e: gF0 X n.+2 = gF0 S0 2 => rew [GDom] e in t)
       (eq_sym (descF0DescS1 HD) • eq_sym (descTotalS (DescS HD))))
    (descCellFaceK HD 1 q.+1 (⇑ Hq) (⇑ Hq) ε t)
    (descCellFaceK HD 1 r (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω t)
    (f_equal (fun z: gF0 X n.+2 = gF0 S0 2 =>
        gFaceC S0 (descChain HD).2 1 q.+1 (⇑ Hq) ε (rew [GDom] z in t))
       (eq_sym (descF0DescS1 HD)))
    (f_equal (fun e: gF0 X n.+2 = gF0 S0 2 =>
        gFaceC S0 (descChain HD).2 1 q.+1 (⇑ Hq) ε (rew [GDom] e in t))
       (eq_sym (descTotalS (DescS HD))))
    (ccFuse (gFaceC S0 (descChain HD).2 1 q.+1 (⇑ Hq) ε)
       (eq_sym (descF0DescS1 HD)) (eq_sym (descTotalS (DescS HD))) t)
    (f_equal (fun z: gF0 X n.+2 = gF0 S0 2 =>
        gFaceC S0 (descChain HD).2 1 r (Hr ↕ ↑ Hq) ω (rew [GDom] z in t))
       (eq_sym (descF0DescS1 HD)))
    (f_equal (fun e: gF0 X n.+2 = gF0 S0 2 =>
        gFaceC S0 (descChain HD).2 1 r (Hr ↕ ↑ Hq) ω (rew [GDom] e in t))
       (eq_sym (descTotalS (DescS HD))))
    (ccFuse (gFaceC S0 (descChain HD).2 1 r (Hr ↕ ↑ Hq) ω)
       (eq_sym (descF0DescS1 HD)) (eq_sym (descTotalS (DescS HD))) t)
    (fun d => gFaceCohC S0 (descChain HD).2 0 q Hq r Hr ε ω d)
    (descCellFaceKSq HD 0 q Hq r Hr ε ω t)).
Qed.

(** The restriction law of the cell frames at an arbitrary stage

    The stage of the ladder is measured by a chain out of the position's own
    dependency data: at a chain of length [L], the cell frames are [getFrame]
    along it, and the face at the complementary dimension is the face at
    dimension [0] of the bottom of that chain — which is the construction's
    own restriction there ([getFrameGetPainting]).  Projecting a further
    chain of length [q] raises the local dimension to [q]
    ([getFrameRestr]), which is the general form the restriction clause of
    the frame identification asks for.

    The local-dimension-[0] law at a lower stage is not the projection of the
    one above: projecting a restriction shifts the local index by one, so
    each stage consumes its own instance of these lemmas at its own chain. *)

Lemma descCellRestrAt {n} {XpB0: (νGpdAt n).(prefix)} {S0: νGpdFrom n XpB0}
  (HD: Desc S0) {pB kB} {dcB: DepsCohs pB kB}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (dim: nat) (Hdim: dim <= 0 + n)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + dim)%nat)
  (ε: arity) (t: (g X).(G0) n.+1):
  descCell HD ((g X).(GFace) (0 + n) dim Hdim ε t)
  = νFace cB ε (descCells (DescS HD) t).
Proof.
  now exact (descCellFace HD dim Hdim Hdim ε t
    • gFaceCAsνFace S0 (descChain HD).2 dim Hdim cB Hlen ε
        (descCell (DescS HD) t)).
Defined.

(** The frame identification at a level, at the top stage

    The candidate frame of a descended cell is the frame translation of the
    frame the cell reads.  This is the shape [fillerEquivOf] consumes. *)

Definition FrtInvTr {m} {XpA XpB: (νGpdAt m.+1).(prefix)}
  (W: TrTower m.+1 XpA XpB) (T: PshTower (g X) m XpA)
  (SB: νGpdFrom m.+1 XpB) (HD: Desc SB): Type :=
  forall (D: νFrame XpB) (c: this SB D),
  mkPshFrame (g X) (towerPshDeps (g X) T)
    (rew [GDom] (eq_sym (descTotal HD)) in
      ((D; c): ({D0: νFrame XpB & this SB D0}: HGpd)))
  = mkFrameEqv (towerTrDeps W) D.

(** The filler equivalence of the round trip at a level: the candidate-filler
    contraction over the frame identification, in the direction the
    translation tower stores it — from the [X] side to the [f (g X)] side,
    fibrewise over the frame translation. *)

Definition fgThisTr {m} {XpA XpB: (νGpdAt m.+1).(prefix)}
  (W: TrTower m.+1 XpA XpB) (T: PshTower (g X) m XpA)
  (SB: νGpdFrom m.+1 XpB) (HD: Desc SB) (FRT: FrtInvTr W T SB HD):
  towerFillerEqv W (mkPshFiller (g X) (towerPshDeps (g X) T)) (this SB) :=
  fun D => symEquiv (fillerEquivOf (mkFrameEqv (towerTrDeps W))
    (descTotal HD) (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT D).

(** Level [0]: the frame is [gunit], the candidate frame map is constant, and
    the frame translation the translation tower computes at the empty tower is the
    identity, so the identification is [hunit_ext]. *)

Definition pshF0A: gF0 X 0 -> νFrame (tt: (νGpdAt 0).(prefix)) := fun _ => tt.

Definition frt0 (D: νFrame (tt: (νGpdAt 0).(prefix))) (c: this X D):
  pshF0A (rew [GDom] (eq_sym (descTotal DescZ)) in
    ((D; c): ({D0: νFrame (tt: (νGpdAt 0).(prefix)) & this X D0}: HGpd)))
  = mkFrameEqv (towerTrDeps (trTower0 tt tt)) D :=
  hunit_ext tt (mkFrameEqv (towerTrDeps (trTower0 tt tt)) D).

Definition fgThis0:
  towerFillerEqv (trTower0 tt tt) (pshFiller0 (g X)) (this X) :=
  fun D => symEquiv (fillerEquivOf (mkFrameEqv (towerTrDeps (trTower0 tt tt)))
    (descTotal DescZ) pshF0A frt0 D).

Definition fgTowerStep0:
  TrTower 1 ((tt; pshFiller0 (g X)): (νGpdAt 1).(prefix))
    ((tt; this X): (νGpdAt 1).(prefix)) :=
  trTowerStep (trTower0 tt tt) fgThis0.

(** The frame identification, stage by stage

    The identification the level step carries is not the top equation alone:
    the step splits it, by [eq_existT_curried], into the same equation at the
    stage below and a layer equation, so it is carried in the shape of the two
    stage-indexed frame lists it compares — [mkPshFrameTypes] on the [f (g X)]
    side, [mkFrameEqvTypes] for the translation. *)

Fixpoint mkFrtFrameTypes (M: nat) {p k}:
  forall {framesA framesB: mkFrameTypes p k}
    (eqvs: mkFrameEqvTypes framesA framesB)
    (pshFrames: mkPshFrameTypes (g X) M framesA)
    (cells: mkPshFrameTypes (g X) M framesB), Type :=
  match p return forall (framesA framesB: mkFrameTypes p k)
    (eqvs: mkFrameEqvTypes framesA framesB)
    (pshFrames: mkPshFrameTypes (g X) M framesA)
    (cells: mkPshFrameTypes (g X) M framesB), Type with
  | 0 => fun _ _ _ _ _ => unit
  | S p => fun framesA framesB eqvs pshFrames cells =>
    { _: mkFrtFrameTypes M eqvs.1 pshFrames.1 cells.1 &T
      forall t: (g X).(G0) M, pshFrames.2 t = eqvs.2 (cells.2 t) }
  end.

(** The [X]-side stage list of a cell-to-frame map

    A frame of the construction is a nested Σ, so a map into the top stage
    determines the maps into all lower stages by iterated first projection.
    The recursion is over the dependency data rather than over a bare
    [mkFrameTypes], because only [mkFrames] exposes that nesting.  The top
    entry is kept out of the fixpoint so that it stays the given map
    definitionally at a variable stage. *)

Fixpoint mkCellFramesPrefix (M: nat) {p k}:
  forall (deps: DepsRestr p k),
  ((g X).(G0) M -> mkFrame deps) ->
  mkPshFrameTypes (g X) M (mkFrames deps).1 :=
  match p return forall (deps: DepsRestr p k),
    ((g X).(G0) M -> mkFrame deps) ->
    mkPshFrameTypes (g X) M (mkFrames deps).1 with
  | 0 => fun _ _ => tt
  | S p => fun deps top =>
    (mkCellFramesPrefix M deps.(1) (fun t => (top t).1); fun t => (top t).1)
  end.

Definition mkCellFrames (M: nat) {p k} (deps: DepsRestr p k)
  (top: (g X).(G0) M -> mkFrame deps):
  mkPshFrameTypes (g X) M (mkFrames deps) :=
  (mkCellFramesPrefix M deps top; top).

(** The cell frames as a chain

    A cell-frame list is the one determined by [getFrame] along a chain out
    of the level's own dependency data.  Projecting the list is extending the
    chain by one step, definitionally, so the ladder's stage recursion and
    the chain the restriction law is stated over step together. *)

Definition mkCellFramesOf (M: nat) {P K} {depsTop: DepsRestr P K} {p k}
  {deps: DepsRestr p k} (c: DepsChain depsTop deps)
  (top: (g X).(G0) M -> mkFrame depsTop):
  mkPshFrameTypes (g X) M (mkFrames deps) :=
  mkCellFrames M deps (fun t => getFrame c (top t)).

(** The [X]-side painting value of a cell

    The painting the descended cell reads at a stage: at the top it is the
    filler the cell descends to, and one stage down it pairs the layer of the
    frame one stage up with the value there — the mirror of [mkPshPainting]. *)

Fixpoint mkCellValuesPrefix (M: nat) {p k}:
  forall (deps: DepsRestr p k) (extraDeps: DepsRestrExtension p k deps)
    (top: (g X).(G0) M -> mkFrame deps)
    (val: forall u, mkPainting extraDeps (top u)),
  mkPshPaintingTypes (g X) M (mkCellFramesPrefix M deps top)
    (mkPaintingsPrefix extraDeps) :=
  match p return forall (deps: DepsRestr p k)
    (extraDeps: DepsRestrExtension p k deps)
    (top: (g X).(G0) M -> mkFrame deps)
    (val: forall u, mkPainting extraDeps (top u)),
    mkPshPaintingTypes (g X) M (mkCellFramesPrefix M deps top)
      (mkPaintingsPrefix extraDeps) with
  | 0 => fun _ _ _ _ => tt
  | S p => fun deps extraDeps top val =>
    (mkCellValuesPrefix M deps.(1) (deps; extraDeps)%extradepsrestr
       (fun t => (top t).1) (fun u => ((top u).2; val u));
     fun u => ((top u).2; val u))
  end.

Definition mkCellValues (M: nat) {p k} (deps: DepsRestr p k)
  (extraDeps: DepsRestrExtension p k deps)
  (top: (g X).(G0) M -> mkFrame deps)
  (val: forall u, mkPainting extraDeps (top u)):
  mkPshPaintingTypes (g X) M (mkCellFrames M deps top)
    (mkPaintings extraDeps) :=
  (mkCellValuesPrefix M deps extraDeps top val; val).

(** The painting a cell reads at a stage

    Descending a painting chain splits the cell the top pair forms: at every
    step the layer the frame has just passed becomes the first component of
    the painting one stage down.  This is the section of [getPainting] over
    the frame projection [getFrame (extChainDeps c)]. *)

Fixpoint chainPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext):
  forall (d: mkFrame depsTop), mkPainting extTop d ->
  mkPainting ext (getFrame (extChainDeps c) d) :=
  match c in ExtChain _ ext0
    return forall (d: mkFrame depsTop), mkPainting extTop d ->
      mkPainting ext0 (getFrame (extChainDeps c) d) with
  | ExtChainNil => fun d cp => cp
  | ExtChainCons c' => fun d cp =>
      ((getFrame (extChainDeps c') d).2; chainPainting c' d cp)
  end.

(** The cell values as a chain

    The values of the cell-frame list of a chain: the painting the descended
    pair reads at the chain's stage.  As for the frames, projecting the list
    is extending the chain by one step, definitionally. *)

Definition mkCellValuesOf (M: nat) {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop} {p k} {deps: DepsRestr p k}
  {ext: DepsRestrExtension p k deps} (c: ExtChain extTop ext)
  (top: (g X).(G0) M -> mkFrame depsTop)
  (val: forall u, mkPainting extTop (top u)):
  mkPshPaintingTypes (g X) M (mkCellFramesOf M (extChainDeps c) top)
    (mkPaintings ext) :=
  mkCellValues M deps ext (fun t => getFrame (extChainDeps c) (top t))
    (fun u => chainPainting c (top u) (val u)).

(** Descending a rebuilt cell recovers the painting it was built from: the
    section law of [getPainting], in the pair form that avoids a transport
    over [getFrameGetPainting]. *)

Lemma chainPaintingGetPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext):
  forall (d: mkFrame deps) (cp: mkPainting ext d),
  ((getFrame (extChainDeps c) (getPainting c d cp).1;
    chainPainting c (getPainting c d cp).1 (getPainting c d cp).2)
   : {D: mkFrame deps &T mkPainting ext D}) = (d; cp).
Proof.
  induction c as [|p k deps ext c IH]; intros d cp.
  - now reflexivity.
  - now exact (f_equal (fun w: {D: mkFrame deps &T mkPainting ext D} =>
      ((w.1.1; (w.1.2; w.2)):
        {D: mkFrame deps.(1) &T mkPainting (deps; ext)%extradepsrestr D}))
      (IH (d; cp.1) cp.2)).
Defined.

(** The deep cell retains the frame read one stage above it.  The path is
    now reflexivity after exposing the chain constructor. *)

Lemma getFrameDeepCell {P0 K0: nat} {dc2Top: DepsCohs2 P0 K0} {p0 k0: nat} {dc2: DepsCohs2 p0 k0}
  (c: DepsCohs2Chain dc2Top dc2)
  (z: {d: mkFrame (mkDepsCohs dc2Top).(_deps) &T mkPainting (mkDepsCohs dc2Top).(_extraDeps) d}):
  getFrame (cohsChainNext (cohs2ChainDepsCohs c)) z.1 = ((deepCell c z).1; (deepCell c z).2.1).
Proof.
  now reflexivity.
Defined.

(** Reading the frame of the canonical face identification commutes with
    rebuilding a cell.  These 2-cells retain the painting correction needed
    by the frame-square ladder, including when the two paintings are only
    propositionally equal. *)

Lemma faceDeepAsνFaceReadCellZero {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c2: DepsCohs2Chain dc2Top dc2)
  (Hj: 0 <= k)
  (Hlen: cohs2ChainLen c2 = (cohsChainLen (cohs2ChainDepsCohs c2) + 0)%nat)
  (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  let c := cohs2ChainDepsCohs c2 in
  let Y := restrCell dc2.(_extraDepsCohs) 0 Hj ε
    (deepCell c2 (d; Q)).1 (deepCell c2 (d; Q)).2 in
  chainPaintingGetPainting (cohsChainExt c) Y.1 Y.2
  = f_equal (fun z => (getFrame (extChainDeps (cohsChainExt c)) z.1;
        chainPainting (cohsChainExt c) z.1 z.2))
      (faceDeepAsνFace c2 0 Hj c Hlen ε d Q)
    • chainPaintingGetPainting (cohsChainExt c)
        (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext c) d).1)
        (nth (getFrame (cohsChainNext c) d).2 ε)
    • f_equal (fun x: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))) =>
        ((mkRestrFrame 0 leR_O ε x.1; nth x.2 ε):
          {D: mkFrame dc2.(_depsCohs).(_deps) &T mkPainting dc2.(_depsCohs).(_extraDeps) D}))
        (getFrameDeepCell c2 (d; Q)).
Proof.
  destruct c2.
  - now reflexivity.
  - unfold faceDeepAsνFace; cbn.
    unfold faceDeepZero, νFacePackIrr.
    rewrite (dcPackUIP (dcPackEq _ _ _) eq_refl).
    cbn [νFaceAsDeep].
    rewrite eq_trans_refl_l.
    now reflexivity.
Defined.

Lemma faceDeepAsνFaceReadZero {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c2: DepsCohs2Chain dc2Top dc2)
  (Hj: 0 <= k)
  (Hlen: cohs2ChainLen c2 = (cohsChainLen (cohs2ChainDepsCohs c2) + 0)%nat)
  (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  let c := cohs2ChainDepsCohs c2 in
  let Y := restrCell dc2.(_extraDepsCohs) 0 Hj ε
    (deepCell c2 (d; Q)).1 (deepCell c2 (d; Q)).2 in
  projT1_eq (chainPaintingGetPainting (cohsChainExt c) Y.1 Y.2)
  = f_equal (fun z => getFrame (extChainDeps (cohsChainExt c)) z.1)
      (faceDeepAsνFace c2 0 Hj c Hlen ε d Q)
    • projT1_eq (chainPaintingGetPainting (cohsChainExt c)
        (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext c) d).1)
        (nth (getFrame (cohsChainNext c) d).2 ε)).
Proof.
  destruct c2.
  - now reflexivity.
  - unfold faceDeepAsνFace; cbn.
    unfold faceDeepZero, νFacePackIrr.
    rewrite (dcPackUIP (dcPackEq _ _ _) eq_refl).
    cbn [νFaceAsDeep].
    rewrite eq_trans_refl_l.
    now reflexivity.
Defined.

Lemma faceDeepAsνFaceReadSucc {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p.+1 k} (c2: DepsCohs2Chain dc2Top dc2)
  (Hj: 1 <= k.+1)
  (Hlen: cohs2ChainLen (DepsCohs2ChainCons c2)
    = (cohsChainLen (cohs2ChainDepsCohs c2) + 1)%nat)
  (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2Top.(_depsCohs))))
  (Q: mkPainting (mkExtraDeps dc2Top.(_extraDepsCohs)) d):
  let c := cohs2ChainDepsCohs c2 in
  let Y := restrCell (proj1DepsCohs2 dc2).(_extraDepsCohs) 1 Hj ε
    (deepCell (DepsCohs2ChainCons c2) (d; Q)).1
    (deepCell (DepsCohs2ChainCons c2) (d; Q)).2 in
  projT1_eq (chainPaintingGetPainting (cohsChainExt c) (Y.1; Y.2.1) Y.2.2)
  = f_equal (fun z => getFrame (extChainDeps (cohsChainExt c)) z.1)
      (faceDeepAsνFace (DepsCohs2ChainCons c2) 1 Hj c Hlen ε d Q)
    • projT1_eq (chainPaintingGetPainting (cohsChainExt c)
        (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext c) d).1)
        (nth (getFrame (cohsChainNext c) d).2 ε)).
Proof.
  pose (H0 := eq_sym (cohs2ChainDepsCohsLen c2)
    • eq_sym (addZeroR (cohsChainLen (cohs2ChainDepsCohs c2)))).
  assert (EF:
    faceDeepAsνFace (DepsCohs2ChainCons c2) 1 Hj (cohs2ChainDepsCohs c2) Hlen ε d Q
    = faceDeepAsνFace c2 0 (⇓ Hj) (cohs2ChainDepsCohs c2) H0 ε d Q).
  {
    now exact (f_equal
      (fun h => faceDeepAsνFace c2 0 (⇓ Hj) (cohs2ChainDepsCohs c2) h ε d Q)
      (natUIP _ H0)).
  }
  cbn zeta. rewrite EF.
  now exact (faceDeepAsνFaceReadZero c2 (⇓ Hj) H0 ε d Q).
Defined.

(** The restriction law of the cell lists at a stage, frames and values at
    once

    At the chain the stage is named by, the entry of the cell-frame list and
    the entry of the cell-value list at a face cell are the [ε]-restriction
    of the frame the cell reads one level up and the [ε]-component of its top
    layer.  Keeping the two as one path in the total space of the stage's
    paintings is what lets the stored painting equivalence — which reads a
    frame and a value together — be moved along it in one step. *)

Lemma descCellPairRestrAt {n} {XpB0: (νGpdAt n).(prefix)} {S0: νGpdFrom n XpB0}
  (HD: Desc S0) {pB kB} {dcB: DepsCohs pB kB}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (dim: nat) (Hdim: dim <= 0 + n)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + dim)%nat)
  (ε: arity) (t: (g X).(G0) n.+1):
  ((getFrame (extChainDeps (cohsChainExt cB))
      (descCells HD ((g X).(GFace) (0 + n) dim Hdim ε t));
    chainPainting (cohsChainExt cB)
      (descCells HD ((g X).(GFace) (0 + n) dim Hdim ε t))
      ((descCell HD ((g X).(GFace) (0 + n) dim Hdim ε t)).2))
   : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D})
  = (mkRestrFrame (depsCohs := dcB) 0 leR_O ε
       (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).1;
     nth (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).2 ε).
Proof.
  refine (f_equal (fun w: νTotal S0 =>
    ((getFrame (extChainDeps (cohsChainExt cB)) w.1;
      chainPainting (cohsChainExt cB) w.1 w.2)
     : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D}))
    (descCellRestrAt HD cB dim Hdim Hlen ε t) • _).
  now exact (chainPaintingGetPainting (cohsChainExt cB)
    (mkRestrFrame (depsCohs := dcB) 0 leR_O ε
      (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).1)
    (nth (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).2 ε)).
Defined.

(** The pair form of the descent's restriction law, read off the face
    identification: the frame and the painting of a face cell, as one path in
    the total space of the stage's paintings, are the image of
    [descCellFace] under the pair map, followed by the [νFace] identification
    and the section law of [getPainting].  This is how the ladder's own pair
    laws are matched with the legs of the descent's δ-δ square. *)

Lemma descCellPairRestrAtAsFace {n} {XpB0: (νGpdAt n).(prefix)}
  {S0: νGpdFrom n XpB0} (HD: Desc S0) {pB kB} {dcB: DepsCohs pB kB}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (dim: nat) (Hdim: dim <= 0 + n)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + dim)%nat)
  (ε: arity) (t: (g X).(G0) n.+1):
  descCellPairRestrAt HD cB dim Hdim Hlen ε t
  = f_equal (fun w: νTotal S0 =>
      ((getFrame (extChainDeps (cohsChainExt cB)) w.1;
        chainPainting (cohsChainExt cB) w.1 w.2)
       : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D}))
      (descCellFace HD dim Hdim Hdim ε t)
    • (f_equal (fun w: νTotal S0 =>
        ((getFrame (extChainDeps (cohsChainExt cB)) w.1;
          chainPainting (cohsChainExt cB) w.1 w.2)
         : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D}))
        (gFaceCAsνFace S0 (descChain HD).2 dim Hdim cB Hlen ε
           (descCell (DescS HD) t))
       • chainPaintingGetPainting (cohsChainExt cB)
           (mkRestrFrame (depsCohs := dcB) 0 leR_O ε
             (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).1)
           (nth (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).2 ε)).
Proof.
  unfold descCellPairRestrAt, descCellRestrAt.
  rewrite eq_trans_map_distr.
  now rewrite eq_trans_assoc.
Defined.

(** The frame half of the descent's face identification, read as the frame
    half of the stage's pair restriction law: the two differ by the [νFace]
    identification and the section law of [getPainting], the same two
    corrections [descCellPairRestrAtAsFace] exhibits at the level of pairs. *)

Lemma descCellFaceFrameAsPairFst {n} {XpB0: (νGpdAt n).(prefix)}
  {S0: νGpdFrom n XpB0} (HD: Desc S0) {pB kB} {dcB: DepsCohs pB kB}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (dim: nat) (Hdim: dim <= 0 + n)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + dim)%nat)
  (ε: arity) (t: (g X).(G0) n.+1):
  f_equal (fun z: νTotal S0 => getFrame (extChainDeps (cohsChainExt cB)) z.1)
    (descCellFace HD dim Hdim Hdim ε t)
  = projT1_eq (descCellPairRestrAt HD cB dim Hdim Hlen ε t)
    • eq_sym (f_equal (fun z: νTotal S0 =>
          getFrame (extChainDeps (cohsChainExt cB)) z.1)
          (gFaceCAsνFace S0 (descChain HD).2 dim Hdim cB Hlen ε
             (descCell (DescS HD) t))
        • projT1_eq (chainPaintingGetPainting (cohsChainExt cB)
             (mkRestrFrame (depsCohs := dcB) 0 leR_O ε
               (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).1)
             (nth (getFrame (cohsChainNext cB) (descCells (DescS HD) t)).2 ε))).
Proof.
  assert (TR: forall (A0: Type) (a0 b0 c0: A0) (u0: a0 = b0) (v0: b0 = c0),
    u0 = (u0 • v0) • eq_sym v0).
  { intros A0 a0 b0 c0 u0 v0. now destruct v0, u0. }
  unfold projT1_eq.
  rewrite (descCellPairRestrAtAsFace HD cB dim Hdim Hlen ε t).
  rewrite 2 (eq_trans_map_distr (fun w: {D: mkFrame dcB.(_deps) &T
    mkPainting dcB.(_extraDeps) D} => w.1)).
  rewrite (f_equal_compose
    (fun w: νTotal S0 =>
       ((getFrame (extChainDeps (cohsChainExt cB)) w.1;
         chainPainting (cohsChainExt cB) w.1 w.2)
        : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D}))
    (fun w: {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D} => w.1)
    (descCellFace HD dim Hdim Hdim ε t)).
  rewrite (f_equal_compose
    (fun w: νTotal S0 =>
       ((getFrame (extChainDeps (cohsChainExt cB)) w.1;
         chainPainting (cohsChainExt cB) w.1 w.2)
        : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D}))
    (fun w: {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D} => w.1)
    (gFaceCAsνFace S0 (descChain HD).2 dim Hdim cB Hlen ε
       (descCell (DescS HD) t))).
  now exact (TR _ _ _ _ _ _).
Defined.

(** The painting-level identification

    The stage-indexed statement that the presheaf painting value at a cell,
    moved along the frame identification, is the stored painting equivalence
    at the cell's own value.  The presheaf painting at a stage below the top
    is the layer of the frame one stage up ([mkPshPainting] at [AddPshDep]),
    and the painting equivalence pairs the layer equivalence with the one
    above it ([mkPaintingEqv] at [AddTrDep]), so an entry of this list at a
    stage splits into the layer equation one stage up and the entry one stage
    up.  At the top stage of a tower the two sides are the tautological filler
    of a cell and the level's own filler equivalence, which is where
    [fillerEquivOfWhole] enters. *)

Fixpoint mkFrtPaintingTypes (M: nat) {p k}:
  forall {framesA framesB: mkFrameTypes p k}
    {eqvs: mkFrameEqvTypes framesA framesB}
    {pshFrames: mkPshFrameTypes (g X) M framesA}
    {cells: mkPshFrameTypes (g X) M framesB}
    (frt: mkFrtFrameTypes M eqvs pshFrames cells)
    {paintingsA: mkPaintingTypes p k framesA}
    {paintingsB: mkPaintingTypes p k framesB}
    (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB)
    (pshPaintings: mkPshPaintingTypes (g X) M pshFrames paintingsA)
    (cellValues: mkPshPaintingTypes (g X) M cells paintingsB), Type :=
  match p return forall (framesA framesB: mkFrameTypes p k)
    (eqvs: mkFrameEqvTypes framesA framesB)
    (pshFrames: mkPshFrameTypes (g X) M framesA)
    (cells: mkPshFrameTypes (g X) M framesB)
    (frt: mkFrtFrameTypes M eqvs pshFrames cells)
    (paintingsA: mkPaintingTypes p k framesA)
    (paintingsB: mkPaintingTypes p k framesB)
    (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB)
    (pshPaintings: mkPshPaintingTypes (g X) M pshFrames paintingsA)
    (cellValues: mkPshPaintingTypes (g X) M cells paintingsB), Type with
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ => unit
  | S p => fun framesA framesB eqvs pshFrames cells frt
             paintingsA paintingsB pEqvs pshPaintings cellValues =>
    { _: mkFrtPaintingTypes M frt.1 pEqvs.1 pshPaintings.1 cellValues.1 &T
      forall u: (g X).(G0) M,
        rew [fun x: framesA.2 => paintingsA.2 x] (frt.2 u) in
          pshPaintings.2 u
        = pEqvs.2 (cells.2 u) (cellValues.2 u) }
  end.

(** The staged data the frame identification is carried with

    A stage of the ladder is named by a chain out of the position's own
    dependency data: the [X]-side dependencies at that stage are the ones the
    chain lands on, and the cell frames and cell values are the descended
    cells read there.  The translation's [A]-side dependencies, the
    translation itself and the presheaf data over it are carried; the [B]
    side is determined by the chain, which is what lets the stage recursion
    and the restriction laws of the descent step together. *)

Class FrtDeps (M: nat) {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) := {
  _frDepsA: DepsRestr p.+1 k;
  _frBound: p.+1 <= M.+1;
  _frFrameEqvs: mkFrameEqvTypes _frDepsA.(_frames)
    (mkDepsRestr (depsCohs := dcB)).(_frames);
  _frPaintingEqvs: mkPaintingEqvTypes _frFrameEqvs
    _frDepsA.(_paintings) (mkDepsRestr (depsCohs := dcB)).(_paintings);
  _frTrRestrs: (mkTrRestrTypesAndFrames _frFrameEqvs
    _frPaintingEqvs).(TrRestrTypesDef) _frDepsA.(_restrFrames)
    (mkDepsRestr (depsCohs := dcB)).(_restrFrames);
  _frPshFrames: mkPshFrameTypes (g X) M _frDepsA.(_frames);
  _frPshPaintings: mkPshPaintingTypes (g X) M _frPshFrames
    _frDepsA.(_paintings);
  _frPshRestrs: (mkPshRestrTypesAndFrames (g X) M _frBound _frPshFrames
    _frPshPaintings).(PshRestrTypesDef (g X)) _frDepsA.(_restrFrames);
  _frFrames: mkFrtFrameTypes M _frFrameEqvs _frPshFrames
    (mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD));
  _frPaintings: mkFrtPaintingTypes M _frFrames _frPaintingEqvs _frPshPaintings
    (mkCellValuesOf M (cohsChainExt cB) (descCells HD)
      (fun u => (descCell HD u).2));
}.

(** The two bundles the constructions of the tower and of the translation tower consume:
    the translation data at the stage, and the presheaf data over its [A]
    side. *)

Definition frTr {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB):
  TrDepsRestr p.+1 k := {|
  _depsA := F.(_frDepsA);
  _depsB := mkDepsRestr (depsCohs := dcB);
  _frameEqvs := F.(_frFrameEqvs);
  _paintingEqvs := F.(_frPaintingEqvs);
  _trRestrs := F.(_frTrRestrs);
|}.

#[local]
Instance frtPshDeps {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB):
  PshDepsRestr (g X) M p.+1 k := {|
  _pdeps := F.(_frDepsA);
  _pshBound := F.(_frBound);
  _pshFrames := F.(_frPshFrames);
  _pshPaintings := F.(_frPshPaintings);
  _pshRestrs := F.(_frPshRestrs);
|}.

(** Projecting the stage is extending the chain: the cell frames and cell
    values the class derives from the longer chain are the projections of the
    ones it derives from the shorter, definitionally. *)

#[local]
Instance proj1FrtDeps {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p.+1 k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB):
  FrtDeps M HD (DepsCohsChainCons cB).
Proof.
  unshelve econstructor.
  - now exact (proj1DepsRestr F.(_frDepsA)).
  - now exact (↓ F.(_frBound)).
  - now exact (F.(_frFrameEqvs).1).
  - now exact (F.(_frPaintingEqvs).1).
  - now exact (F.(_frPshFrames).1).
  - now exact (F.(_frPshPaintings).1).
  - now exact (F.(_frFrames).1).
  - now exact (F.(_frTrRestrs).1).
  - now exact (F.(_frPshRestrs).1).
  - now exact (F.(_frPaintings).1).
Defined.

(** The identification one level up, over a given [X]-side cell frame map,
    and the same list one stage down — the shape the stage step splits it
    into. *)

Definition FrtFramesType {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB))): Type :=
  mkFrtFrameTypes M.+1 (mkFrameEqvs (frTr F))
    (mkPshFrames (g X) (frtPshDeps F))
    (mkCellFrames M.+1 (mkDepsRestr (depsCohs := dcB)) top).

Definition FrtFramesPrevType {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB))): Type :=
  mkFrtFrameTypes M.+1 (mkFrameEqvs (proj1TrDepsRestr (frTr F)))
    (mkPshFrames (g X) (proj1PshDepsRestr (g X) (frtPshDeps F)))
    (mkCellFrames M.+1 (proj1DepsRestr (mkDepsRestr (depsCohs := dcB)))
      (fun t => (top t).1)).

(** The layer equation the stage step leaves: the presheaf layer of a cell,
    moved along the identification at the stage below, is the layer
    equivalence at the cell's own frame. *)

Definition mkFrtLayerType {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top) (t: (g X).(G0) M.+1): Type :=
  rew [fun a => mkLayer F.(_frDepsA).(_restrFrames).2 a] (prev.2 t) in
    mkPshLayer (g X) F.(_frPshPaintings) F.(_frPshRestrs) (⇓ F.(_frBound)) t
  = mkTrLayerEquiv F.(_frPaintingEqvs) F.(_frTrRestrs) (top t).1 (top t).2.

(** The stage step. *)

Definition mkFrtFrameStep {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top)
  (lay: forall t, mkFrtLayerType F top prev t): FrtFramesType F top :=
  (prev; fun t => eq_existT_curried (prev.2 t) (lay t)).

(** The top entry of the carried list is the frame identification in the form
    [fillerEquivOf] consumes: the candidate frame of a cell is the frame
    translation of the frame the cell reads. *)

Definition frtTop {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (H: FrtFramesType F top) (t: (g X).(G0) M.+1):
  mkPshFrame (g X) (frtPshDeps F) t = mkFrameEqv (frTr F) (top t) := H.2 t.

(** The layer bridge

    A layer built by [lam] on one side and by [lmap] on the other, with a
    transport of the whole layer along a path of its index, is determined by
    its components: [nth_rew] moves the transport inside, [nth_lam] and
    [nth_lmap] read the two sides.  This is the [lam]-against-[lmap] form of
    [lmap2_rew_eq], which asks for a common underlying layer on both sides —
    the presheaf layer has none. *)

Lemma lamLmapRewEq {T Y: Type} {P: Y -> HGpd} {rf0: arity -> T -> Y}
  {d1 d2: T} (E: d1 = d2) (f: forall ω, P (rf0 ω d1))
  {B: arity -> HGpd} (l: Layer B) (G: forall ω, B ω -> P (rf0 ω d2))
  (H: forall ω, rew [fun d => P (rf0 ω d)] E in f ω = G ω (nth l ω)):
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E in lam f = lmap G l.
Proof.
  apply ext; intro ω.
  refine (nth_rew (B := fun d ω => P (rf0 ω d)) E (lam f) ω • _).
  refine (f_equal (fun x => rew [fun d => P (rf0 ω d)] E in x)
    (nth_lam f ω) • _).
  now exact (H ω • eq_sym (nth_lmap G l ω)).
Defined.

(** The [lam]-against-[lmap] bridge, component by component: the companion of
    [nth_dpath_lmap2_chain] for [lamLmapRewEq]. *)

Lemma nth_dpath_lamLmapRewEq {T Y: Type} {P: Y -> HGpd} {rf0: arity -> T -> Y}
  {d1 d2: T} (E: d1 = d2) (f: forall ω, P (rf0 ω d1))
  {B: arity -> HGpd} (l: Layer B) (G: forall ω, B ω -> P (rf0 ω d2))
  (H: forall ω, rew [fun d => P (rf0 ω d)] E in f ω = G ω (nth l ω)) (ω: arity):
  nth_dpath (Bd := fun d ω => P (rf0 ω d)) (lamLmapRewEq E f l G H) ω
  = f_equal (fun x => rew [fun d => P (rf0 ω d)] E in x) (nth_lam f ω)
    • (H ω • eq_sym (nth_lmap G l ω)).
Proof.
  unfold nth_dpath, lamLmapRewEq.
  rewrite ap_nth_ext.
  now exact (eq_trans_sym_cancel_l
    (nth_rew (B := fun d ω => P (rf0 ω d)) E (lam f) ω) _).
Defined.

(** The layer equation, component by component

    At an arity the equation is between the presheaf painting at the ε-face
    of the cell, moved along the identification at the stage below and along
    the presheaf's own diagonal restriction path, and the stored painting
    equivalence at the ε-restriction of the cell's own frame.  No layer
    algebra remains in it. *)

Definition mkFrtResidueType {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top)
  (t: (g X).(G0) M.+1) (ω: arity): Type :=
  rew [fun d: ((mkRestrFrameTypesAndFrames F.(_frDepsA).(_paintings).1)
                 .(FrameDef) F.(_frDepsA).(_restrFrames).1).2 =>
       F.(_frDepsA).(_paintings).2
         (F.(_frDepsA).(_restrFrames).2 0 leR_O ω d)]
      (prev.2 t) in
    rew [fun x: F.(_frDepsA).(_frames).2 =>
         F.(_frDepsA).(_paintings).2 x]
        (F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ω t) in
      F.(_frPshPaintings).2 ((g X).(GFace) M p (⇓ F.(_frBound)) ω t)
  = compEquiv
      (F.(_frPaintingEqvs).2
         ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ω
            (top t).1))
      (rewEquiv (fun x: F.(_frDepsA).(_frames).2 =>
         F.(_frDepsA).(_paintings).2 x)
         (F.(_frTrRestrs).2 0 leR_O ω (top t).1))
      (nth (top t).2 ω).

Definition mkFrtLayerOfNth {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top) (t: (g X).(G0) M.+1)
  (H: forall ω, mkFrtResidueType F top prev t ω): mkFrtLayerType F top prev t.
Proof.
  unfold mkFrtLayerType, mkPshLayer, mkTrLayerEquiv, layerEquiv.
  unshelve eapply lamLmapRewEq.
  now exact H.
Defined.
(** The restriction clause of the frame identification, at one stage

    The square saying that the identification at a face cell, read through the
    restriction law of the cell frames, agrees with the identification one
    level up restricted: the two stored restriction laws [Qpsh] and [Qtr] are
    its other two edges.  [Qcells] supplies the [X]-side restriction law of the cell
    frames, obtained from the descent. *)

Definition mkFrtRestrTypeStep {M p k}
  {framesA framesB: mkFrameTypes p.+1 k}
  {eqvs: mkFrameEqvTypes framesA framesB}
  {pshFrames: mkPshFrameTypes (g X) M framesA}
  {cells: mkPshFrameTypes (g X) M framesB}
  (frt: mkFrtFrameTypes M eqvs pshFrames cells)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  {prevPsh: PshRestrBlock (g X) M pshFrames.1 prevA}
  {prevTr: TrRestrBlock eqvs.1 prevA prevB}
  {RA: mkRestrFrameTypesStep framesA prevA}
  {RB: mkRestrFrameTypesStep framesB prevB}
  (Qpsh: mkPshRestrTypesStep (g X) pshFrames prevPsh RA)
  (Qtr: mkTrRestrTypesStep eqvs prevTr RA RB)
  (cellsNext: (g X).(G0) M.+1 -> (prevB.(FrameDef) RB.1).2)
  (frtNext: forall t: (g X).(G0) M.+1,
     (prevPsh.(PshFramesDef (g X)) Qpsh.1).2 t
     = (prevTr.(FrameEqvDef) Qtr.1).2 (cellsNext t))
  (Qcells: forall q (Hq: q <= k) (Hqp: q + p <= M) (ε: arity)
     (t: (g X).(G0) M.+1),
     cells.2 ((g X).(GFace) M (q + p) Hqp ε t)
     = RB.2 q Hq ε (cellsNext t)): Type :=
  forall q (Hq: q <= k) (Hqp: q + p <= M) (ε: arity) (t: (g X).(G0) M.+1),
  (frt.2 ((g X).(GFace) M (q + p) Hqp ε t)
   • f_equal (fun x => eqvs.2 x) (Qcells q Hq Hqp ε t))
  • Qtr.2 q Hq ε (cellsNext t)
  = Qpsh.2 q Hq Hqp ε t • f_equal (RA.2 q Hq ε) (frtNext t).

(** The layer equation from the restriction clause

    The residue of the stage step is the restriction clause at local
    dimension [0], read through the carried painting identification: the
    presheaf painting at the ω-face of the cell is the stored painting
    equivalence at the ω-component of the cell's own top layer, and the two
    frame paths the two readings are transported along differ by exactly the
    square the clause states.  The descent supplies the [X]-side edge as one
    path of pairs ([descCellPairRestrAt]), so the frame and the value move
    together through the selected residue boundary. *)

Definition mkFrtResidueOfRestr {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top)
  (Hpair: forall (ε: arity) (t: (g X).(G0) M.+1),
     (((mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD)).2
         ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t);
       (mkCellValuesOf M (cohsChainExt cB) (descCells HD)
         (fun u => (descCell HD u).2)).2
         ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t))
      : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D})
     = ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ε (top t).1;
        nth (top t).2 ε))
  (HR: forall (ε: arity) (t: (g X).(G0) M.+1),
     (F.(_frFrames).2 ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t)
      • f_equal (fun x => F.(_frFrameEqvs).2 x) (projT1_eq (Hpair ε t)))
     • F.(_frTrRestrs).2 0 leR_O ε (top t).1
     = F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ε t
       • f_equal (F.(_frDepsA).(_restrFrames).2 0 leR_O ε) (prev.2 t))
  (t: (g X).(G0) M.+1) (ω: arity): mkFrtResidueType F top prev t ω
  := residueFill
       (fun x: F.(_frDepsA).(_frames).2 =>
          (F.(_frDepsA).(_paintings).2 x).(GDom))
       (fun d => F.(_frDepsA).(_restrFrames).2 0 leR_O ω d)
       (fun x => F.(_frFrameEqvs).2 x)
       (fun d v => F.(_frPaintingEqvs).2 d v)
       (prev.2 t)
       (F.(_frPshPaintings).2 ((g X).(GFace) M p (⇓ F.(_frBound)) ω t))
       (F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ω t)
       (F.(_frFrames).2 ((g X).(GFace) M p (⇓ F.(_frBound)) ω t))
       (Hpair ω t)
       (F.(_frTrRestrs).2 0 leR_O ω (top t).1)
       (HR ω t)
       (F.(_frPaintings).2 ((g X).(GFace) M p (⇓ F.(_frBound)) ω t)).

Definition mkFrtLayerOfRestr {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top)
  (Hpair: forall (ε: arity) (t: (g X).(G0) M.+1),
     (((mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD)).2
         ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t);
       (mkCellValuesOf M (cohsChainExt cB) (descCells HD)
         (fun u => (descCell HD u).2)).2
         ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t))
      : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D})
     = ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ε (top t).1;
        nth (top t).2 ε))
  (HR: forall (ε: arity) (t: (g X).(G0) M.+1),
     (F.(_frFrames).2 ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t)
      • f_equal (fun x => F.(_frFrameEqvs).2 x) (projT1_eq (Hpair ε t)))
     • F.(_frTrRestrs).2 0 leR_O ε (top t).1
     = F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ε t
       • f_equal (F.(_frDepsA).(_restrFrames).2 0 leR_O ε) (prev.2 t))
  (t: (g X).(G0) M.+1): mkFrtLayerType F top prev t :=
  mkFrtLayerOfNth F top prev t
    (fun ω => mkFrtResidueOfRestr F top prev Hpair HR t ω).

(** The restriction clause, and the identification it determines

    The [X]-side cell frame map of a stage is the descended cell projected
    along the stage's chain; extending the chain is taking its first
    projection, so one definition serves every stage of the ladder. *)

Definition descTop {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB):
  (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)) :=
  fun t => getFrame (cohsChainNext cB) (descCells (DescS HD) t).

(** The restriction clause reads one chosen frame path at each local
    dimension. Its zero path projects the pair law; positive paths share
    the parent's source change and projection. *)

Definition FrtQcellsAt {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB): Type :=
  forall q (Hq: q <= k) (Hqp: q + p <= M) (ε: arity) (t: (g X).(G0) M.+1),
  (mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD)).2
    ((g X).(GFace) M (q + p) Hqp ε t)
  = (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq ε (descTop HD cB t).1.

(** Positive-offset restriction paths are projected from the chosen parent
    cell after changing its source to the child dimension. *)
Fixpoint descQcellsPaired {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (q: nat) {struct q}:
  forall {p k} {dcB: DepsCohs p k}
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (Hq: q <= k) (Hqp: q + p <= M) (epsilon: arity) (t: (g X).(G0) M.+1),
  (mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD)).2
    ((g X).(GFace) M (q + p) Hqp epsilon t)
  = (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq epsilon
      (descTop HD cB t).1.
Proof.
  destruct q as [|q]; intros p k dcB cB Hlen Hq Hqp epsilon t.
  - now exact (projT1_eq (descCellPairRestrAt HD cB p Hqp Hlen epsilon t)).
  - destruct cB as [|p k dcB cB].
    + now destruct (leR_O_contra Hq).
    + pose (Hdim := leR_eq (plus_n_Sm q p) Hqp).
      pose (Hparent := Hlen • plus_n_Sm (cohsChainLen cB) p).
      pose (parent := descQcellsPaired M XpB0 S0 HD q p.+1 k dcB cB
        Hparent (⇓ Hq) Hdim epsilon t).
      pose (index := f_equal
        (fun u => getFrame (extChainDeps (cohsChainExt cB)) (descCells HD u))
        (pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
          (Hq := Hdim) (Hq' := Hqp) epsilon t)).
      now exact (projT1_eq (path_reindex_source (eq_sym index) parent)).
Defined.

Definition descQcellsPairedAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat):
  FrtQcellsAt HD cB :=
  fun q => descQcellsPaired HD q cB Hlen.

(** The external projection law uses the caller's length equality. The
    recursion's length equality is aligned once, together with both path
    components, before applying the selected source-reindex cell. *)
Section DescQcellsPairedProjection.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) {p k} {dcB: DepsCohs p.+1 k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p.+1)%nat)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M)
  (epsilon: arity) (t: (g X).(G0) M.+1).

Let childLen := Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p).
Let computedLen := childLen • plus_n_Sm (cohsChainLen cB) p.
Let originalParent := descQcellsPaired HD q cB Hlen Hq Hqp epsilon t.
Let adjustedParent := descQcellsPaired HD q cB computedLen Hq Hqp epsilon t.
Let lengthCell := f_equal (fun H => descQcellsPaired HD q cB H Hq Hqp epsilon t)
  (natUIP Hlen computedLen).
Let indexCell := f_equal
  (fun u => getFrame (extChainDeps (cohsChainExt cB)) (descCells HD u))
  (pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
    (Hq := Hqp) (Hq' := leR_add_shift Hqp) epsilon t).
Let childCell := path_reindex_source (eq_sym indexCell) adjustedParent.

Definition descQcellsPairedConsLayerAligned := projT2_eq childCell.

Definition descQcellsPairedCons:
  projT1_eq (descQcellsPaired HD q cB Hlen Hq Hqp epsilon t) =
  projT1_eq indexCell • descQcellsPaired HD q.+1 (DepsCohsChainCons cB)
    childLen (⇑ Hq) (leR_add_shift Hqp) epsilon t :=
  pair_path_parameter_cell lengthCell •
    source_projection_recover_comp indexCell adjustedParent.

Lemma descQcellsPairedCons_dep:
  rew [fun e => rew [fun x =>
      GDom (mkLayer dcB.(_deps).(_restrFrames).2
        (painting := dcB.(_deps).(_paintings).2) x)] e in
      (getFrame (extChainDeps (cohsChainExt cB))
        (descCells HD ((g X).(GFace) M (q + p.+1) Hqp epsilon t))).2 =
      ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq epsilon
        (descTop HD cB t).1).2]
    descQcellsPairedCons in projT2_eq originalParent =
  projT2_eq indexCell ⊙ descQcellsPairedConsLayerAligned.
Proof.
  now exact (pair_path_parameter_cell_dep lengthCell ⊙
    source_projection_recover_comp_dep indexCell adjustedParent).
Defined.
End DescQcellsPairedProjection.

Definition descQcells {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat):
  FrtQcellsAt HD cB :=
  descQcellsPairedAt cB Hlen.

(** The block

    The restriction clauses at stages [<= p+1], together with the frame
    identification one level up that they determine: the layer equation a
    stage leaves is its own clause at local dimension [0]
    ([mkFrtLayerOfRestr]), so the identification is computed from the clauses
    rather than carried beside them.  This mirrors
    [mkPshRestrTypesAndFrames], where the presheaf's restriction data
    determines the frame maps one level up.

    The recursion extends the chain at every step and stops at its bottom
    stage; the length condition it carries is what lets the descent's law be
    read at the face of the dimension the stage measures. *)

Class FrtRestrBlock {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB) := {
  FrtRestrDataDef: Type;
  FrtRestrFramesDef: FrtRestrDataDef -> FrtFramesType F (descTop HD cB);
}.

Fixpoint mkFrtRestrTypesAndFrames (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB),
  FrtRestrBlock F :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB), FrtRestrBlock F with
  | 0 => fun k dcB cB Hlen F => {|
      FrtRestrDataDef :=
        mkFrtRestrTypeStep F.(_frFrames) F.(_frPshRestrs) F.(_frTrRestrs)
          (fun t => (descTop HD cB t).1) (fun t => hunit_ext tt _)
          (descQcells cB Hlen);
      FrtRestrFramesDef Q :=
        mkFrtFrameStep F (descTop HD cB) (tt; fun t => hunit_ext tt _)
          (fun t => mkFrtLayerOfRestr F (descTop HD cB)
             (tt; fun t => hunit_ext tt _)
             (fun ε t => descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t)
             (fun ε t => Q 0 leR_O (⇓ F.(_frBound)) ε t) t);
    |}
  | S p => fun k dcB cB Hlen F =>
    let prevB := mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
      (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F) in
    {|
      FrtRestrDataDef :=
        { Q: prevB.(FrtRestrDataDef) &T
          mkFrtRestrTypeStep F.(_frFrames) F.(_frPshRestrs) F.(_frTrRestrs)
            (fun t => (descTop HD cB t).1)
            (fun t => (prevB.(FrtRestrFramesDef) Q).2 t)
            (descQcells cB Hlen) };
      FrtRestrFramesDef Q :=
        mkFrtFrameStep F (descTop HD cB) (prevB.(FrtRestrFramesDef) Q.1)
          (fun t => mkFrtLayerOfRestr F (descTop HD cB)
             (prevB.(FrtRestrFramesDef) Q.1)
             (fun ε t =>
                descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t)
             (fun ε t => Q.2 0 leR_O (⇓ F.(_frBound)) ε t) t);
    |}
  end.

(** The painting identification, level by level

    The entry of the painting list at a stage below the top splits, by
    [eq_existT_curried_dep], into the layer equation of the stage above — the
    one the frame ladder consumes — and the entry at that stage.  So the whole
    list at a level is determined by its top entry together with the
    restriction clauses, and it is built by the same stage recursion as the
    frames. *)

Lemma mkFrtPaintingStepDown {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (prev: FrtFramesPrevType F top)
  (lay: forall t, mkFrtLayerType F top prev t)
  (E: forall t: (g X).(G0) M.+1,
     rew [fun x => mkPainting XA x] ((mkFrtFrameStep F top prev lay).2 t) in
       mkPshPainting (g X) PX t
     = mkPaintingEqv TX (top t) (val t))
  (t: (g X).(G0) M.+1):
  rew [fun x => mkPainting (F.(_frDepsA); XA)%extradepsrestr x] (prev.2 t) in
    mkPshPainting (g X) (AddPshDep (g X) M (frtPshDeps F) PX) t
  = mkPaintingEqv (AddTrDep (frTr F) TX) (top t).1 ((top t).2; val t).
Proof.
  now exact (eq_existT_curried_dep (H := prev.2 t) (Hu := lay t) (Hv := E t)).
Defined.

(** The top entry of the painting list: the tautological filler of a cell,
    moved along the level's own frame identification. *)

Definition FrtPaintingTopType {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  {XA: DepsRestrExtension p.+1 k F.(_frDepsA)}
  {XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB))}
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (H: FrtFramesType F top): Type :=
  forall t: (g X).(G0) M.+1,
    rew [fun x => mkPainting XA x] (H.2 t) in mkPshPainting (g X) PX t
    = mkPaintingEqv TX (top t) (val t).

Fixpoint mkFrtPaintingsPrefix (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (val: forall u, mkPainting XB (descTop HD cB u))
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)),
  @mkFrtPaintingTypes M.+1 p.+1 k.+1
    (mkFrames (frTr F).(_depsA)).1 (mkFrames (frTr F).(_depsB)).1
    (mkFrameEqvs (frTr F)).1 (mkPshFrames (g X) (frtPshDeps F)).1
    (mkCellFrames M.+1 (mkDepsRestr (depsCohs := dcB)) (descTop HD cB)).1
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q).1
    (mkPaintings XA).1 (mkPaintings XB).1
    (mkPaintingEqvs TX).1 (mkPshPaintings (g X) PX).1
    (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB (descTop HD cB) val).1.
Proof.
  destruct p; intros k dcB cB Hlen F XA XB TX PX val Q E.
  - refine (tt; _).
    intro t.
    now exact (mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
      (tt; fun t0 => hunit_ext tt _)
      (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
         (tt; fun t1 => hunit_ext tt _)
         (fun ε t1 => descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t1)
         (fun ε t1 => Q 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
      E t).
  - unshelve refine ((fun Eprev => (mkFrtPaintingsPrefix M XpB0 S0 HD p k.+1 _
      (DepsCohsChainCons cB) (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
      (proj1FrtDeps F) (F.(_frDepsA); XA)%extradepsrestr
      (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
      (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
      (fun u => ((descTop HD cB u).2; val u)) Q.1 Eprev; Eprev)) _).
    intro t.
    now exact (mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
      ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
        (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
        (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
      (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
         ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
           (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
           (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
         (fun ε t1 => descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
         (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
      E t).
Defined.

Definition mkFrtPaintingsOfRestr (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (val: forall u, mkPainting XB (descTop HD cB u))
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)):
  mkFrtPaintingTypes M.+1
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
    (mkPaintingEqvs TX) (mkPshPaintings (g X) PX)
    (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB (descTop HD cB) val).
Proof.
  now exact (mkFrtPaintingsPrefix M HD p cB Hlen F XA XB TX PX val Q E; E).
Defined.

(** The two entries of the list, read off its stage recursion: the top entry
    is the datum it was built from, and the list below the top is the list at
    the stage below, at the clauses and the top entry stepped down. *)

Lemma frtPaintingTopPath (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
  (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall u, mkPainting XB (descTop HD cB u))
  (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cB) val
        ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)):
  (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E).2 = E.
Proof. now reflexivity. Defined.

Lemma frtPaintingStepPath (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {k} {dcB: DepsCohs p.+1 k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p.+1)%nat)
  (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+2 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+2 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall u, mkPainting XB (descTop HD cB u))
  (Q: (mkFrtRestrTypesAndFrames M HD p.+1 cB Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cB) val
        ((mkFrtRestrTypesAndFrames M HD p.+1 cB Hlen F).(FrtRestrFramesDef) Q)):
  (mkFrtPaintingsOfRestr M HD p.+1 cB Hlen F XA XB TX PX val Q E).1
  = mkFrtPaintingsOfRestr M HD p (DepsCohsChainCons cB)
      (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F)
      (F.(_frDepsA); XA)%extradepsrestr
      (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
      (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
      (fun u => ((descTop HD cB u).2; val u)) Q.1
      (fun t => mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
         ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
             (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
             (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
         (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
            ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
                (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
                (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
            (fun ε t1 =>
               descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
            (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
         E t).
Proof. now reflexivity. Qed.

(** The same two entries read as an explicit [mkFrtPaintingStepDown]: the
    entry below the top of the list is the top entry stepped down along the
    layer equation the clauses determine.  This is the fact about the
    painting identification one level up that the rung-1 clause at layers
    consumes; stating it pointwise avoids asking for the two [X]-side cell
    frame maps of the two levels to agree. *)

Lemma frtPaintingsPrevEntry0 (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) {k} {dcB: DepsCohs 0 k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + 0)%nat)
  (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension 1 k F.(_frDepsA))
  (XB: DepsRestrExtension 1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall u, mkPainting XB (descTop HD cB u))
  (Q: (mkFrtRestrTypesAndFrames M HD 0 cB Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cB) val
        ((mkFrtRestrTypesAndFrames M HD 0 cB Hlen F).(FrtRestrFramesDef) Q))
  (t: (g X).(G0) M.+1):
  (mkFrtPaintingsOfRestr M HD 0 cB Hlen F XA XB TX PX val Q E).1.2 t
  = mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
      (tt; fun t0 => hunit_ext tt _)
      (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
         (tt; fun t1 => hunit_ext tt _)
         (fun ε t1 => descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t1)
         (fun ε t1 => Q 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
      E t.
Proof.
  now reflexivity.
Qed.

Lemma frtPaintingsPrevEntryS (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {k} {dcB: DepsCohs p.+1 k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p.+1)%nat)
  (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+2 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+2 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall u, mkPainting XB (descTop HD cB u))
  (Q: (mkFrtRestrTypesAndFrames M HD p.+1 cB Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cB) val
        ((mkFrtRestrTypesAndFrames M HD p.+1 cB Hlen F).(FrtRestrFramesDef) Q))
  (t: (g X).(G0) M.+1):
  (mkFrtPaintingsOfRestr M HD p.+1 cB Hlen F XA XB TX PX val Q E).1.2 t
  = mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
      ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
          (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
          (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
      (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
         ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
             (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
             (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
         (fun ε t1 => descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
         (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
      E t.
Proof. now reflexivity. Defined.

(** The ladder at a tower

    The staged data at a level of the round trip: the translation data of the
    translation tower on the [f (g X)] side, the presheaf-generated tower on the
    other, and the carried stage-indexed identification.  The chain is empty:
    a tower's own dependency data is the top of the ladder. *)

Definition descCellFrames {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0):
  mkPshFrameTypes (g X) M (mkFrames (νDepsCohsAt S0).(_deps)) :=
  mkCellFramesOf M
    (extChainDeps (cohsChainExt (DepsCohsChainNil (dcTop := νDepsCohsAt S0))))
    (descCells HD).

Definition descCellValues {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0):
  mkPshPaintingTypes (g X) M (descCellFrames HD)
    (mkPaintings (νDepsCohsAt S0).(_extraDeps)) :=
  mkCellValuesOf M (cohsChainExt (DepsCohsChainNil (dcTop := νDepsCohsAt S0)))
    (descCells HD) (fun u => (descCell HD u).2).

Definition towerFrtDeps {m} {XpA: (νGpdAt m.+1).(prefix)}
  {XpB0: (νGpdAt m).(prefix)} {S0: νGpdFrom m XpB0}
  (W: TrTower m.+1 XpA ((XpB0; this S0): (νGpdAt m.+1).(prefix)))
  (T: PshTower (g X) m XpA) (HD: Desc S0)
  (frt: mkFrtFrameTypes m W.(_twFrameEqvs) T.(_twFrames (g X))
    (descCellFrames HD))
  (frp: mkFrtPaintingTypes m frt W.(_twPaintingEqvs) T.(_twPaintings (g X))
    (descCellValues HD)):
  FrtDeps m HD (DepsCohsChainNil (dcTop := νDepsCohsAt S0)).
Proof.
  unshelve econstructor.
  - now exact ((towerTrDeps W).(_depsA)).
  - now exact leR_refl.
  - now exact (W.(_twFrameEqvs)).
  - now exact (W.(_twPaintingEqvs)).
  - now exact (T.(_twFrames (g X))).
  - now exact (T.(_twPaintings (g X))).
  - now exact frt.
  - now exact (W.(_twTrRestrs)).
  - now exact (T.(_twRestrs (g X))).
  - now exact frp.
Defined.

(** Level 0

    The frame identification is between elements of [gunit]; the painting
    identification is the tautological filler of a cell against the level's
    own filler equivalence, i.e. [fillerEquivOfWhole] read at its second
    component.  The two frame paths it is transported along are parallel
    paths in [unit], hence equal. *)

Definition frt0List:
  mkFrtFrameTypes 0 fgTowerStep0.(_twFrameEqvs)
    ((tower1 (g X)).(_twFrames (g X))) (descCellFrames DescZ)
  := (tt; fun t => hunit_ext tt _).

Definition frp0List:
  mkFrtPaintingTypes 0 frt0List fgTowerStep0.(_twPaintingEqvs)
    ((tower1 (g X)).(_twPaintings (g X))) (descCellValues DescZ).
Proof.
  refine (tt; _).
  intro u.
  pose proof (fillerEquivOfWhole (mkFrameEqv (towerTrDeps (trTower0 tt tt)))
     (descTotal DescZ) pshF0A frt0 (descCells DescZ u)
     ((descCell DescZ u).2)) as HW.
  assert (HP: frt0List.2 u = projT1_eq HW).
  { etransitivity; [now apply hunit_ext_uniq |
      symmetry; now apply hunit_ext_uniq]. }
  refine (_ • projT2_eq HW).
  rewrite HP.
  assert (Hu: rew [GDom] (eq_sym (descTotal DescZ)) in
      ((descCells DescZ u; (descCell DescZ u).2): νTotal X) = u).
  { now apply (rew_sym_cancel (P := GDom) (descTotal DescZ) u). }
  refine (f_equal (fun p => rew [fun a: mkFrame (towerTrDeps
      (trTower0 tt tt)).(_depsA) => {cell: gF0 X 0 &T a = pshF0A cell}]
      (projT1_eq HW) in p) _).
  now exact (f_equal (fun z: gF0 X 0 =>
    ((z; eq_refl): {cell: gF0 X 0 &T tt = pshF0A cell})) (eq_sym Hu)).
Defined.

(** The top entry of the list the ladder produces is the identification the
    filler contraction consumes; the cell it is read at is the descended pair,
    so the frame the identification lands on is that pair's own frame. *)

Definition frtInvOfFrames {m} {XpA: (νGpdAt m.+1).(prefix)}
  {XpB0: (νGpdAt m).(prefix)} {S0: νGpdFrom m XpB0}
  (W: TrTower m.+1 XpA ((XpB0; this S0): (νGpdAt m.+1).(prefix)))
  (T: PshTower (g X) m XpA) (HD: Desc S0)
  (frt: mkFrtFrameTypes m W.(_twFrameEqvs) T.(_twFrames (g X))
    (descCellFrames HD))
  (frp: mkFrtPaintingTypes m frt W.(_twPaintingEqvs) T.(_twPaintings (g X))
    (descCellValues HD))
  (H: FrtFramesType (towerFrtDeps W T HD frt frp) (descCells (DescS HD))):
  FrtInvTr W T (next S0) (DescS HD) :=
  frtOfCellRule (mkFrameEqv (towerTrDeps W)) (descTotal (DescS HD))
    (mkPshFrame (g X) (towerPshDeps (g X) T))
    (frtTop (towerFrtDeps W T HD frt frp) (descCells (DescS HD)) H).

Definition fgThisOfFrames {m} {XpA: (νGpdAt m.+1).(prefix)}
  {XpB0: (νGpdAt m).(prefix)} {S0: νGpdFrom m XpB0}
  (W: TrTower m.+1 XpA ((XpB0; this S0): (νGpdAt m.+1).(prefix)))
  (T: PshTower (g X) m XpA) (HD: Desc S0)
  (frt: mkFrtFrameTypes m W.(_twFrameEqvs) T.(_twFrames (g X))
    (descCellFrames HD))
  (frp: mkFrtPaintingTypes m frt W.(_twPaintingEqvs) T.(_twPaintings (g X))
    (descCellValues HD))
  (H: FrtFramesType (towerFrtDeps W T HD frt frp) (descCells (DescS HD))):
  towerFillerEqv W (mkPshFiller (g X) (towerPshDeps (g X) T))
    (this (next S0)) :=
  fgThisTr W T (next S0) (DescS HD) (frtInvOfFrames W T HD frt frp H).

(** The round trip level by level

    The [X]-side position at level [m] is the one [νGpdPack] reaches, with
    the descent witness stepped once per level; the [f (g X)]-side tower is
    the presheaf-generated one. *)

Fixpoint descAt (m: nat): Desc ((νGpdPack m X).2) :=
  match m with
  | 0 => DescZ
  | S m => DescS (descAt m)
  end.

Definition pshTw (m: nat): PshTower (g X) m (pshApprox (g X) m.+1) :=
  (pshChain (g X) m.+1).2.1.

Definition FgTower (m: nat): Type :=
  TrTower m.+1 (pshApprox (g X) m.+1) ((νGpdPack m.+1 X).1).

Definition FgFrt (m: nat) (W: FgTower m): Type :=
  mkFrtFrameTypes m W.(_twFrameEqvs) ((pshTw m).(_twFrames (g X)))
    (descCellFrames (descAt m)).

Definition FgFrp (m: nat) (W: FgTower m) (frt: FgFrt m W): Type :=
  mkFrtPaintingTypes m frt W.(_twPaintingEqvs)
    ((pshTw m).(_twPaintings (g X))) (descCellValues (descAt m)).

Definition fgDeps (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt):
  FrtDeps m (descAt m)
    (DepsCohsChainNil (dcTop := νDepsCohsAt ((νGpdPack m X).2))) :=
  towerFrtDeps W (pshTw m) (descAt m) frt frp.

(** The level indexing is transport-free: the frame identification the ladder
    produces at level [m] is, on the nose, the one the level above carries. *)

Definition fgWNext (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt)
  (H: FrtFramesType (fgDeps m W frt frp) (descCells (descAt m.+1))):
  FgTower m.+1 :=
  trTowerStep W (fgThisOfFrames W (pshTw m) (descAt m) frt frp H).

(** The restriction clauses at a level, and the frame identification one
    level up they determine.  The chain is empty and its length condition is
    the descent's own. *)

Definition fgBlock (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt): FrtRestrBlock (fgDeps m W frt frp) :=
  mkFrtRestrTypesAndFrames m (descAt m) m
    (DepsCohsChainNil (dcTop := νDepsCohsAt ((νGpdPack m X).2)))
    (descChainLen (descAt m)) (fgDeps m W frt frp).

Definition FgRestrData (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt): Type :=
  (fgBlock m W frt frp).(FrtRestrDataDef).

Definition fgFrtOf (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt) (Q: FgRestrData m W frt frp):
  FrtFramesType (fgDeps m W frt frp) (descCells (descAt m.+1)) :=
  (fgBlock m W frt frp).(FrtRestrFramesDef) Q.

(** The painting identification one level up: the ladder's painting list at a
    tower, read from the same restriction clauses.  Its top entry is
    [fillerEquivOfTopEntry] at the level's own filler equivalence. *)

Definition fgFrpOf (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt) (Q: FgRestrData m W frt frp):
  FgFrp m.+1 (fgWNext m W frt frp (fgFrtOf m W frt frp Q))
    (fgFrtOf m W frt frp Q).
Proof.
  unshelve refine (mkFrtPaintingsOfRestr m (descAt m) m
    (DepsCohsChainNil (dcTop := νDepsCohsAt ((νGpdPack m X).2)))
    (descChainLen (descAt m)) (fgDeps m W frt frp)
    (TopRestrDep (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m))))
    (TopRestrDep (this (next ((νGpdPack m X).2))))
    (TopTrDep (T := frTr (fgDeps m W frt frp))
      (fgThisOfFrames W (pshTw m) (descAt m) frt frp
        (fgFrtOf m W frt frp Q)))
    (TopPshDep (g X) m (P := frtPshDeps (fgDeps m W frt frp)))
    (fun u => (descCell (descAt m.+1) u).2) Q _).
  intro t.
  now exact (fillerEquivOfTopEntry (mkFrameEqv (towerTrDeps W))
    (descTotal (descAt m.+1))
    (mkPshFrame (g X) (towerPshDeps (g X) (pshTw m)))
    (frtTop (fgDeps m W frt frp) (descCells (descAt m.+1))
      (fgFrtOf m W frt frp Q)) t).
Defined.

(** The state of the round trip at a level

    The level carries the translation tower's *prefix* rather than its tower: the tower
    is what the prefix computes ([fgTowerAt]), so the tower of the level
    above is the tower of the prefix extended by the filler equivalence the
    level emits, definitionally.  Besides the prefix it carries the frame
    identification, the painting identification, and the restriction clauses
    of the frame identification — the rung-1 datum the step one level up
    consumes. *)

Definition FgPrefix (m: nat): Type :=
  (trAt m.+1 (pshApprox (g X) m.+1) ((νGpdPack m.+1 X).1)).(trPrefix).

Definition fgTowerAt (m: nat) (P: FgPrefix m): FgTower m :=
  (trAt m.+1 (pshApprox (g X) m.+1) ((νGpdPack m.+1 X).1)).(trData) P.

Definition frtTrBaseOf {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (cohsA: mkCohFrameTypes rpA) (cohsB: mkCohFrameTypes rpB):
  TrDepsCohsBase p.+1 k := {|
  _trDeps := frTr F;
  _tExtA := XA;
  _tExtB := XB;
  _trExt := TX;
  _tRpA := rpA;
  _tRpB := rpB;
  _trRestrPaintings := trRp;
  _tCohsA := cohsA;
  _tCohsB := cohsB;
|}.

Definition frtPshCohsOf {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA):
  PshDepsCohs (g X) M p.+1 k := {|
  _pshDeps := frtPshDeps F;
  _pExtraDeps := XA;
  _pshExtraDeps := PX;
  _pRestrPaintings := rpA;
  _pshRestrPaintings := pshRp;
  _pCohs := cohsA;
|}.
Class FrtDepsCohs (M: nat) {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) := {
  _fcF: FrtDeps M HD cB;
  _fcXA: DepsRestrExtension p.+1 k _fcF.(_frDepsA);
  _fcXB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB));
  _fcTX: TrDepsExtension (frTr _fcF) _fcXA _fcXB;
  _fcPX: PshDepsExtension (g X) M (frtPshDeps _fcF) _fcXA;
  _fcRpA: mkRestrPaintingTypes _fcXA;
  _fcRpB: mkRestrPaintingTypes _fcXB;
  _fcTrRp: mkTrRestrPaintingTypes (frTr _fcF) _fcTX _fcRpA _fcRpB;
  _fcPshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps _fcF) _fcPX _fcRpA;
  _fcCohsA: mkCohFrameTypes _fcRpA;
  _fcCohsB: mkCohFrameTypes _fcRpB;
  _fcTrCohs: mkTrCohTypes (frtTrBaseOf _fcF _fcXA _fcXB _fcTX _fcRpA _fcRpB
    _fcTrRp _fcCohsA _fcCohsB);
  _fcPshCohs: mkPshRestrCohData (g X)
    (frtPshCohsOf _fcF _fcXA _fcPX _fcRpA _fcPshRp _fcCohsA);
}.

Definition frtTrBase {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB):
  TrDepsCohsBase p.+1 k :=
  frtTrBaseOf FC.(_fcF) FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcRpA)
    FC.(_fcRpB) FC.(_fcTrRp) FC.(_fcCohsA) FC.(_fcCohsB).

Definition frtTrCohs {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB):
  TrDepsCohs p.+1 k :=
  {| _trBase := frtTrBase FC; _trCohs := FC.(_fcTrCohs) |}.

Definition frtPshCohs {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB):
  PshDepsCohs (g X) M p.+1 k :=
  frtPshCohsOf FC.(_fcF) FC.(_fcXA) FC.(_fcPX) FC.(_fcRpA) FC.(_fcPshRp)
    FC.(_fcCohsA).

Definition frtDcB {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB):
  DepsCohs p.+1 k := trDepsCohsB (frtTrBase FC).
#[local]
Instance proj1FrtDepsCohs {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p.+1 k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB):
  FrtDepsCohs M HD (DepsCohsChainCons cB).
Proof.
  unshelve econstructor.
  -
  now exact (proj1FrtDeps FC.(_fcF)).
  -
  now exact ((FC.(_fcF).(_frDepsA); FC.(_fcXA))%extradepsrestr).
  -
  now exact ((mkDepsRestr (depsCohs := dcB); FC.(_fcXB))%extradepsrestr).
  -
  now exact (AddTrDep (frTr FC.(_fcF)) FC.(_fcTX)).
  -
  now exact (AddPshDep (g X) M (frtPshDeps FC.(_fcF)) FC.(_fcPX)).
  -
  now exact (FC.(_fcRpA).1).
  -
  now exact (FC.(_fcRpB).1).
  -
  now exact (FC.(_fcTrRp).1).
  -
  now exact (FC.(_fcPshRp).1).
  -
  now exact (FC.(_fcCohsA).1).
  -
  now exact (FC.(_fcCohsB).1).
  -
  now exact (FC.(_fcTrCohs).1).
  -
  now exact (FC.(_fcPshCohs).1).
Defined.

Definition FrtFramesNextType {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC)): Type :=
  mkFrtFrameTypes M.+1 (mkFrameEqvs (frTr FC.(_fcF)))
    (mkPshFrames (g X) (frtPshDeps FC.(_fcF)))
    (mkCellFramesOf M.+1 (extChainDeps (cohsChainExt cB'))
      (descCells (DescS HD))).
Definition FrtPaintingsNextType {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (frames: FrtFramesNextType FC cB'): Type :=
  mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs FC.(_fcTX))
    (mkPshPaintings (g X) FC.(_fcPX))
    (mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
      (fun u => (descCell (DescS HD) u).2)).
Definition mkFrtDepsOf {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames):
  FrtDeps M.+1 (DescS HD) cB'.
Proof.
  unshelve econstructor.
  -
  now exact (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).
  -
  now exact (⇑ FC.(_fcF).(_frBound)).
  -
  now exact (mkFrameEqvs (frTr FC.(_fcF))).
  -
  now exact (mkPaintingEqvs FC.(_fcTX)).
  -
  now exact (mkPshFrames (g X) (frtPshDeps FC.(_fcF))).
  -
  now exact (mkPshPaintings (g X) FC.(_fcPX)).
  -
  now exact frames.
  -
  now exact (mkTrRestrFrames (frtTrCohs FC)).
  -
  now exact (mkPshRestrFrames (g X) (frtPshCohs FC) FC.(_fcPshCohs)).
  -
  now exact paintings.
Defined.

Definition pshRp (m: nat): PshTowerRestrPaintings (g X) (pshTw m) :=
  (pshChain (g X) m.+1).2.2.1.
Definition pshRc (m: nat): PshTowerRestrCohs (g X) (pshTw m) (pshRp m) :=
  (pshChain (g X) m.+1).2.2.2.1.

(** The staged data at a level, over the level's four components rather than
    over the level itself: the level record carries a field whose type
    mentions this construction, so it has to be available before the record
    is declared. *)

Definition towerFrtDepsCohsOf (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt) (Q: FgRestrData m W frt frp):
  FrtDepsCohs m (descAt m)
    (DepsCohsChainNil (dcTop := νDepsCohsAt ((νGpdPack m X).2))).
Proof.
  unshelve econstructor.
  -
  now exact (fgDeps m W frt frp).
  -
  now exact (TopRestrDep (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m)))).
  -
  now exact (TopRestrDep (this (next ((νGpdPack m X).2)))).
  -
  now exact (TopTrDep (T := frTr (fgDeps m W frt frp))
        (fgThisOfFrames W (pshTw m) (descAt m) frt frp
           (fgFrtOf m W frt frp Q))).
  -
  now exact (TopPshDep (g X) m (P := frtPshDeps (fgDeps m W frt frp))).
  -
  now exact ((νDataAt (pshApprox (g X) m.+1)).(restrPaintings)
        (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m)))).
  -
  now exact ((νDataAt _).(restrPaintings) (this (next ((νGpdPack m X).2)))).
  -
  now exact (W.(_twTrRestrPaintings) _ _
        (fgThisOfFrames W (pshTw m) (descAt m) frt frp
           (fgFrtOf m W frt frp Q))).
  -
  now exact (pshRp m).
  -
  now exact ((νDataAt (pshApprox (g X) m.+1)).(cohFrames)
        (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m)))).
  -
  now exact ((νDataAt _).(cohFrames) (this (next ((νGpdPack m X).2)))).
  -
  now exact (W.(_twTrCohs) _ _
        (fgThisOfFrames W (pshTw m) (descAt m) frt frp
           (fgFrtOf m W frt frp Q))).
  -
  now exact (pshRc m).
Defined.

Definition frtTopNext {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC)):
  (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)) :=
  fun t => getFrame (extChainDeps (cohsChainExt cB')) (descCells (DescS HD) t).

(** The restriction clause at the bottom stage, one level up

    At the bottom stage the frames the clause equates are the ones the
    construction generates at dimension [0], which are [hunit]; the clause is
    therefore free there, at every level.  This is the datum the bottom of
    the layer-clause recursion asks for. *)

Lemma frtRestrData0Next (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {k} {dcB: DepsCohs 0 k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB}
  (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + 1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) 0 (DepsCohsChainCons cB')
     (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') 0))
     (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))).(FrtRestrDataDef).
Proof.
  intros q Hq Hqp ε t.
  etransitivity; [now apply hunit_ext_uniq |
    symmetry; now apply hunit_ext_uniq].
Defined.

Definition FrtPairLawAt {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB))): Type :=
  forall (ε: arity) (t: (g X).(G0) M.+1),
    (((mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD)).2
        ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t);
      (mkCellValuesOf M (cohsChainExt cB) (descCells HD)
        (fun u => (descCell HD u).2)).2
        ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t))
     : {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D})
    = ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ε (top t).1;
       nth (top t).2 ε).
Definition FrtRestr0At {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType F top) (Hpair: FrtPairLawAt F top): Type :=
  forall (ε: arity) (t: (g X).(G0) M.+1),
    (F.(_frFrames).2 ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t)
     • f_equal (fun x => F.(_frFrameEqvs).2 x) (projT1_eq (Hpair ε t)))
    • F.(_frTrRestrs).2 0 leR_O ε (top t).1
    = F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ε t
      • f_equal (F.(_frDepsA).(_restrFrames).2 0 leR_O ε) (prev.2 t).
Definition FrtSplitStep {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (frames: FrtFramesType F top): Type :=
  { Hpair: FrtPairLawAt F top &T
    { HR: FrtRestr0At F top frames.1 Hpair &T
      forall t, frames.2 t
        = eq_existT_curried (frames.1.2 t)
            (mkFrtLayerOfRestr F top frames.1 Hpair HR t) } }.
Fixpoint FrtSplitDataAt (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (F: FrtDeps M HD cB)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (frames: FrtFramesType F top), Type :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (F: FrtDeps M HD cB)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (frames: FrtFramesType F top), Type with
  | 0 => fun k dcB cB F top frames => FrtSplitStep F top frames
  | S p => fun k dcB cB F top frames =>
    { _: FrtSplitDataAt M HD p (DepsCohsChainCons cB) (proj1FrtDeps F)
           (fun t => (top t).1) frames.1 &T FrtSplitStep F top frames }
  end.
Fixpoint frtSplitOfQ (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef)),
  FrtSplitDataAt M HD p cB F (descTop HD cB)
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q) :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef)),
  FrtSplitDataAt M HD p cB F (descTop HD cB)
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q) with
  | 0 => fun k dcB cB Hlen F Q =>
    ((fun ε t => descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t);
     ((fun ε t => Q 0 leR_O (⇓ F.(_frBound)) ε t);
      (fun t => eq_refl)))
  | S p => fun k dcB cB Hlen F Q =>
    (frtSplitOfQ M HD p (DepsCohsChainCons cB)
       (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F) Q.1;
     ((fun ε t => descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t);
      ((fun ε t => Q.2 0 leR_O (⇓ F.(_frBound)) ε t);
       (fun t => eq_refl))))
  end.

(** The rung-1 clause at layers

    The restriction clause of the frame identification at a stage is an
    equation between two composites of paths of frames.  One level up a frame
    is a pair of a frame one stage down and a layer, so the clause splits into
    the clause one stage down — which the stage recursion supplies — and an
    equation between the two composites of *layer* paths the same five edges
    determine.  That second half is the datum below: the ladder's rung-1
    clause one dimension up.

    Its five edges are the layer of the stage step at the ε-face of the cell,
    the descent's own layer law ([descQcells] read at its painting
    component), the translation's restriction layer, the presheaf's
    restriction layer, and the layer of the stage step one stage down.  The
    last one is stated over an arbitrary frame identification one stage down
    and an arbitrary restriction clause for it, so that the datum mentions
    none of the data the stage recursion produces. *)

Definition frtPairLawPrev {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames):
  FrtPairLawAt (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
    (descTop (DescS HD) (DepsCohsChainCons cB')) :=
  fun ε t => descCellPairRestrAt (DescS HD) (DepsCohsChainCons cB') p
    (⇓ (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frBound))
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p)) ε t.

Definition FrtRestrLayerStep {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair): Type :=
  forall q (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (ε: arity)
    (t: (g X).(G0) M.+2)
    (prev: FrtFramesPrevType
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')))
    (HRPrev: FrtRestr0At
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')) prev
             (frtPairLawPrev FC cB' Hlen' frames paintings)),
  DPathEq
    (mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR
       ((g X).(GFace) M.+1 (q + p.+1) Hqp ε t)
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] sigT_map_eq
         (P := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 x0)
         (fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
            (frTr FC.(_fcF)).(_trRestrs) a l)
         (projT2_eq (descQcells cB' Hlen' q Hq Hqp ε t))
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] mkTrRestrLayer (frtTrCohs FC).(_trBase)
         (mkTrRestrFrames (proj1TrDepsCohs (frtTrCohs FC)))
         (frtTrCohs FC).(_trCohs).2 q Hq ε (descTop (DescS HD) cB' t).1)
    (mkPshRestrLayerMerged (g X) (frtPshCohs FC)
       (mkPshRestrFrames (g X)
          (proj1PshDepsCohs (g X)
             (frtPshCohsOf FC.(_fcF) FC.(_fcXA) FC.(_fcPX) FC.(_fcRpA)
                FC.(_fcPshRp) FC.(_fcCohsA)))
          FC.(_fcPshCohs).1)
       FC.(_fcPshCohs).2 q Hq Hqp ε t
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] sigT_map_eq
         (P := fun x0 => (mkLayer
            (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
            (painting := (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkRestrFrames (depsCohs :=
            proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2 q.+1 (⇑ Hq) ε x0)
         (fun a l => mkRestrLayer
            (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2
            (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq ε a l)
         (mkFrtLayerOfRestr
            (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
            (descTop (DescS HD) (DepsCohsChainCons cB')) prev
            (frtPairLawPrev FC cB' Hlen' frames paintings) HRPrev t)).

Lemma eq_existT_curried_eta {A: Type} {P: A -> Type}
  {u v: {a: A &T P a}} (e: u = v):
  (= projT1_eq e; projT2_eq e) = e.
Proof.
  now exact (totalPathReencode e).
Defined.
Lemma mkTrRestrFramesStepPath {p k} (TC: TrDepsCohs p.+1 k) q (Hq: q <= k)
  (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB
        (proj1TrDepsCohsBase TC.(_trBase))))):
  (mkTrRestrFrames TC).2 q Hq ε d
  = (= (mkTrRestrFrames (proj1TrDepsCohs TC)).2 q.+1 (⇑ Hq) ε d.1;
     mkTrRestrLayer TC.(_trBase) (mkTrRestrFrames (proj1TrDepsCohs TC))
       TC.(_trCohs).2 q Hq ε d).
Proof.
  now reflexivity.
Qed.
Lemma frtBlockStepPath (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p k: nat) (dcB: DepsCohs p.+1 k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p.+1)%nat)
  (F: FrtDeps M HD cB)
  (Q: (mkFrtRestrTypesAndFrames M HD p.+1 cB Hlen F).(FrtRestrDataDef))
  (t: (g X).(G0) M.+1):
  ((mkFrtRestrTypesAndFrames M HD p.+1 cB Hlen F).(FrtRestrFramesDef) Q).2 t
  = (= ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
           (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
           (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1).2 t;
     mkFrtLayerOfRestr F (descTop HD cB)
       ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
           (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
           (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
       (fun ε t1 => descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
       (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t).
Proof.
  now reflexivity.
Qed.
Lemma f_equal_mkFrameEqv {p k} (T: TrDepsRestr p.+1 k)
  {d d': mkFrame T.(_depsB)} (K: d.1 = d'.1)
  (W: rew [fun x => (mkLayer T.(_depsB).(_restrFrames).2
        (painting := T.(_depsB).(_paintings).2) x).(GDom)] K in d.2 = d'.2):
  f_equal (fun x => (mkFrameEqvs T).2 x) (= K; W)
  = (= f_equal (fun x => (mkFrameEqvs (proj1TrDepsRestr T)).2 x) K;
     sigT_map_eq
       (P := fun x => (mkLayer T.(_depsB).(_restrFrames).2
          (painting := T.(_depsB).(_paintings).2) x).(GDom))
       (Q := fun x => (mkLayer T.(_depsA).(_restrFrames).2
          (painting := T.(_depsA).(_paintings).2) x).(GDom))
       (f := fun x => (mkFrameEqvs (proj1TrDepsRestr T)).2 x)
       (fun a l => mkTrLayerEquiv T.(_paintingEqvs) T.(_trRestrs) a l) W).
Proof.
  now exact (f_equal_eq_existT_curried
      (P := fun x => (mkLayer T.(_depsB).(_restrFrames).2
         (painting := T.(_depsB).(_paintings).2) x).(GDom))
      (Q := fun x => (mkLayer T.(_depsA).(_restrFrames).2
         (painting := T.(_depsA).(_paintings).2) x).(GDom))
      (fun x => (mkFrameEqvs (proj1TrDepsRestr T)).2 x)
      (fun a l => mkTrLayerEquiv T.(_paintingEqvs) T.(_trRestrs) a l) K W).
Qed.
Lemma f_equal_mkRestrFrame {p k} (dc: DepsCohs p.+1 k) q (Hq: q <= k)
  (ε: arity)
  {d d': mkFrame (mkDepsRestr (depsCohs := dc)).(1)}
  (K: d.1 = d'.1)
  (W: rew [fun x => (mkLayer (mkDepsRestr (depsCohs := dc)).(1).(_restrFrames).2
        (painting := (mkDepsRestr (depsCohs := dc)).(1).(_paintings).2)
        x).(GDom)] K in d.2 = d'.2):
  f_equal ((mkRestrFrames (depsCohs := dc)).2 q Hq ε) (= K; W)
  = (= f_equal ((mkRestrFrames (depsCohs := proj1DepsCohs dc)).2 q.+1 (⇑ Hq) ε)
        K;
     sigT_map_eq
       (P := fun x => (mkLayer (mkDepsRestr (depsCohs := dc)).(1).(_restrFrames).2
          (painting := (mkDepsRestr (depsCohs := dc)).(1).(_paintings).2)
          x).(GDom))
       (Q := fun x => (mkLayer dc.(_deps).(_restrFrames).2
          (painting := dc.(_deps).(_paintings).2) x).(GDom))
       (f := fun x => (mkRestrFrames (depsCohs := proj1DepsCohs dc)).2
          q.+1 (⇑ Hq) ε x)
       (fun a l => mkRestrLayer dc.(_restrPaintings).2 dc.(_cohs).2 q Hq ε a l)
       W).
Proof.
  now exact (f_equal_eq_existT_curried
      (P := fun x => (mkLayer (mkDepsRestr (depsCohs := dc)).(1).(_restrFrames).2
         (painting := (mkDepsRestr (depsCohs := dc)).(1).(_paintings).2)
         x).(GDom))
      (Q := fun x => (mkLayer dc.(_deps).(_restrFrames).2
         (painting := dc.(_deps).(_paintings).2) x).(GDom))
      (fun x => (mkRestrFrames (depsCohs := proj1DepsCohs dc)).2 q.+1 (⇑ Hq) ε x)
      (fun a l => mkRestrLayer dc.(_restrPaintings).2 dc.(_cohs).2 q Hq ε a l)
      K W).
Qed.

Lemma eq_ind_r_projT1 {A: Type} {Pf: A -> Type} {u v: {a: A &T Pf a}}
  (H: u = v):
  eq_ind_r (fun g: {a: A &T Pf a} => g.1 = v.1) eq_refl H
  = f_equal (fun x: {a: A &T Pf a} => x.1) H.
Proof.
  now destruct H.
Qed.
Lemma getFrameGetPaintingCons {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p.+1 k} {ext: DepsRestrExtension p.+1 k deps}
  (c: ExtChain extTop ext) (d: mkFrame deps.(1))
  (cp: mkPainting (deps; ext)%extradepsrestr d):
  getFrameGetPainting (ExtChainCons c) d cp
  = f_equal (fun x: mkFrame deps => x.1)
      (getFrameGetPainting c (d; cp.1) cp.2).
Proof.
  unfold getFrameGetPainting; cbn.
  now exact (eq_ind_r_projT1 (getFrameGetPainting c (d; cp.1) cp.2)).
Qed.
Lemma chainPaintingGetPaintingCons {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p.+1 k} {ext: DepsRestrExtension p.+1 k deps}
  (c: ExtChain extTop ext) (d: mkFrame deps.(1))
  (cp: mkPainting (deps; ext)%extradepsrestr d):
  chainPaintingGetPainting (ExtChainCons c) d cp
  = f_equal (fun w: {D: mkFrame deps &T mkPainting ext D} =>
      ((w.1.1; (w.1.2; w.2)):
        {D: mkFrame deps.(1) &T mkPainting (deps; ext)%extradepsrestr D}))
      (chainPaintingGetPainting c (d; cp.1) cp.2).
Proof.
  now reflexivity.
Qed.
Lemma f_equal_comp2 {A B C: Type} (f: A -> B) (g: B -> C) {a b: A} (e: a = b):
  f_equal g (f_equal f e) = f_equal (fun x => g (f x)) e.
Proof.
  now exact (f_equal_compose f g e).
Qed.

Lemma descQcellsCons {n} {XpB0: (νGpdAt n).(prefix)}
  {S0: νGpdFrom n XpB0} (HD: Desc S0) {P k} {dcB: DepsCohs P.+1 k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + P.+1)%nat)
  (q: nat) (Hq: q <= k) (Hqp: q + P.+1 <= n)
  (Hq': q.+1 <= k.+1) (Hqp': q.+1 + P <= n)
  (ε: arity) (t: (g X).(G0) n.+1):
  projT1_eq (descQcells cB Hlen q Hq Hqp ε t)
  = projT1_eq (f_equal (fun u => getFrame (extChainDeps (cohsChainExt cB))
      (descCells HD u)) (pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q P)) ε t))
    • descQcells (DepsCohsChainCons cB)
        (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) P)) q.+1 Hq' Hqp' ε t.
Proof.
  now exact (descQcellsPairedCons HD cB Hlen q Hq Hqp ε t).
Defined.

Definition descQcellsCons_dep := @descQcellsPairedCons_dep.

Lemma eq_trans_naturality {A B: Type} (f g: A -> B)
  (H: forall u, f u = g u) {u1 u2: A} (e: u1 = u2):
  H u1 • f_equal g e = f_equal f e • H u2.
Proof.
  now exact (eq_sym (eq_trans_natural f g H e)).
Qed.
(** The rung-1 clause of the frame identification at a stage, from the
    clause one stage down

    The clause is an equation between two composites of paths of frames one
    level up, so it splits into a base half and a fibre half.  The base is
    the descent's own restriction law read through [descQcellsCons] composed
    with the clause one stage down; the fibre is the layer clause
    [FrtRestrLayerStep] of the stage. *)

Section RestrictionStepSelection.
Context {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair).

Definition frtRestrPrevBlock :=
  mkFrtRestrTypesAndFrames M.+1 (DescS HD) p (DepsCohsChainCons cB')
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p))
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).

Definition FrtRestrPrevData: Type := frtRestrPrevBlock.(FrtRestrDataDef).

Definition frtRestrPrevFrames (Qprev: FrtRestrPrevData):
  FrtFramesPrevType (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
    (descTop (DescS HD) (DepsCohsChainCons cB')) :=
  (frtRestrPrevBlock.(FrtRestrFramesDef) Qprev).1.

Definition frtRestrPrevClause (Qprev: FrtRestrPrevData):
  mkFrtRestrTypeStep
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frFrames)
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frPshRestrs)
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frTrRestrs)
    (fun t => (descTop (DescS HD) (DepsCohsChainCons cB') t).1)
    (fun t => (frtRestrPrevFrames Qprev).2 t)
    (descQcells (DepsCohsChainCons cB')
      (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p))).
Proof.
  unfold FrtRestrPrevData, frtRestrPrevFrames, frtRestrPrevBlock in *.
  destruct p; [now exact Qprev | now exact Qprev.2].
Defined.

Definition frtRestrPrevZero (Qprev: FrtRestrPrevData):
  FrtRestr0At (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
    (descTop (DescS HD) (DepsCohsChainCons cB')) (frtRestrPrevFrames Qprev)
    (frtPairLawPrev FC cB' Hlen' frames paintings) :=
  fun epsilon t => frtRestrPrevClause Qprev 0 leR_O
    (⇓ (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frBound)) epsilon t.

Definition frtRestrLayerLeft
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (ε: arity)
    (t: (g X).(G0) M.+2)
    (prev: FrtFramesPrevType
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')))
    (HRPrev: FrtRestr0At
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')) prev
             (frtPairLawPrev FC cB' Hlen' frames paintings)) :=
  (mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR
       ((g X).(GFace) M.+1 (q + p.+1) Hqp ε t)
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] sigT_map_eq
         (P := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 x0)
         (fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
            (frTr FC.(_fcF)).(_trRestrs) a l)
         (projT2_eq (descQcells cB' Hlen' q Hq Hqp ε t))
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] mkTrRestrLayer (frtTrCohs FC).(_trBase)
         (mkTrRestrFrames (proj1TrDepsCohs (frtTrCohs FC)))
         (frtTrCohs FC).(_trCohs).2 q Hq ε (descTop (DescS HD) cB' t).1).

Definition frtRestrLayerRight
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (ε: arity)
    (t: (g X).(G0) M.+2)
    (prev: FrtFramesPrevType
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')))
    (HRPrev: FrtRestr0At
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')) prev
             (frtPairLawPrev FC cB' Hlen' frames paintings)) :=
  (mkPshRestrLayerMerged (g X) (frtPshCohs FC)
       (mkPshRestrFrames (g X)
          (proj1PshDepsCohs (g X)
             (frtPshCohsOf FC.(_fcF) FC.(_fcXA) FC.(_fcPX) FC.(_fcRpA)
                FC.(_fcPshRp) FC.(_fcCohsA)))
          FC.(_fcPshCohs).1)
       FC.(_fcPshCohs).2 q Hq Hqp ε t
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] sigT_map_eq
         (P := fun x0 => (mkLayer
            (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
            (painting := (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkRestrFrames (depsCohs :=
            proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2 q.+1 (⇑ Hq) ε x0)
         (fun a l => mkRestrLayer
            (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2
            (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq ε a l)
         (mkFrtLayerOfRestr
            (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
            (descTop (DescS HD) (DepsCohsChainCons cB')) prev
            (frtPairLawPrev FC cB' Hlen' frames paintings) HRPrev t)).

Definition frtRestrBaseCell (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2):
  DPathBaseCell
    (frtRestrLayerLeft q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrLayerRight q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev)).
Proof.
  unfold DPathBaseCell.
  unshelve refine (restriction_step_cell
    (fun u => (mkPshFrames (g X) (frtPshDeps FC.(_fcF))).1.2 u)
    (fun u => (getFrame (extChainDeps (cohsChainExt cB'))
      (descCells (DescS HD) u)).1)
    (fun z => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 z)
    frames.1.2
    (pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
      (Hq := Hqp) (Hq' := leR_add_shift Hqp) epsilon t)
    (projT1_eq (descQcells cB' Hlen' q Hq Hqp epsilon t))
    (descQcells (DepsCohsChainCons cB')
      (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p))
      q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t)
    _ _ _ _
    (frtRestrPrevClause Qprev q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t)).
  refine (descQcellsCons (DescS HD) cB' Hlen' q Hq Hqp (⇑ Hq)
    (leR_add_shift Hqp) epsilon t • _).
  unfold projT1_eq.
  now exact (f_equal (fun z => z • _)
    (f_equal_compose
      (fun u => getFrame (extChainDeps (cohsChainExt cB')) (descCells (DescS HD) u))
      (fun z: mkFrame (frtDcB FC).(_deps) => z.1)
      (pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
        (Hq := Hqp) (Hq' := leR_add_shift Hqp) epsilon t))).
Defined.

Definition FrtRestrLayerStepAtChosen (Qprev: FrtRestrPrevData): Type :=
  forall q (Hq: q <= k)
    (Hqp: q + p.+1 <= M.+1) (epsilon: arity) (t: (g X).(G0) M.+2),
  DPathCellOver
    (frtRestrLayerLeft q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrLayerRight q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t).

Definition FrtRestrLayerStepChosen: Type :=
  forall Qprev: FrtRestrPrevData, FrtRestrLayerStepAtChosen Qprev.

(** The previous generated frame exposes the same layer used by its clause. *)
Definition frtRestrPrevPair (Qprev: FrtRestrPrevData) (t: (g X).(G0) M.+2):
  (frtRestrPrevBlock.(FrtRestrFramesDef) Qprev).2 t =
  DPathTotal
    (P := fun x => (mkLayer
      (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frDepsA).(_restrFrames).2
      (painting := (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings)).(_frDepsA).(_paintings).2)
      x).(GDom))
    (mkFrtLayerOfRestr
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
    (descTop (DescS HD) (DepsCohsChainCons cB')) (frtRestrPrevFrames Qprev)
    (frtPairLawPrev FC cB' Hlen' frames paintings) (frtRestrPrevZero Qprev) t).
Proof.
  unfold DPathTotal, FrtRestrPrevData, frtRestrPrevZero, frtRestrPrevClause,
    frtRestrPrevFrames, frtRestrPrevBlock in *.
  destruct p; now reflexivity.
Defined.

Context (Hsplit: forall t, frames.2 t =
  (=frames.1.2 t;
    mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR t)).

Definition frtRestrFrameLeft
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2) :=
  (frames.2 ((g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t)
    • f_equal (mkFrameEqv (frTr FC.(_fcF)))
      (descQcells cB' Hlen' q Hq Hqp epsilon t))
    • (mkTrRestrFrames (frtTrCohs FC)).2 q Hq epsilon
        (descTop (DescS HD) cB' t).1.

Definition frtRestrFrameRight (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2) :=
  (mkPshRestrFrames (g X) (frtPshCohs FC) FC.(_fcPshCohs)).2 q Hq Hqp epsilon t
    • f_equal ((mkRestrFrames (depsCohs := trDepsCohsA (frtTrBase FC))).2
        q Hq epsilon) ((frtRestrPrevBlock.(FrtRestrFramesDef) Qprev).2 t).

Definition frtRestrLeftNorm (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2):
  frtRestrFrameLeft q Hq Hqp epsilon t =
  DPathTotal
    (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom))
    (frtRestrLayerLeft q Hq Hqp epsilon t
    (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev)) :=
  sigT_path_paste (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom))
    (sigT_path_paste (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom)) (Hsplit ((g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t))
      (sigT_total_map_cell
        (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
          (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x).(GDom))
        (Q := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
          (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom))
        (fun x => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 x)
        (fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
          (frTr FC.(_fcF)).(_trRestrs) a l)
        (descQcells cB' Hlen' q Hq Hqp epsilon t)))
    eq_refl.

Definition frtRestrRightNorm (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2):
  frtRestrFrameRight Qprev q Hq Hqp epsilon t =
  DPathTotal
    (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom))
    (frtRestrLayerRight q Hq Hqp epsilon t
    (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev)) :=
  sigT_path_paste (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom)) eq_refl
    (f_equal (fun e => f_equal
        ((mkRestrFrames (depsCohs := trDepsCohsA (frtTrBase FC))).2 q Hq epsilon) e)
        (frtRestrPrevPair Qprev t)
      • f_equal_eq_existT_curried
        (P := fun x => (mkLayer
          (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
          (painting := (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).(1).(_paintings).2)
          x).(GDom))
        (Q := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
          (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom))
        ((mkRestrFrames (depsCohs := proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2
          q.+1 (⇑ Hq) epsilon)
        (fun a l => mkRestrLayer (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2
          (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq epsilon a l)
        ((frtRestrPrevFrames Qprev).2 t)
        (mkFrtLayerOfRestr (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
          (descTop (DescS HD) (DepsCohsChainCons cB')) (frtRestrPrevFrames Qprev)
          (frtPairLawPrev FC cB' Hlen' frames paintings) (frtRestrPrevZero Qprev) t)).

Definition frtRestrCell (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2)
  (HP: DPathCellOver
    (frtRestrLayerLeft q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrLayerRight q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t)):
  frtRestrFrameLeft q Hq Hqp epsilon t = frtRestrFrameRight Qprev q Hq Hqp epsilon t :=
  sigT_route_cell (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom)) (frtRestrLeftNorm Qprev q Hq Hqp epsilon t)
    (frtRestrRightNorm Qprev q Hq Hqp epsilon t)
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t) HP.

(** The next rung refers to the exact selected restriction cell and both
    route encodings. Its canonical pair witness uses those same transports. *)
Lemma frtRestrCell_dep (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2)
  (HP: DPathCellOver
    (frtRestrLayerLeft q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrLayerRight q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t))
  (R: mkFrame (frTr FC.(_fcF)).(_depsA) -> Type) {a b}
  (vl: rew [R] frtRestrFrameLeft q Hq Hqp epsilon t in a = b)
  (vr: rew [R] frtRestrFrameRight Qprev q Hq Hqp epsilon t in a = b)
  (HH: rew [fun e => rew [R] e in a = b]
    frtRestrCell Qprev q Hq Hqp epsilon t HP in vl = vr):
  sigT_route_lift_result
    (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom)) R
    (frtRestrLeftNorm Qprev q Hq Hqp epsilon t)
    (frtRestrRightNorm Qprev q Hq Hqp epsilon t)
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t) HP vl vr.
Proof.
  now exact (sigT_route_cell_dep
    (P := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
      (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom)) R
    (frtRestrLeftNorm Qprev q Hq Hqp epsilon t)
    (frtRestrRightNorm Qprev q Hq Hqp epsilon t)
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t) HP vl vr HH).
Defined.

(** The painting certificate is indexed by the emitted restriction cell,
    rather than by an arbitrary parallel frame cell. *)
Definition FrtRestrPaintingCellSelected (Qprev: FrtRestrPrevData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (epsilon: arity)
  (t: (g X).(G0) M.+2)
  (HP: DPathCellOver
    (frtRestrLayerLeft q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrLayerRight q Hq Hqp epsilon t
      (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev))
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t))
  {a b}
  (vl: rew [fun d => GDom (mkPainting FC.(_fcXA) d)]
    frtRestrFrameLeft q Hq Hqp epsilon t in a = b)
  (vr: rew [fun d => GDom (mkPainting FC.(_fcXA) d)]
    frtRestrFrameRight Qprev q Hq Hqp epsilon t in a = b): Type :=
  DPathCellOver (P := fun d => GDom (mkPainting FC.(_fcXA) d)) vl vr
    (frtRestrCell Qprev q Hq Hqp epsilon t HP).

Definition frtRestrLayerStepSelect
  (HP: FrtRestrLayerStep FC cB' Hlen' frames paintings Hpair HR)
  (Qprev: FrtRestrPrevData): FrtRestrLayerStepAtChosen Qprev :=
  fun q Hq Hqp epsilon t => HP q Hq Hqp epsilon t
    (frtRestrPrevFrames Qprev) (frtRestrPrevZero Qprev)
    (frtRestrBaseCell Qprev q Hq Hqp epsilon t).

End RestrictionStepSelection.

Lemma mkFrtRestrStepChosen (M: nat) {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) (p k: nat) (dcB: DepsCohs p.+1 k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+2)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD p.+1 cB FC.(_fcF) (frtTopNext FC cB') frames)
  (Qprev: (mkFrtRestrTypesAndFrames M.+1 (DescS HD) p.+1
    (DepsCohsChainCons cB')
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
    (mkFrtDepsOf (proj1FrtDepsCohs FC) (DepsCohsChainCons cB')
       frames.1 paintings.1)).(FrtRestrDataDef))
  (HP: FrtRestrLayerStepAtChosen FC cB' Hlen' frames paintings SD.2.1 SD.2.2.1 Qprev):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) p.+2 cB' Hlen'
     (mkFrtDepsOf FC cB' frames paintings)).(FrtRestrDataDef).
Proof.
  now exact (Qprev; fun q Hq Hqp ε t =>
    frtRestrCell FC cB' Hlen' frames paintings SD.2.1 SD.2.2.1 SD.2.2.2 Qprev q Hq Hqp ε t
      (HP q Hq Hqp ε t)).
Defined.

Lemma frtBlockStepPath0 (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (k: nat) (dcB: DepsCohs 0 k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + 0)%nat)
  (F: FrtDeps M HD cB)
  (Q: (mkFrtRestrTypesAndFrames M HD 0 cB Hlen F).(FrtRestrDataDef))
  (t: (g X).(G0) M.+1):
  ((mkFrtRestrTypesAndFrames M HD 0 cB Hlen F).(FrtRestrFramesDef) Q).2 t
  = (= (((tt; fun t0 => hunit_ext tt _)
         : FrtFramesPrevType F (descTop HD cB)).2 t);
     mkFrtLayerOfRestr F (descTop HD cB)
       ((tt; fun t0 => hunit_ext tt _): FrtFramesPrevType F (descTop HD cB))
       (fun ε t1 => descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t1)
       (fun ε t1 => Q 0 leR_O (⇓ F.(_frBound)) ε t1) t).
Proof.
  now reflexivity.
Qed.
Lemma mkFrtRestrStep0Chosen (M: nat) {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) (k: nat) (dcB: DepsCohs 0 k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + 1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD 0 cB FC.(_fcF) (frtTopNext FC cB') frames)
  (Qprev: (mkFrtRestrTypesAndFrames M.+1 (DescS HD) 0
    (DepsCohsChainCons cB')
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') 0))
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))).(FrtRestrDataDef))
  (HP: FrtRestrLayerStepAtChosen FC cB' Hlen' frames paintings SD.1 SD.2.1 Qprev):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) 1 cB' Hlen'
     (mkFrtDepsOf FC cB' frames paintings)).(FrtRestrDataDef).
Proof.
  now exact (Qprev; fun q Hq Hqp ε t =>
    frtRestrCell FC cB' Hlen' frames paintings SD.1 SD.2.1 SD.2.2 Qprev q Hq Hqp ε t
      (HP q Hq Hqp ε t)).
Defined.


Lemma mkFrtRestrStep (M: nat) {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) (p k: nat) (dcB: DepsCohs p.+1 k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+2)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD p.+1 cB FC.(_fcF) (frtTopNext FC cB') frames)
  (HP: FrtRestrLayerStep FC cB' Hlen' frames paintings SD.2.1 SD.2.2.1)
  (Qprev: (mkFrtRestrTypesAndFrames M.+1 (DescS HD) p.+1
    (DepsCohsChainCons cB')
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
    (mkFrtDepsOf (proj1FrtDepsCohs FC) (DepsCohsChainCons cB')
       frames.1 paintings.1)).(FrtRestrDataDef)):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) p.+2 cB' Hlen'
     (mkFrtDepsOf FC cB' frames paintings)).(FrtRestrDataDef).
Proof.
  now exact (mkFrtRestrStepChosen M HD p k dcB cB FC cB' Hlen' frames paintings SD Qprev
    (frtRestrLayerStepSelect FC cB' Hlen' frames paintings SD.2.1 SD.2.2.1 HP Qprev)).
Defined.

Lemma mkFrtRestrStep0 (M: nat) {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) (k: nat) (dcB: DepsCohs 0 k)
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + 1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD 0 cB FC.(_fcF) (frtTopNext FC cB') frames)
  (HP: FrtRestrLayerStep FC cB' Hlen' frames paintings SD.1 SD.2.1)
  (Qprev: (mkFrtRestrTypesAndFrames M.+1 (DescS HD) 0
    (DepsCohsChainCons cB')
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') 0))
    (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))).(FrtRestrDataDef)):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) 1 cB' Hlen'
     (mkFrtDepsOf FC cB' frames paintings)).(FrtRestrDataDef).
Proof.
  now exact (mkFrtRestrStep0Chosen M HD k dcB cB FC cB' Hlen' frames paintings SD Qprev
    (frtRestrLayerStepSelect FC cB' Hlen' frames paintings SD.1 SD.2.1 HP Qprev)).
Defined.

(** The layer data of a stage-indexed identification

    What the clause step consumes at every stage, beside the split datum: the
    rung-1 clause at layers there, universally quantified over the pair law
    and the dimension-[0] clause it is stated with, and at the bottom the
    clause of the bottom stage.  The recursion is the one the identification
    itself steps by, so a datum at a stage is a datum for every stage below
    it. *)

Definition frtSplitHead {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (F: FrtDeps M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (frames: FrtFramesType F top)
  (SD: FrtSplitDataAt M HD p cB F top frames): FrtSplitStep F top frames.
Proof.
  destruct p; [now exact SD | now exact SD.2].
Defined.

Record FrtStepBlock (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames) := {
  StepInput: Type;
  StepPrevious: StepInput -> FrtRestrPrevData FC cB' Hlen' frames paintings;
  StepLayer: forall sp: StepInput,
    FrtRestrLayerStepAtChosen FC cB' Hlen' frames paintings
      (frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD).1
      (frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD).2.1
      (StepPrevious sp);
}.

Arguments StepInput {M XpB0 S0 HD p k dcB cB FC cB' Hlen' frames paintings SD} _.
Arguments StepPrevious {M XpB0 S0 HD p k dcB cB FC cB' Hlen' frames paintings SD} _ _.
Arguments StepLayer {M XpB0 S0 HD p k dcB cB FC cB' Hlen' frames paintings SD} _ _.

Definition RestrNext (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
  (B: FrtStepBlock M HD p cB FC cB' Hlen' frames paintings SD) (sp: B.(StepInput)):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) p.+1 cB' Hlen'
    (mkFrtDepsOf FC cB' frames paintings)).(FrtRestrDataDef) :=
  (B.(StepPrevious) sp; fun q Hq Hqp epsilon t =>
    frtRestrCell FC cB' Hlen' frames paintings
      (frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD).1
      (frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD).2.1
      (frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD).2.2
      (B.(StepPrevious) sp) q Hq Hqp epsilon t (B.(StepLayer) sp q Hq Hqp epsilon t)).

Arguments RestrNext {M XpB0 S0 HD p k dcB cB FC cB' Hlen' frames paintings SD} B sp.

Fixpoint mkFrtStepTypesAndRestrNext (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames),
  FrtStepBlock M HD p cB FC cB' Hlen' frames paintings SD :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames),
  FrtStepBlock M HD p cB FC cB' Hlen' frames paintings SD with
  | 0 => fun k dcB cB FC cB' Hlen' frames paintings SD => {|
      StepInput :=
        { Qprev: (mkFrtRestrTypesAndFrames M.+1 (DescS HD) 0
            (DepsCohsChainCons cB')
            (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') 0))
            (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))).(FrtRestrDataDef) &T
          FrtRestrLayerStepAtChosen FC cB' Hlen' frames paintings SD.1 SD.2.1 Qprev };
      StepPrevious sp := sp.1;
      StepLayer sp := sp.2;
    |}
  | S p => fun k dcB cB FC cB' Hlen' frames paintings SD =>
      let prev := mkFrtStepTypesAndRestrNext M HD p (DepsCohsChainCons cB)
        (proj1FrtDepsCohs FC) (DepsCohsChainCons cB')
        (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
        frames.1 paintings.1 SD.1 in
      {|
        StepInput := { spPrev: prev.(StepInput) &T
          FrtRestrLayerStepAtChosen FC cB' Hlen' frames paintings
            SD.2.1 SD.2.2.1 (RestrNext prev spPrev) };
        StepPrevious sp := RestrNext prev sp.1;
        StepLayer sp := sp.2;
      |}
  end.

Definition FrtStepDataAt (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames): Type :=
  (mkFrtStepTypesAndRestrNext M HD p cB FC cB' Hlen' frames paintings SD).(StepInput).

Definition mkFrtRestrNext (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  (k: nat) (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
    (SP: FrtStepDataAt M HD p cB FC cB' Hlen' frames paintings SD):
  (mkFrtRestrTypesAndFrames M.+1 (DescS HD) p.+1 cB' Hlen'
     (mkFrtDepsOf FC cB' frames paintings)).(FrtRestrDataDef) :=
  (RestrNext (mkFrtStepTypesAndRestrNext M HD p cB FC cB' Hlen' frames paintings SD)) SP.

(** The layer data a level carries beside its restriction clauses: the
    stage-indexed rung-1 clause at layers ([FrtRestrLayerStep]) of the
    identification the level emits, which is what the clause step one level
    up consumes. *)

Definition fgSplitOf (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp) :=
  frtSplitOfQ m (descAt m) m DepsCohsChainNil (descChainLen (descAt m))
    (fgDeps m (fgTowerAt m P) frt frp) Q.

Definition FgLevelDatumType (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp): Type :=
  FrtStepDataAt m (descAt m) m DepsCohsChainNil
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q) DepsCohsChainNil
    (descChainLen (descAt m.+1)) (fgFrtOf m (fgTowerAt m P) frt frp Q)
    (fgFrpOf m (fgTowerAt m P) frt frp Q) (fgSplitOf m P frt frp Q).

Record FgLevel (m: nat) := {
  lvP: FgPrefix m;
  lvFrt: FgFrt m (fgTowerAt m lvP);
  lvFrp: FgFrp m (fgTowerAt m lvP) lvFrt;
  lvQ: FgRestrData m (fgTowerAt m lvP) lvFrt lvFrp;
  lvSP: FgLevelDatumType m lvP lvFrt lvFrp lvQ;
}.

Arguments lvP {m} _.
Arguments lvFrt {m} _.
Arguments lvFrp {m} _.
Arguments lvQ {m} _.
Arguments lvSP {m} _.

Definition lvW {m} (s: FgLevel m): FgTower m := fgTowerAt m s.(lvP).

(** Level [0]: the frame identification is between elements of [gunit], and
    so is its restriction clause, which is therefore free. *)

Definition frtRestr0:
  FgRestrData 0 fgTowerStep0 frt0List frp0List.
Proof.
  intros q Hq Hqp ε t.
  etransitivity; [now apply hunit_ext_uniq |
    symmetry; now apply hunit_ext_uniq].
Defined.

Definition FgLevel0Datum: Type :=
  FgLevelDatumType 0 ((tt; fgThis0): FgPrefix 0) frt0List frp0List frtRestr0.

Definition fgLevel0 (D0: FgLevel0Datum): FgLevel 0.
Proof.
  unshelve econstructor.
  - now exact ((tt; fgThis0): FgPrefix 0).
  - now exact frt0List.
  - now exact frp0List.
  - now exact frtRestr0.
  - now exact D0.
Defined.

(** The level step: the carried restriction clauses produce the frame
    identification one level up, the painting identification follows
    ([fgFrpOf]), and the translation tower's whole next tower is the prefix extended by
    the filler equivalence the level emits.  The only datum the step still
    consumes is the restriction clause one level up. *)

Definition fgFrtNextOf (m: nat) (s: FgLevel m):
  FgFrt m.+1 (fgWNext m (lvW s) s.(lvFrt) s.(lvFrp)
    (fgFrtOf m (lvW s) s.(lvFrt) s.(lvFrp) s.(lvQ))) :=
  fgFrtOf m (lvW s) s.(lvFrt) s.(lvFrp) s.(lvQ).

Definition fgThisAtLevel (m: nat) (s: FgLevel m):
  towerFillerEqv (lvW s) (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m)))
    (this ((νGpdPack m.+1 X).2)) :=
  fgThisOfFrames (lvW s) (pshTw m) (descAt m) s.(lvFrt) s.(lvFrp)
    (fgFrtNextOf m s).

Definition fgPrefixNext (m: nat) (s: FgLevel m): FgPrefix m.+1 :=
  (s.(lvP); fgThisAtLevel m s).

Definition fgFrpNextOf (m: nat) (s: FgLevel m):
  FgFrp m.+1 (fgTowerAt m.+1 (fgPrefixNext m s)) (fgFrtNextOf m s) :=
  fgFrpOf m (lvW s) s.(lvFrt) s.(lvFrp) s.(lvQ).

(** The stage fixpoint produces the next restriction clauses from
    the carried clauses, read as split data, and the level's layer data. *)

Definition towerFrtDepsCohs (m: nat) (s: FgLevel m):
  FrtDepsCohs m (descAt m)
    (DepsCohsChainNil (dcTop := νDepsCohsAt ((νGpdPack m X).2))) :=
  towerFrtDepsCohsOf m (lvW s) s.(lvFrt) s.(lvFrp) s.(lvQ).

Definition fgQNext (m: nat) (s: FgLevel m):
  FgRestrData m.+1 (fgTowerAt m.+1 (fgPrefixNext m s)) (fgFrtNextOf m s)
    (fgFrpNextOf m s) :=
  mkFrtRestrNext m (descAt m) m _ _ DepsCohsChainNil (towerFrtDepsCohs m s)
    DepsCohsChainNil (descChainLen (descAt m.+1)) (fgFrtNextOf m s)
    (fgFrpNextOf m s)
    (fgSplitOf m s.(lvP) s.(lvFrt) s.(lvFrp) s.(lvQ))
    s.(lvSP).

(** The layer data required at the next level. *)

Definition FgStepData: Type :=
  forall (m: nat) (s: FgLevel m),
  FgLevelDatumType m.+1 (fgPrefixNext m s) (fgFrtNextOf m s)
    (fgFrpNextOf m s) (fgQNext m s).

Definition fgLevelStep (m: nat) (s: FgLevel m)
  (SP: FgLevelDatumType m.+1 (fgPrefixNext m s) (fgFrtNextOf m s)
         (fgFrpNextOf m s) (fgQNext m s)):
  FgLevel m.+1 := {|
  lvP := fgPrefixNext m s;
  lvFrt := fgFrtNextOf m s;
  lvFrp := fgFrpNextOf m s;
  lvQ := fgQNext m s;
  lvSP := SP;
|}.

Fixpoint fgLevels (D0: FgLevel0Datum) (D: FgStepData) (m: nat): FgLevel m :=
  match m with
  | 0 => fgLevel0 D0
  | S m => let s := fgLevels D0 D m in fgLevelStep m s (D m s)
  end.

(** The chain, and the levelwise equivalence

    The translation tower's prefix at level [m] is the one the levels have built; the
    telescope's own stage at that level is indexed by [νGpdPack m (f (g X))]
    instead, so the chain carries the identification of the two unfoldings
    of [f (g X)].  It is [eq_refl] at every level, but neither side reduces
    at a variable level, so it is carried and eliminated at the start of the
    step.  The step is stated over a variable unfolding, so that the
    elimination is legitimate: [νGpdPack m.+1] does not contain
    [νGpdPack m] as a subterm. *)

Definition fgPrefixAt (D0: FgLevel0Datum) (D: FgStepData) (m: nat):
  (trAt m (pshApprox (g X) m) ((νGpdPack m X).1)).(trPrefix) :=
  match m return (trAt m (pshApprox (g X) m) ((νGpdPack m X).1)).(trPrefix) with
  | 0 => tt
  | S m => (fgLevels D0 D m).(lvP)
  end.

(** The filler equivalence the level emits: the datum of the translation tower's
    telescope there. *)

Definition fgThisAt (D0: FgLevel0Datum) (D: FgStepData) (m: nat):
  towerFillerEqv ((trAt m (pshApprox (g X) m)
    ((νGpdPack m X).1)).(trData) (fgPrefixAt D0 D m))
    ((pshApprox (g X) m.+1).2) (((νGpdPack m.+1 X).1).2) :=
  match m return towerFillerEqv ((trAt m (pshApprox (g X) m)
    ((νGpdPack m X).1)).(trData) (fgPrefixAt D0 D m))
    ((pshApprox (g X) m.+1).2) (((νGpdPack m.+1 X).1).2) with
  | 0 => fgThis0
  | S m => fgThisAtLevel m (fgLevels D0 D m)
  end.

Lemma fgPrefixAtS (D0: FgLevel0Datum) (D: FgStepData) (m: nat):
  fgPrefixAt D0 D m.+1
  = ((fgPrefixAt D0 D m; fgThisAt D0 D m):
      (trAt m.+1 (pshApprox (g X) m.+1) ((νGpdPack m.+1 X).1)).(trPrefix)).
Proof. now destruct m. Defined.

Definition FgPack (m: nat): {Xp: (νGpdAt m).(prefix) &T νGpdFrom m Xp} :=
  (pshApprox (g X) m; pshFrom (g X) m).

Definition FgChainState (D0: FgLevel0Datum) (D: FgStepData) (m: nat)
  (Y: {Xp: (νGpdAt m).(prefix) &T νGpdFrom m Xp})
  (P: (trAt m Y.1 ((νGpdPack m X).1)).(trPrefix)): Type :=
  { HP: FgPack m = Y &T
    rew [fun w: {Xp: (νGpdAt m).(prefix) &T νGpdFrom m Xp} =>
         (trAt m w.1 ((νGpdPack m X).1)).(trPrefix)] HP in
      (fgPrefixAt D0 D m: (trAt m (FgPack m).1 ((νGpdPack m X).1)).(trPrefix))
    = P }.

Definition fgChainStep (D0: FgLevel0Datum) (D: FgStepData) (m: nat)
  (Y: {Xp: (νGpdAt m).(prefix) &T νGpdFrom m Xp})
  (P: (trAt m Y.1 ((νGpdPack m X).1)).(trPrefix))
  (s: FgChainState D0 D m Y P):
  { E: towerFillerEqv ((trAt m Y.1 ((νGpdPack m X).1)).(trData) P)
         (this Y.2) (this ((νGpdPack m X).2)) &T
    FgChainState D0 D m.+1
      (((Y.1; this Y.2); next Y.2):
        {Xp: (νGpdAt m.+1).(prefix) &T νGpdFrom m.+1 Xp})
      ((P; E): (trAt m.+1 (Y.1; this Y.2)
        (((νGpdPack m X).1); this ((νGpdPack m X).2))).(trPrefix)) }.
Proof.
  destruct s as [HP HE].
  destruct HP.
  cbn in HE.
  destruct HE.
  unshelve refine (fgThisAt D0 D m; (eq_refl; _)).
  now exact (fgPrefixAtS D0 D m).
Defined.

Fixpoint fgChain (D0: FgLevel0Datum) (D: FgStepData) (m: nat):
  { P: (trAt m (νGpdPack m (f (g X))).1 ((νGpdPack m X).1)).(trPrefix) &T
    FgChainState D0 D m (νGpdPack m (f (g X))) P } :=
  match m return { P: (trAt m (νGpdPack m (f (g X))).1
      ((νGpdPack m X).1)).(trPrefix) &T
      FgChainState D0 D m (νGpdPack m (f (g X))) P } with
  | 0 => (tt; (eq_refl; eq_refl))
  | S m => let s := fgChain D0 D m in
           let e := fgChainStep D0 D m (νGpdPack m (f (g X))) s.1 s.2 in
           ((s.1; e.1); e.2)
  end.

(** The round trip: the levelwise equivalence [f (g X) ≃ X].  Both
    coherences of the limit are [eq_refl] because a stage of the translation tower's
    telescope at level [m.+1] is a Σ-type over the stage at [m] whose bond
    is its first projection. *)

Definition fgOfData (D0: FgLevel0Datum) (D: FgStepData): νGpdsEquiv (f (g X)) X :=
  limit (trTel (f (g X)) X) 0 tt (fun m _ => (fgChain D0 D m).1) eq_refl
    (fun m _ _ => eq_refl).

(** The dimension-[0] reading of a stored restriction painting

    A generated [mkRestrPainting] is, at local dimension [0], the [ζ]-entry of
    the layer of its argument ([νGpd.v]'s base case), so a tower whose restr
    paintings are generated satisfies this clause definitionally.  Stating it
    lets the clause at layers be reduced without unfolding either tower. *)

Definition FrtRpZeroType {p k} {DR: DepsRestr p.+1 k}
  (Xe: DepsRestrExtension p.+1 k DR) (rp: mkRestrPaintingTypes Xe): Type :=
  forall (Hq: 0 <= k) (ζ: arity) (d: mkFrame DR.(1))
    (c: (mkPaintings (DR; Xe)%extradepsrestr).2 d),
  rp.2 0 Hq ζ d c = nth c.1 ζ.

(** The rung-1 clause at paintings

    The clause at frames ([FrtRestr0At]) is a square of paths of [A]-side
    frames: the identification at a face cell, read through the two towers'
    restriction laws of frames, agrees with the identification one level up
    restricted.  Over that square sits the same square one level down, between
    paths of [A]-side *paintings*, and this is the datum the clause at layers
    needs besides the split datum: its two content edges are the two towers'
    stored restriction-painting laws, which are free fields of [FrtDepsCohs]
    and occur in the clause at layers on opposite sides.

    The left composite runs along the stage's own painting identification at
    the face cell, the descent's law for the cell pair (read at its painting
    component, and corrected by the dimension-[0] reading of the [B]-side
    restriction paintings, which is what makes the two composable), and the
    translation's restriction-painting law at the cell one level up.  The
    right composite runs along the presheaf's restriction-painting law and the
    [A]-side restriction painting of the painting identification one stage
    down. The clause is indexed by the specified restriction cell
    [HR ε t]. *)

Definition FrtRestrPaintingType {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
     (mkPshPaintings (g X) PX)
     (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
  (Hpair: FrtPairLawAt F top)
  (HR: FrtRestr0At F top frames.1 Hpair) (HrpB: FrtRpZeroType XB rpB): Type :=
  forall (ε: arity) (t: (g X).(G0) M.+1),
  DPathCellOver
    ((F.(_frPaintings).2 ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t)
      ⊙[fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
      (sigT_map_eq
         (P := fun a: (mkDepsRestr (depsCohs := dcB)).(_frames).2 =>
                 (mkDepsRestr (depsCohs := dcB)).(_paintings).2 a)
         (Q := fun x: F.(_frDepsA).(_frames).2 =>
                 F.(_frDepsA).(_paintings).2 x)
         (f := fun a => F.(_frFrameEqvs).2 a)
         (fun a c => F.(_frPaintingEqvs).2 a c) (projT2_eq (Hpair ε t))
       • eq_sym (f_equal
           (F.(_frPaintingEqvs).2
              ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ε
                 (top t).1))
           (HrpB leR_O ε (top t).1 ((top t).2; val t)))))
     ⊙[fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
     trRp.2 0 leR_O ε (top t).1 ((top t).2; val t))
    (pshRp.2 0 leR_O (⇓ F.(_frBound)) ε t
     ⊙[fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
     sigT_map_eq
       (Q := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)
       (f := fun n => F.(_frDepsA).(_restrFrames).2 0 leR_O ε n)
       (fun n c => rpA.2 0 leR_O ε n c) (paintings.1.2 t)) (HR ε t).

(** The dimension-[0] data of the two towers' restriction paintings

    The three clauses a stage carries besides the painting identification: the
    dimension-[0] readings of the two towers' restriction paintings, and the
    rung-1 clause at paintings stated with the [B]-side reading. *)

Definition FrtRpStepAt {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
     (mkPshPaintings (g X) PX)
     (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
  (Hpair: FrtPairLawAt F top) (HR: FrtRestr0At F top frames.1 Hpair): Type :=
  { _: FrtRpZeroType XA rpA &T
    { HrpB: FrtRpZeroType XB rpB &T
      FrtRestrPaintingType F XA XB TX PX rpA rpB trRp pshRp top val frames
        paintings Hpair HR HrpB } }.

(** What the layer clause consumes about the painting identification

    Two facts, at an arbitrary [X]-side cell frame map [top] and an arbitrary
    family of values [val] over it: the top entry of the painting list read
    as a transport of the presheaf painting along the frame identification
    the clauses determine ([E]), and the entry below the top read as an
    explicit [mkFrtPaintingStepDown] of that top entry.  Stating them over
    [top] and [val] rather than over the chain lets the same definition serve
    both the abstract stage recursion and the ladder, whose lists are typed
    at [descTop HD cB].

 *)

Definition FrtPtStepAt {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
     (mkPshPaintings (g X) PX)
     (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
  (Hpair: FrtPairLawAt F top)
  (HR: FrtRestr0At F top frames.1 Hpair): Type :=
  { E: FrtPaintingTopType F TX PX top val
         (mkFrtFrameStep F top frames.1
            (fun t => mkFrtLayerOfRestr F top frames.1 Hpair HR t)) &T
    { _: forall u, paintings.1.2 u
           = mkFrtPaintingStepDown F XA XB TX PX top val frames.1
               (fun t => mkFrtLayerOfRestr F top frames.1 Hpair HR t) E u &T
      FrtRpStepAt F XA XB TX PX rpA rpB trRp pshRp top val frames paintings
        Hpair HR } }.

(** The same at the identification one level up, where the cell frame map is
    the descended cell read along the chain. *)

Definition FrtPtStep {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair): Type :=
  FrtPtStepAt FC.(_fcF) FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX)
    FC.(_fcRpA) FC.(_fcRpB) FC.(_fcTrRp) FC.(_fcPshRp)
    (frtTopNext FC cB')
    ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
        (fun u => (descCell (DescS HD) u).2)).2)
    frames paintings Hpair HR.

(** The same at every stage, by the recursion the identification steps by. *)

Fixpoint FrtPtChainAt (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (val: forall u, mkPainting XB (top u))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
       (mkPshPaintings (g X) PX)
       (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cB F top frames), Type :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (val: forall u, mkPainting XB (top u))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
       (mkPshPaintings (g X) PX)
       (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cB F top frames), Type with
  | 0 => fun k dcB cB F XA XB TX PX rpA rpB trRp pshRp top val frames
           paintings SD =>
    FrtPtStepAt F XA XB TX PX rpA rpB trRp pshRp top val frames paintings
      SD.1 SD.2.1
  | S p => fun k dcB cB F XA XB TX PX rpA rpB trRp pshRp top val frames
             paintings SD =>
    { _: FrtPtChainAt M HD p (DepsCohsChainCons cB) (proj1FrtDeps F)
           (F.(_frDepsA); XA)%extradepsrestr
           (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
           (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
           rpA.1 rpB.1 trRp.1 pshRp.1
           (fun t => (top t).1) (fun u => ((top u).2; val u))
           frames.1 paintings.1 SD.1 &T
      FrtPtStepAt F XA XB TX PX rpA rpB trRp pshRp top val frames paintings
        SD.2.1 SD.2.2.1 }
  end.

(** The three clauses at every stage, by the same recursion. *)

Fixpoint FrtRpChainAt (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (val: forall u, mkPainting XB (top u))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
       (mkPshPaintings (g X) PX)
       (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cB F top frames), Type :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (val: forall u, mkPainting XB (top u))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
       (mkPshPaintings (g X) PX)
       (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cB F top frames), Type with
  | 0 => fun k dcB cB F XA XB TX PX rpA rpB trRp pshRp top val frames
           paintings SD =>
    FrtRpStepAt F XA XB TX PX rpA rpB trRp pshRp top val frames paintings SD.1 SD.2.1
  | S p => fun k dcB cB F XA XB TX PX rpA rpB trRp pshRp top val frames
             paintings SD =>
    { _: FrtRpChainAt M HD p (DepsCohsChainCons cB) (proj1FrtDeps F)
           (F.(_frDepsA); XA)%extradepsrestr
           (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
           (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
           rpA.1 rpB.1 trRp.1 pshRp.1
           (fun t => (top t).1) (fun u => ((top u).2; val u))
           frames.1 paintings.1 SD.1 &T
      FrtRpStepAt F XA XB TX PX rpA rpB trRp pshRp top val frames paintings
        SD.2.1 SD.2.2.1 }
  end.

Definition FrtPtChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames): Type :=
  FrtPtChainAt M HD p cB FC.(_fcF) FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX)
    FC.(_fcRpA) FC.(_fcRpB) FC.(_fcTrRp) FC.(_fcPshRp)
    (frtTopNext FC cB')
    ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
        (fun u => (descCell (DescS HD) u).2)).2)
    frames paintings SD.

(** The δ-δ exchange law of the cell-pair identification

    [FrtPairLawAt] identifies the cell pair the descent assigns to a face of
    a cell with the restriction of the identification's frame map at the
    cell.  Taking two faces of a cell in either order gives two such
    identifications of the same pair, and the clause at layers needs them to
    agree: the square below relates the pair law at [ω] of the [ε]-face with
    the pair law at [ε] of the [ω]-face, through the presheaf's face exchange
    law on one side and the [B]-side tower's exchange of restrictions on the
    other.

    Every leg is spelled in the vocabulary of the identification one level
    up ([descQcells], [frtPairLawPrev]); the [B]-side dimension-[0] reading
    of restriction paintings enters exactly once, at the instance the clause
    at paintings ([FrtRestrPaintingType]) uses, so that the square and that
    clause are stated over the same reading.

    The maps involved: *)

(** The cell pair at a cell of the presheaf, as the descent reads it: the
    frame and the value the chain assigns to the cell (the left-hand side of
    [FrtPairLawAt]). *)

Definition frtCellPair {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc S0) {p k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (u: (g X).(G0) M):
  {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D} :=
  ((mkCellFramesOf M (extChainDeps (cohsChainExt cB)) (descCells HD)).2 u;
   (mkCellValuesOf M (cohsChainExt cB) (descCells HD)
      (fun u0 => (descCell HD u0).2)).2 u).

(** The restricted pair at a frame one level up: the restriction of the
    frame at [ω] and the [ω]-entry of its layer (the right-hand side of
    [FrtPairLawAt]). *)

Definition frtPairRestrAt {p k} (dcB: DepsCohs p k) (ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dcB))):
  {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D} :=
  (mkRestrFrame (depsCohs := dcB) 0 leR_O ω d.1; nth d.2 ω).

(** The restricted pair at a painting one level up, read through the
    [B]-side restriction of paintings at dimension [0]. *)

Definition frtPairRestrPaintingAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (ε: arity)
  (z: {D: mkFrame (mkDepsRestr (depsCohs := dcB)).(1) &T
          (mkPaintings ((mkDepsRestr (depsCohs := dcB));
             FC.(_fcXB))%extradepsrestr).2 D}):
  {D: mkFrame dcB.(_deps) &T mkPainting dcB.(_extraDeps) D} :=
  (mkRestrFrame (depsCohs := dcB) 0 leR_O ε z.1;
   FC.(_fcRpB).2 0 leR_O ε z.1 z.2).

(** The exchange leg of the square: restricting a frame one level up at [ε]
    and reading the restricted pair at [ω] agrees with restricting at [ω]
    first and reading the restricted pair at [ε] through the [B]-side
    restriction of paintings.  Its frame half is the [B]-side tower's stored
    frame coherence; its painting half is the [ω]-entry of the restricted
    layer, which is that entry of the layer restricted at [ε], moved along the
    coherence. *)

Definition frtPairSqExchange {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (Hq: 0 <= k) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs := frtDcB FC)).(1)):
  frtPairRestrAt dcB ω
    ((mkDepsRestr (depsCohs := frtDcB FC)).(_restrFrames).2 0 Hq ε D)
  = frtPairRestrPaintingAt FC ε
      ((mkDepsRestr (depsCohs := proj1DepsCohs (frtDcB FC))).(_restrFrames).2
         0 leR_O ω D.1;
       nth D.2 ω) :=
  (= eq_sym (FC.(_fcCohsB).2 0 Hq 0 leR_O ε ω D.1);
     rewSwapSym _ (FC.(_fcCohsB).2 0 Hq 0 leR_O ε ω D.1)
       (nth_lmap _ D.2 ω)).

(** The square itself, at a stage of the identification one level up.
    Parameters: [FC], the stage's coherence data; [cB'], [Hlen'], the chain
    one level up and its length; [frames], [paintings], the frame and
    painting identifications one level up; [Hpair], the pair law at the
    stage; [HrpB], the [B]-side dimension-[0] reading of restriction
    paintings.  Quantified over the two faces [ε] (taken first, one level up)
    and [ω], the cell [t], and the two bounds. *)

Definition FrtPairSqAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HrpB: FrtRpZeroType FC.(_fcXB) FC.(_fcRpB)): Type :=
  forall (Hq: 0 <= k) (Hqp: 0 + p.+1 <= M.+1) (ε ω: arity)
    (t: (g X).(G0) M.+2),
  f_equal (frtCellPair HD cB)
    ((g X).(GFaceCoh) M (0 + p) (⇓ leR_add_shift Hqp) p (leR_add_l 0) ε ω t)
  • (Hpair ω ((g X).(GFace) M.+1 (0 + p.+1) Hqp ε t)
     • (f_equal (frtPairRestrAt dcB ω) (descQcells cB' Hlen' 0 Hq Hqp ε t)
        • frtPairSqExchange FC Hq ε ω (descTop (DescS HD) cB' t).1))
  = Hpair ε ((g X).(GFace) M.+1 p (leR_add_l 0 ↕ ↑ (⇓ leR_add_shift Hqp)) ω t)
    • (eq_existT_curried
         (P := fun D: mkFrame dcB.(_deps) => mkPainting dcB.(_extraDeps) D)
         eq_refl
         (eq_sym (HrpB leR_O ε
           (frtTopNext FC cB'
              ((g X).(GFace) M.+1 p (leR_add_l 0 ↕ ↑ (⇓ leR_add_shift Hqp)) ω t)).1
           ((frtTopNext FC cB'
               ((g X).(GFace) M.+1 p (leR_add_l 0 ↕ ↑ (⇓ leR_add_shift Hqp)) ω t)).2;
            (mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
               (fun u => (descCell (DescS HD) u).2)).2
              ((g X).(GFace) M.+1 p (leR_add_l 0 ↕ ↑ (⇓ leR_add_shift Hqp)) ω t))))
       • f_equal (frtPairRestrPaintingAt FC ε)
           (frtPairLawPrev FC cB' Hlen' frames paintings ω t)).

(** The δ-δ square of the pair law at every stage, by the recursion the
    identification steps by; the square of a stage is stated at the
    [B]-side dimension-[0] reading that stage's clause at paintings carries. *)

Fixpoint FrtSqChainAt (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
    (PT: FrtPtChain M HD p cB FC cB' Hlen' frames paintings SD), Type :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
    (PT: FrtPtChain M HD p cB FC cB' Hlen' frames paintings SD), Type with
  | 0 => fun k dcB cB FC cB' Hlen' frames paintings SD PT =>
    FrtPairSqAt FC cB' Hlen' frames paintings SD.1 PT.2.2.2.1
  | S p => fun k dcB cB FC cB' Hlen' frames paintings SD PT =>
    { _: FrtSqChainAt M HD p (DepsCohsChainCons cB) (proj1FrtDepsCohs FC)
           (DepsCohsChainCons cB')
           (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
           frames.1 paintings.1 SD.1 PT.1 &T
      FrtPairSqAt FC cB' Hlen' frames paintings SD.2.1 PT.2.2.2.2.1 }
  end.

(** The two providers of the rung-1 clause at layers

    At the bottom stage the clause is asked for on its own; at a successor
    stage the recursion has the whole datum one stage down in hand, and the
    layer half of the clause is that datum's own clause, so the successor
    provider takes it as an argument. *)

Definition FrtRestrLayerStepAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair)
  (q: nat): Type :=
  forall (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (ε: arity)
    (t: (g X).(G0) M.+2)
    (prev: FrtFramesPrevType
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')))
    (HRPrev: FrtRestr0At
             (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
             (descTop (DescS HD) (DepsCohsChainCons cB')) prev
             (frtPairLawPrev FC cB' Hlen' frames paintings)),
  DPathEq
    (mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR
       ((g X).(GFace) M.+1 (q + p.+1) Hqp ε t)
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] sigT_map_eq
         (P := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 x0)
         (fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
            (frTr FC.(_fcF)).(_trRestrs) a l)
         (projT2_eq (descQcells cB' Hlen' q Hq Hqp ε t))
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] mkTrRestrLayer (frtTrCohs FC).(_trBase)
         (mkTrRestrFrames (proj1TrDepsCohs (frtTrCohs FC)))
         (frtTrCohs FC).(_trCohs).2 q Hq ε (descTop (DescS HD) cB' t).1)
    (mkPshRestrLayerMerged (g X) (frtPshCohs FC)
       (mkPshRestrFrames (g X)
          (proj1PshDepsCohs (g X)
             (frtPshCohsOf FC.(_fcF) FC.(_fcXA) FC.(_fcPX) FC.(_fcRpA)
                FC.(_fcPshRp) FC.(_fcCohsA)))
          FC.(_fcPshCohs).1)
       FC.(_fcPshCohs).2 q Hq Hqp ε t
     ⊙[fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
                 (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2)
                 x0).(GDom)] sigT_map_eq
         (P := fun x0 => (mkLayer
            (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
            (painting := (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkRestrFrames (depsCohs :=
            proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2 q.+1 (⇑ Hq) ε x0)
         (fun a l => mkRestrLayer
            (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2
            (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq ε a l)
         (mkFrtLayerOfRestr
            (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
            (descTop (DescS HD) (DepsCohsChainCons cB')) prev
            (frtPairLawPrev FC cB' Hlen' frames paintings) HRPrev t)).

Set Keyed Unification.

(** The two facts at the ladder

    The ladder's painting list is [mkFrtPaintingsOfRestr], so both facts are
    the two readings of its entries: the top entry is the datum it was built
    from ([frtPaintingTopPath], which is how the [E] component is the [E] the
    list carries), and the entry below the top is that datum stepped down
    ([frtPaintingsPrevEntry0] / [frtPaintingsPrevEntryS]).  As [frtSplitOfQ],
    this is stated at [descTop HD cB], where the ladder's lists are typed. *)

Fixpoint mkFrtPtChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (val: forall u, mkPainting XB (descTop HD cB u))
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q))
    (RP: FrtRpChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp
           (descTop HD cB) val
           ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
           (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
           (frtSplitOfQ M HD p cB Hlen F Q)),
  FrtPtChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp (descTop HD cB) val
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
    (frtSplitOfQ M HD p cB Hlen F Q) :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (val: forall u, mkPainting XB (descTop HD cB u))
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q))
    (RP: FrtRpChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp
           (descTop HD cB) val
           ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
           (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
           (frtSplitOfQ M HD p cB Hlen F Q)),
  FrtPtChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp (descTop HD cB) val
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
    (frtSplitOfQ M HD p cB Hlen F Q) with
  | 0 => fun k dcB cB Hlen F XA XB TX PX rpA rpB trRp pshRp val Q E RP =>
    (E; ((fun _ => eq_refl); RP))
  | S p => fun k dcB cB Hlen F XA XB TX PX rpA rpB trRp pshRp val Q E RP =>
    (mkFrtPtChain M HD p (DepsCohsChainCons cB)
       (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F)
       (F.(_frDepsA); XA)%extradepsrestr
       (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
       (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
       rpA.1 rpB.1 trRp.1 pshRp.1
       (fun u => ((descTop HD cB u).2; val u)) Q.1
       (fun t => mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
              (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
              (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
          (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
             ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
                 (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
                 (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
             (fun ε t1 =>
                descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
             (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
          E t) RP.1;
     (E; ((fun _ => eq_refl); RP.2)))
  end.

(** At a level of the round trip the chain is empty, and the [X]-side cell
    frame map the ladder's lists are typed at is the one the stage data is
    stated with. *)

Definition FgRpChain (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp): Type :=
  FrtRpChainAt m (descAt m) m DepsCohsChainNil
    (fgDeps m (fgTowerAt m P) frt frp)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcXA)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcXB)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTX)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPX)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcRpA)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcRpB)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTrRp)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPshRp)
    (descTop (descAt m) DepsCohsChainNil)
    (fun u => (descCell (descAt m.+1) u).2)
    (fgFrtOf m (fgTowerAt m P) frt frp Q)
    (fgFrpOf m (fgTowerAt m P) frt frp Q) (fgSplitOf m P frt frp Q).

Definition fgPtChain (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp)
  (RP: FgRpChain m P frt frp Q):
  FrtPtChain m (descAt m) m DepsCohsChainNil
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q) DepsCohsChainNil
    (descChainLen (descAt m.+1)) (fgFrtOf m (fgTowerAt m P) frt frp Q)
    (fgFrpOf m (fgTowerAt m P) frt frp Q) (fgSplitOf m P frt frp Q).
Proof.
  now exact (mkFrtPtChain m (descAt m) m DepsCohsChainNil
    (descChainLen (descAt m)) (fgDeps m (fgTowerAt m P) frt frp)
    _ _ _ _ _ _ _ _ _ Q _ RP).
Defined.

(** The two providers of the rung-1 clause at paintings, at the bottom level
    and at a level step; all the data the clause is about are generated there
    (the level's own painting list, the tower's restriction paintings, the
    presheaf's), so both are statements about generated data rather than
    carried ones. *)

Definition FgRpChainBaseType: Type :=
  FgRpChain 0 ((tt; fgThis0): FgPrefix 0) frt0List frp0List frtRestr0.

Definition FgRpChainStepType: Type :=
  forall (m: nat) (s: FgLevel m),
  FgRpChain m.+1 (fgPrefixNext m s) (fgFrtNextOf m s) (fgFrpNextOf m s)
    (fgQNext m s).

(** The rung-1 clause at paintings, at the ladder

    The three clauses a stage of the frame ladder carries besides the
    painting identification ([FrtRpStepAt]) at the data a level of the round
    trip generates, and the provider of the level step ([fgRpStep]).

    The two dimension-[0] readings of the two towers' restriction paintings
    hold at a generated tower by computation; the content is the third
    clause, the rung-1 clause at paintings ([FrtRestrPaintingType]).  At the
    ladder its two free edges are explicit — the translation's is
    [trLayerEqvNth] and the presheaf's is [nth_lam] — and once both are
    rewritten to those the clause is the residue of the stage step
    ([mkFrtResidueOfRestr]) read at an arity, which is what
    [mkFrtLayerOfRestr] is built from.  So the clause is the definition of
    the residue chain, conjugated by the two dimension-[0] readings.
    The clause retains the residue's chosen [HR] as its base cell. *)

(** The dimension-[0] readings, stage by stage

    A stage of the ladder projects the four restriction-painting families it
    carries, so the reading each stage needs is a chain of one clause per
    stage, by the same recursion as the family it is about.  At generated
    data every entry of the chain holds by computation, since the prefix of
    a generated family is again generated. *)

Fixpoint RpZeroChain (p: nat) {struct p}:
  forall {k} {DR: DepsRestr p k} (Xe: DepsRestrExtension p k DR)
    (rp: mkRestrPaintingTypes Xe), Type :=
  match p return forall k (DR: DepsRestr p k)
    (Xe: DepsRestrExtension p k DR) (rp: mkRestrPaintingTypes Xe), Type with
  | 0 => fun _ _ _ _ => unit
  | S p => fun k DR Xe rp =>
    { _: RpZeroChain p (DR; Xe)%extradepsrestr rp.1 &T FrtRpZeroType Xe rp }
  end.
Fixpoint rpZeroChainPrefix (p: nat) {struct p}:
  forall {k} {depsCohs: DepsCohs p k} (XC: DepsCohsExtension p k depsCohs),
  RpZeroChain p (mkDepsRestr (depsCohs := depsCohs); mkExtraDeps XC)%extradepsrestr
    (mkRestrPaintings XC).1 :=
  match p return forall k (depsCohs: DepsCohs p k)
    (XC: DepsCohsExtension p k depsCohs),
    RpZeroChain p (mkDepsRestr (depsCohs := depsCohs); mkExtraDeps XC)%extradepsrestr
      (mkRestrPaintings XC).1 with
  | 0 => fun k depsCohs XC => tt
  | S p => fun k depsCohs XC =>
    (rpZeroChainPrefix p (AddCohDep depsCohs XC); fun Hq zeta d c => eq_refl)
  end.

Definition rpZeroChainOf (p: nat) {k} {depsCohs: DepsCohs p k}
  (XC: DepsCohsExtension p k depsCohs):
  RpZeroChain p.+1 (mkExtraDeps XC) (mkRestrPaintings XC) :=
  (rpZeroChainPrefix p XC; fun Hq zeta d c => eq_refl).

Definition TrRpZeroType {p k} (T: TrDepsRestr p.+1 k)
  {XA: DepsRestrExtension p.+1 k T.(_depsA)}
  {XB: DepsRestrExtension p.+1 k T.(_depsB)}
  (TX: TrDepsExtension T XA XB)
  {rpA: mkRestrPaintingTypes XA} {rpB: mkRestrPaintingTypes XB}
  (trRp: mkTrRestrPaintingTypes T TX rpA rpB)
  (HrpA: FrtRpZeroType XA rpA) (HrpB: FrtRpZeroType XB rpB): Type :=
  forall (Hq: 0 <= k) (ε: arity) (d: mkFrame T.(_depsB).(1))
    (c: (mkPaintings (T.(_depsB); XB)%extradepsrestr).2 d),
  trRp.2 0 Hq ε d c
  = rew <- [fun z => rew [T.(_depsA).(_paintings).2]
                       T.(_trRestrs).2 0 Hq ε d in
                     T.(_paintingEqvs).2
                       (T.(_depsB).(_restrFrames).2 0 Hq ε d) z
                   = rpA.2 0 Hq ε (mkFrameEqv (proj1TrDepsRestr T) d)
                       (mkPaintingEqv (AddTrDep T TX) d c)]
      (HrpB Hq ε d c) in
    rew <- [fun z => rew [T.(_depsA).(_paintings).2]
                       T.(_trRestrs).2 0 Hq ε d in
                     T.(_paintingEqvs).2
                       (T.(_depsB).(_restrFrames).2 0 Hq ε d) (nth c.1 ε)
                   = z]
      (HrpA Hq ε (mkFrameEqv (proj1TrDepsRestr T) d)
         (mkPaintingEqv (AddTrDep T TX) d c)) in
    eq_sym (trLayerEqvNth T.(_paintingEqvs) T.(_trRestrs) d c.1 ε).
Fixpoint TrRpZeroChain (p: nat) {struct p}:
  forall {k} (T: TrDepsRestr p k)
    {XA: DepsRestrExtension p k T.(_depsA)}
    {XB: DepsRestrExtension p k T.(_depsB)}
    (TX: TrDepsExtension T XA XB)
    {rpA: mkRestrPaintingTypes XA} {rpB: mkRestrPaintingTypes XB}
    (trRp: mkTrRestrPaintingTypes T TX rpA rpB)
    (HA: RpZeroChain p XA rpA) (HB: RpZeroChain p XB rpB), Type :=
  match p return forall k (T: TrDepsRestr p k)
    (XA: DepsRestrExtension p k T.(_depsA))
    (XB: DepsRestrExtension p k T.(_depsB))
    (TX: TrDepsExtension T XA XB)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes T TX rpA rpB)
    (HA: RpZeroChain p XA rpA) (HB: RpZeroChain p XB rpB), Type with
  | 0 => fun _ _ _ _ _ _ _ _ _ _ => unit
  | S p => fun k T XA XB TX rpA rpB trRp HA HB =>
    { _: TrRpZeroChain p (proj1TrDepsRestr T) (AddTrDep T TX) trRp.1 HA.1 HB.1
      &T TrRpZeroType T TX trRp HA.2 HB.2 }
  end.
Fixpoint trRpZeroChainOf (p: nat) {struct p}:
  forall {k} {TC: TrDepsCohs p k}
    {XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase))}
    {XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase))}
    (TCX: TrDepsCohsExtension TC XCA XCB),
  TrRpZeroChain p.+1 (mkTrDepsRestr TC) (mkTrExtraDeps TCX)
    (mkTrRestrPaintings TCX) (rpZeroChainOf p XCA) (rpZeroChainOf p XCB) :=
  match p return forall k (TC: TrDepsCohs p k)
    (XCA: DepsCohsExtension p k (trDepsCohsA TC.(_trBase)))
    (XCB: DepsCohsExtension p k (trDepsCohsB TC.(_trBase)))
    (TCX: TrDepsCohsExtension TC XCA XCB),
    TrRpZeroChain p.+1 (mkTrDepsRestr TC) (mkTrExtraDeps TCX)
      (mkTrRestrPaintings TCX) (rpZeroChainOf p XCA) (rpZeroChainOf p XCB) with
  | 0 => fun k TC XCA XCB TCX => (tt; fun Hq ε d c => eq_refl)
  | S p => fun k TC XCA XCB TCX =>
    (trRpZeroChainOf p (AddTrCohDep TC TCX); fun Hq ε d c => eq_refl)
  end.
Definition PshRpZeroType {m p k} (P: PshDepsRestr (g X) m p.+1 k)
  {Xe: DepsRestrExtension p.+1 k P.(_pdeps _)}
  (PX: PshDepsExtension (g X) m P Xe)
  {rp: mkRestrPaintingTypes Xe}
  (pshRp: mkPshRestrPaintingTypes (g X) P PX rp)
  (Hrp: FrtRpZeroType Xe rp): Type :=
  forall (Hq: 0 <= k) (Hqp: 0 + p <= m) (ε: arity) (d: (g X).(G0) m.+1),
  pshRp.2 0 Hq Hqp ε d
  = rew <- [fun z => rew [P.(_pdeps _).(_paintings).2]
                       P.(_pshRestrs _).2 0 Hq Hqp ε d in
                     P.(_pshPaintings _).2 ((g X).(GFace) m (0 + p) Hqp ε d)
                   = z]
      (Hrp Hq ε (mkPshFrame (g X) (proj1PshDepsRestr (g X) P) d)
         (mkPshPainting (g X) (AddPshDep (g X) m P PX) d)) in
    eq_sym (nth_lam _ ε).
Fixpoint PshRpZeroChain (p: nat) {struct p}:
  forall {m k} (P: PshDepsRestr (g X) m p k)
    {Xe: DepsRestrExtension p k P.(_pdeps _)}
    (PX: PshDepsExtension (g X) m P Xe)
    {rp: mkRestrPaintingTypes Xe}
    (pshRp: mkPshRestrPaintingTypes (g X) P PX rp)
    (H: RpZeroChain p Xe rp), Type :=
  match p return forall m k (P: PshDepsRestr (g X) m p k)
    (Xe: DepsRestrExtension p k P.(_pdeps _))
    (PX: PshDepsExtension (g X) m P Xe)
    (rp: mkRestrPaintingTypes Xe)
    (pshRp: mkPshRestrPaintingTypes (g X) P PX rp)
    (H: RpZeroChain p Xe rp), Type with
  | 0 => fun _ _ _ _ _ _ _ _ => unit
  | S p => fun m k P Xe PX rp pshRp H =>
    { _: PshRpZeroChain p (proj1PshDepsRestr (g X) P)
           (AddPshDep (g X) m P PX) pshRp.1 H.1
      &T PshRpZeroType P PX pshRp H.2 }
  end.
Fixpoint pshRpZeroChainOf (p: nat) {struct p}:
  forall {m k} {PC2: PshDepsCohs2 (g X) m p k}
    {XC: DepsCohsExtension p k (pshDepsCohs (g X) PC2.(_pshDepsCohs _))}
    (PCX: PshDepsCohsExtension (g X) m PC2 XC),
  PshRpZeroChain p.+1 (mkPshDepsRestr (g X) PC2) (mkPshExtraDeps (g X) PCX)
    (mkPshRestrPaintings (g X) PCX) (rpZeroChainOf p XC) :=
  match p return forall m k (PC2: PshDepsCohs2 (g X) m p k)
    (XC: DepsCohsExtension p k (pshDepsCohs (g X) PC2.(_pshDepsCohs _)))
    (PCX: PshDepsCohsExtension (g X) m PC2 XC),
    PshRpZeroChain p.+1 (mkPshDepsRestr (g X) PC2) (mkPshExtraDeps (g X) PCX)
      (mkPshRestrPaintings (g X) PCX) (rpZeroChainOf p XC) with
  | 0 => fun m k PC2 XC PCX => (tt; fun Hq Hqp ε d => eq_refl)
  | S p => fun m k PC2 XC PCX =>
    (pshRpZeroChainOf p (AddPshCohDep (g X) m PC2 PCX);
     fun Hq Hqp ε d => eq_refl)
  end.

(** The same two readings phrased over the stage class rather than over the
    translation and presheaf bundles it computes, which is the form the
    clause at paintings is stated in. *)

Definition TrRpZeroTypeF {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  {XA: DepsRestrExtension p.+1 k F.(_frDepsA)}
  {XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB))}
  (TX: TrDepsExtension (frTr F) XA XB)
  {rpA: mkRestrPaintingTypes XA} {rpB: mkRestrPaintingTypes XB}
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (HrpA: FrtRpZeroType XA rpA) (HrpB: FrtRpZeroType XB rpB): Type :=
  forall (Hq: 0 <= k) (ε: arity)
    (d: mkFrame (mkDepsRestr (depsCohs := dcB)).(1))
    (c: (mkPaintings ((mkDepsRestr (depsCohs := dcB));
           XB)%extradepsrestr).2 d),
  trRp.2 0 Hq ε d c
  = rew <- [fun z: (mkDepsRestr (depsCohs := dcB)).(_paintings).2
                     ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 Hq ε d)
            =>
            rew [fun x: F.(_frDepsA).(_frames).2 =>
                 F.(_frDepsA).(_paintings).2 x]
                F.(_frTrRestrs).2 0 Hq ε d in
            F.(_frPaintingEqvs).2
              ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 Hq ε d) z
            = rpA.2 0 Hq ε (mkFrameEqv (proj1TrDepsRestr (frTr F)) d)
                (mkPaintingEqv (AddTrDep (frTr F) TX) d c)]
      (HrpB Hq ε d c) in
    rew <- [fun z: F.(_frDepsA).(_paintings).2
                     (F.(_frDepsA).(_restrFrames).2 0 Hq ε
                        (mkFrameEqv (proj1TrDepsRestr (frTr F)) d)) =>
            rew [fun x: F.(_frDepsA).(_frames).2 =>
                 F.(_frDepsA).(_paintings).2 x]
                F.(_frTrRestrs).2 0 Hq ε d in
            F.(_frPaintingEqvs).2
              ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 Hq ε d)
              (nth c.1 ε)
            = z]
      (HrpA Hq ε (mkFrameEqv (proj1TrDepsRestr (frTr F)) d)
         (mkPaintingEqv (AddTrDep (frTr F) TX) d c)) in
    eq_sym (trLayerEqvNth F.(_frPaintingEqvs) F.(_frTrRestrs) d c.1 ε).
Lemma trRpZeroF {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} {F: FrtDeps M HD cB}
  {XA: DepsRestrExtension p.+1 k F.(_frDepsA)}
  {XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB))}
  {TX: TrDepsExtension (frTr F) XA XB}
  {rpA: mkRestrPaintingTypes XA} {rpB: mkRestrPaintingTypes XB}
  {trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB}
  {HrpA: FrtRpZeroType XA rpA} {HrpB: FrtRpZeroType XB rpB}
  (H: TrRpZeroType (frTr F) TX trRp HrpA HrpB):
  TrRpZeroTypeF F TX trRp HrpA HrpB.
Proof.
  now exact H.
Qed.
Definition PshRpZeroTypeF {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  {XA: DepsRestrExtension p.+1 k F.(_frDepsA)}
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  {rpA: mkRestrPaintingTypes XA}
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (HrpA: FrtRpZeroType XA rpA): Type :=
  forall (ε: arity) (u: (g X).(G0) M.+1),
  pshRp.2 0 leR_O (⇓ F.(_frBound)) ε u
  = rew <- [fun z: F.(_frDepsA).(_paintings).2
                     (F.(_frDepsA).(_restrFrames).2 0 leR_O ε
                        (mkPshFrame (g X)
                           (proj1PshDepsRestr (g X) (frtPshDeps F)) u)) =>
            rew [fun x: F.(_frDepsA).(_frames).2 =>
                 F.(_frDepsA).(_paintings).2 x]
                F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ε u in
            F.(_frPshPaintings).2
              ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε u) = z]
      (HrpA leR_O ε (mkPshFrame (g X) (proj1PshDepsRestr (g X) (frtPshDeps F)) u)
         (mkPshPainting (g X) (AddPshDep (g X) M (frtPshDeps F) PX) u)) in
    eq_sym (nth_lam
      (fun ε0: arity =>
       rew [fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
           F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ε0 u in
       F.(_frPshPaintings).2 ((g X).(GFace) M p (⇓ F.(_frBound)) ε0 u)) ε).
Lemma pshRpZeroF {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} {F: FrtDeps M HD cB}
  {XA: DepsRestrExtension p.+1 k F.(_frDepsA)}
  {PX: PshDepsExtension (g X) M (frtPshDeps F) XA}
  {rpA: mkRestrPaintingTypes XA}
  {pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA}
  {HrpA: FrtRpZeroType XA rpA}
  (H: PshRpZeroType (frtPshDeps F) PX pshRp HrpA):
  PshRpZeroTypeF F PX pshRp HrpA.
Proof.
  now intros ε u; now exact (H leR_O (⇓ F.(_frBound)) ε u).
Qed.

(** The clause at paintings at one stage

    [FrtRestrPaintingType] with the entry of the painting list below the top
    replaced by its value: at the ladder that list is
    [mkFrtPaintingsOfRestr], whose entry below the top is the top entry
    stepped down along the stage's own layer equation
    ([frtPaintingsPrevEntry0] / [frtPaintingsPrevEntryS]). *)

Definition FrtRestrPaintingStepSelected {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (prev: FrtFramesPrevType F top)
  (Hpair: FrtPairLawAt F top)
  (HR: FrtRestr0At F top prev Hpair)
  (E: FrtPaintingTopType F TX PX top val
        (mkFrtFrameStep F top prev
           (fun t => mkFrtLayerOfRestr F top prev Hpair HR t)))
  (HrpB: FrtRpZeroType XB rpB): Type :=
  forall (ε: arity) (t: (g X).(G0) M.+1),
  DPathCellOver
    ((F.(_frPaintings).2 ((g X).(GFace) M (0 + p) (⇓ F.(_frBound)) ε t)
      ⊙[fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
      (sigT_map_eq
         (P := fun a: (mkDepsRestr (depsCohs := dcB)).(_frames).2 =>
                 (mkDepsRestr (depsCohs := dcB)).(_paintings).2 a)
         (Q := fun x: F.(_frDepsA).(_frames).2 =>
                 F.(_frDepsA).(_paintings).2 x)
         (f := fun a => F.(_frFrameEqvs).2 a)
         (fun a c => F.(_frPaintingEqvs).2 a c) (projT2_eq (Hpair ε t))
       • eq_sym (f_equal
           (F.(_frPaintingEqvs).2
              ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ε
                 (top t).1))
           (HrpB leR_O ε (top t).1 ((top t).2; val t)))))
     ⊙[fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
     trRp.2 0 leR_O ε (top t).1 ((top t).2; val t))
    (pshRp.2 0 leR_O (⇓ F.(_frBound)) ε t
     ⊙[fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x]
     sigT_map_eq
       (Q := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)
       (f := fun n => F.(_frDepsA).(_restrFrames).2 0 leR_O ε n)
       (fun n c => rpA.2 0 leR_O ε n c)
       (mkFrtPaintingStepDown F XA XB TX PX top val prev
          (fun t0 => mkFrtLayerOfRestr F top prev Hpair HR t0) E t)) (HR ε t).

Definition FrtRestrPaintingStepsSelected: Type :=
  forall (M: nat) (XpB0: (νGpdAt M).(prefix)) (S0: νGpdFrom M XpB0)
    (HD: Desc S0) (p k: nat) (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB) (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (HrpA: FrtRpZeroType XA rpA) (HrpB: FrtRpZeroType XB rpB)
    (HtrRp: TrRpZeroType (frTr F) TX trRp HrpA HrpB)
    (HpshRp: PshRpZeroType (frtPshDeps F) PX pshRp HrpA)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (val: forall u, mkPainting XB (top u))
    (prev: FrtFramesPrevType F top)
    (Hpair: FrtPairLawAt F top)
    (HR: FrtRestr0At F top prev Hpair)
    (E: FrtPaintingTopType F TX PX top val
          (mkFrtFrameStep F top prev
             (fun t => mkFrtLayerOfRestr F top prev Hpair HR t))),
  FrtRestrPaintingStepSelected F XA XB TX PX rpA rpB trRp pshRp top val prev Hpair
    HR E HrpB.

Lemma frtRestrPaintingStepSelectedOf: FrtRestrPaintingStepsSelected.
Proof.
  intros M XpB0 S0 HD p k dcB cB F XA XB TX PX rpA rpB trRp pshRp
    HrpA HrpB HtrRp HpshRp top val prev Hpair HR E.
  intros ε t.
  unfold DPathCellOver.
  rewrite (pshRpZeroF HpshRp ε t).
  rewrite (trRpZeroF HtrRp leR_O ε (top t).1 ((top t).2; val t)).
  rewrite (corrCancelB2
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)
    (F.(_frPaintingEqvs).2
       ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ε (top t).1))
    (HrpB leR_O ε (top t).1 ((top t).2; val t))).
  rewrite rewCorrR.
  rewrite (sigT_trans_eq_trans_r
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  rewrite (rewBaseTrans
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  rewrite (sigT_map_eq_htpy
    (Q := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)
    (f := fun n => F.(_frDepsA).(_restrFrames).2 0 leR_O ε n)
    (fun n c => rpA.2 0 leR_O ε n c) (fun n c => nth c.1 ε)
    (fun n c => HrpA leR_O ε n c)).
  rewrite (corrCancelL
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  rewrite (sigT_trans_eq_trans_r
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  apply (f_equal (fun z => z • eq_sym (HrpA leR_O ε
    (mkFrameEqv (proj1TrDepsRestr (frTr F)) (top t).1)
    (mkPaintingEqv (AddTrDep (frTr F) TX) (top t).1 ((top t).2; val t))))).
  unfold mkFrtPaintingStepDown.
  rewrite nth_dpath_sigT_fst.
  unfold mkFrtLayerOfRestr, mkFrtLayerOfNth.
  rewrite nth_dpath_lamLmapRewEq.
  unfold mkFrtResidueOfRestr.
  rewrite (convP_change
    (fun x: F.(_frDepsA).(_frames).2 => (F.(_frDepsA).(_paintings).2 x).(GDom))
    (fun d => F.(_frDepsA).(_restrFrames).2 0 leR_O ε d)).
  rewrite (corrCancelL2
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  rewrite <- (sigT_trans_eq_rew_l
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  rewrite (sigT_trans_eq_trans_r
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  rewrite (sigT_trans_eq_finish _ (F.(_frTrRestrs).2 0 leR_O ε (top t).1) _).
  rewrite (rewBaseTrans
    (P := fun x: F.(_frDepsA).(_frames).2 => F.(_frDepsA).(_paintings).2 x)).
  lazymatch goal with
  | |- @eq _ (@eq_trans ?A ?x ?y ?z ?L ?tail) _ =>
      refine (f_equal (fun h: x = y => h • tail) _)
  end.
  lazymatch goal with
  | |- context [@residueFill ?YY ?TT1 ?DD ?PP ?DDp ?rr ?phi ?pe ?y1 ?y2
      ?edge ?a ?w ?e1 ?c1 ?a2 ?v1 ?c2 ?n ?hp ?trR ?hr ?fp] =>
    now exact (@residueFill_boundary YY TT1 DD PP DDp rr phi pe y1 y2 edge
      a w e1 c1 a2 v1 c2 n hp trR hr fp)
  end.
Defined.

(** The chain at a level

    One [FrtRpStepAt] per stage, by the recursion of [mkFrtPtChain]. *)

Fixpoint mkFrtRpChain (SP: FrtRestrPaintingStepsSelected) (M: nat)
  {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (HA: RpZeroChain p.+1 XA rpA) (HB: RpZeroChain p.+1 XB rpB)
    (HT: TrRpZeroChain p.+1 (frTr F) TX trRp HA HB)
    (HP: PshRpZeroChain p.+1 (frtPshDeps F) PX pshRp HA)
    (val: forall u, mkPainting XB (descTop HD cB u))
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)),
  FrtRpChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp (descTop HD cB) val
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
    (frtSplitOfQ M HD p cB Hlen F Q).
Proof.
  destruct p; intros k dcB cB Hlen F XA XB TX PX rpA rpB trRp pshRp
    HA HB HT HP val Q E.
  -
  refine (HA.2; (HB.2; _)).
  now exact (SP M XpB0 S0 HD 0 k dcB cB F XA XB TX PX rpA rpB trRp pshRp
    HA.2 HB.2 HT.2 HP.2 (descTop HD cB) val (tt; fun t => hunit_ext tt _)
    (fun ε t => descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t)
    (fun ε t => Q 0 leR_O (⇓ F.(_frBound)) ε t) E).
  -
  unshelve refine (_; (HA.2; (HB.2; _))).
  +
  now exact (mkFrtRpChain SP M XpB0 S0 HD p k.+1 _ (DepsCohsChainCons cB)
    (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F)
    (F.(_frDepsA); XA)%extradepsrestr
    (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
    (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
    rpA.1 rpB.1 trRp.1 pshRp.1 HA.1 HB.1 HT.1 HP.1
    (fun u => ((descTop HD cB u).2; val u)) Q.1
    (fun t => mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
       ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
           (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
           (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
       (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
          ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
              (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
              (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
          (fun ε t1 =>
             descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
          (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
       E t)).
  +
  intros ε t.
  now exact (SP M XpB0 S0 HD p.+1 k dcB cB F XA XB TX PX rpA rpB trRp pshRp
    HA.2 HB.2 HT.2 HP.2 (descTop HD cB) val
    ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
        (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
        (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
    (fun ε0 t0 => descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε0 t0)
    (fun ε0 t0 => Q.2 0 leR_O (⇓ F.(_frBound)) ε0 t0) E ε t).
Defined.

(** The four chains of dimension-[0] readings at a level: the two [νGpd]
    sides at any level, the translation side at a level whose tower is the
    translation tower's, and the presheaf side at a successor level, where the
    presheaf's own chain reduces. *)

Definition rpAChainOf (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt) (Q: FgRestrData m W frt frp):
  RpZeroChain m.+1 (towerFrtDepsCohsOf m W frt frp Q).(_fcXA)
    (towerFrtDepsCohsOf m W frt frp Q).(_fcRpA) :=
  rpZeroChainOf m (TopCohDep
    (mkPshFiller (g X) (towerPshDeps (g X) (pshTw m)))).
Definition rpBChainOf (m: nat) (W: FgTower m) (frt: FgFrt m W)
  (frp: FgFrp m W frt) (Q: FgRestrData m W frt frp):
  RpZeroChain m.+1 (towerFrtDepsCohsOf m W frt frp Q).(_fcXB)
    (towerFrtDepsCohsOf m W frt frp Q).(_fcRpB) :=
  rpZeroChainOf m (TopCohDep (this (next ((νGpdPack m X).2)))).
Definition fgTowerPrev (m: nat) (P: FgPrefix m):
  TrTower m (pshApprox (g X) m.+1).1 ((νGpdPack m.+1 X).1).1 :=
  (trAt m (pshApprox (g X) m.+1).1 ((νGpdPack m.+1 X).1).1).(trData) P.1.
Definition trRpChainOf (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp):
  TrRpZeroChain m.+1 (frTr (fgDeps m (fgTowerAt m P) frt frp))
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTX)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTrRp)
    (rpAChainOf m (fgTowerAt m P) frt frp Q)
    (rpBChainOf m (fgTowerAt m P) frt frp Q) :=
  trRpZeroChainOf m (TopTrCohDep (TC := towerCohs (fgTowerPrev m P) P.2)
    (fgThisOfFrames (fgTowerAt m P) (pshTw m) (descAt m) frt frp
       (fgFrtOf m (fgTowerAt m P) frt frp Q))).
Definition pshRpChainOf (m: nat) (P: FgPrefix m.+1)
  (frt: FgFrt m.+1 (fgTowerAt m.+1 P))
  (frp: FgFrp m.+1 (fgTowerAt m.+1 P) frt)
  (Q: FgRestrData m.+1 (fgTowerAt m.+1 P) frt frp):
  PshRpZeroChain m.+2
    (frtPshDeps (fgDeps m.+1 (fgTowerAt m.+1 P) frt frp))
    (towerFrtDepsCohsOf m.+1 (fgTowerAt m.+1 P) frt frp Q).(_fcPX)
    (towerFrtDepsCohsOf m.+1 (fgTowerAt m.+1 P) frt frp Q).(_fcPshRp)
    (rpAChainOf m.+1 (fgTowerAt m.+1 P) frt frp Q) :=
  pshRpZeroChainOf m.+1 (@TopPshCohDep (g X) m m.+1
    (towerPshDepsCohs2 (g X) (pshTw m) (pshRp m) (pshRc m))).
Definition fgRpChainOfChains (SP: FrtRestrPaintingStepsSelected) (m: nat)
  (P: FgPrefix m) (frt: FgFrt m (fgTowerAt m P))
  (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp)
  (HA: RpZeroChain m.+1
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcXA)
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcRpA))
  (HB: RpZeroChain m.+1
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcXB)
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcRpB))
  (HT: TrRpZeroChain m.+1 (frTr (fgDeps m (fgTowerAt m P) frt frp))
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTX)
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTrRp) HA HB)
  (HP: PshRpZeroChain m.+1 (frtPshDeps (fgDeps m (fgTowerAt m P) frt frp))
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPX)
         (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPshRp) HA):
  FgRpChain m P frt frp Q.
Proof.
  now exact (mkFrtRpChain SP m (descAt m) m DepsCohsChainNil
    (descChainLen (descAt m)) (fgDeps m (fgTowerAt m P) frt frp)
    _ _ _ _ _ _ _ _ HA HB HT HP _ Q _).
Defined.
Definition rpsOf (SP: FrtRestrPaintingStepsSelected): FgRpChainStepType :=
  fun m s =>
    fgRpChainOfChains SP m.+1 (fgPrefixNext m s) (fgFrtNextOf m s)
      (fgFrpNextOf m s) (fgQNext m s)
      (rpAChainOf m.+1 (fgTowerAt m.+1 (fgPrefixNext m s)) (fgFrtNextOf m s)
         (fgFrpNextOf m s) (fgQNext m s))
      (rpBChainOf m.+1 (fgTowerAt m.+1 (fgPrefixNext m s)) (fgFrtNextOf m s)
         (fgFrpNextOf m s) (fgQNext m s))
      (trRpChainOf m.+1 (fgPrefixNext m s) (fgFrtNextOf m s)
         (fgFrpNextOf m s) (fgQNext m s))
      (pshRpChainOf m (fgPrefixNext m s) (fgFrtNextOf m s)
         (fgFrpNextOf m s) (fgQNext m s)).

(** The provider of the level step *)

Definition fgRpStep: FgRpChainStepType := rpsOf frtRestrPaintingStepSelectedOf.

(** The restriction-painting chain at level [0] has one entry, whose
    presheaf clause holds by computation at the bottom of the tower. *)

Definition pshRpChain0:
  PshRpZeroChain 1
    (frtPshDeps (fgDeps 0 (fgTowerAt 0 ((tt; fgThis0): FgPrefix 0))
       frt0List frp0List))
    (towerFrtDepsCohsOf 0 (fgTowerAt 0 ((tt; fgThis0): FgPrefix 0))
       frt0List frp0List frtRestr0).(_fcPX)
    (towerFrtDepsCohsOf 0 (fgTowerAt 0 ((tt; fgThis0): FgPrefix 0))
       frt0List frp0List frtRestr0).(_fcPshRp)
    (rpAChainOf 0 (fgTowerAt 0 ((tt; fgThis0): FgPrefix 0)) frt0List frp0List
       frtRestr0)
  := (tt; fun Hq Hqp ε u => eq_refl).

Definition fgRpBase: FgRpChainBaseType :=
  fgRpChainOfChains frtRestrPaintingStepSelectedOf 0 ((tt; fgThis0): FgPrefix 0)
    frt0List frp0List frtRestr0
    (rpAChainOf 0 (fgTowerAt 0 ((tt; fgThis0): FgPrefix 0)) frt0List frp0List
       frtRestr0)
    (rpBChainOf 0 (fgTowerAt 0 ((tt; fgThis0): FgPrefix 0)) frt0List frp0List
       frtRestr0)
    (trRpChainOf 0 ((tt; fgThis0): FgPrefix 0) frt0List frp0List frtRestr0)
    pshRpChain0.

Lemma pshRestrPaintingSuccTotal (ps: νGpdPresentation arity)
  {m p k} (PC: PshDepsCohs2 ps m p.+1 k)
  {XC: DepsCohsExtension p.+1 k (pshDepsCohs ps PC.(_pshDepsCohs _))}
  (PCX: PshDepsCohsExtension ps m PC XC)
  (q: nat) (Hq: q.+1 <= k.+1) (Hdim: q.+1 + p <= m.+1)
  (ε: arity) (d: ps.(G0) m.+2):
  (= (mkPshRestrFrames ps
        (proj1PshDepsCohs ps PC.(_pshDepsCohs _)) PC.(_pshRestrCohs _).1).2
        q.+1 Hq Hdim ε d;
     mkPshRestrPainting ps (AddPshCohDep ps m PC PCX) q.+1 Hq Hdim ε d) =
  f_equal unassoc
    (f_equal (fun z =>
       (mkPshFrame ps PC.(_pshDepsCohs _).(_pshDeps _) z;
        mkPshPainting ps PC.(_pshDepsCohs _).(_pshExtraDeps _) z))
       (pshFaceDimIrr ps (plus_n_Sm q p)
         (Hq := Hdim) (Hq' := leR_eq (plus_n_Sm q p) Hdim) ε d)
     • (= (mkPshRestrFrames ps PC.(_pshDepsCohs _) PC.(_pshRestrCohs _)).2
             q (⇓ Hq) (leR_eq (plus_n_Sm q p) Hdim) ε d;
          mkPshRestrPainting ps PCX q (⇓ Hq)
            (leR_eq (plus_n_Sm q p) Hdim) ε d)).
Proof.
  cbn [mkPshRestrPainting].
  lazymatch goal with
  | |- @eq _ (@eq_existT_curried _ _ _ _ _ _ _
         (@eq_existT_curried_dep ?A ?x ?L ?Cc ?y ?a ?u ?c ?v ?cv ?b ?h)) _ =>
    refine (eq_trans (eq_sym (@f_equal_unassoc_curried A L Cc x y a u v b c cv h)) _)
  end.
  apply f_equal.
  lazymatch goal with
  | |- @eq _ (@eq_existT_curried ?A ?P ?x ?y ?v ?w ?e
         (@path_reindex_source _ _ _ _
           (@rew_align_dep _ _ _ ?xp _ _ ?ep ?b _ ?vp ?Hv ?Hc) ?h)) _ =>
    refine (eq_trans (@totalPathAlignmentStrict A P x xp y e ep b v vp w Hv Hc h) _)
  end.
  refine (f_equal (fun rr => rr • _) _).
  now exact (@totalPathSectionMap _ _
    (fun a => mkPainting PC.(_pshDepsCohs _).(_pExtraDeps _) a)
    (mkPshFrame ps PC.(_pshDepsCohs _).(_pshDeps _))
    (mkPshPainting ps PC.(_pshDepsCohs _).(_pshExtraDeps _)) _ _
    (pshFaceDimIrr ps (plus_n_Sm q p) (Hq := Hdim)
      (Hq' := leR_eq (plus_n_Sm q p) Hdim) ε d)).
Defined.

Lemma restrCellCohShift {p k} (dc3: DepsCohs3 p.+1 k)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 (proj1DepsCohs3 dc3))).(_depsCohs))).(1))
  (C: (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 (proj1DepsCohs3 dc3))).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 (proj1DepsCohs3 dc3))).(_extraDepsCohs))).2 D):
  restrCellCoh (proj1DepsCohs3 dc3) Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D C
  = f_equal unassoc (restrCellCoh dc3 Q HQ R HR ε ω (D; C.1) C.2).
Proof.
  unfold restrCellCoh.
  now refine (eq_sym (f_equal_unassoc_curried
    ((mkDepsCohs (proj1DepsCohs2 dc3.(_depsCohs2))).(_cohs).2 Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω D)
    (mkCohLayer dc3.(_depsCohs2).(_cohPaintings).2 dc3.(_depsCohs2).(_coh2Frames).2 Q HQ R HR ε ω D C.1)
    (mkCohPainting dc3.(_extraDepsCohs2) Q HQ R HR ε ω (D; C.1) C.2))).
Defined.

(** The cell a stage sees, one stage below its extension. *)
Definition CellBelow {p k} (dc3: DepsCohs3 p k): Type :=
  { D: mkFrame (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1) &T
    (mkPaintings (mkDepsRestr (depsCohs :=
        (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
        mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D }.

Definition assocC {p k} {dc3: DepsCohs3 p.+1 k}
  (w: CellBelow (proj1DepsCohs3 dc3)): CellBelow dc3 :=
  ((w.1; w.2.1); w.2.2).

Lemma faceAtCohUpShift {P K} {dc3Top: DepsCohs3 P K}
  (e0: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p.+1 k}
  (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity)
  (w: CellBelow (proj1DepsCohs3 dc3)):
  faceAtCohUp e0 (DepsCohs3ChainCons a) Q.+1 (⇑ HQ) R.+1 (⇑ HR) ε ω w.1 w.2
  = faceAtCohUp e0 a Q HQ R HR ε ω (assocC w).1 (assocC w).2.
Proof.
  rewrite 2 faceAtCohUpConj.
  apply conjShiftM.
  - now exact (f_equal_compose unassoc
      (fun w0 => faceAt (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)) Q.+1 (⇑ HQ) ε w0.1 w0.2)
      (deepCellFaceAtUp e0 a R (HR ↕ ↑ HQ) ω (assocC w).1 (assocC w).2)).
  - refine (eq_trans (f_equal (fun z => f_equal (faceRebuild (DepsCohs3ChainCons a)) z)
      (restrCellCohShift dc3 Q HQ R HR ε ω w.1 w.2)) _).
    now exact (f_equal_compose unassoc (faceRebuild (DepsCohs3ChainCons a))
      (restrCellCoh dc3 Q HQ R HR ε ω (assocC w).1 (assocC w).2)).
  - now exact (f_equal_compose unassoc
      (fun w0 => faceAt (cohs3ChainDepsCohs2 (DepsCohs3ChainCons a)) R.+1 (⇑ HR ↕ ⇑ HQ) ω w0.1 w0.2)
      (deepCellFaceAtUp e0 a Q.+1 (⇑ HQ) ε (assocC w).1 (assocC w).2)).
Defined.

(** The two endpoints of the stored exchange, as functions of the cell. *)
Definition cellL {P K} {dc3Top: DepsCohs3 P K} (e0: DepsCohs3Extension P K dc3Top)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity) (w: CellBelow dc3) :=
  deepCell (cohs3ChainDepsCohs2 a)
    (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) R (HR ↕ ↑ HQ) ω w.1 w.2).

Definition cellR {P K} {dc3Top: DepsCohs3 P K} (e0: DepsCohs3Extension P K dc3Top)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (Q: nat) (HQ: Q <= k) (R: nat) (HR: R <= Q) (ε ω: arity) (w: CellBelow dc3) :=
  deepCell (cohs3ChainDepsCohs2 a)
    (faceAt (cohs3ChainDepsCohs2 (chainUp1 e0 a)) Q.+1 (⇑ HQ) ε w.1 w.2).

Lemma cohs3ChainLenCompose {P K} {dc3Top: DepsCohs3 P K}
  {pM kM} {dc3M: DepsCohs3 pM kM} (aH: DepsCohs3Chain dc3Top dc3M)
  {p k} {dc3: DepsCohs3 p k} (aL: DepsCohs3Chain dc3M dc3):
  cohs3ChainLen (cohs3ChainCompose aH aL) = cohs3ChainLen aH + cohs3ChainLen aL.
Proof.
  induction aL; cbn.
  - now rewrite <- plus_n_O.
  - now rewrite IHaL, <- plus_n_Sm.
Defined.

(** Splitting a chain at a prescribed length from the bottom. *)
Definition Split {P K} {dc3Top: DepsCohs3 P K} {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain dc3Top dc3) (n: nat): Type :=
  { pM: nat &T { kM: nat &T { dc3M: DepsCohs3 pM kM &T
    { aH: DepsCohs3Chain dc3Top dc3M &T { aL: DepsCohs3Chain dc3M dc3 &T
      { _: cohs3ChainCompose aH aL = a &T cohs3ChainLen aL = n } } } } } }.

Fixpoint chainSplit (n: nat) {P K} {dc3Top: DepsCohs3 P K} {p k}
  {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3) {struct n}:
  n <= cohs3ChainLen a -> Split a n.
Proof.
  destruct n as [|n]; intro H.
  - now exact (p; (k; (dc3; (a; (DepsCohs3ChainNil; (eq_refl; eq_refl)))))).
  - destruct a as [|p' k' dc3' a'].
    + now destruct (leR_O_contra H).
    + destruct (chainSplit n _ _ _ _ _ _ a' (⇓ H))
        as (pM & kM & dc3M & aH & aL & Heq & Hn).
      now exact (pM; (kM; (dc3M; (aH; (DepsCohs3ChainCons aL;
        (f_equal DepsCohs3ChainCons Heq; f_equal S Hn)))))).
Defined.

(** The stage's coherence data with the [B]-side generated from a
    [DepsCohs2]: the [B]-side extension, restriction paintings and frame
    coherences are the fields of [mkDepsCohs dc2], so the chain one level
    up lands at [mkDepsCohs dc2] and the identification of the two chains'
    frame readings is canonical. *)

Definition mkFrtDepsCohsGen {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dc2: DepsCohs2 p k}
  (c: DepsCohs2Chain (νDepsCohs2At S0) dc2)
  (F: FrtDeps M HD (cohs2ChainDepsCohs c))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc2).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
           (mkDepsCohs dc2).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA (mkDepsCohs dc2).(_extraDeps) TX
             rpA (mkDepsCohs dc2).(_restrPaintings) trRp cohsA
             (mkDepsCohs dc2).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA)):
  FrtDepsCohs M HD (cohs2ChainDepsCohs c) := {|
  _fcF := F; _fcXA := XA; _fcXB := (mkDepsCohs dc2).(_extraDeps); _fcTX := TX;
  _fcPX := PX; _fcRpA := rpA; _fcRpB := (mkDepsCohs dc2).(_restrPaintings);
  _fcTrRp := trRp; _fcPshRp := pshRp; _fcCohsA := cohsA;
  _fcCohsB := (mkDepsCohs dc2).(_cohs); _fcTrCohs := trCohs;
  _fcPshCohs := pshCohs |}.

(** The chain one level up a stage reads through: the base chain of the lift
    of the upper part of the descent chain, which lands at [mkDepsCohs] of the
    [DepsCohs2] that part lands on. *)

Definition frtChainUp {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {p k} {dc3M: DepsCohs3 p k} (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M):
  DepsCohsChain (νDepsCohsAt (next S0)) (mkDepsCohs dc3M.(_depsCohs2)) :=
  cohs2ChainDepsCohs (cohs3ChainDepsCohs2 (cohs3ChainUp (νExt3At S0) aH)).

(** The frame chain one level up the base chain induces is the one the lifted
    chain induces through its extensions. *)

Fixpoint chainNextUpEq {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {p k} {dc3M: DepsCohs3 p k} (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M):
  cohsChainNext (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))
  = extChainDeps (cohsChainExt (frtChainUp aH)) :=
  match aH with
  | DepsCohs3ChainNil => eq_refl
  | DepsCohs3ChainCons aH' => f_equal DepsChainCons (chainNextUpEq aH')
  end.

Definition frtTopAlignU {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) {p k} {dc3M: DepsCohs3 p k}
  (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M) (t: (g X).(G0) M.+1):
  descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) t
  = getFrame (extChainDeps (cohsChainExt (frtChainUp aH)))
      (descCells (DescS HD) t) :=
  f_equal (fun ch => getFrame ch (descCells (DescS HD) t)) (chainNextUpEq aH).

Definition frtPairLawAlignU {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) {p k} {dc3M: DepsCohs3 p k}
  (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
  (Hlen: cohs3ChainLen (descChain HD).2
         = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) + p)%nat)
  (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))):
  FrtPairLawAt F (fun t => getFrame (extChainDeps (cohsChainExt (frtChainUp aH)))
    (descCells (DescS HD) t)) :=
  fun ε t => descCellPairRestrAt HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) p
      (⇓ F.(_frBound)) Hlen ε t
    • f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ε) (frtTopAlignU HD aH t).

(** The dimension-[0] reading of generated restriction paintings. *)

Definition frtRpZeroGen {p k} (dc2: DepsCohs2 p k):
  FrtRpZeroType (mkDepsCohs dc2).(_extraDeps) (mkDepsCohs dc2).(_restrPaintings) :=
  fun Hq ζ d cc => eq_refl.

Section LadderSqU.
Context {M: nat} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0} (HD: Desc S0)
  {p k: nat} {dc3M: DepsCohs3 p k} (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
  (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX rpA
     (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp cohsA (mkDepsCohs dc3M.(_depsCohs2)).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA))
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) + p)%nat)
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen (frtChainUp aH) + p.+1)%nat)
  (frames: FrtFramesNextType (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs) (frtChainUp aH))
  (paintings: FrtPaintingsNextType (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs) (frtChainUp aH) frames).
Let FCgen := mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs.
(** Reading frame and painting comparisons along a chain. *)

Lemma faceDeepAsνFaceZero {P0 K0: nat} {dc2Top: DepsCohs2 P0 K0} {p0 k0: nat} {dc2: DepsCohs2 p0 k0}
  (c: DepsCohs2Chain dc2Top dc2) (Hj: 0 <= k0)
  (H: cohs2ChainLen c = (cohsChainLen (cohs2ChainDepsCohs c) + 0)%nat) (ε0: arity)
  (d: mkFrame (mkDepsCohs dc2Top).(_deps)) (Q: mkPainting (mkDepsCohs dc2Top).(_extraDeps) d):
  faceDeepAsνFace c 0 Hj (cohs2ChainDepsCohs c) H ε0 d Q
  = eq_sym (f_equal (fun z: {D: mkFrame dc2.(_depsCohs).(_deps) &T mkPainting dc2.(_depsCohs).(_extraDeps) D} =>
        getPainting (cohsChainExt (cohs2ChainDepsCohs c)) z.1 z.2)
      (f_equal (fun x: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))) =>
         ((mkRestrFrame 0 leR_O ε0 x.1; nth x.2 ε0)
          : {D: mkFrame dc2.(_depsCohs).(_deps) &T mkPainting dc2.(_depsCohs).(_extraDeps) D}))
        (getFrameDeepCell c (d; Q)))).
Proof.
  destruct c; cbn.
  -
  now reflexivity.
  -
  unfold faceDeepZero, νFacePackIrr.
  rewrite (dcPackUIP (dcPackEq _ _ _) eq_refl).
  now reflexivity.
Defined.

Lemma getFrameDeepCellFst {P0 K0: nat} {dc2Top: DepsCohs2 P0 K0} {p0 k0: nat} {dc2: DepsCohs2 p0 k0}
  (c: DepsCohs2Chain dc2Top dc2)
  (z: {d: mkFrame (mkDepsCohs dc2Top).(_deps) &T mkPainting (mkDepsCohs dc2Top).(_extraDeps) d}):
  f_equal (fun x => x.1) (getFrameDeepCell c z) = eq_refl.
Proof.
  now reflexivity.
Defined.

Lemma deepCellRebuildFrame {p' k'} {dc3: DepsCohs3 p' k'} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (D: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(1))
  (C: (mkPaintings ((mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))); mkExtraDeps dc3.(_depsCohs2).(_extraDepsCohs))%extradepsrestr).2 D):
  getFrameDeepCell (cohs3ChainDepsCohs2 a) (getPainting (cohsChainExt (frtChainUp a)) (D; C.1) C.2)
  • f_equal (fun w => ((w.1; w.2.1) : mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))))
      (deepCellRebuildUp (νExt3At S0) a (D; C))
  = f_equal (fun ch => getFrame ch (getPainting (cohsChainExt (frtChainUp a)) (D; C.1) C.2).1) (chainNextUpEq a)
    • projT1_eq (chainPaintingGetPainting (cohsChainExt (frtChainUp a)) (D; C.1) C.2).
Proof.
  revert D C.
  induction a as [|p1 k1 dc1 a IH]; intros D C.
  -
  now reflexivity.
  -
  cbn [cohs3ChainDepsCohs2 cohs3ChainUp frtChainUp chainNextUpEq deepCellRebuildUp getPainting cohsChainExt].
  cbn [getFrameDeepCell].
  rewrite eq_trans_refl_l.
  assert (dcruCons: deepCellRebuildUp (νExt3At S0) (DepsCohs3ChainCons a) (D; C)
    = f_equal (fun w: {D0: mkFrame (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs))).(1) &T (mkPaintings (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs)); mkExtraDeps dc1.(_depsCohs2).(_extraDepsCohs))).2 D0} =>
        ((w.1.1; (w.1.2; w.2)) : {D0: mkFrame (mkDepsRestr (depsCohs := (proj1DepsCohs3 dc1).(_depsCohs2).(_depsCohs))).(1) &T (mkPaintings (mkDepsRestr (depsCohs := (proj1DepsCohs3 dc1).(_depsCohs2).(_depsCohs)); mkExtraDeps (proj1DepsCohs3 dc1).(_depsCohs2).(_extraDepsCohs))).2 D0}))
        (deepCellRebuildUp (νExt3At S0) a ((D; C.1); C.2))).
  {
    now reflexivity.
  }
  rewrite dcruCons.
  rewrite (chainPaintingGetPaintingCons (cohsChainExt (frtChainUp a)) (D; C.1) C.2).
  pose (aRe := fun w: {D0: mkFrame (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs))).(1) &T (mkPaintings (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs)); mkExtraDeps dc1.(_depsCohs2).(_extraDepsCohs))).2 D0} =>
    ((w.1; w.2.1) : mkFrame (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs))))).
  pose proof (IH (D; C.1) C.2) as IHi.
  change (deepCellRebuildUp (νExt3At S0) a ((D; C.1); C.2)) with (deepCellRebuildUp (νExt3At S0) a ((D; C.1); C.2)) in *.
  pose proof (f_equal (fun e: (_: mkFrame (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs)))) = _ => f_equal (fun x: mkFrame (mkDepsRestr (depsCohs := dc1.(_depsCohs2).(_depsCohs))) => x.1) e) IHi) as J.
  cbv beta in J.
  rewrite 2 eq_trans_map_distr in J.
  rewrite (getFrameDeepCellFst (cohs3ChainDepsCohs2 a)) in J.
  rewrite eq_trans_refl_l in J.
  unfold projT1_eq in J |- *.
  Unset Keyed Unification.
  match goal with |- f_equal ?al (f_equal ?ga ?xd) = _ =>
    match type of J with f_equal ?pp (f_equal ?ar _) = _ =>
      assert (HL: f_equal al (f_equal ga xd) = f_equal pp (f_equal ar xd)) by
        now exact (eq_trans (@f_equal_compose _ _ _ _ _ ga al xd)
                        (eq_sym (@f_equal_compose _ _ _ _ _ ar pp xd))) end end.
  match goal with |- _ = f_equal ?rc (f_equal ?cc ?xn) • _ =>
    match type of J with _ = f_equal ?pp (f_equal ?ra _) • _ =>
      assert (HN: f_equal rc (f_equal cc xn) = f_equal pp (f_equal ra xn)) by
        now exact (eq_trans (@f_equal_compose _ _ _ _ _ cc rc xn)
                        (eq_sym (@f_equal_compose _ _ _ _ _ ra pp xn))) end end.
  unfold projT1_eq in J |- *.
  match goal with |- _ = _ • f_equal ?bp (f_equal ?be ?xc) =>
    match type of J with _ = _ • f_equal ?pp (f_equal ?pa _) =>
      assert (HC: f_equal bp (f_equal be xc) = f_equal pp (f_equal pa xc)) by
        now exact (eq_trans (@f_equal_compose _ _ _ _ _ be bp xc)
                        (eq_sym (@f_equal_compose _ _ _ _ _ pa pp xc))) end end.
  Unset Keyed Unification.
  now exact (eq_trans HL (eq_trans J (f_equal2 (fun p q => p • q) (eq_sym HN) (eq_sym HC)))).
Defined.

Set Keyed Unification.

Lemma frtPairSqLadderU:
  FrtPairSqAt FCgen (frtChainUp aH) Hlen' frames paintings (frtPairLawAlignU HD aH Hlen F) (frtRpZeroGen dc3M.(_depsCohs2)).
Proof.
  intros Hq Hqp ε ω t.
  unfold frtPairLawAlignU, frtRpZeroGen, frtPairSqExchange, frtPairLawPrev.
  cbn [descQcells descQcellsPairedAt descQcellsPaired].
  rewrite (descCellPairRestrAtAsFace HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) p (⇓ F.(_frBound)) Hlen ω ((g X).(GFace) M.+1 (0 + p.+1) Hqp ε t)).
  rewrite (descCellPairRestrAtAsFace HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) p (⇓ F.(_frBound)) Hlen ε ((g X).(GFace) M.+1 p (leR_add_l 0 ↕ ↑ (⇓ leR_add_shift Hqp)) ω t)).
  rewrite (descCellPairRestrAtAsFace (DescS HD) (DepsCohsChainCons (frtChainUp aH)) p (⇓ (proj1FrtDeps (mkFrtDepsOf FCgen (frtChainUp aH) frames paintings)).(_frBound)) (Hlen' • eq_sym (plus_n_Sm (cohsChainLen (frtChainUp aH)) p)) ω t).
  pose (cB := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)).
  pose (cB' := frtChainUp aH).
  pose (Cp := fun w: νTotal S0 =>
    ((getFrame (extChainDeps (cohsChainExt cB)) w.1; chainPainting (cohsChainExt cB) w.1 w.2)
     : {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D})).
  pose (Cw := fun w: νTotal (next S0) =>
    ((getFrame (extChainDeps (cohsChainExt (DepsCohsChainCons cB'))) w.1;
      chainPainting (cohsChainExt (DepsCohsChainCons cB')) w.1 w.2)
     : {D: mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))).(1) &T
          (mkPaintings ((mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))); FCgen.(_fcXB))%extradepsrestr).2 D})).
  pose (gfB := fun z: gF0 S0 1 => getFrame (cohsChainNext cB) z.1).
  pose (gf' := fun z: gF0 S0 1 => getFrame (extChainDeps (cohsChainExt cB')) z.1).
  pose (Hal := fun z: gF0 S0 1 => f_equal (fun ch => getFrame ch z.1) (chainNextUpEq aH)).
  pose proof (path_suffix_solve (eq_sym
    (descCellFaceFrameAsPairFst (DescS HD) cB' p.+1 Hqp Hlen' ε t))) as DQeq.
  rewrite eq_sym_involutive in DQeq.
  rewrite DQeq.
  change (f_equal (frtCellPair HD cB) ((g X).(GFaceCoh) M (0 + p) (⇓ leR_add_shift Hqp) p (leR_add_l 0) ε ω t))
    with (f_equal (fun u => Cp (descCell HD u)) ((g X).(GFaceCoh) M (0 + p) (⇓ leR_add_shift Hqp) p (leR_add_l 0) ε ω t)).
  rewrite <- (f_equal_compose (descCell HD) Cp).
  refine (sqAssembleGen (descCell HD) Cp
    (gFaceC S0 (descChain HD).2 0 p (⇓ F.(_frBound)) ω)
    (gFaceC S0 (descChain HD).2 0 p (⇓ F.(_frBound)) ε)
    (fun z: gF0 S0 1 => νFace cB ω z.1) (fun z: gF0 S0 1 => νFace cB ε z.1)
    gfB gf' (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ω) (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ε)
    Cw (frtPairRestrPaintingAt FCgen ε) (fun y => eq_refl)
    (fun y => gFaceCAsνFace S0 (descChain HD).2 p (⇓ F.(_frBound)) cB Hlen ω y)
    (fun y => gFaceCAsνFace S0 (descChain HD).2 p (⇓ F.(_frBound)) cB Hlen ε y)
    (fun y => chainPaintingGetPainting (cohsChainExt cB)
       (mkRestrFrame 0 leR_O ω (getFrame (cohsChainNext cB) y.1).1)
       (nth (getFrame (cohsChainNext cB) y.1).2 ω))
    (fun y => chainPaintingGetPainting (cohsChainExt cB)
       (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext cB) y.1).1)
       (nth (getFrame (cohsChainNext cB) y.1).2 ε))
    Hal
    ((g X).(GFaceCoh) M (0 + p) (⇓ leR_add_shift Hqp) p (leR_add_l 0) ε ω t)
    (descCellFace (DescS HD) p.+1 Hqp Hqp ε t)
    (descCellFace (DescS HD) p _ _ ω t)
    (descCellFace HD p (⇓ F.(_frBound)) (⇓ F.(_frBound)) ω ((g X).(GFace) M.+1 (0 + p.+1) Hqp ε t))
    (descCellFace HD p (⇓ F.(_frBound)) (⇓ F.(_frBound)) ε ((g X).(GFace) M.+1 p (leR_add_l 0 ↕ ↑ (⇓ leR_add_shift Hqp)) ω t))
    (gFaceCohC S0 (descChain HD).2 0 p (⇓ F.(_frBound)) p leR_refl ε ω (descCell (DescS (DescS HD)) t))
    (descCellFaceSq HD p (⇓ F.(_frBound)) p leR_refl ε ω t)
    (f_equal gf' (gFaceCAsνFace (next S0) (descChain (DescS HD)).2 p.+1 Hqp cB' Hlen' ε (descCell (DescS (DescS HD)) t))
     • projT1_eq (chainPaintingGetPainting (cohsChainExt cB')
         (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext cB') (descCells (DescS (DescS HD)) t)).1)
         (nth (getFrame (cohsChainNext cB') (descCells (DescS (DescS HD)) t)).2 ε)))
    (gFaceCAsνFace (next S0) (descChain (DescS HD)).2 p _ (DepsCohsChainCons cB')
       (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p)) ω (descCell (DescS (DescS HD)) t))
    (chainPaintingGetPainting (cohsChainExt (DepsCohsChainCons cB'))
       (mkRestrFrame 0 leR_O ω (getFrame (cohsChainNext (DepsCohsChainCons cB')) (descCells (DescS (DescS HD)) t)).1)
       (nth (getFrame (cohsChainNext (DepsCohsChainCons cB')) (descCells (DescS (DescS HD)) t)).2 ω))
    _ _).
  assert (EX: forall (pb kb: nat) (dc3bot: DepsCohs3 pb kb) (a: DepsCohs3Chain (νDepsCohs3At S0) dc3bot)
    (Hlen0: cohs3ChainLen a = (cohsChainLen cB + p)%nat)
    (Hlen'0: cohs3ChainLen (chainUp1 (νExt3At S0) a) = (cohsChainLen cB' + p.+1)%nat)
    (Hp0: p <= 0 + kb) (Hqp0: p.+1 <= 0 + kb.+1) (Hpw: p <= 0 + kb.+1) (T: gF0 S0 2),
    f_equal Cp (gFaceCohC S0 a 0 p Hp0 p leR_refl ε ω (T))
    • (f_equal Cp (gFaceCAsνFace S0 a p Hp0 cB Hlen0 ω (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p.+1 Hqp0 ε (T)))
       • (chainPaintingGetPainting (cohsChainExt cB) (mkRestrFrame 0 leR_O ω (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p.+1 Hqp0 ε (T)).1).1)
            (nth (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p.+1 Hqp0 ε (T)).1).2 ω)
          • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ω) (Hal (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p.+1 Hqp0 ε (T)))
             • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ω)
                  (f_equal gf' (gFaceCAsνFace (next S0) (chainUp1 (νExt3At S0) a) p.+1 Hqp0 cB' Hlen'0 ε (T))
                   • projT1_eq
                       (chainPaintingGetPainting (cohsChainExt cB') (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext cB') (T.1)).1)
                          (nth (getFrame (cohsChainNext cB') (T.1)).2 ε)))
                • (=eq_sym (FCgen.(_fcCohsB).2 0 Hq 0 leR_O ε ω ((getFrame (cohsChainNext cB') T.1)).1.1);
                  rewSwapSym (fun D : mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) => mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D)
                    (FCgen.(_fcCohsB).2 0 Hq 0 leR_O ε ω ((getFrame (cohsChainNext cB') T.1)).1.1)
                    (nth_lmap
                       (fun (ω0 : arity)
                          (c : (mkPaintings ((frtDcB FCgen).(_deps);(frtDcB FCgen).(_extraDeps))).2
                                 (((mkCohFrameTypesAndRestrFrames (frtDcB FCgen).(_restrPaintings).1).(RestrFramesDef) (frtDcB FCgen).(_cohs).1).2 0 (leR_O ↕ ↑ Hq) ω0
                                    ((getFrame (cohsChainNext cB') T.1)).1.1)) =>
                        rew [fun x : (frtDcB FCgen).(_deps).(_frames).2 => (frtDcB FCgen).(_deps).(_paintings).2 x]
                            (frtDcB FCgen).(_cohs).2 0 Hq 0 leR_O ε ω0 ((getFrame (cohsChainNext cB') T.1)).1.1 in
                        (frtDcB FCgen).(_restrPaintings).2 0 Hq ε
                          (((mkCohFrameTypesAndRestrFrames (frtDcB FCgen).(_restrPaintings).1).(RestrFramesDef) (frtDcB FCgen).(_cohs).1).2 0 (leR_O ↕ ↑ Hq) ω0
                             ((getFrame (cohsChainNext cB') T.1)).1.1)
                          c)
                       ((getFrame (cohsChainNext cB') T.1)).1.2 ω)))))) =
    f_equal Cp
      (gFaceCAsνFace S0 a p Hp0 cB Hlen0 ε
         (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p Hpw ω (T)))
    • (chainPaintingGetPainting (cohsChainExt cB)
         (mkRestrFrame 0 leR_O ε
            (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p Hpw ω (T)).1).1)
         (nth (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p Hpw ω (T)).1).2 ε)
       • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ε)
            (Hal (gFaceC (next S0) (chainUp1 (νExt3At S0) a) 0 p Hpw ω (T)))
          • (eq_sym eq_refl
             • (f_equal (frtPairRestrPaintingAt FCgen ε)
                  (f_equal Cw
                     (gFaceCAsνFace (next S0) (chainUp1 (νExt3At S0) a) p Hpw (DepsCohsChainCons cB')
                        (Hlen'0 • eq_sym (plus_n_Sm (cohsChainLen cB') p)) ω (T)))
                • f_equal (frtPairRestrPaintingAt FCgen ε)
                    (chainPaintingGetPainting (cohsChainExt (DepsCohsChainCons cB')) (mkRestrFrame 0 leR_O ω (getFrame (cohsChainNext (DepsCohsChainCons cB')) (T.1)).1)
                       (nth (getFrame (cohsChainNext (DepsCohsChainCons cB')) (T.1)).2 ω))))))).
  intros pb kb dc3bot a Hlen0 Hlen'0 Hp0 Hqp0 Hpw T.
  destruct (chainSplit p a (leR_eq_r (eq_sym Hlen0) (leR_add_l (cohsChainLen cB)))) as (pM & kM & dc3M' & aH' & aL & Heq & Hn).
  destruct Heq.
  assert (addCancelR: forall (n za zb: nat), za + n = zb + n -> za = zb).
  {
    intro n.
    induction n as [|n IHn]; intros za zb zH.
    -
    now rewrite <- 2 plus_n_O in zH.
    -
    rewrite <- 2 plus_n_Sm in zH.
    now exact (IHn za zb (f_equal Nat.pred zH)).
  }
  assert (HlenAH: cohs3ChainLen aH' + p = cohs3ChainLen aH + p).
  {
    transitivity (cohs3ChainLen (cohs3ChainCompose aH' aL)).
    -
    rewrite (cohs3ChainLenCompose aH' aL).
    now rewrite Hn.
    -
    rewrite Hlen0.
    unfold cB.
    rewrite (cohs2ChainDepsCohsLen (cohs3ChainDepsCohs2 aH)).
    now rewrite (cohs3ChainDepsCohs2Len aH).
  }
  pose proof (chain3PackEq (pM; (kM; (dc3M'; aH'))) (p; (k; (dc3M; aH))) (addCancelR _ _ _ HlenAH)) as E.
  assert (packElim: forall (s t: Chain3Pack (νDepsCohs3At S0)) (E0: s = t) (P: forall (p0 k0: nat) (dc0: DepsCohs3 p0 k0), DepsCohs3Chain (νDepsCohs3At S0) dc0 -> Type), P s.1 s.2.1 s.2.2.1 s.2.2.2 -> P t.1 t.2.1 t.2.2.1 t.2.2.2).
  {
    intros zs zt zE zP zH.
    now exact (eq_rect zs
      (fun z => zP z.1 z.2.1 z.2.2.1 z.2.2.2) zH zt zE).
  }
  revert aL Hn Hlen0 Hlen'0.
  pattern pM, kM, dc3M', aH'.
  refine (packElim _ _ (eq_sym E) _ _).
  intros aL Hn Hlen0 Hlen'0.
  cbn in aL, Hn, Hlen0, Hlen'0.
  assert (EXAL: forall (pb0 kb0: nat) (dc3bot0: DepsCohs3 pb0 kb0) (aL: DepsCohs3Chain dc3M dc3bot0)
    (Hp0: cohs3ChainLen aL <= 0 + kb0) (Hqp0: (cohs3ChainLen aL).+1 <= 0 + kb0.+1) (Hpw: cohs3ChainLen aL <= 0 + kb0.+1)
    (HA HB: cohs2ChainLen (cohs3ChainDepsCohs2 (cohs3ChainCompose aH aL)) = (cohsChainLen cB + cohs3ChainLen aL)%nat)
    (HC: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL))) = (cohsChainLen cB' + (cohs3ChainLen aL).+1)%nat)
    (HD: cohs2ChainLen (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL))) = (cohsChainLen (DepsCohsChainCons cB') + cohs3ChainLen aL)%nat)
    (T: gF0 S0 2),
    f_equal Cp (gFaceCohC S0 (cohs3ChainCompose aH aL) 0 (cohs3ChainLen aL) Hp0 (cohs3ChainLen aL) leR_refl ε ω (T))
    • (f_equal Cp (faceDeepAsνFace (cohs3ChainDepsCohs2 (cohs3ChainCompose aH aL)) (cohs3ChainLen aL) Hp0 cB HA ω (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL).+1 Hqp0 ε (T)).1 (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL).+1 Hqp0 ε (T)).2)
       • (chainPaintingGetPainting (cohsChainExt cB) (mkRestrFrame 0 leR_O ω (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL).+1 Hqp0 ε (T)).1).1)
            (nth (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL).+1 Hqp0 ε (T)).1).2 ω)
          • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ω) (Hal (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL).+1 Hqp0 ε (T)))
             • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ω)
                  (f_equal gf' (faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL))) (cohs3ChainLen aL).+1 Hqp0 cB' HC ε (T).1 (T).2)
                   • projT1_eq
                       (chainPaintingGetPainting (cohsChainExt cB') (mkRestrFrame 0 leR_O ε (getFrame (cohsChainNext cB') (T.1)).1)
                          (nth (getFrame (cohsChainNext cB') (T.1)).2 ε)))
                • (=eq_sym (FCgen.(_fcCohsB).2 0 Hq 0 leR_O ε ω ((getFrame (cohsChainNext cB') T.1)).1.1);
                  rewSwapSym (fun D : mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) => mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D)
                    (FCgen.(_fcCohsB).2 0 Hq 0 leR_O ε ω ((getFrame (cohsChainNext cB') T.1)).1.1)
                    (nth_lmap
                       (fun (ω0 : arity)
                          (c : (mkPaintings ((frtDcB FCgen).(_deps);(frtDcB FCgen).(_extraDeps))).2
                                 (((mkCohFrameTypesAndRestrFrames (frtDcB FCgen).(_restrPaintings).1).(RestrFramesDef) (frtDcB FCgen).(_cohs).1).2 0 (leR_O ↕ ↑ Hq) ω0
                                    ((getFrame (cohsChainNext cB') T.1)).1.1)) =>
                        rew [fun x : (frtDcB FCgen).(_deps).(_frames).2 => (frtDcB FCgen).(_deps).(_paintings).2 x]
                            (frtDcB FCgen).(_cohs).2 0 Hq 0 leR_O ε ω0 ((getFrame (cohsChainNext cB') T.1)).1.1 in
                        (frtDcB FCgen).(_restrPaintings).2 0 Hq ε
                          (((mkCohFrameTypesAndRestrFrames (frtDcB FCgen).(_restrPaintings).1).(RestrFramesDef) (frtDcB FCgen).(_cohs).1).2 0 (leR_O ↕ ↑ Hq) ω0
                             ((getFrame (cohsChainNext cB') T.1)).1.1)
                          c)
                       ((getFrame (cohsChainNext cB') T.1)).1.2 ω)))))) =
    f_equal Cp
      (faceDeepAsνFace (cohs3ChainDepsCohs2 (cohs3ChainCompose aH aL)) (cohs3ChainLen aL) Hp0 cB HB ε
         (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL) Hpw ω (T)).1 (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL) Hpw ω (T)).2)
    • (chainPaintingGetPainting (cohsChainExt cB)
         (mkRestrFrame 0 leR_O ε
            (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL) Hpw ω (T)).1).1)
         (nth (getFrame (cohsChainNext cB) (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL) Hpw ω (T)).1).2 ε)
       • (f_equal (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ε)
            (Hal (gFaceC (next S0) (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL)) 0 (cohs3ChainLen aL) Hpw ω (T)))
          • (eq_sym eq_refl
             • (f_equal (frtPairRestrPaintingAt FCgen ε)
                  (f_equal Cw
                     (faceDeepAsνFace (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) (cohs3ChainCompose aH aL))) (cohs3ChainLen aL) Hpw (DepsCohsChainCons cB') HD ω (T).1 (T).2))
                • f_equal (frtPairRestrPaintingAt FCgen ε)
                    (chainPaintingGetPainting (cohsChainExt (DepsCohsChainCons cB')) (mkRestrFrame 0 leR_O ω (getFrame (cohsChainNext (DepsCohsChainCons cB')) (T.1)).1)
                       (nth (getFrame (cohsChainNext (DepsCohsChainCons cB')) (T.1)).2 ω))))))).
  2: {
    unfold gFaceCAsνFace.
    pose proof (EXAL _ _ _ aL) as EA.
    rewrite Hn in EA.
    now exact (EA Hp0 Hqp0 Hpw _ _ _ _ T).
  }
  intros pb0 kb0 dc3bot0 aL0.
  induction aL0 as [|p1 k1 dc1 aL0 IH]; intros Hp1 Hqp1 Hpw1 HA0 HB0 HC0 HD0 T0.
  2: {
    cbn [cohs3ChainCompose cohs3ChainLen gFaceCohC].
    rewrite (faceAtCohUpShift (νExt3At S0) (cohs3ChainCompose aH aL0) (cohs3ChainLen aL0) (⇓ Hp1) (cohs3ChainLen aL0) leR_refl ε ω (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) (DepsCohs3ChainCons (cohs3ChainCompose aH aL0)))) T0)).
    cbn [cohs3ChainDepsCohs2 chainUp1 cohs3ChainUp faceDeepAsνFace].
    now exact (IH (⇓ Hp1) (⇓ Hqp1) (⇓ Hpw1) _ _ _ _ T0).
  }
  cbn [cohs3ChainCompose cohs3ChainLen].
  cbn [gFaceCohC].
  rewrite (faceAtCohUpConj (νExt3At S0) aH 0 Hp1 0 leR_refl ε ω (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) aH)) T0).1 (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) aH)) T0).2).

  pose (SigM := {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D}).
  pose (CB1 := {D: mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))).(1) &T (mkPaintings ((mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))); mkExtraDeps dc3M.(_depsCohs2).(_extraDepsCohs))%extradepsrestr).2 D}).
  pose (gp := fun z: SigM => getPainting (cohsChainExt cB) z.1 z.2).
  pose (sC := (fun z: SigM => chainPaintingGetPainting (cohsChainExt cB) z.1 z.2) : forall z: SigM, Cp (gp z) = z).
  pose (Re := fun w: CB1 => (restrCell dc3M.(_depsCohs2).(_extraDepsCohs) 0 Hp1 ε w.1 w.2 : SigM)).
  pose (Rw := fun w: CB1 => (restrCell dc3M.(_depsCohs2).(_extraDepsCohs) 0 (leR_refl ↕ Hp1) ω w.1 w.2 : SigM)).
  assert (fAeqE: forall (w1 w2: CB1) (e: w1 = w2), f_equal (fun w: CB1 => faceAt (cohs3ChainDepsCohs2 aH) 0 Hp1 ε w.1 w.2) e = f_equal gp (f_equal Re e)).
  {
    intros w1 w2 e.
    now exact (eq_sym (f_equal_compose Re gp e)).
  }
  assert (fAeqW: forall (w1 w2: CB1) (e: w1 = w2), f_equal (fun w: CB1 => faceAt (cohs3ChainDepsCohs2 aH) 0 (leR_refl ↕ Hp1) ω w.1 w.2) e = f_equal gp (f_equal Rw e)).
  {
    intros w1 w2 e.
    now exact (eq_sym (f_equal_compose Rw gp e)).
  }
  rewrite 5 eq_trans_map_distr.
  rewrite <- eq_sym_map_distr.
  rewrite fAeqE.
  rewrite fAeqW.
  rewrite 3 (sectionPath gp Cp sC).
  rewrite 2 (faceDeepAsνFaceZero (cohs3ChainDepsCohs2 aH)).
  pose (gpX := fun z: SigM => getPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))) z.1 z.2).
  pose (sC2 := (fun z: SigM => chainPaintingGetPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))) z.1 z.2) : forall z: SigM, Cp (gpX z) = z).
  pose (sC3 := (fun z: {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D} => chainPaintingGetPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))) z.1 z.2)
    : forall z: {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D},
      Cp ((fun z0: {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D} => getPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))) z0.1 z0.2) z) = z).
  refine (eq_trans (f_equal (fun z => _ • (z • _)) (sectionPathSym (fun z: {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D} => getPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))) z.1 z.2) Cp sC3
    (f_equal (fun x: mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))) => ((mkRestrFrame 0 leR_O ω x.1; nth x.2 ω) : {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D}))
       (getFrameDeepCell (cohs3ChainDepsCohs2 aH) ((gFaceC (next S0) (chainUp1 (νExt3At S0) aH) 0 1 Hqp1 ε T0).1; (gFaceC (next S0) (chainUp1 (νExt3At S0) aH) 0 1 Hqp1 ε T0).2))))) _).
  refine (eq_trans _ (eq_sym (f_equal (fun z => z • _) (sectionPathSym (fun z: {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D} => getPainting (cohsChainExt (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))) z.1 z.2) Cp sC3
    (f_equal (fun x: mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))) => ((mkRestrFrame 0 leR_O ε x.1; nth x.2 ε) : {D: mkFrame dc3M.(_depsCohs2).(_depsCohs).(_deps) &T mkPainting dc3M.(_depsCohs2).(_depsCohs).(_extraDeps) D}))
       (getFrameDeepCell (cohs3ChainDepsCohs2 aH) ((gFaceC (next S0) (chainUp1 (νExt3At S0) aH) 0 0 Hpw1 ω T0).1; (gFaceC (next S0) (chainUp1 (νExt3At S0) aH) 0 0 Hpw1 ω T0).2))))))).
  rewrite <- symExistTSwap.

  refine (exchangeConjugate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

  try (unfold projT1_eq in J |- *).
  Unset Keyed Unification.
  pose (Yw := restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3M)).(_extraDepsCohs) 1 (⇑ Hp1) ε
    (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) aH)) T0).1
    (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) aH)) T0).2).

  pose (NCR := faceDeepAsνFaceReadSucc
    (cohs3ChainDepsCohs2 (cohs3ChainUp (νExt3At S0) aH))
    Hqp1 HC0 ε T0.1 T0.2).
  pose (NCRW := deepCellRebuildFrame aH Yw.1 Yw.2).
  pose (rhoW := fun w: CB1 => ((w.1; w.2.1):
    mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))))).
  lazymatch goal with
  | |- f_equal ?psi ?pi • f_equal ?rw ?dd =
       f_equal ?psia ?ha • (f_equal ?psib ?hb • f_equal ?psic ?hc) =>
      refine (@mapThreePaths _ _ _ rhoW psi _ _ _ _ _ pi dd ha hb hc _)
  end.
  now exact (eq_trans NCRW (f_equal (fun e => _ • e) NCR)).
  pose (Ye := restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3M)).(_extraDepsCohs)
    0 Hpw1 ω
    (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) aH)) T0).1
    (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At S0) aH)) T0).2).
  pose (NER := deepCellRebuildFrame aH Ye.1 Ye.2).
  unfold νFacePackIrr.
  rewrite (dcPackUIP (dcPackEq _ _ _) eq_refl).
  cbn [νFaceAsDeep].
  rewrite 2 eq_trans_refl_l.
  pose (rhoE := fun w: CB1 => ((w.1; w.2.1): mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))))).
  refine (eq_trans (mapPathCancel rhoE (frtPairRestrAt dc3M.(_depsCohs2).(_depsCohs) ε) _ _ _ _ NER) _).
  cbn [getFrameDeepCell f_equal eq_sym].
  rewrite eq_trans_refl_l.
  f_equal.
  f_equal.
  lazymatch goal with
  | |- _ = f_equal ?r (chainPaintingGetPainting _ ?db ?cb) =>
    pose (EQ := chainPaintingGetPaintingCons (cohsChainExt cB') db cb);
    refine (eq_trans _ (eq_sym (f_equal (fun e => f_equal r e) EQ)))
  end.
  unfold EQ, projT1_eq.
  lazymatch goal with
  | |- f_equal ?psi (f_equal ?pj ?cp) = f_equal ?r (f_equal ?ass ?cp2) =>
    now exact (eq_trans (@f_equal_compose _ _ _ _ _ pj psi cp)
      (eq_sym (@f_equal_compose _ _ _ _ _ ass r cp2)))
  end.
  now exact (EX _ _ _ (descChain HD).2 Hlen Hlen' _ _ _ (descCell (DescS (DescS HD)) t)).
Defined.
End LadderSqU.

Lemma frtPairSqLadder: forall {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) {p k} {dc3M: DepsCohs3 p k}
  (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
  (Hlen: cohs3ChainLen (descChain HD).2
         = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) + p)%nat)
  (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
           (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX
             rpA (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp cohsA
             (mkDepsCohs dc3M.(_depsCohs2)).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen (frtChainUp aH) + p.+1)%nat)
  (frames: FrtFramesNextType (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs) (frtChainUp aH))
  (paintings: FrtPaintingsNextType (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs) (frtChainUp aH) frames),
  FrtPairSqAt (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs)
    (frtChainUp aH) Hlen' frames paintings (frtPairLawAlignU HD aH Hlen F)
    (frtRpZeroGen dc3M.(_depsCohs2)).
Proof.
  intros M XpB0 S0 HD p k dc3M aH Hlen F XA TX PX rpA trRp pshRp
    cohsA trCohs pshCohs Hlen' frames paintings.
  now exact (@frtPairSqLadderU M XpB0 S0 HD p k dc3M aH F XA TX PX rpA trRp pshRp
    cohsA trCohs pshCohs Hlen Hlen' frames paintings).
Defined.

Set Keyed Unification.
Lemma frtPairSqAtIrr {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair1 Hpair2: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HrpB1 HrpB2: FrtRpZeroType FC.(_fcXB) FC.(_fcRpB))
  (HP: forall ε t, Hpair1 ε t = Hpair2 ε t) (HB: HrpB1 = HrpB2):
  FrtPairSqAt FC cB' Hlen' frames paintings Hpair1 HrpB1 ->
  FrtPairSqAt FC cB' Hlen' frames paintings Hpair2 HrpB2.
Proof.
  intros SQ Hq Hqp ε ω t.
  rewrite <- (HP ω), <- (HP ε), <- HB.
  now exact (SQ Hq Hqp ε ω t).
Defined.

(** Canonicity of the split datum and of the painting identification along
    the stage recursion, at an arbitrary cell frame map identified with the
    descent's own: the pair law of every stage is the descent's pair law
    read through that identification, and the [B]-side dimension-[0] reading
    of every stage is the one of a given chain of readings. *)

Fixpoint FrtCanonicalSquare (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (HB: RpZeroChain p.+1 XB rpB)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (Hal: forall t, descTop HD cB t = top t)
    (val: forall u, mkPainting XB (top u))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
       (mkPshPaintings (g X) PX)
       (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cB F top frames)
    (PT: FrtPtChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp top val
           frames paintings SD), Type :=
  match p return forall k (dcB: DepsCohs p k)
    (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (HB: RpZeroChain p.+1 XB rpB)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (Hal: forall t, descTop HD cB t = top t)
    (val: forall u, mkPainting XB (top u))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
       (mkPshPaintings (g X) PX)
       (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cB F top frames)
    (PT: FrtPtChainAt M HD p cB F XA XB TX PX rpA rpB trRp pshRp top val
           frames paintings SD), Type with
  | 0 => fun k dcB cB Hlen F XA XB TX PX rpA rpB trRp pshRp HB top Hal val
           frames paintings SD PT =>
    { _: forall ε t, SD.1 ε t
           = descCellPairRestrAt HD cB 0 (⇓ F.(_frBound)) Hlen ε t
             • f_equal (frtPairRestrAt dcB ε) (Hal t) &T
      PT.2.2.2.1 = HB.2 }
  | S p => fun k dcB cB Hlen F XA XB TX PX rpA rpB trRp pshRp HB top Hal val
             frames paintings SD PT =>
    { _: FrtCanonicalSquare M HD p (DepsCohsChainCons cB)
           (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F)
           (F.(_frDepsA); XA)%extradepsrestr
           (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
           (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
           rpA.1 rpB.1 trRp.1 pshRp.1 HB.1
           (fun t => (top t).1) (fun t => f_equal (fun d => d.1) (Hal t))
           (fun u => ((top u).2; val u))
           frames.1 paintings.1 SD.1 PT.1 &T
      { _: forall ε t, SD.2.1 ε t
             = descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t
               • f_equal (frtPairRestrAt dcB ε) (Hal t) &T
        PT.2.2.2.2.1 = HB.2 } }
  end.
(** Stepping the frame chain identification with the chain. *)

Lemma frtTopAlignUCons {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) {p k} {dc3M: DepsCohs3 p.+1 k}
  (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M) (t: (g X).(G0) M.+1):
  frtTopAlignU HD (DepsCohs3ChainCons aH) t
  = f_equal (fun d => d.1) (frtTopAlignU HD aH t).
Proof.
  unfold frtTopAlignU.
  cbn [chainNextUpEq].
  rewrite (f_equal_compose DepsChainCons
    (fun ch => getFrame ch (descCells (DescS HD) t)) (chainNextUpEq aH)).
  now rewrite (f_equal_compose
    (fun ch => getFrame ch (descCells (DescS HD) t))
    (fun d: mkFrame (mkDepsRestr (depsCohs := dc3M.(_depsCohs2).(_depsCohs))) => d.1)
    (chainNextUpEq aH)).
Defined.

(** The canonicity chain at the ladder: the split datum is [frtSplitOfQ],
    whose pair laws are the descent's, and the painting identification is
    [mkFrtPtChain] over the chain of dimension-[0] readings, whose [B]-side
    readings are that chain's. *)

Fixpoint frtCanonicalSquareOf (SP: FrtRestrPaintingStepsSelected) (M: nat)
  {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat)
  {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
    (F: FrtDeps M HD cB)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (HA: RpZeroChain p.+1 XA rpA) (HB: RpZeroChain p.+1 XB rpB)
    (HT: TrRpZeroChain p.+1 (frTr F) TX trRp HA HB)
    (HP: PshRpZeroChain p.+1 (frtPshDeps F) PX pshRp HA)
    (val: forall u, mkPainting XB (descTop HD cB u))
    (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD cB) val
          ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)),
  FrtCanonicalSquare M HD p cB Hlen F XA XB TX PX rpA rpB trRp pshRp HB (descTop HD cB)
    (fun t => eq_refl) val
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
    (frtSplitOfQ M HD p cB Hlen F Q)
    (mkFrtPtChain M HD p cB Hlen F XA XB TX PX rpA rpB trRp pshRp val Q E
       (mkFrtRpChain SP M HD p cB Hlen F XA XB TX PX rpA rpB trRp pshRp
          HA HB HT HP val Q E)).
Proof.
  destruct p; intros k dcB cB Hlen F XA XB TX PX rpA rpB trRp pshRp
    HA HB HT HP val Q E.
  -
  now exact (fun ε t => eq_refl; eq_refl).
  -
  refine (_; (fun ε t => eq_refl; eq_refl)).
  now exact (frtCanonicalSquareOf SP M XpB0 S0 HD p k.+1 _ (DepsCohsChainCons cB)
    (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p)) (proj1FrtDeps F)
    (F.(_frDepsA); XA)%extradepsrestr
    (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
    (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
    rpA.1 rpB.1 trRp.1 pshRp.1 HA.1 HB.1 HT.1 HP.1
    (fun u => ((descTop HD cB u).2; val u)) Q.1
    (fun t => mkFrtPaintingStepDown F XA XB TX PX (descTop HD cB) val
       ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
           (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
           (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
       (fun t0 => mkFrtLayerOfRestr F (descTop HD cB)
          ((mkFrtRestrTypesAndFrames M HD p (DepsCohsChainCons cB)
              (Hlen • eq_sym (plus_n_Sm (cohsChainLen cB) p))
              (proj1FrtDeps F)).(FrtRestrFramesDef) Q.1)
          (fun ε t1 =>
             descCellPairRestrAt HD cB p.+1 (⇓ F.(_frBound)) Hlen ε t1)
          (fun ε t1 => Q.2 0 leR_O (⇓ F.(_frBound)) ε t1) t0)
       E t)).
Defined.
(** The δ-δ square at every stage of the ladder.  The stage is named by the
    upper part of the descent chain it reads through; the coherence data of
    the stage have their [B]-side generated from the [DepsCohs2] that part
    lands on, so that its chain one level up is the lift of its base chain
    and the two frame readings are identified canonically.  The data one
    level up are arbitrary, related to the descent's own by the canonicity
    chain. *)

Fixpoint mkFrtSqChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc S0) (p: nat) {struct p}:
  forall {k} {dc3M: DepsCohs3 p k}
    (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps))
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
             (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings))
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (cohsA: mkCohFrameTypes rpA)
    (trCohs: mkTrCohTypes (frtTrBaseOf F XA
               (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX rpA
               (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp cohsA
               (mkDepsCohs dc3M.(_depsCohs2)).(_cohs)))
    (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA))
    (Hlen: cohs3ChainLen (descChain HD).2
           = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) + p)%nat)
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen (frtChainUp aH) + p.+1)%nat)
    (frames: FrtFramesNextType
               (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp
                  pshRp cohsA trCohs pshCohs)
               (frtChainUp aH))
    (paintings: FrtPaintingsNextType
                  (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp
                     pshRp cohsA trCohs pshCohs)
                  (frtChainUp aH) frames)
    (SD: FrtSplitDataAt M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) F
           (frtTopNext (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA
              trRp pshRp cohsA trCohs pshCohs)
              (frtChainUp aH)) frames)
    (PT: FrtPtChain M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))
           (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
              cohsA trCohs pshCohs)
           (frtChainUp aH) Hlen' frames paintings SD)
    (Hal: forall t, descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) t
          = frtTopNext (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA
              trRp pshRp cohsA trCohs pshCohs)
              (frtChainUp aH) t)
    (HH: forall t, Hal t = frtTopAlignU HD aH t)
    (SC: FrtCanonicalSquare M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) Hlen F XA
           (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX PX rpA
           (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp pshRp
           (rpZeroChainOf p dc3M.(_depsCohs2).(_extraDepsCohs))
           (frtTopNext (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA
              trRp pshRp cohsA trCohs pshCohs)
              (frtChainUp aH)) Hal
           ((mkCellValuesOf M.+1 (cohsChainExt (frtChainUp aH))
               (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).2)
           frames paintings SD PT),
  FrtSqChainAt M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))
    (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA
       trCohs pshCohs)
    (frtChainUp aH) Hlen' frames paintings SD PT.
Proof.
  destruct p; intros k dc3M aH F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs
    Hlen Hlen' frames paintings SD PT Hal HH SC.
  -
  refine (frtPairSqAtIrr (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs) (frtChainUp aH) Hlen' frames paintings
    (frtPairLawAlignU HD aH Hlen F) SD.1
    (frtRpZeroGen dc3M.(_depsCohs2)) PT.2.2.2.1 _ _
    (frtPairSqLadder HD aH Hlen F XA TX PX rpA trRp pshRp
       cohsA trCohs pshCohs Hlen' frames paintings)).
  +
  intros ε t.
  unfold frtPairLawAlignU.
  rewrite <- (HH t).
  now exact (eq_sym (SC.1 ε t)).
  +
  now exact (eq_sym SC.2).
  -
  refine (_; _).
  +
  refine (mkFrtSqChain M XpB0 S0 HD p k.+1 (proj1DepsCohs3 dc3M)
    (DepsCohs3ChainCons aH) (proj1FrtDeps F) (F.(_frDepsA); XA)%extradepsrestr
    (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
    rpA.1 trRp.1 pshRp.1 cohsA.1 trCohs.1 pshCohs.1
    (Hlen • eq_sym (plus_n_Sm _ p)) (Hlen' • eq_sym (plus_n_Sm _ p.+1))
    frames.1 paintings.1 SD.1 PT.1
    (fun t => f_equal (fun d => d.1) (Hal t)) _ SC.1).
  intro t.
  rewrite (frtTopAlignUCons HD aH t).
  now rewrite (HH t).
  +
  refine (frtPairSqAtIrr (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs) (frtChainUp aH) Hlen' frames paintings
    (frtPairLawAlignU HD aH Hlen F) SD.2.1
    (frtRpZeroGen dc3M.(_depsCohs2)) PT.2.2.2.2.1 _ _
    (frtPairSqLadder HD aH Hlen F XA TX PX rpA trRp pshRp
       cohsA trCohs pshCohs Hlen' frames paintings)).
  *
  intros ε t.
  unfold frtPairLawAlignU.
  rewrite <- (HH t).
  now exact (eq_sym (SC.2.1 ε t)).
  *
  now exact (eq_sym SC.2.2).
Defined.

(** Canonicity of the clauses at paintings

    The square at the ladder is built from the descent's own pair laws and
    from the canonical dimension-[0] readings of the [B]-side restriction
    paintings, so the clauses at paintings a level receives must be the
    ones built over those readings ([fgRpChainOfChains] at [rpBChainOf]). *)

Definition FgRpCanonicalAt (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp)
  (RP: FgRpChain m P frt frp Q): Type :=
  { SP: FrtRestrPaintingStepsSelected &T
    { HA: RpZeroChain m.+1
            (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcXA)
            (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcRpA) &T
      { HT: TrRpZeroChain m.+1 (frTr (fgDeps m (fgTowerAt m P) frt frp))
              (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTX)
              (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTrRp) HA
              (rpBChainOf m (fgTowerAt m P) frt frp Q) &T
        { HP: PshRpZeroChain m.+1
                (frtPshDeps (fgDeps m (fgTowerAt m P) frt frp))
                (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPX)
                (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPshRp) HA &T
          RP = fgRpChainOfChains SP m P frt frp Q HA
                 (rpBChainOf m (fgTowerAt m P) frt frp Q) HT HP } } } }.

Definition FgRpCanonicalBaseType (RP0: FgRpChainBaseType): Type :=
  FgRpCanonicalAt 0 ((tt; fgThis0): FgPrefix 0) frt0List frp0List frtRestr0 RP0.

Definition FgRpCanonicalStepType (RPS: FgRpChainStepType): Type :=
  forall (m: nat) (s: FgLevel m),
  FgRpCanonicalAt m.+1 (fgPrefixNext m s) (fgFrtNextOf m s) (fgFrpNextOf m s)
    (fgQNext m s) (RPS m s).

Definition fgRpBaseCanonical: FgRpCanonicalBaseType fgRpBase :=
  (frtRestrPaintingStepSelectedOf; (_; (_; (_; eq_refl)))).

Definition fgRpStepCanonical: FgRpCanonicalStepType fgRpStep :=
  fun m s => (frtRestrPaintingStepSelectedOf; (_; (_; (_; eq_refl)))).

(** The square chain at a level, from the canonical clauses at paintings. *)

Definition fgSqChain (m: nat) (P: FgPrefix m)
  (frt: FgFrt m (fgTowerAt m P)) (frp: FgFrp m (fgTowerAt m P) frt)
  (Q: FgRestrData m (fgTowerAt m P) frt frp)
  (RP: FgRpChain m P frt frp Q) (HC: FgRpCanonicalAt m P frt frp Q RP):
  FrtSqChainAt m (descAt m) m DepsCohsChainNil
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q) DepsCohsChainNil
    (descChainLen (descAt m.+1)) (fgFrtOf m (fgTowerAt m P) frt frp Q)
    (fgFrpOf m (fgTowerAt m P) frt frp Q) (fgSplitOf m P frt frp Q)
    (fgPtChain m P frt frp Q RP).
Proof.
  destruct HC as (SP & HA & HT & HP & E).
  symmetry in E.
  destruct E.
  now exact (mkFrtSqChain m (descAt m) m
    DepsCohs3ChainNil (fgDeps m (fgTowerAt m P) frt frp)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcXA)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTX)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPX)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcRpA)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTrRp)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPshRp)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcCohsA)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcTrCohs)
    (towerFrtDepsCohsOf m (fgTowerAt m P) frt frp Q).(_fcPshCohs)
    (descChainLen (descAt m)) (descChainLen (descAt m.+1))
    (fgFrtOf m (fgTowerAt m P) frt frp Q) (fgFrpOf m (fgTowerAt m P) frt frp Q)
    (fgSplitOf m P frt frp Q)
    (fgPtChain m P frt frp Q
       (fgRpChainOfChains SP m P frt frp Q HA
          (rpBChainOf m (fgTowerAt m P) frt frp Q) HT HP))
    (fun t => eq_refl) (fun t => eq_refl)
    (frtCanonicalSquareOf SP m (descAt m) m DepsCohsChainNil (descChainLen (descAt m))
       (fgDeps m (fgTowerAt m P) frt frp) _ _ _ _ _ _ _ _ HA
       (rpBChainOf m (fgTowerAt m P) frt frp Q) HT HP _ Q _)).
Defined.

End FG.
End Translation.
