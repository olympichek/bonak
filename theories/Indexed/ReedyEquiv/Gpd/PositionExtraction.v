(** Reading the extraction at a relative position of a indexed tower. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Notation LeSProp NatLemmas RewLemmas Limit.
From Bonak.Indexed.Gpd Require Import Layer νGpd Pasting.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Face PresheafOfνGpd PathAlgebra
  PartialDiagram.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

Module PositionExtractionOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core) (Extraction: ExtractionSig A Core Faces).
Include PartialDiagramOn A Core Faces Extraction.

Module Relative.
Export Partial.
Import A Extraction.

Local Fixpoint rightZero (n: nat): n = n + 0 :=
  match n with 0 => eq_refl | S n => f_equal S (rightZero n) end.

Local Fixpoint rightSucc (n m: nat): (n + m).+1 = n + m.+1 :=
  match n with 0 => eq_refl | S n => f_equal S (rightSucc n m) end.

(** Extraction at an arbitrary position uses the same operations as [g]. *)
Definition positionPresentation {p} {X: (νGpdAt p).(prefix)}
  (L: νGpdFrom p X): νGpdPresentation arity := {|
  G0 := gF0 L;
  GFace n q Hq a := gFaceC L DepsCohs3ChainNil n q
    (leR_eq_r (rightZero n) Hq) a;
  GFaceCoh n q Hq r Hr a b t := gFaceCohC L DepsCohs3ChainNil n q
    (leR_eq_r (rightZero n) Hq) r Hr a b t;
  GFaceCoh2 n q Hq r Hr s Hs a b c t := gFaceCoh2C L DepsCohs3ChainNil n q
    (leR_eq_r (rightZero n) Hq) r Hr s Hs a b c t;
|}.

Section Descent.
Context {P0} {Xpre: (νGpdAt P0).(prefix)} (X: νGpdFrom P0 Xpre).

Inductive Desc: forall n, PartialState P0 n -> Type :=
| DescZ: Desc 0 (partialState X 0)
| DescS {n} {z: PartialState P0 n}: Desc n z -> Desc n.+1 (stateNext z).

(** Relative transports reduce at concrete continuation depths. *)
Fixpoint descF0 {n} {z: PartialState P0 n} (D: Desc n z) (k: nat) {struct D}:
  gF0 X (k + n) = gF0 z.2.2.1 k :=
  match D in @Desc n0 z0 return gF0 X (k + n0) = gF0 z0.2.2.1 k with
  | DescZ => f_equal (gF0 X) (eq_sym (rightZero k))
  | @DescS n1 z1 D' =>
      rew [fun j => gF0 X j = gF0 (next z1.2.2.1) k] (rightSucc k n1)
        in descF0 D' k.+1
  end.

Definition descChain {n} {z: PartialState P0 n} (D: Desc n z) := z.2.2.2.

Definition descTotal {n} {z: PartialState P0 n} (D: Desc n z):
  gF0 X n = stateTotal z := descF0 D 0.

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

Lemma gFaceLevelCohCore {mY} {Ypre: (νGpdAt mY).(prefix)} (Y: νGpdFrom mY Ypre)
  {k1 k2: nat} (e0: k1 = k2)
  (e1: k1.+1 = k2.+1) (He1: e1 = f_equal S e0)
  (e2: k1.+2 = k2.+2) (He2: e2 = f_equal S e1)
  (q: nat) (Hq1: q <= k1 + 0) (Hq2: q <= k2 + 0)
  (r0: nat) (Hr: r0 <= q) (ε ω: arity) (t: gF0 Y k1.+2):
  (f_equal (gFaceC Y DepsCohs3ChainNil k2 q Hq2 ε)
      (gFaceLevelCore Y DepsCohs3ChainNil e1 e2 He2 r0
        (leR_eq_r (rightSucc k1 0 • PeanoNat.Nat.add_1_r k1
              • rightZero k1.+1) (Hr ↕ (↑ Hq1)))
        (leR_eq_r (rightSucc k2 0 • PeanoNat.Nat.add_1_r k2
              • rightZero k2.+1) (Hr ↕ (↑ Hq2))) ω t)
    • gFaceLevelCore Y DepsCohs3ChainNil e0 e1 He1 q Hq1 Hq2 ε
        (gFaceC Y DepsCohs3ChainNil k1.+1 r0
          (leR_eq_r (rightSucc k1 0 • PeanoNat.Nat.add_1_r k1
              • rightZero k1.+1) (Hr ↕ (↑ Hq1))) ω t))
  • f_equal
      (fun w => rew [GDom]
        eq_sym (f_equal (gF0 Y) (eq_sym e0)) in w)
      (gFaceCohC Y DepsCohs3ChainNil k1 q Hq1 r0 Hr ε ω t)
  =
  gFaceCohC Y DepsCohs3ChainNil k2 q Hq2 r0 Hr ε ω
    (rew [GDom] eq_sym (f_equal (gF0 Y) (eq_sym e2)) in t)
  • (f_equal (gFaceC Y DepsCohs3ChainNil k2 r0 (Hr ↕ Hq2) ω)
      (gFaceLevelCore Y DepsCohs3ChainNil e1 e2 He2 q.+1
        (leR_eq_r (rightSucc k1 0 • PeanoNat.Nat.add_1_r k1
              • rightZero k1.+1) (⇑ Hq1))
        (leR_eq_r (rightSucc k2 0 • PeanoNat.Nat.add_1_r k2
              • rightZero k2.+1) (⇑ Hq2)) ε t)
    • gFaceLevelCore Y DepsCohs3ChainNil e0 e1 He1 r0
        (Hr ↕ Hq1) (Hr ↕ Hq2) ω
        (gFaceC Y DepsCohs3ChainNil k1.+1 q.+1
          (leR_eq_r (rightSucc k1 0 • PeanoNat.Nat.add_1_r k1
              • rightZero k1.+1) (⇑ Hq1)) ε t)).
Proof.
  destruct e0; cbn in He1; subst e1; cbn in He2; subst e2.
  unfold gFaceLevelCore; cbn.
  set (HH := gFaceCohC Y DepsCohs3ChainNil k1 q Hq1 r0 Hr ε ω t) in *.
  clearbody HH.
  rewrite f_equal_id.
  now exact (eq_trans_refl_l HH).
Defined.

(** Transporting the equality itself makes the comparison reduce at
    concrete relative levels, without inserting unit paths. *)

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
      eq_sym ((rew [fun l => Y.(G0) l = A1] e1 in p1)) in u)
  = rew [GDom]
      eq_sym ((rew [fun l => Y.(G0) l = A0] e0 in p0)) in v.
Proof.
  destruct e0; cbn in He; subst e1. now exact P.
Defined.

(** The same reindexing preserves the selected exchange square. *)

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
        eq_sym ((rew [fun l => Y.(G0) l = A0] e0 in p0)) in w)
      Csrc
  = Y.(GFaceCoh) l2 q Hq2 r0 Hr ε ω
      (rew [GDom]
        eq_sym ((rew [fun l => Y.(G0) l = A2] e2 in p2)) in t)
    • (f_equal (Y.(GFace) l2 r0 (Hr ↕ Hq2) ω)
        (faceDescStepCore Y e1 e2 He2 p1 p2 q.+1
          (⇑ Hq1) (⇑ Hq2) ε t uq Pq)
      • faceDescStepCore Y e0 e1 He1 p0 p1 r0
          (Hr ↕ Hq1) (Hr ↕ Hq2) ω uq ud Prq).
Proof.
  destruct e0; cbn in He1; subst e1; cbn in He2; subst e2.
  now exact IH.
Defined.

(** The faces of the extracted diagram agree with the faces at the
    descended position. Transparent arithmetic keeps adjacent levels aligned. *)

Lemma descFaceG {n} {z: PartialState P0 n} (D: Desc n z)
  (k dim: nat) (HdX: dim <= k + n) (HdS: dim <= k + n)
  (ε: arity) (t: gF0 z.2.2.1 k.+1):
  (positionPresentation X).(GFace) (k + n) dim HdX ε
    (rew [GDom] (eq_sym (descF0 D k.+1)) in t) =
  rew [GDom] (eq_sym (descF0 D k)) in
    gFaceC z.2.2.1 (descChain D).2 k dim HdS ε t.
Proof.
  revert k dim HdX HdS ε t.
  induction D as [|n0 zbase HDbase IH];
    intros k dim HdX HdS ε t.
  - cbn [descF0 descChain].
    now exact (gFaceLevelCore X DepsCohs3ChainNil
      (rightZero k) (rightZero k.+1)
      eq_refl
      dim HdS (leR_eq_r (rightZero (k + 0)) HdX) ε t).
  - cbn [descF0 descChain].
    now exact (faceDescStepCore (positionPresentation X)
      (rightSucc k n0) (rightSucc k.+1 n0)
      eq_refl
      (descF0 HDbase k.+1) (descF0 HDbase k.+2)
      dim (leR_eq_r (eq_sym (rightSucc k n0)) HdX) HdX ε
      t
      (gFaceC (next zbase.2.2.1)
        (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
        k dim HdS ε t)
      (IH k.+1 dim
        (leR_eq_r (eq_sym (rightSucc k n0)) HdX)
        (leR_eq_r (eq_sym (rightSucc k n0)) HdS)
        ε t)).
Defined.

(** The successor equation of [descFaceG], kept named so its recursive call
    stays folded when the coherence proof rewrites the four boundary paths. *)

Lemma descFaceGS {n} {z: PartialState P0 n} (D: Desc n z) (k dim: nat)
  (HdX HdS: dim <= k + n.+1) (ε: arity)
  (t: gF0 (next z.2.2.1) k.+1):
  descFaceG (DescS D) k dim HdX HdS ε t
  = faceDescStepCore (positionPresentation X)
      (rightSucc k n) (rightSucc k.+1 n)
      eq_refl
      (descF0 D k.+1) (descF0 D k.+2)
      dim (leR_eq_r (eq_sym (rightSucc k n)) HdX) HdX ε
      t
      (gFaceC (next z.2.2.1) (chainUp1 (νExt3At z.2.2.1) (descChain D).2)
        k dim HdS ε t)
      (descFaceG D k.+1 dim
        (leR_eq_r (eq_sym (rightSucc k n)) HdX)
        (leR_eq_r (eq_sym (rightSucc k n)) HdS) ε t).
Proof.
  now reflexivity.
Defined.

(** Naturality of the descent face identification. *)

Lemma descFaceGCoh {n} {z: PartialState P0 n} (D: Desc n z)
  (k q: nat) (Hq: q <= k + n) (r0: nat) (Hr: r0 <= q)
  (ε ω: arity) (t: gF0 z.2.2.1 k.+2):
  (f_equal ((positionPresentation X).(GFace) (k + n) q Hq ε)
      (descFaceG D k.+1 r0 (Hr ↕ ↑ Hq) (Hr ↕ ↑ Hq) ω t)
    • descFaceG D k q Hq Hq ε
        (gFaceC z.2.2.1 (descChain D).2 k.+1 r0 (Hr ↕ ↑ Hq) ω t))
  • f_equal (fun w => rew [GDom] eq_sym (descF0 D k) in w)
      (gFaceCohC z.2.2.1 (descChain D).2 k q Hq r0 Hr ε ω t)
  = (positionPresentation X).(GFaceCoh) (k + n) q Hq r0 Hr ε ω
      (rew [GDom] eq_sym (descF0 D k.+2) in t)
    • (f_equal ((positionPresentation X).(GFace) (k + n) r0 (Hr ↕ Hq) ω)
        (descFaceG D k.+1 q.+1 (⇑ Hq) (⇑ Hq) ε t)
      • descFaceG D k r0 (Hr ↕ Hq) (Hr ↕ Hq) ω
          (gFaceC z.2.2.1 (descChain D).2 k.+1 q.+1 (⇑ Hq) ε t)).
Proof.
  revert k q Hq r0 Hr ε ω t.
  induction D as [|n0 zbase HDbase IH];
    intros k q Hq r0 Hr ε ω t.
  - unfold descFaceG; cbn.
    now exact (gFaceLevelCohCore X
      (rightZero k) (rightZero k.+1)
      eq_refl
      (rightZero k.+2)
      eq_refl
      q Hq (leR_eq_r (rightZero (k + 0)) Hq)
      r0 Hr ε ω t).
  - rewrite 4 descFaceGS.
    cbn [descF0 descChain].
    now exact (faceDescStepCohCore (positionPresentation X)
      (rightSucc k n0) (rightSucc k.+1 n0)
      eq_refl
      (rightSucc k.+2 n0)
      eq_refl
      (descF0 HDbase k.+1) (descF0 HDbase k.+2)
      (descF0 HDbase k.+3)
      q (leR_eq_r (eq_sym (rightSucc k n0)) Hq) Hq
      r0 Hr ε ω t
      (gFaceC (next zbase.2.2.1)
        (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
        k.+1 r0 (Hr ↕ ↑ Hq) ω t)
      (gFaceC (next zbase.2.2.1)
        (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
        k q Hq ε
        (gFaceC (next zbase.2.2.1)
          (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
          k.+1 r0 (Hr ↕ ↑ Hq) ω t))
      (gFaceC (next zbase.2.2.1)
        (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
        k.+1 q.+1 (⇑ Hq) ε t)
      (gFaceC (next zbase.2.2.1)
        (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
        k r0 (Hr ↕ Hq) ω
        (gFaceC (next zbase.2.2.1)
          (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
          k.+1 q.+1 (⇑ Hq) ε t))
      (descFaceG HDbase k.+2 r0
        (leR_eq_r (eq_sym (rightSucc k.+1 n0)) (Hr ↕ ↑ Hq))
        (leR_eq_r (eq_sym (rightSucc k.+1 n0)) (Hr ↕ ↑ Hq)) ω t)
      (descFaceG HDbase k.+1 q
        (leR_eq_r (eq_sym (rightSucc k n0)) Hq)
        (leR_eq_r (eq_sym (rightSucc k n0)) Hq) ε
        (gFaceC (next zbase.2.2.1)
          (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
          k.+1 r0 (Hr ↕ ↑ Hq) ω t))
      (descFaceG HDbase k.+2 q.+1
        (leR_eq_r (eq_sym (rightSucc k.+1 n0)) (⇑ Hq))
        (leR_eq_r (eq_sym (rightSucc k.+1 n0)) (⇑ Hq)) ε t)
      (descFaceG HDbase k.+1 r0
        (leR_eq_r (eq_sym (rightSucc k n0)) (Hr ↕ Hq))
        (leR_eq_r (eq_sym (rightSucc k n0)) (Hr ↕ Hq)) ω
        (gFaceC (next zbase.2.2.1)
          (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
          k.+1 q.+1 (⇑ Hq) ε t))
      (gFaceCohC (next zbase.2.2.1)
        (chainUp1 (νExt3At zbase.2.2.1) (descChain HDbase).2)
        k q Hq r0 Hr ε ω t)
      (IH k.+1 q (leR_eq_r (eq_sym (rightSucc k n0)) Hq)
        r0 Hr ε ω t)).
Defined.


Fixpoint descPartial (k: nat): Desc k (partialState X k) :=
  match k with
  | 0 => DescZ
  | S k => DescS (descPartial k)
  end.

End Descent.

End Relative.

End PositionExtractionOn.
