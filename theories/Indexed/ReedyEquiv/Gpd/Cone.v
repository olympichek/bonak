(** A residual attachment of coherent face presentations. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Funext Notation RewLemmas LeSProp CohShapes HomotopyPullback.
From Bonak.Presentation.Gpd Require Import Presentation.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

Module GpdCone.

Definition residualShiftPresentation {A: HSet} (P: νGpdPresentation A):
  νGpdPresentation A := {|
  G0 k := P.(G0) (S k);
  GFace k q Hq a := P.(GFace) (S k) (S q) (⇑ Hq) a;
  GFaceCoh k q Hq r Hr a c := P.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c;
  GFaceCoh2 k q Hq r Hr s Hs a c d :=
    P.(GFaceCoh2) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) (S s) (⇑ Hs) a c d;
|}.


Local Lemma coneExchangeAlgebra {T: Type}
  {x0 x1 x2 x3 x4 x5 y0 y1 z0 z1 z2 z3: T}
  (a: x0 = x1) (b: x1 = x2) (c: x2 = x3)
  (d: x0 = x4) (e: x4 = x5) (f: x5 = x3)
  (u: x0 = y0) (v: x4 = y1) (w: y0 = y1)
  (l0: z1 = z0) (l1: y0 = z1) (r0: z3 = z2) (r1: y1 = z3)
  (h: z0 = z2)
  (hex: (a • b) • c = d • (e • f))
  (natural: u • w = d • v)
  (boundary: (l1 • l0) • h = w • (r1 • r0)):
  c • (eq_sym f • ((eq_sym e • (v • r1)) • r0)) =
    (eq_sym b • ((eq_sym a • (u • l1)) • l0)) • h.
Proof.
  destruct a, b, c, d, e, u, l0, l1, r0, r1.
  cbn [f_equal] in *.
  rewrite 2 eq_trans_refl_l in hex.
  rewrite eq_trans_refl_l in natural, boundary.
  rewrite eq_trans_refl_l in hex, natural.
  rewrite <- hex. cbn in *.
  rewrite 4 eq_trans_refl_l. now exact (eq_sym (boundary • natural)).
Defined.

Local Lemma setFiberPathExt {X: Type} (P: X -> HSet)
  {u v: {x: X &T P x}} (p q: u = v)
  (base: projT1_eq p = projT1_eq q): p = q.
Proof.
  apply (eqvInj (sigTPathEquiv u v)).
  refine (eq_existT_curried base _). now apply (P v.1).(UIP).
Defined.

Local Lemma productPathEta {X Y: Type} {x y: {_: X &T Y}} (p: x = y):
  eq_existT_nondep (f_equal (fun z: {_: X &T Y} => z.1) p)
    (f_equal (fun z: {_: X &T Y} => z.2) p) = p.
Proof. now destruct p. Defined.

Local Lemma productPathExt {X Y: Type} {x y: {_: X &T Y}} (p q: x = y)
  (left: f_equal (fun z: {_: X &T Y} => z.1) p = f_equal (fun z: {_: X &T Y} => z.1) q)
  (right: f_equal (fun z: {_: X &T Y} => z.2) p = f_equal (fun z: {_: X &T Y} => z.2) q): p = q.
Proof. rewrite <- (productPathEta p), <- (productPathEta q). now rewrite left, right. Defined.

Section AttachmentPathExt.
Context {I W: Type} {T B: HGpd} (r: I -> W -> B) (b: T -> B).
Local Definition Cone := {w: W &T forall a: I, {t: T &T r a w = b t}}.
Local Definition Flat := {z: {_: W &T I -> T} &T forall a: I, r a z.1 = b (z.2 a)}.
Local Definition flatten: Equiv Cone Flat.
Proof.
  refine (qinvEquiv
    (fun z => ((z.1; fun a => (z.2 a).1); fun a => (z.2 a).2))
    (fun z => (z.1.1; fun a => (z.1.2 a; z.2 a))) _ _).
  - now intro z.
  - now intros [[w t] h].
Defined.

Lemma attachmentPathExt {u v: Cone} (p q: u = v)
  (base: projT1_eq p = projT1_eq q)
  (cells: forall a, f_equal (fun z: Cone => (z.2 a).1) p =
    f_equal (fun z: Cone => (z.2 a).1) q): p = q.
Proof.
  apply (eqvInj (symEquiv (eqvInjEquiv flatten))).
  cbn [symEquiv eqvInjEquiv invEq eqvFun eqvIsEquiv qinvEquiv linv].
  apply (setFiberPathExt (fun z: {_: W &T I -> T} => hpiT (fun a => hpaths (r a z.1) (b (z.2 a))))).
  apply productPathExt.
  - unfold projT1_eq. rewrite 4 f_equal_compose. now exact base.
  - apply happlyInj; intro a.
    unfold happly, projT1_eq. rewrite 6 f_equal_compose. now exact (cells a).
Defined.
End AttachmentPathExt.

Section ConePresentation.
Context {A: HSet} (Q C: νGpdPresentation A).
Context (b: forall n, C.(G0) n -> Q.(G0) n).
Context (bFace: forall n q (Hq: q <= n) a x,
  Q.(GFace) n q Hq a (b (S n) x) = b n (C.(GFace) n q Hq a x)).
Context (bCoh: forall n q (Hq: q <= n) r (Hr: r <= q) a c x,
  (f_equal (Q.(GFace) n q Hq a) (bFace (S n) r (Hr ↕ ↑ Hq) c x)
    • bFace n q Hq a (C.(GFace) (S n) r (Hr ↕ ↑ Hq) c x))
    • f_equal (b n) (C.(GFaceCoh) n q Hq r Hr a c x)
  = Q.(GFaceCoh) n q Hq r Hr a c (b (S (S n)) x)
    • (f_equal (Q.(GFace) n r (Hr ↕ Hq) c) (bFace (S n) (S q) (⇑ Hq) a x)
      • bFace n r (Hr ↕ Hq) c (C.(GFace) (S n) (S q) (⇑ Hq) a x))).

Definition coneObject (k: nat): HGpd :=
  gsigT (A := Q.(G0) (S k)) (fun w =>
    gforall a: A, gsigT (A := C.(G0) k) (fun t =>
      hgpdOfHSet (hpaths (Q.(GFace) k 0 leR_O a w) (b k t)))).

Definition coneFace k q (Hq: q <= k) a (u: coneObject (S k)): coneObject k :=
  (Q.(GFace) (S k) (S q) (⇑ Hq) a u.1;
    fun c => (C.(GFace) k q Hq a (u.2 c).1;
      eq_sym (Q.(GFaceCoh) k q Hq 0 leR_O a c u.1)
        • (f_equal (Q.(GFace) k q Hq a) (u.2 c).2
          • bFace k q Hq a (u.2 c).1))).

Lemma coneExchangeSquare k q (Hq: q <= k) r (Hr: r <= q) a c
  (u: coneObject (S (S k))) d:
  f_equal (Q.(GFace) k 0 leR_O d)
      (Q.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u.1)
    • ((coneFace k r (Hr ↕ Hq) c
      (coneFace (S k) (S q) (⇑ Hq) a u)).2 d).2
  = ((coneFace k q Hq a
      (coneFace (S k) r (Hr ↕ ↑ Hq) c u)).2 d).2
    • f_equal (b k) (C.(GFaceCoh) k q Hq r Hr a c (u.2 d).1).
Proof.
  cbn [coneFace projT1 projT2].
  rewrite 4 eq_trans_map_distr, 2 fEqualSym.
  eapply coneExchangeAlgebra.
  - now exact (Q.(GFaceCoh2) k q Hq r Hr 0 leR_O a c d u.1).
  - rewrite 2 f_equal_compose.
    now exact (homotopyNat _ _
      (fun x => Q.(GFaceCoh) k q Hq r Hr a c x) (u.2 d).2).
  - now exact (bCoh k q Hq r Hr a c (u.2 d).1).
Defined.

Definition coneExchange k q (Hq: q <= k) r (Hr: r <= q) a c
  (u: coneObject (S (S k))):
  coneFace k q Hq a (coneFace (S k) r (Hr ↕ ↑ Hq) c u) =
    coneFace k r (Hr ↕ Hq) c (coneFace (S k) (S q) (⇑ Hq) a u) :=
  attachmentEq (fun d => Q.(GFace) k 0 leR_O d) (b k)
    (coneFace k q Hq a (coneFace (S k) r (Hr ↕ ↑ Hq) c u))
    (coneFace k r (Hr ↕ Hq) c (coneFace (S k) (S q) (⇑ Hq) a u))
    (Q.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u.1)
    (fun d => C.(GFaceCoh) k q Hq r Hr a c (u.2 d).1)
    (coneExchangeSquare k q Hq r Hr a c u).

Lemma coneExchangeBase k q (Hq: q <= k) r (Hr: r <= q) a c
  (u: coneObject (S (S k))):
  f_equal (fun z: coneObject k => z.1) (coneExchange k q Hq r Hr a c u) =
    Q.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u.1.
Proof. now apply attachmentEqBase. Defined.

Lemma coneExchangeCell k q (Hq: q <= k) r (Hr: r <= q) a c
  (u: coneObject (S (S k))) d:
  f_equal (fun z: coneObject k => (z.2 d).1) (coneExchange k q Hq r Hr a c u) =
    C.(GFaceCoh) k q Hq r Hr a c (u.2 d).1.
Proof.
  unfold coneExchange.
  now exact (attachmentEqTop (fun d => Q.(GFace) k 0 leR_O d) (b k)
    (coneFace k q Hq a (coneFace (S k) r (Hr ↕ ↑ Hq) c u))
    (coneFace k r (Hr ↕ Hq) c (coneFace (S k) (S q) (⇑ Hq) a u))
    _ (fun d => C.(GFaceCoh) k q Hq r Hr a c (u.2 d).1) _ d).
Defined.

Lemma coneFaceBaseAp k q (Hq: q <= k) a {u v: coneObject (S k)} (e: u = v):
  f_equal (fun z: coneObject k => z.1) (f_equal (coneFace k q Hq a) e) =
    f_equal (Q.(GFace) (S k) (S q) (⇑ Hq) a) (f_equal (fun z: coneObject (S k) => z.1) e).
Proof. now destruct e. Defined.

Lemma coneFaceCellAp k q (Hq: q <= k) a {u v: coneObject (S k)} (e: u = v) d:
  f_equal (fun z: coneObject k => (z.2 d).1) (f_equal (coneFace k q Hq a) e) =
    f_equal (C.(GFace) k q Hq a)
      (f_equal (fun z: coneObject (S k) => (z.2 d).1) e).
Proof. now destruct e. Defined.

Lemma coneHex k q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r)
  a c d (u: coneObject (S (S (S k)))):
  hexagonal_coherence
    (coneFace k q Hq a) (coneFace k s (Hs ↕ (Hr ↕ Hq)) d)
    (coneFace k r (Hr ↕ Hq) c)
    (coneExchange (S k) r (Hr ↕ ↑ Hq) s Hs c d u)
    (coneExchange (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u)
    (coneExchange (S k) (S q) (⇑ Hq) s (↑ (Hs ↕ Hr)) a d u)
    (coneExchange k q Hq s (Hs ↕ Hr) a d
      (coneFace (S (S k)) (S r) (⇑ (Hr ↕ ↑ Hq)) c u))
    (coneExchange k q Hq r Hr a c
      (coneFace (S (S k)) s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) d u))
    (coneExchange k r (Hr ↕ Hq) s Hs c d
      (coneFace (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a u)).
Proof.
  unfold hexagonal_coherence.
  apply (attachmentPathExt (fun a => Q.(GFace) k 0 leR_O a) (b k)).
  - unfold projT1_eq at 1 2.
    rewrite 4 eq_trans_map_distr.
    rewrite 3 coneFaceBaseAp.
    rewrite (coneExchangeBase (S k) r (Hr ↕ ↑ Hq) s Hs c d u).
    rewrite
      (coneExchangeBase k q Hq s (Hs ↕ Hr) a d (coneFace (S (S k)) (S r) (⇑ (Hr ↕ ↑ Hq)) c u)),
      (coneExchangeBase (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u),
      (coneExchangeBase k q Hq r Hr a c (coneFace (S (S k)) s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) d u)),
      (coneExchangeBase (S k) (S q) (⇑ Hq) s (↑ (Hs ↕ Hr)) a d u),
      (coneExchangeBase k r (Hr ↕ Hq) s Hs c d (coneFace (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a u)).
    now exact (Q.(GFaceCoh2) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr)
      (S s) (⇑ Hs) a c d u.1).
  - intro e. rewrite 4 eq_trans_map_distr.
    rewrite 3 coneFaceCellAp.
    rewrite (coneExchangeCell (S k) r (Hr ↕ ↑ Hq) s Hs c d u e),
      (coneExchangeCell k q Hq s (Hs ↕ Hr) a d (coneFace (S (S k)) (S r) (⇑ (Hr ↕ ↑ Hq)) c u) e),
      (coneExchangeCell (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c u e),
      (coneExchangeCell k q Hq r Hr a c (coneFace (S (S k)) s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) d u) e),
      (coneExchangeCell (S k) (S q) (⇑ Hq) s (↑ (Hs ↕ Hr)) a d u e),
      (coneExchangeCell k r (Hr ↕ Hq) s Hs c d (coneFace (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a u) e).
    now exact (C.(GFaceCoh2) k q Hq r Hr s Hs a c d (u.2 e).1).
Defined.

Definition conePresentation: νGpdPresentation A := {|
  G0 := coneObject;
  GFace := coneFace;
  GFaceCoh := coneExchange;
  GFaceCoh2 := coneHex;
|}.
Local Lemma inverseBoundaryAlgebra {T: Type} {x0 x1 x2 x3 x4 x5: T}
  (a: x0 = x1) (bb: x1 = x2) (h: x2 = x3)
  (c: x0 = x4) (d: x4 = x5) (e: x5 = x3)
  (square: (a • bb) • h = c • (d • e)):
  (eq_sym bb • eq_sym a) • c = h • (eq_sym e • eq_sym d).
Proof.
  destruct a, bb, c, d, e. cbn in square |- *.
  rewrite eq_trans_refl_l in square. now rewrite square.
Defined.

Local Lemma boundaryConeAlgebra {T: Type} {x0 x1 x2 x3 x4 x5: T}
  (a: x0 = x1) (bb: x1 = x2) (h: x2 = x3)
  (c: x0 = x4) (p: x4 = x5) (r: x5 = x3)
  (square: (a • bb) • h = c • (p • r)):
  eq_sym p • (eq_sym c • (a • bb)) = r • eq_sym h.
Proof.
  destruct a, bb, c, p, r. cbn in square |- *.
  rewrite eq_trans_refl_l in square. now rewrite square.
Defined.

Definition coneBoundary k (x: C.(G0) (S k)): coneObject k :=
  (b (S k) x; fun a => (C.(GFace) k 0 leR_O a x; bFace k 0 leR_O a x)).

Lemma coneBoundaryFaceSquare k q (Hq: q <= k) a
  (x: C.(G0) (S (S k))) d:
  f_equal (Q.(GFace) k 0 leR_O d) (eq_sym (bFace (S k) (S q) (⇑ Hq) a x))
    • ((coneFace k q Hq a (coneBoundary (S k) x)).2 d).2
  = ((coneBoundary k (C.(GFace) (S k) (S q) (⇑ Hq) a x)).2 d).2
    • f_equal (b k) (eq_sym (C.(GFaceCoh) k q Hq 0 leR_O a d x)).
Proof.
  cbn [coneBoundary coneFace projT1 projT2]. rewrite 2 fEqualSym.
  apply boundaryConeAlgebra. now apply bCoh.
Defined.

Definition coneBoundaryFace k q (Hq: q <= k) a (x: C.(G0) (S (S k))):
  coneBoundary k (C.(GFace) (S k) (S q) (⇑ Hq) a x) =
    coneFace k q Hq a (coneBoundary (S k) x) :=
  attachmentEq (fun d => Q.(GFace) k 0 leR_O d) (b k)
    (coneBoundary k (C.(GFace) (S k) (S q) (⇑ Hq) a x))
    (coneFace k q Hq a (coneBoundary (S k) x))
    (eq_sym (bFace (S k) (S q) (⇑ Hq) a x))
    (fun d => eq_sym (C.(GFaceCoh) k q Hq 0 leR_O a d x))
    (coneBoundaryFaceSquare k q Hq a x).

Lemma coneBoundaryFaceBase k q (Hq: q <= k) a (x: C.(G0) (S (S k))):
  f_equal (fun z: coneObject k => z.1) (coneBoundaryFace k q Hq a x) =
    eq_sym (bFace (S k) (S q) (⇑ Hq) a x).
Proof. now apply attachmentEqBase. Defined.

Lemma coneBoundaryFaceCell k q (Hq: q <= k) a (x: C.(G0) (S (S k))) d:
  f_equal (fun z: coneObject k => (z.2 d).1) (coneBoundaryFace k q Hq a x) =
    eq_sym (C.(GFaceCoh) k q Hq 0 leR_O a d x).
Proof.
  unfold coneBoundaryFace.
  now exact (attachmentEqTop (fun d => Q.(GFace) k 0 leR_O d) (b k)
    (coneBoundary k (C.(GFace) (S k) (S q) (⇑ Hq) a x))
    (coneFace k q Hq a (coneBoundary (S k) x))
    _ (fun d => eq_sym (C.(GFaceCoh) k q Hq 0 leR_O a d x)) _ d).
Defined.

Lemma coneBoundaryBaseAp k {x y: C.(G0) (S k)} (e: x = y):
  f_equal (fun z: coneObject k => z.1) (f_equal (coneBoundary k) e) = f_equal (b (S k)) e.
Proof. now destruct e. Defined.

Lemma coneBoundaryCellAp k {x y: C.(G0) (S k)} (e: x = y) d:
  f_equal (fun z: coneObject k => (z.2 d).1) (f_equal (coneBoundary k) e) =
    f_equal (C.(GFace) k 0 leR_O d) e.
Proof. now destruct e. Defined.

Lemma coneBoundaryCoh k q (Hq: q <= k) r (Hr: r <= q) a c
  (x: C.(G0) (S (S (S k)))):
  (coneBoundaryFace k q Hq a (C.(GFace) (S (S k)) (S r) (⇑ (Hr ↕ ↑ Hq)) c x)
    • f_equal (coneFace k q Hq a) (coneBoundaryFace (S k) r (Hr ↕ ↑ Hq) c x))
    • coneExchange k q Hq r Hr a c (coneBoundary (S (S k)) x)
  = f_equal (coneBoundary k)
      (C.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c x)
    • (coneBoundaryFace k r (Hr ↕ Hq) c
        (C.(GFace) (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a x)
      • f_equal (coneFace k r (Hr ↕ Hq) c)
        (coneBoundaryFace (S k) (S q) (⇑ Hq) a x)).
Proof.
  apply (attachmentPathExt (fun a => Q.(GFace) k 0 leR_O a) (b k)).
  - unfold projT1_eq at 1 2. rewrite 4 eq_trans_map_distr.
    rewrite 2 coneFaceBaseAp, coneBoundaryBaseAp,
      4 coneBoundaryFaceBase,
      (coneExchangeBase k q Hq r Hr a c (coneBoundary (S (S k)) x)), 2 fEqualSym.
    now exact (inverseBoundaryAlgebra _ _ _ _ _ _
      (bCoh (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c x)).
  - intro d. rewrite 4 eq_trans_map_distr.
    rewrite 2 coneFaceCellAp, coneBoundaryCellAp,
      (coneBoundaryFaceCell k q Hq a
        (C.(GFace) (S (S k)) (S r) (⇑ (Hr ↕ ↑ Hq)) c x) d),
      (coneBoundaryFaceCell (S k) r (Hr ↕ ↑ Hq) c x d),
      (coneBoundaryFaceCell k r (Hr ↕ Hq) c
        (C.(GFace) (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a x) d),
      (coneBoundaryFaceCell (S k) (S q) (⇑ Hq) a x d),
      (coneExchangeCell k q Hq r Hr a c (coneBoundary (S (S k)) x) d), 2 fEqualSym.
    now exact (inverseBoundaryAlgebra _ _ _ _ _ _
      (C.(GFaceCoh2) k q Hq r Hr 0 leR_O a c d x)).
Defined.
End ConePresentation.

End GpdCone.
