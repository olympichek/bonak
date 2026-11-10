(** Composition of face comparisons and their exchange squares. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Notation RewLemmas.

Local Lemma composeForwardFaceLeg {B0 B1 C0 C1: Type}
  (f0: B0 -> C0) (f1: B1 -> C1) (b: B1 -> B0) (c: C1 -> C0)
  (beta: forall y, f0 (b y) = c (f1 y))
  {s t: B1} (p: s = t) {z: B0} (q: z = b s)
  {u: C1} (r: f1 t = u):
  (f_equal f0 q • beta s) • f_equal c (f_equal f1 p • r) =
    f_equal f0 (q • f_equal b p) • (beta t • f_equal c r).
Proof.
  destruct p; cbn [f_equal]. rewrite eq_trans_refl_l.
  now apply eqTransAssoc.
Defined.

Lemma composeForwardFaceSquare
  {A0 A1 A2 B0 B1 B2 C0 C1 C2: Type}
  (e0: A0 -> B0) (e1: A1 -> B1) (e2: A2 -> B2)
  (f0: B0 -> C0) (f1: B1 -> C1) (f2: B2 -> C2)
  (al ar: A1 -> A0) (au av: A2 -> A1)
  (bl br: B1 -> B0) (bu bv: B2 -> B1)
  (cl cr: C1 -> C0) (cu cv: C2 -> C1)
  (alphaL: forall x, e0 (al x) = bl (e1 x))
  (alphaR: forall x, e0 (ar x) = br (e1 x))
  (alphaU: forall x, e1 (au x) = bu (e2 x))
  (alphaV: forall x, e1 (av x) = bv (e2 x))
  (betaL: forall y, f0 (bl y) = cl (f1 y))
  (betaR: forall y, f0 (br y) = cr (f1 y))
  (betaU: forall y, f1 (bu y) = cu (f2 y))
  (betaV: forall y, f1 (bv y) = cv (f2 y))
  (cohA: forall x, al (au x) = ar (av x))
  (cohB: forall y, bl (bu y) = br (bv y))
  (cohC: forall z, cl (cu z) = cr (cv z))
  (x: A2)
  (squareA:
    (alphaL (au x) • f_equal bl (alphaU x)) • cohB (e2 x) =
      f_equal e0 (cohA x) • (alphaR (av x) • f_equal br (alphaV x)))
  (squareB:
    (betaL (bu (e2 x)) • f_equal cl (betaU (e2 x))) • cohC (f2 (e2 x)) =
      f_equal f0 (cohB (e2 x)) • (betaR (bv (e2 x)) • f_equal cr (betaV (e2 x)))):
  ((f_equal f0 (alphaL (au x)) • betaL (e1 (au x)))
    • f_equal cl (f_equal f1 (alphaU x) • betaU (e2 x)))
    • cohC (f2 (e2 x)) =
  f_equal (fun a => f0 (e0 a)) (cohA x)
    • ((f_equal f0 (alphaR (av x)) • betaR (e1 (av x)))
      • f_equal cr (f_equal f1 (alphaV x) • betaV (e2 x))).
Proof.
  rewrite (composeForwardFaceLeg f0 f1 bl cl betaL (alphaU x)
    (alphaL (au x)) (betaU (e2 x))),
    (composeForwardFaceLeg f0 f1 br cr betaR (alphaV x)
    (alphaR (av x)) (betaV (e2 x))).
  rewrite <- eq_trans_assoc, squareB, eq_trans_assoc,
    <- eq_trans_map_distr, squareA, eq_trans_map_distr,
    f_equal_compose.
  now apply eqTransAssoc.
Defined.

(** The comparison on a composite face is the composite of the two
    comparisons on that face. Naturality is path induction on [p]. *)
Local Lemma composeFaceLeg {B0 B1 C0 C1: Type}
  (f0: B0 -> C0) (f1: B1 -> C1) (b: B1 -> B0) (c: C1 -> C0)
  (beta: forall y, c (f1 y) = f0 (b y))
  {s t: B1} (p: s = t) {z: C1} (q: z = f1 s)
  {u: B0} (r: b t = u):
  f_equal c (q • f_equal f1 p) • (beta t • f_equal f0 r) =
    (f_equal c q • beta s) • f_equal f0 (f_equal b p • r).
Proof.
  destruct p; cbn [f_equal].
  now rewrite eq_trans_refl_r, eq_trans_refl_l, eq_trans_assoc.
Defined.

Lemma composeFaceSquare
  {A0 A1 A2 B0 B1 B2 C0 C1 C2: Type}
  (e0: A0 -> B0) (e1: A1 -> B1) (e2: A2 -> B2)
  (f0: B0 -> C0) (f1: B1 -> C1) (f2: B2 -> C2)
  (al ar: A1 -> A0) (au av: A2 -> A1)
  (bl br: B1 -> B0) (bu bv: B2 -> B1)
  (cl cr: C1 -> C0) (cu cv: C2 -> C1)
  (alphaL: forall x, bl (e1 x) = e0 (al x))
  (alphaR: forall x, br (e1 x) = e0 (ar x))
  (alphaU: forall x, bu (e2 x) = e1 (au x))
  (alphaV: forall x, bv (e2 x) = e1 (av x))
  (betaL: forall y, cl (f1 y) = f0 (bl y))
  (betaR: forall y, cr (f1 y) = f0 (br y))
  (betaU: forall y, cu (f2 y) = f1 (bu y))
  (betaV: forall y, cv (f2 y) = f1 (bv y))
  (cohA: forall x, al (au x) = ar (av x))
  (cohB: forall y, bl (bu y) = br (bv y))
  (cohC: forall z, cl (cu z) = cr (cv z))
  (x: A2)
  (squareA:
    (f_equal bl (alphaU x) • alphaL (au x)) • f_equal e0 (cohA x) =
      cohB (e2 x) • (f_equal br (alphaV x) • alphaR (av x)))
  (squareB:
    (f_equal cl (betaU (e2 x)) • betaL (bu (e2 x))) • f_equal f0 (cohB (e2 x)) =
      cohC (f2 (e2 x)) • (f_equal cr (betaV (e2 x)) • betaR (bv (e2 x)))):
  (f_equal cl (betaU (e2 x) • f_equal f1 (alphaU x))
    • (betaL (e1 (au x)) • f_equal f0 (alphaL (au x))))
    • f_equal (fun a => f0 (e0 a)) (cohA x) =
  cohC (f2 (e2 x))
    • (f_equal cr (betaV (e2 x) • f_equal f1 (alphaV x))
      • (betaR (e1 (av x)) • f_equal f0 (alphaR (av x)))).
Proof.
  rewrite (composeFaceLeg f0 f1 bl cl betaL (alphaU x)
    (betaU (e2 x)) (alphaL (au x))),
    (composeFaceLeg f0 f1 br cr betaR (alphaV x)
    (betaV (e2 x)) (alphaR (av x))).
  rewrite <- (f_equal_compose e0 f0 (cohA x)), <- eq_trans_assoc,
    <- eq_trans_map_distr, squareA, eq_trans_map_distr, eq_trans_assoc,
    squareB.
  now rewrite <- eq_trans_assoc.
Defined.

