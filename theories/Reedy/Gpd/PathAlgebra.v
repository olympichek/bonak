(** Generic path algebra: squares and cubes of path-diagram arrows, and
    identities between composites of paths. Nothing here is specific to Reedy
    diagrams. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd Equiv Notation RewLemmas.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.

Set Primitive Projections.
Set Printing Projections.

(** A cube of diagram squares whose comparison arrows are identity arrows
    given by object equalities. *)
Set Keyed Unification.

Section IsomorphismCube.
Context {C: Category} (F: PathDiagramFamily C).
Local Abbreviation D := (pathData _ _ F.(pfStr)).

Definition diagramSquare {a b c d: C.(CObj)}
  (f: C.(CHom) a b) (g: C.(CHom) b d)
  (h: C.(CHom) a c) (j: C.(CHom) c d)
  (square: f ⨟ g = h ⨟ j) (x: F.(pfObj) a):
  D.(phom) g (D.(phom) f x) = D.(phom) j (D.(phom) h x) :=
  D.(pcomp) f g x • (phomEq D square x • eq_sym (D.(pcomp) h j x)).

Definition diagramFactor {a b c: C.(CObj)} (e: a = b)
  (g: C.(CHom) b c) (h: C.(CHom) a c)
  (factor: idToHom e ⨟ g = h) (x: F.(pfObj) a):
  D.(phom) g (D.(phom) (idToHom e) x) = D.(phom) h x :=
  D.(pcomp) (idToHom e) g x • phomEq D factor x.

Lemma diagramFactorRefl {a b: C.(CObj)} (f: C.(CHom) a b)
  (factor: idToHom (@eq_refl _ a) ⨟ f = f) (x: F.(pfObj) a):
  diagramFactor eq_refl f f factor x = f_equal (D.(phom) f) (pidPt D a x).
Proof.
  unfold diagramFactor. cbn [idToHom].
  refine (transCongR (pcompUnitLPt D (pathUnitL _ _ F.(pfStr))
    a b f factor x) _ • _).
  now apply transSymCancelR2.
Defined.

Local Lemma squareUnitAlgebra {T: Type} {a b c d e: T}
  (p: a = b) (q: c = b) (r: d = b) (s: e = b) (h: c = e)
  (comparison: h • s = q):
  (p • eq_sym q) • (h • eq_sym (r • eq_sym s)) = p • eq_sym r.
Proof.
  destruct p, q, r, s. cbn in comparison |- *.
  now rewrite comparison.
Defined.

Lemma diagramSquareUnit {a b: C.(CObj)} (f: C.(CHom) a b)
  (square: f ⨟ C.(cid) b = C.(cid) a ⨟ f) (x: F.(pfObj) a):
  diagramSquare f (C.(cid) b) (C.(cid) a) f square x =
    pidPt D b (D.(phom) f x) • eq_sym (f_equal (D.(phom) f) (pidPt D a x)).
Proof.
  unfold diagramSquare.
  refine (transCongR (pcompUnitRPt D (pathUnitR _ _ F.(pfStr))
    a b f (C.(cidr) f) x) _ • _).
  refine (transCongL _ (transCongL _ (f_equal (@eq_sym _ _ _)
    (pcompUnitLPt D (pathUnitL _ _ F.(pfStr)) a b f (C.(cidl) f) x))) • _).
  apply squareUnitAlgebra.
  refine (eq_sym (eq_trans_map_distr
    (fun w: C.(CHom) a b => D.(phom) w x) square (C.(cidl) f)) • _).
  apply (f_equal (fun e: f ⨟ C.(cid) b = f => phomEq D e x)).
  now apply (C.(CHom) a b).(UIP).
Defined.

Lemma diagramIsoCube {a0 a1 b0 b1 c0 c1: C.(CObj)}
  (e0: a0 = b0) (e1: a1 = b1)
  (f: C.(CHom) a0 a1) (g: C.(CHom) b0 b1) (h: C.(CHom) c0 c1)
  (t0: C.(CHom) a0 c0) (t1: C.(CHom) a1 c1)
  (z0: C.(CHom) b0 c0) (z1: C.(CHom) b1 c1)
  (reindex: f ⨟ idToHom e1 = idToHom e0 ⨟ g)
  (factor0: idToHom e0 ⨟ z0 = t0) (factor1: idToHom e1 ⨟ z1 = t1)
  (raw: f ⨟ t1 = t0 ⨟ h) (normalized: g ⨟ z1 = z0 ⨟ h)
  (x: F.(pfObj) a0):
  f_equal (D.(phom) z1) (diagramSquare f (idToHom e1) (idToHom e0) g reindex x)
    • (diagramSquare g z1 z0 h normalized (D.(phom) (idToHom e0) x)
      • f_equal (D.(phom) h) (diagramFactor e0 z0 t0 factor0 x)) =
  diagramFactor e1 z1 t1 factor1 (D.(phom) f x)
    • diagramSquare f t1 t0 h raw x.
Proof.
  destruct e0, e1.
  assert (ef: f = g).
  { exact (eq_sym (C.(cidr) f) • (reindex • C.(cidl) g)). }
  destruct ef.
  assert (et0: z0 = t0).
  { exact (eq_sym (C.(cidl) z0) • factor0). }
  destruct et0.
  assert (et1: z1 = t1).
  { exact (eq_sym (C.(cidl) z1) • factor1). }
  destruct et1.
  replace normalized with raw by now apply (C.(CHom) _ _).(UIP).
  rewrite diagramSquareUnit, 2 diagramFactorRefl, eq_trans_map_distr, fEqualSym.
  rewrite 2 f_equal_compose.
  pose proof (homotopyNat
    (fun y => D.(phom) z1 (D.(phom) f y))
    (fun y => D.(phom) h (D.(phom) z0 y))
    (diagramSquare f z1 z0 h raw) (pidPt D a0 x)) as natural.
  rewrite <- natural.
  now apply transCancelMid2.
Defined.

End IsomorphismCube.

(** A cube of diagram squares whose four comparison arrows are given by
    object equalities. *)

Local Lemma boundaryCubeAlgebra {T: Type} {A B C D E F G H: T}
  (p: A = B) (q: C = B) (r: D = B) (s: D = E)
  (a: A = G) (b: G = F) (c: H = F) (d: E = F) (t: B = F)
  (targetNatural: a • b = p • t) (sourceNatural: r • t = s • d):
  (p • eq_sym q) • ((q • eq_sym r) • s) =
    a • ((b • eq_sym c) • (c • eq_sym d)).
Proof.
  destruct p, q, r, s, a, b, c.
  cbn in targetNatural, sourceNatural |- *.
  rewrite eq_trans_refl_l in targetNatural.
  rewrite 2 eq_trans_refl_l in sourceNatural.
  rewrite <- targetNatural in sourceNatural.
  now rewrite <- sourceNatural.
Defined.

Section BoundaryCube.
Context {C: Category} (F: PathDiagramFamily C).
Local Abbreviation D := (pathData _ _ F.(pfStr)).

(** The four comparison edges are object equalities. After path
    induction, their diagram comparisons are the chosen unit paths;
    naturality of those paths supplies the cube equation. *)
Lemma diagramBoundaryCube {a0 a1 b0 b1 c0 c1 d0 d1: C.(CObj)}
  (ea0: a0 = b0) (ea1: a1 = b1) (ec0: c0 = d0) (ec1: c1 = d1)
  (f: C.(CHom) a0 a1) (g: C.(CHom) b0 b1)
  (h: C.(CHom) c0 c1) (j: C.(CHom) d0 d1)
  (t0: C.(CHom) a0 c0) (t1: C.(CHom) a1 c1)
  (z0: C.(CHom) b0 d0) (z1: C.(CHom) b1 d1)
  (whole: f ⨟ idToHom ea1 = idToHom ea0 ⨟ g)
  (component: h ⨟ idToHom ec1 = idToHom ec0 ⨟ j)
  (boundary0: t0 ⨟ idToHom ec0 = idToHom ea0 ⨟ z0)
  (boundary1: t1 ⨟ idToHom ec1 = idToHom ea1 ⨟ z1)
  (raw: f ⨟ t1 = t0 ⨟ h) (normalized: g ⨟ z1 = z0 ⨟ j)
  (x: F.(pfObj) a0):
  diagramSquare F t1 (idToHom ec1) (idToHom ea1) z1 boundary1 (D.(phom) f x)
    • (f_equal (D.(phom) z1)
        (diagramSquare F f (idToHom ea1) (idToHom ea0) g whole x)
      • diagramSquare F g z1 z0 j normalized (D.(phom) (idToHom ea0) x)) =
  f_equal (D.(phom) (idToHom ec1)) (diagramSquare F f t1 t0 h raw x)
    • (diagramSquare F h (idToHom ec1) (idToHom ec0) j component (D.(phom) t0 x)
      • f_equal (D.(phom) j)
          (diagramSquare F t0 (idToHom ec0) (idToHom ea0) z0 boundary0 x)).
Proof.
  destruct ea0, ea1, ec0, ec1.
  assert (ef: f = g).
  { exact (eq_sym (C.(cidr) f) • (whole • C.(cidl) g)). }
  destruct ef.
  assert (eh: h = j).
  { exact (eq_sym (C.(cidr) h) • (component • C.(cidl) j)). }
  destruct eh.
  assert (et0: t0 = z0).
  { exact (eq_sym (C.(cidr) t0) • (boundary0 • C.(cidl) z0)). }
  destruct et0.
  assert (et1: t1 = z1).
  { exact (eq_sym (C.(cidr) t1) • (boundary1 • C.(cidl) z1)). }
  destruct et1.
  replace normalized with raw by now apply (C.(CHom) _ _).(UIP).
  change
    (diagramSquare F t1 (C.(cid) c1) (C.(cid) a1) t1 boundary1 (D.(phom) f x)
      • (f_equal (D.(phom) t1)
          (diagramSquare F f (C.(cid) a1) (C.(cid) a0) f whole x)
        • diagramSquare F f t1 t0 h raw (D.(phom) (C.(cid) a0) x)) =
    f_equal (D.(phom) (C.(cid) c1)) (diagramSquare F f t1 t0 h raw x)
      • (diagramSquare F h (C.(cid) c1) (C.(cid) c0) h component (D.(phom) t0 x)
        • f_equal (D.(phom) h)
            (diagramSquare F t0 (C.(cid) c0) (C.(cid) a0) t0 boundary0 x))).
  rewrite (diagramSquareUnit F t1 boundary1 (D.(phom) f x)),
    (diagramSquareUnit F f whole x),
    (diagramSquareUnit F h component (D.(phom) t0 x)),
    (diagramSquareUnit F t0 boundary0 x).
  rewrite 2 eq_trans_map_distr, 2 fEqualSym, 2 f_equal_compose.
  apply (boundaryCubeAlgebra _ _ _ _ _ _ _ _
    (diagramSquare F f t1 t0 h raw x)).
  - pose proof (homotopyNat (D.(phom) (C.(cid) c1)) (fun y => y)
      (pidPt D c1) (diagramSquare F f t1 t0 h raw x)) as natural.
    now rewrite f_equal_id in natural.
  - now exact (homotopyNat
      (fun y => D.(phom) t1 (D.(phom) f y))
      (fun y => D.(phom) h (D.(phom) t0 y))
      (diagramSquare F f t1 t0 h raw) (pidPt D a0 x)).
Defined.

End BoundaryCube.

Lemma diagramBoundaryCubeAlong {C: Category} (F: PathDiagramFamily C)
  {a0 a1 b0 b1 c0 c1 d0 d1: C.(CObj)}
  (ea0: a0 = b0) (ea1: a1 = b1) (ec0: c0 = d0) (ec1: c1 = d1)
  (sa0: C.(CHom) a0 b0) (sa1: C.(CHom) a1 b1)
  (sc0: C.(CHom) c0 d0) (sc1: C.(CHom) c1 d1)
  (ha0: sa0 = idToHom ea0) (ha1: sa1 = idToHom ea1)
  (hc0: sc0 = idToHom ec0) (hc1: sc1 = idToHom ec1)
  (f: C.(CHom) a0 a1) (g: C.(CHom) b0 b1)
  (h: C.(CHom) c0 c1) (j: C.(CHom) d0 d1)
  (t0: C.(CHom) a0 c0) (t1: C.(CHom) a1 c1)
  (z0: C.(CHom) b0 d0) (z1: C.(CHom) b1 d1)
  (whole: f ⨟ sa1 = sa0 ⨟ g) (component: h ⨟ sc1 = sc0 ⨟ j)
  (boundary0: t0 ⨟ sc0 = sa0 ⨟ z0) (boundary1: t1 ⨟ sc1 = sa1 ⨟ z1)
  (raw: f ⨟ t1 = t0 ⨟ h) (normalized: g ⨟ z1 = z0 ⨟ j)
  (x: F.(pfObj) a0):
  let D := pathData _ _ F.(pfStr) in
  diagramSquare F t1 sc1 sa1 z1 boundary1 (D.(phom) f x)
    • (f_equal (D.(phom) z1) (diagramSquare F f sa1 sa0 g whole x)
      • diagramSquare F g z1 z0 j normalized (D.(phom) sa0 x)) =
  f_equal (D.(phom) sc1) (diagramSquare F f t1 t0 h raw x)
    • (diagramSquare F h sc1 sc0 j component (D.(phom) t0 x)
      • f_equal (D.(phom) j) (diagramSquare F t0 sc0 sa0 z0 boundary0 x)).
Proof.
  subst sa0 sa1 sc0 sc1.
  now exact (diagramBoundaryCube F ea0 ea1 ec0 ec1 f g h j t0 t1 z0 z1
    whole component boundary0 boundary1 raw normalized x).
Defined.

Unset Keyed Unification.

(** Identities between composites of paths: maps of composites,
    cancellations and pasted triangles. *)
Lemma mapTrans {B C: Type} (F: B -> C) {x y z: B} (p: x = y) (q: y = z):
  f_equal F (p • q) = f_equal F p • f_equal F q.
Proof. now destruct p, q. Defined.

Lemma mappedInverseCancel {B C: Type} (F: B -> C) {x y z: B}
  (e: x = y) (h: y = z):
  f_equal F (eq_sym e) • f_equal F (e • h) = f_equal F h.
Proof. now destruct e, h. Defined.

Lemma inverseCancel {T: Type} {x y z: T} (p: x = y) (q: y = z):
  eq_sym p • (p • q) = q.
Proof. now destruct p, q. Defined.

Lemma inverseComposite {T: Type} {x y z: T} (p: x = y) (q: y = z):
  eq_sym (p • q) = eq_sym q • eq_sym p.
Proof. now destruct p, q. Defined.

Lemma inverseSquare {T: Type} {a b c d: T}
  (p: a = b) (q: b = c) (r: a = d) (s: d = c)
  (h: eq_sym p • r = q • eq_sym s): p • q = r • s.
Proof.
  destruct p, s. cbn in h |- *.
  rewrite eq_trans_refl_l in h |- *. now symmetry.
Defined.

Lemma conjugatePaste {T: Type} {a b c d v w y z: T}
  (p: a = v) (q: b = w) (r: c = y) (s: v = w) (t: w = y)
  (u: c = d) (h: y = z) (j: d = z) (triangle: r • h = u • j):
  (p • (s • eq_sym q)) • ((q • (t • eq_sym r)) • u)
    = p • ((s • (t • h)) • eq_sym j).
Proof.
  destruct p, q, r, s, t, u. cbn in triangle |- *.
  rewrite 2 eq_trans_refl_l in triangle. rewrite triangle. now destruct j.
Defined.

Lemma reversePasting {T: Type} {a b c d e: T}
  (p: a = b) (q: b = c) (r: c = d) (s: a = e) (t: e = d)
  (h: p • (q • r) = s • t):
  r • eq_sym t = eq_sym q • (eq_sym p • s).
Proof.
  destruct p, q, r, s. cbn in h |- *.
  rewrite eq_trans_refl_l in h. rewrite <- h. now reflexivity.
Defined.

(** The component of the identity transformation of a path of functors. *)
Lemma natComponent {C D: Category} {U V: Functor C D}
  (e: U = V) (i: C.(CObj)):
  (@idToHom (functorCategory C D) _ _ e).(ncomp) i =
    @idToHom D _ _ (f_equal (fun W: Functor C D => W.(fobj) i) e).
Proof. now destruct e. Defined.

(** Prepending a fixed path is an equivalence of path types. *)
Definition prependPathEquiv {T: Type} {x y z: T} (e: x = y): Equiv (y = z) (x = z) :=
  qinvEquiv (fun p => e • p) (fun p => eq_sym e • p)
    (fun p => eq_trans_sym_cancel_l e p) (fun p => transSymCancelL e p).
