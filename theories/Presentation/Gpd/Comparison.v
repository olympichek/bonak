(** Equivalences preserving face maps and their selected exchange paths. *)
Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd Equiv Notation LeSProp RewLemmas Funext PathSquares.
From Bonak.Presentation.Gpd Require Import Presentation.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Type GpdComparisonArity.
Parameter arity: HSet.
End GpdComparisonArity.

Module GpdComparison (A: GpdComparisonArity).
Import A.

(** Only the carrier, face, and exchange data enter a comparison. *)
Record FaceComparison {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g} := {
  comparisonCell k: Equiv (G k) (H k);
  comparisonFace k q (Hq: q <= k) a (t: G k.+1):
    g k q Hq a (comparisonCell k.+1 t) = comparisonCell k (f k q Hq a t);
  comparisonCoh k q (Hq: q <= k) r (Hr: r <= q) a b (t: G k.+2):
    (f_equal (g k q Hq a) (comparisonFace k.+1 r (Hr ↕ ↑ Hq) b t)
      • comparisonFace k q Hq a (f k.+1 r (Hr ↕ ↑ Hq) b t))
      • f_equal (comparisonCell k) (c k q Hq r Hr a b t) =
    d k q Hq r Hr a b (comparisonCell k.+2 t)
      • (f_equal (g k r (Hr ↕ Hq) b) (comparisonFace k.+1 q.+1 (⇑ Hq) a t)
        • comparisonFace k r (Hr ↕ Hq) b (f k.+1 q.+1 (⇑ Hq) a t));
}.
Arguments FaceComparison G H f g c d : clear implicits.

Definition composeComparison {G H I: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H} {h: GFaceType arity I}
  {c: GCohType arity f} {d: GCohType arity g} {e: GCohType arity h}
  (u: FaceComparison G H f g c d) (v: FaceComparison H I g h d e):
  FaceComparison G I f h c e.
Proof.
  refine (@Build_FaceComparison G I f h c e
    (fun k => compEquiv (u.(comparisonCell) k) (v.(comparisonCell) k))
    (fun k q Hq a t => v.(comparisonFace) k q Hq a (u.(comparisonCell) k.+1 t)
      • f_equal (v.(comparisonCell) k) (u.(comparisonFace) k q Hq a t)) _).
  intros k q Hq r Hr a b t.
  now exact (composeFaceSquare
    (u.(comparisonCell) k) (u.(comparisonCell) k.+1) (u.(comparisonCell) k.+2)
    (v.(comparisonCell) k) (v.(comparisonCell) k.+1) (v.(comparisonCell) k.+2)
    (f k q Hq a) (f k r (Hr ↕ Hq) b)
    (f k.+1 r (Hr ↕ ↑ Hq) b) (f k.+1 q.+1 (⇑ Hq) a)
    (g k q Hq a) (g k r (Hr ↕ Hq) b)
    (g k.+1 r (Hr ↕ ↑ Hq) b) (g k.+1 q.+1 (⇑ Hq) a)
    (h k q Hq a) (h k r (Hr ↕ Hq) b)
    (h k.+1 r (Hr ↕ ↑ Hq) b) (h k.+1 q.+1 (⇑ Hq) a)
    (u.(comparisonFace) k q Hq a) (u.(comparisonFace) k r (Hr ↕ Hq) b)
    (u.(comparisonFace) k.+1 r (Hr ↕ ↑ Hq) b) (u.(comparisonFace) k.+1 q.+1 (⇑ Hq) a)
    (v.(comparisonFace) k q Hq a) (v.(comparisonFace) k r (Hr ↕ Hq) b)
    (v.(comparisonFace) k.+1 r (Hr ↕ ↑ Hq) b) (v.(comparisonFace) k.+1 q.+1 (⇑ Hq) a)
    (c k q Hq r Hr a b) (d k q Hq r Hr a b) (e k q Hq r Hr a b) t
    (u.(comparisonCoh) k q Hq r Hr a b t)
    (v.(comparisonCoh) k q Hq r Hr a b (u.(comparisonCell) k.+2 t))).
Defined.

Definition shiftComparison {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g}
  (u: FaceComparison G H f g c d):
  FaceComparison (fun k => G k.+1) (fun k => H k.+1)
    (fun k q Hq a => f k.+1 q.+1 (⇑ Hq) a)
    (fun k q Hq a => g k.+1 q.+1 (⇑ Hq) a)
    (fun k q Hq r Hr a b => c k.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b)
    (fun k q Hq r Hr a b => d k.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b) :=
  @Build_FaceComparison _ _ _ _ _ _
    (fun k => u.(comparisonCell) k.+1)
    (fun k q Hq a => u.(comparisonFace) k.+1 q.+1 (⇑ Hq) a)
    (fun k q Hq r Hr a b => u.(comparisonCoh) k.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b).

Definition pointwiseComparison {G: nat -> HGpd}
  {f g: GFaceType arity G} {c: GCohType arity f} {d: GCohType arity g}
  (h: forall k q (Hq: q <= k) a t, g k q Hq a t = f k q Hq a t)
  (square: GSqType arity d c h): FaceComparison G G f g c d.
Proof.
  refine (@Build_FaceComparison G G f g c d (fun _ => idEquiv) h _).
  intros k q Hq r Hr a b t.
  rewrite f_equal_id,
    (homotopyNat (g k q Hq a) (f k q Hq a) (h k q Hq a) (h k.+1 r (Hr ↕ ↑ Hq) b t)),
    (homotopyNat (g k r (Hr ↕ Hq) b) (f k r (Hr ↕ Hq) b)
      (h k r (Hr ↕ Hq) b) (h k.+1 q.+1 (⇑ Hq) a t)).
  now exact (eq_sym (square k q Hq r Hr a b t)).
Defined.

Local Lemma invertFaceSquare {T: Type} {x0 x1 x2 x3 x4 x5: T}
  (a: x0 = x1) (b: x1 = x2) (c: x2 = x3)
  (d: x0 = x5) (e: x5 = x4) (f: x4 = x3)
  (H: (a • b) • c = d • (e • f)):
  c • (eq_sym f • eq_sym e) = (eq_sym b • eq_sym a) • d.
Proof.
  destruct a, b, e, f; cbn in *.
  now exact (eq_sym (eq_trans_refl_l c) • H • eq_sym (eq_trans_refl_l d)).
Defined.

Lemma comparisonForwardCoh {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g}
  (u: FaceComparison G H f g c d) k q (Hq: q <= k) r (Hr: r <= q) a b (t: G k.+2):
  (eq_sym (u.(comparisonFace) k q Hq a (f k.+1 r (Hr ↕ ↑ Hq) b t))
    • f_equal (g k q Hq a) (eq_sym (u.(comparisonFace) k.+1 r (Hr ↕ ↑ Hq) b t)))
    • d k q Hq r Hr a b (u.(comparisonCell) k.+2 t) =
  f_equal (u.(comparisonCell) k) (c k q Hq r Hr a b t)
    • (eq_sym (u.(comparisonFace) k r (Hr ↕ Hq) b (f k.+1 q.+1 (⇑ Hq) a t))
      • f_equal (g k r (Hr ↕ Hq) b) (eq_sym (u.(comparisonFace) k.+1 q.+1 (⇑ Hq) a t))).
Proof.
  rewrite <- 2 eq_sym_f_equal.
  now exact (eq_sym (invertFaceSquare _ _ _ _ _ _ (u.(comparisonCoh) k q Hq r Hr a b t))).
Defined.

Definition comparisonOfForward {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g}
  (e: forall k, Equiv (G k) (H k))
  (phi: forall k q (Hq: q <= k) a t,
    e k (f k q Hq a t) = g k q Hq a (e k.+1 t))
  (coh: forall k q (Hq: q <= k) r (Hr: r <= q) a b (t: G k.+2),
    (phi k q Hq a (f k.+1 r (Hr ↕ ↑ Hq) b t)
      • f_equal (g k q Hq a) (phi k.+1 r (Hr ↕ ↑ Hq) b t))
      • d k q Hq r Hr a b (e k.+2 t) =
    f_equal (e k) (c k q Hq r Hr a b t)
      • (phi k r (Hr ↕ Hq) b (f k.+1 q.+1 (⇑ Hq) a t)
        • f_equal (g k r (Hr ↕ Hq) b) (phi k.+1 q.+1 (⇑ Hq) a t))):
  FaceComparison G H f g c d.
Proof.
  refine (@Build_FaceComparison G H f g c d e
    (fun k q Hq a t => eq_sym (phi k q Hq a t)) _).
  intros k q Hq r Hr a b t.
  rewrite <- 2 eq_sym_f_equal.
  now exact (eq_sym (invertFaceSquare _ _ _ _ _ _ (coh k q Hq r Hr a b t))).
Defined.

Definition inverseComparisonFace {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  (e: forall k, Equiv (G k) (H k))
  (phi: forall k q (Hq: q <= k) a t,
    g k q Hq a (e (S k) t) = e k (f k q Hq a t))
  k q (Hq: q <= k) a (y: H (S k)):
  f k q Hq a (invEq (e (S k)) y) = invEq (e k) (g k q Hq a y) :=
  eq_sym (retEq (e k) (f k q Hq a (invEq (e (S k)) y)))
    • f_equal (invEq (e k))
      (eq_sym (phi k q Hq a (invEq (e (S k)) y))
        • f_equal (g k q Hq a) ((toIsHAE (e (S k))).(haeSec) y)).

Lemma inverseComparisonCoh {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g}
  (e: forall k, Equiv (G k) (H k))
  (phi: forall k q (Hq: q <= k) a t,
    g k q Hq a (e (S k) t) = e k (f k q Hq a t))
  (coh: forall k q (Hq: q <= k) r (Hr: r <= q) a b t,
    (f_equal (g k q Hq a) (phi (S k) r (Hr ↕ ↑ Hq) b t)
      • phi k q Hq a (f (S k) r (Hr ↕ ↑ Hq) b t))
      • f_equal (e k) (c k q Hq r Hr a b t)
    = d k q Hq r Hr a b (e (S (S k)) t)
      • (f_equal (g k r (Hr ↕ Hq) b) (phi (S k) (S q) (⇑ Hq) a t)
        • phi k r (Hr ↕ Hq) b (f (S k) (S q) (⇑ Hq) a t))):
  forall k q (Hq: q <= k) r (Hr: r <= q) a b (t: H (S (S k))),
    (f_equal (f k q Hq a) (inverseComparisonFace e phi (S k) r (Hr ↕ ↑ Hq) b t)
      • inverseComparisonFace e phi k q Hq a (g (S k) r (Hr ↕ ↑ Hq) b t))
      • f_equal (invEq (e k)) (d k q Hq r Hr a b t)
    = c k q Hq r Hr a b (invEq (e (S (S k))) t)
      • (f_equal (f k r (Hr ↕ Hq) b) (inverseComparisonFace e phi (S k) (S q) (⇑ Hq) a t)
        • inverseComparisonFace e phi k r (Hr ↕ Hq) b (g (S k) (S q) (⇑ Hq) a t)).
Proof.
  revert f c g d phi coh.
  pattern H, e. apply hgpdFamilyEquivInd.
  intros f c g d phi coh.
  cbn [idEquiv qinvEquiv eqvFun id] in phi, coh |- *.
  revert c coh.
  pattern f, phi.
  apply (homInd5S (I1 := nat) (I2 := fun _ => nat) (I3 := fun k q => q <= k)
    (I4 := fun _ _ _ => arity) (I5 := fun k _ _ _ => G (S k))
    (B := fun k _ _ _ _ => G k) g).
  intros c coh.
  assert (same: c = d).
  { apply functional_extensionality_dep; intro k.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro r.
    apply spropFunext; intro Hr.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro t.
    pose proof (coh k q Hq r Hr a b t) as h.
    cbn [f_equal] in h. rewrite f_equal_id in h.
    rewrite eq_trans_refl_l, eq_trans_refl_r in h. now exact h. }
  destruct same. intros k q Hq r Hr a b t.
  cbn [inverseComparisonFace invEq retEq toIsHAE haeSec haeInv idEquiv qinvEquiv
    eqvFun eqvIsEquiv linv linvEq rinv rinvEq secEq linvRinvEq id f_equal].
  rewrite f_equal_id. now apply eq_trans_refl_l.
Defined.

Definition inverseComparison {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  {c: GCohType arity f} {d: GCohType arity g}
  (u: FaceComparison G H f g c d): FaceComparison H G g f d c :=
  @Build_FaceComparison H G g f d c
    (fun k => symEquiv (u.(comparisonCell) k))
    (inverseComparisonFace u.(comparisonCell) u.(comparisonFace))
    (inverseComparisonCoh u.(comparisonCell) u.(comparisonFace) u.(comparisonCoh)).

Lemma inverseComparisonUnit {G H: nat -> HGpd}
  {f: GFaceType arity G} {g: GFaceType arity H}
  (e: forall k, Equiv (G k) (H k))
  (phi: forall k q (Hq: q <= k) a t,
    g k q Hq a (e (S k) t) = e k (f k q Hq a t)):
  forall k q (Hq: q <= k) a (y: H (S k)),
  (phi k q Hq a (invEq (e (S k)) y)
    • f_equal (e k) (inverseComparisonFace e phi k q Hq a y))
    • (toIsHAE (e k)).(haeSec) (g k q Hq a y)
  = f_equal (g k q Hq a) ((toIsHAE (e (S k))).(haeSec) y).
Proof.
  revert f g phi. pattern H, e. apply hgpdFamilyEquivInd.
  intros f g phi k q Hq a y.
  cbv beta iota zeta delta [inverseComparisonFace invEq retEq toIsHAE haeSec haeInv
    idEquiv qinvEquiv eqvFun eqvIsEquiv linv linvEq rinv rinvEq secEq linvRinvEq id].
  cbn [f_equal].
  rewrite 2 f_equal_id, eq_trans_refl_l.
  now apply eq_trans_sym_inv_r.
Defined.

End GpdComparison.
