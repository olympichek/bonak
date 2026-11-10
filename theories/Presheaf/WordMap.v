(** Word action preserves coherent maps of face structures. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp RewLemmas.
From Bonak.Presheaf Require Import νSemiShape WordAction.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Set Universe Polymorphism.

Lemma applyWMapId {A: HSet} (n: nat) (P Q: FaceStr A)
  (T: forall k, P.(S0) k -> Q.(S0) k)
  (H: forall k q Hq a x,
    Q.(SFace) k q Hq a (T (S k) x) = T k (P.(SFace) k q Hq a x))
  (x: P.(S0) n):
  applyWMap n n (wid n) P Q T H x • f_equal (T n) (applyW_id P x)
    = applyW_id Q (T n x).
Proof.
  revert P Q T H x. induction n as [|n IH]; intros P Q T H x.
  - now reflexivity.
  - now exact (IH (shiftStr P) (shiftStr Q) (fun k => T (S k))
      (fun k q Hq a x => H (S k) q (↑ Hq) a x) x).
Defined.

Local Lemma mapNatSkipPaste {Z: Type}
  {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11: Z}
  (q: x0 = x1) (b: x1 = x2) (c: x2 = x3) (h: x3 = x4) (i: x4 = x5)
  (d: x1 = x6) (e: x6 = x3) (j: x6 = x7) (k: x7 = x8) (l: x8 = x5)
  (E: x7 = x10) (F: x8 = x11) (u: x0 = x9) (v: x9 = x10) (t: x10 = x11)
  (natq: b • c = d • e)
  (ih: (e • h) • i = (j • k) • l)
  (square: ((q • d) • j) • E = u • v)
  (nath: k • F = E • t):
  ((q • b) • (c • h)) • i = (u • (v • t)) • (eq_sym F • l).
Proof.
  destruct q, b, c, h, i, d, j, k, u, v, F.
  cbn in natq, ih, square, nath |- *.
  rewrite eq_trans_refl_l in natq. symmetry in natq. subst e.
  cbn in ih. rewrite eq_trans_refl_l in ih. symmetry in ih. subst l.
  rewrite eq_trans_refl_l in square. subst E.
  rewrite eq_trans_refl_l in nath. symmetry in nath. subst t.
  now reflexivity.
Defined.

Local Lemma cancelTopSquare {Z: Type} {x0 x1 x2 x3 x4 x5: Z}
  (q: x0 = x1) (a: x0 = x2) (b: x2 = x3) (c: x3 = x4)
  (d: x1 = x5) (e: x5 = x4) (h: (a • b) • c = q • (d • e)):
  ((eq_sym q • a) • b) • c = d • e.
Proof. destruct q. rewrite eq_trans_refl_l in h |- *. now exact h. Defined.

(** The top-face families remain arbitrary because keeping a coordinate
    shifts the face structure without changing those chosen families. *)
Lemma applyWMapNat {A: HSet} (m: nat): forall n (w: Word A n m)
  (P Q: FaceStr A) (T: forall k, P.(S0) k -> Q.(S0) k)
  (H: forall k q Hq a x,
    Q.(SFace) k q Hq a (T (S k) x) = T k (P.(SFace) k q Hq a x))
  (TP: forall k (a: A), P.(S0) (S k) -> P.(S0) k)
  (TQ: forall k (a: A), Q.(S0) (S k) -> Q.(S0) k)
  (HP: forall k q (Hq: q <= k) a b x,
    TP k a (P.(SFace) (S k) q (↑ Hq) b x)
      = P.(SFace) k q Hq b (TP (S k) a x))
  (HQ: forall k q (Hq: q <= k) a b x,
    TQ k a (Q.(SFace) (S k) q (↑ Hq) b x)
      = Q.(SFace) k q Hq b (TQ (S k) a x))
  (K: forall k a x, TQ k a (T (S k) x) = T k (TP k a x))
  (square: forall k q (Hq: q <= k) a b x,
    (f_equal (TQ k a) (H (S k) q (↑ Hq) b x)
      • K k a (P.(SFace) (S k) q (↑ Hq) b x))
      • f_equal (T k) (HP k q Hq a b x)
    = HQ k q Hq a b (T (S (S k)) x)
      • (f_equal (Q.(SFace) k q Hq b) (K (S k) a x)
        • H k q Hq b (TP (S k) a x))) a x,
  (applyWNat m n w Q TQ HQ a (T (S m) x)
    • f_equal (TQ n a)
      (applyWMap m n w (shiftStr P) (shiftStr Q) (fun k => T (S k))
        (fun k q Hq b x => H (S k) q (↑ Hq) b x) x))
      • K n a (applyW m w (shiftStr P) x)
  = (f_equal (applyW m w Q) (K m a x)
      • applyWMap m n w P Q T H (TP m a x))
      • f_equal (T n) (applyWNat m n w P TP HP a x).
Proof.
  induction m as [|m IH]; intros n w P Q T H TP TQ HP HQ K square a x.
  - destruct n as [|n]; [destruct w|now destruct w].
    cbn [applyWNat applyWMap applyW].
    now rewrite eq_trans_refl_l, f_equal_id.
  - destruct w as [[b w]|w].
    + change
        (((f_equal (applyW m w Q) (eq_sym (HQ m m leR_refl a b (T (S (S m)) x)))
          • applyWNat m n w Q TQ HQ a (sTop (shiftStr Q) m b (T (S (S m)) x)))
          • f_equal (TQ n a)
            (f_equal (applyW m w (shiftStr Q)) (H (S m) m (↑ leR_refl) b x)
              • applyWMap m n w (shiftStr P) (shiftStr Q) (fun k => T (S k))
                (fun k q Hq b x => H (S k) q (↑ Hq) b x)
                (sTop (shiftStr P) m b x)))
          • K n a (applyW m w (shiftStr P) (sTop (shiftStr P) m b x))
        = (f_equal (fun z => applyW m w Q (sTop Q m b z)) (K (S m) a x)
            • (f_equal (applyW m w Q) (H m m leR_refl b (TP (S m) a x))
              • applyWMap m n w P Q T H (sTop P m b (TP (S m) a x))))
          • f_equal (T n)
            (f_equal (applyW m w P) (eq_sym (HP m m leR_refl a b x))
              • applyWNat m n w P TP HP a (sTop (shiftStr P) m b x))).
      rewrite 2 eq_trans_map_distr.
      rewrite (fEqualSym (applyW m w P) (HP m m leR_refl a b x)),
        (fEqualSym (T n) (f_equal (applyW m w P) (HP m m leR_refl a b x))).
      rewrite <- (f_equal_compose (Q.(SFace) m m leR_refl b) (applyW m w Q)
        (K (S m) a x)).
      refine (mapNatSkipPaste
        (f_equal (applyW m w Q) (eq_sym (HQ m m leR_refl a b (T (S (S m)) x))))
        (applyWNat m n w Q TQ HQ a (sTop (shiftStr Q) m b (T (S (S m)) x)))
        (f_equal (TQ n a) (f_equal (applyW m w (shiftStr Q))
          (H (S m) m (↑ leR_refl) b x)))
        (f_equal (TQ n a) (applyWMap m n w (shiftStr P) (shiftStr Q)
          (fun k => T (S k)) (fun k q Hq b x => H (S k) q (↑ Hq) b x)
          (sTop (shiftStr P) m b x)))
        (K n a (applyW m w (shiftStr P) (sTop (shiftStr P) m b x)))
        (f_equal (applyW m w Q) (f_equal (TQ m a) (H (S m) m (↑ leR_refl) b x)))
        (applyWNat m n w Q TQ HQ a (T (S m) (sTop (shiftStr P) m b x)))
        (f_equal (applyW m w Q) (K m a (sTop (shiftStr P) m b x)))
        (applyWMap m n w P Q T H (TP m a (sTop (shiftStr P) m b x)))
        (f_equal (T n) (applyWNat m n w P TP HP a (sTop (shiftStr P) m b x)))
        (f_equal (applyW m w Q) (f_equal (T m) (HP m m leR_refl a b x)))
        (f_equal (T n) (f_equal (applyW m w P) (HP m m leR_refl a b x)))
        (f_equal (applyW m w Q) (f_equal (Q.(SFace) m m leR_refl b) (K (S m) a x)))
        (f_equal (applyW m w Q) (H m m leR_refl b (TP (S m) a x)))
        (applyWMap m n w P Q T H (sTop P m b (TP (S m) a x))) _ _ _ _).
      * rewrite 2 f_equal_compose.
        now exact (eq_sym (homotopyNat
          (fun z => applyW m w Q (TQ m a z))
          (fun z => TQ n a (applyW m w (shiftStr Q) z))
          (fun z => applyWNat m n w Q TQ HQ a z)
          (H (S m) m (↑ leR_refl) b x))).
      * now exact (IH n w P Q T H TP TQ HP HQ K square a
          (sTop (shiftStr P) m b x)).
      * rewrite <- 4 eq_trans_map_distr.
        apply f_equal. now apply cancelTopSquare, square.
      * rewrite 2 f_equal_compose.
        now exact (eq_sym (homotopyNat
          (fun z => applyW m w Q (T m z)) (fun z => T n (applyW m w P z))
          (fun z => applyWMap m n w P Q T H z) (HP m m leR_refl a b x))).
    + destruct n as [|n]; [now destruct w|].
      now exact (IH n w (shiftStr P) (shiftStr Q) (fun k => T (S k))
        (fun k q Hq b x => H (S k) q (↑ Hq) b x)
        (fun k => TP (S k)) (fun k => TQ (S k))
        (fun k q Hq a b x => HP (S k) q (↑ Hq) a b x)
        (fun k q Hq a b x => HQ (S k) q (↑ Hq) a b x)
        (fun k a x => K (S k) a x)
        (fun k q Hq a b x => square (S k) q (↑ Hq) a b x) a x).
Defined.

Local Lemma mapCompMixedPaste {Z: Type}
  {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10: Z}
  (a: x0 = x1) (b: x1 = x2) (c: x2 = x3) (d: x3 = x4)
  (u: x0 = x5) (v: x5 = x6) (w: x6 = x7) (z: x7 = x8) (r: x8 = x4)
  (e: x1 = x9) (f: x9 = x3) (g: x9 = x10) (j: x10 = x8) (l: x10 = x6)
  (natq: b • c = e • f)
  (ih: f • d = g • (j • r))
  (square: ((a • e) • g) • l = u • v)
  (nath: j = l • (w • z)):
  (a • b) • (c • d) = u • ((v • w) • (z • r)).
Proof.
  destruct a, b, c, d, u, v, w, z, e, g.
  cbn in natq, ih, square, nath |- *.
  rewrite eq_trans_refl_l in natq. symmetry in natq. subst f.
  rewrite eq_trans_refl_l in square. subst l.
  cbn in nath. subst j.
  rewrite 2 eq_trans_refl_l in ih. symmetry in ih. subst r.
  now reflexivity.
Defined.

Local Lemma homotopyNatReverse {X Y: Type} (f g: X -> Y)
  (h: forall x, f x = g x) {x y: X} (p: x = y):
  h x = f_equal f p • (h y • f_equal g (eq_sym p)).
Proof. destruct p. now rewrite eq_trans_refl_l. Defined.

Lemma applyWMapComp {A: HSet} (p: nat): forall m n (g: Word A m p) (f: Word A n m)
  (P Q: FaceStr A) (T: forall k, P.(S0) k -> Q.(S0) k)
  (H: forall k q Hq a x,
    Q.(SFace) k q Hq a (T (S k) x) = T k (P.(SFace) k q Hq a x))
  (HP: CohOf P) (HQ: CohOf Q)
  (square: forall k q (Hq: q <= k) r (Hr: r <= q) a b x,
    (f_equal (Q.(SFace) k q Hq a) (H (S k) r (Hr ↕ ↑ Hq) b x)
      • H k q Hq a (P.(SFace) (S k) r (Hr ↕ ↑ Hq) b x))
      • f_equal (T k) (HP k q Hq r Hr a b x)
    = HQ k q Hq r Hr a b (T (S (S k)) x)
      • (f_equal (Q.(SFace) k r (Hr ↕ Hq) b) (H (S k) (S q) (⇑ Hq) a x)
        • H k r (Hr ↕ Hq) b (P.(SFace) (S k) (S q) (⇑ Hq) a x))) x,
  applyWComp p m n g f Q HQ (T p x)
    • applyWMap p n (wcomp g f) P Q T H x
  = f_equal (applyW m f Q) (applyWMap p m g P Q T H x)
    • (applyWMap m n f P Q T H (applyW p g P x)
      • f_equal (T n) (applyWComp p m n g f P HP x)).
Proof.
  induction p as [|p IH]; intros m n g f P Q T H HP HQ square x.
  - destruct m as [|m]; [|now destruct g].
    destruct n as [|n]; [|now destruct f].
    now destruct g, f.
  - destruct g as [[b g]|g].
    + change (applyWComp p m n g f Q HQ (sTop Q p b (T (S p) x))
        • (f_equal (applyW p (wcomp g f) Q) (H p p leR_refl b x)
          • applyWMap p n (wcomp g f) P Q T H (sTop P p b x))
        = f_equal (applyW m f Q)
          (f_equal (applyW p g Q) (H p p leR_refl b x)
            • applyWMap p m g P Q T H (sTop P p b x))
          • (applyWMap m n f P Q T H (applyW p g P (sTop P p b x))
            • f_equal (T n) (applyWComp p m n g f P HP (sTop P p b x)))).
      rewrite eq_trans_assoc.
      assert (natq:
        applyWComp p m n g f Q HQ (sTop Q p b (T (S p) x))
          • f_equal (applyW p (wcomp g f) Q) (H p p leR_refl b x)
        = f_equal (applyW m f Q) (f_equal (applyW p g Q) (H p p leR_refl b x))
          • applyWComp p m n g f Q HQ (T p (sTop P p b x))).
      { rewrite f_equal_compose.
        now exact (eq_sym (homotopyNat
          (fun z => applyW m f Q (applyW p g Q z))
          (fun z => applyW p (wcomp g f) Q z)
          (fun z => applyWComp p m n g f Q HQ z) (H p p leR_refl b x))). }
      rewrite natq, eqTransAssoc, (IH m n g f P Q T H HP HQ square (sTop P p b x)).
      rewrite eq_trans_map_distr.
      now rewrite eqTransAssoc.
    + destruct m as [|m]; [now destruct g|].
      destruct f as [[a f]|f].
      * change ((f_equal (applyW m f Q)
            (eq_sym (applyWNat p m g Q (sTop Q) (topCoh HQ) a (T (S p) x)))
          • applyWComp p m n g f Q HQ (sTop Q p a (T (S p) x)))
          • (f_equal (applyW p (wcomp g f) Q) (H p p leR_refl a x)
            • applyWMap p n (wcomp g f) P Q T H (sTop P p a x))
        = f_equal (fun z => applyW m f Q (sTop Q m a z))
            (applyWMap p m g (shiftStr P) (shiftStr Q) (fun k => T (S k))
              (fun k q Hq b x => H (S k) q (↑ Hq) b x) x)
          • ((f_equal (applyW m f Q) (H m m leR_refl a (applyW p g (shiftStr P) x))
              • applyWMap m n f P Q T H (sTop P m a (applyW p g (shiftStr P) x)))
            • f_equal (T n)
              (f_equal (applyW m f P) (eq_sym (applyWNat p m g P (sTop P) (topCoh HP) a x))
                • applyWComp p m n g f P HP (sTop P p a x)))).
        rewrite eq_trans_map_distr.
        rewrite <- (f_equal_compose (sTop Q m a) (applyW m f Q)
          (applyWMap p m g (shiftStr P) (shiftStr Q) (fun k => T (S k))
            (fun k q Hq b x => H (S k) q (↑ Hq) b x) x)).
        refine (mapCompMixedPaste
          (f_equal (applyW m f Q) (eq_sym (applyWNat p m g Q (sTop Q) (topCoh HQ) a (T (S p) x))))
          (applyWComp p m n g f Q HQ (sTop Q p a (T (S p) x)))
          (f_equal (applyW p (wcomp g f) Q) (H p p leR_refl a x))
          (applyWMap p n (wcomp g f) P Q T H (sTop P p a x))
          (f_equal (applyW m f Q) (f_equal (sTop Q m a)
            (applyWMap p m g (shiftStr P) (shiftStr Q) (fun k => T (S k))
              (fun k q Hq b x => H (S k) q (↑ Hq) b x) x)))
          (f_equal (applyW m f Q) (H m m leR_refl a (applyW p g (shiftStr P) x)))
          (applyWMap m n f P Q T H (sTop P m a (applyW p g (shiftStr P) x)))
          (f_equal (T n) (f_equal (applyW m f P)
            (eq_sym (applyWNat p m g P (sTop P) (topCoh HP) a x))))
          (f_equal (T n) (applyWComp p m n g f P HP (sTop P p a x)))
          (f_equal (applyW m f Q) (f_equal (applyW p g Q) (H p p leR_refl a x)))
          (applyWComp p m n g f Q HQ (T p (sTop P p a x)))
          (f_equal (applyW m f Q) (applyWMap p m g P Q T H (sTop P p a x)))
          (applyWMap m n f P Q T H (applyW p g P (sTop P p a x)))
          (f_equal (applyW m f Q) (f_equal (T m)
            (applyWNat p m g P (sTop P) (topCoh HP) a x))) _ _ _ _).
        -- rewrite f_equal_compose.
           now exact (eq_sym (homotopyNat
             (fun z => applyW m f Q (applyW p g Q z))
             (fun z => applyW p (wcomp g f) Q z)
             (fun z => applyWComp p m n g f Q HQ z) (H p p leR_refl a x))).
        -- now exact (IH m n g f P Q T H HP HQ square (sTop P p a x)).
        -- rewrite <- 4 eq_trans_map_distr. apply f_equal.
           apply cancelTopSquare.
           now exact (eq_sym (applyWMapNat p m g P Q T H (sTop P) (sTop Q)
             (topCoh HP) (topCoh HQ) (fun k a x => H k k leR_refl a x)
             (fun k q Hq a b x => square k k leR_refl q Hq a b x) a x)
             • eqTransAssoc _ _ _).
        -- rewrite 2 f_equal_compose.
           now exact (homotopyNatReverse
             (fun z => applyW m f Q (T m z)) (fun z => T n (applyW m f P z))
             (fun z => applyWMap m n f P Q T H z)
             (applyWNat p m g P (sTop P) (topCoh HP) a x)).
      * destruct n as [|n]; [now destruct f|].
        now exact (IH m n g f (shiftStr P) (shiftStr Q) (fun k => T (S k))
          (fun k q Hq a x => H (S k) q (↑ Hq) a x)
          (cohShift HP) (cohShift HQ)
          (fun k q Hq r Hr a b x => square (S k) q (↑ Hq) r Hr a b x) x).
Defined.
