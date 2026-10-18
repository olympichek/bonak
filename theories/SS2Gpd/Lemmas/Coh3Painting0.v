(** Projecting the first component of a dependent pair preserves the
    chosen map and naturality squares and the sigma hexagon. The final
    lemma assembles these laws into a dependent permutahedral coherence. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT Notation RewLemmas Coh2Shapes.
From Bonak.SSGpd Require Import Pasting Coh3Shapes Lemmas.
Set Keyed Unification.

Local Lemma sigT_eq_dep_normalize_fst_map_change {X: Type} {P: X -> Type}
  (R: {x: X &T P x} -> Type) {Y: Type} {Q: Y -> Type}
  (f: X -> Y) (g: forall x, P x -> Q (f x)) {x y: X} {u: P x} {v: P y}
  {p p': x = y} {h: rew [P] p in u = v} {h': rew [P] p' in u = v}
  (H: p = p') (HH: rew [fun e => rew [P] e in u = v] H in h = h')
  {t t': (x; u) = (y; v)} (N: t = (= p; h)) (N': t' = (= p'; h'))
  {r: R (x; u)} {s: R (y; v)}
  (d: rew [R] t in r = s) (d': rew [R] t' in r = s)
  (D: rew [fun e => rew [R] e in r = s]
    (N • (eq_existT_curried_eq H HH • eq_sym N')) in d = d'):
  let L := eq_existT_curried_dep (Q := R) (H := p) (Hu := h)
    (Hv := rew [fun e => rew [R] e in r = s] N in d) in
  let RR := eq_existT_curried_dep (Q := R) (H := p') (Hu := h')
    (Hv := rew [fun e => rew [R] e in r = s] N' in d') in
  let M := fun (e: x = y)
    (z: rew [fun x => {u: P x &T R (x; u)}] e in (u; r) = (v; s)) =>
    sigT_map_eq (Q := Q) (f := f) (fun x (uv: {u: P x &T R (x; u)}) => g x uv.1) z in
  let ML := sigT_map_eq_fst g
    (rew [fun e => rew [R] e in r = s] N in d) in
  let MR := sigT_map_eq_fst g
    (rew [fun e => rew [R] e in r = s] N' in d') in
  let C := f_equal (fun e => f_equal f e) H in
  dpath_change (P := fun e => rew [Q] e in g x u = g y v) (p := C) (eq_sym ML)
    (sigT_map_eq M (sigT_eq_dep_normalize R H HH N N' d d' D))
    (eq_sym MR) =
  sigT_map_eq (fun e (z: rew [P] e in u = v) => sigT_map_eq g z) HH.
Proof.
  subst t t'.
  destruct H, HH.
  destruct p, h, d.
  cbn in *.
  destruct D.
  now reflexivity.
Defined.

Local Lemma dpath_change_cancel_normalizations {X: Type} {P: X -> Type}
  {x y: X} {p: x = y} {a a0 a1: P x} {b b0 b1: P y}
  (s: a = a0) (sl: a0 = a1) (t: b = b0) (tr: b0 = b1)
  (h: rew [P] p in a0 = b0):
  dpath_change (eq_sym (s • sl)) (dpath_change s h t) (eq_sym (t • tr)) =
  dpath_change (eq_sym sl) h (eq_sym tr).
Proof.
  destruct s, sl, t, tr.
  unfold dpath_change. cbn [eq_sym f_equal].
  rewrite 3 eq_trans_refl_l.
  now rewrite 2 eq_trans_refl_r.
Defined.

Section MappedHexProjection.
Context
  {A1 A2 A3 B: Type}
  {P1: A1 -> Type} {R1: forall a, P1 a -> Type}
  {P2: A2 -> Type} {R2: forall a, P2 a -> Type}
  {P3: A3 -> Type} {R3: forall a, P3 a -> Type}
  {P': B -> Type} {R': forall b, P' b -> Type}
  (f1: A1 -> B) (g1: forall a, P1 a -> P' (f1 a))
  (h1: forall a u, R1 a u -> R' (f1 a) (g1 a u))
  (f3: A3 -> B) (g3: forall a, P3 a -> P' (f3 a))
  (h3: forall a u, R3 a u -> R' (f3 a) (g3 a u))
  (f2: A2 -> B) (g2: forall a, P2 a -> P' (f2 a))
  (h2: forall a u, R2 a u -> R' (f2 a) (g2 a u))
  {x0 x1: A1} {x2 x3: A3} {x1' x2': A2}
  {u0: P1 x0} {v0: R1 x0 u0} {u1: P1 x1} {v1: R1 x1 u1}
  {u2: P3 x2} {v2: R3 x2 u2} {u3: P3 x3} {v3: R3 x3 u3}
  {u1': P2 x1'} {v1': R2 x1' u1'} {u2': P2 x2'} {v2': R2 x2' u2'}
  (H1: x0 = x1) (Hu1: rew [P1] H1 in u0 = u1)
  (Hv1: rew [fun z => R1 z.1 z.2] (= H1; Hu1) in
    (v0: (fun z => R1 z.1 z.2) (x0; u0)) = v1)
  (H2: f1 x1 = f3 x2) (Hu2: rew [P'] H2 in g1 x1 u1 = g3 x2 u2)
  (Hv2: rew [fun z => R' z.1 z.2] (= H2; Hu2) in
    (h1 x1 u1 v1: (fun z => R' z.1 z.2) (f1 x1; g1 x1 u1)) = h3 x2 u2 v2)
  (H3: x2 = x3) (Hu3: rew [P3] H3 in u2 = u3)
  (Hv3: rew [fun z => R3 z.1 z.2] (= H3; Hu3) in
    (v2: (fun z => R3 z.1 z.2) (x2; u2)) = v3)
  (H1': f1 x0 = f2 x1') (Hu1': rew [P'] H1' in g1 x0 u0 = g2 x1' u1')
  (Hv1': rew [fun z => R' z.1 z.2] (= H1'; Hu1') in
    (h1 x0 u0 v0: (fun z => R' z.1 z.2) (f1 x0; g1 x0 u0)) = h2 x1' u1' v1')
  (H2': x1' = x2') (Hu2': rew [P2] H2' in u1' = u2')
  (Hv2': rew [fun z => R2 z.1 z.2] (= H2'; Hu2') in
    (v1': (fun z => R2 z.1 z.2) (x1'; u1')) = v2')
  (H3': f2 x2' = f3 x3) (Hu3': rew [P'] H3' in g2 x2' u2' = g3 x3 u3)
  (Hv3': rew [fun z => R' z.1 z.2] (= H3'; Hu3') in
    (h2 x2' u2' v2': (fun z => R' z.1 z.2) (f2 x2'; g2 x2' u2')) = h3 x3 u3 v3)
  (HH: hexagonal_coherence f1 f3 f2 H1 H3 H2' H2 H1' H3')
  (HHu: hexagonal_coherence_dep g1 g3 g2 HH Hu1 Hu3 Hu2' Hu2 Hu1' Hu3')
  (HHv: hexagonal_coherence_dep
    (Q := fun z: {a: B &T P' a} => R' z.1 z.2)
    (f1 := fun z: {a: A1 &T P1 a} => (f1 z.1; g1 z.1 z.2))
    (f2 := fun z: {a: A3 &T P3 a} => (f3 z.1; g3 z.1 z.2))
    (f3 := fun z: {a: A2 &T P2 a} => (f2 z.1; g2 z.1 z.2))
    (fun z => h1 z.1 z.2) (fun z => h3 z.1 z.2) (fun z => h2 z.1 z.2)
    (eq_existT_curried_hex f1 g1 f2 g2 f3 g3 HH HHu)
    Hv1 Hv3 Hv2' Hv2 Hv1' Hv3').

Context {Output: Type} {QOutput: Output -> Type}
  (MapOutput: B -> Output)
  (FiberOutput: forall b, P' b -> QOutput (MapOutput b)).

Let S := fun z: {x: B &T P' x} => R' z.1 z.2.

Let T1 := fun z: {x: A1 &T P1 x} => (f1 z.1; g1 z.1 z.2).

Let T3 := fun z: {x: A3 &T P3 x} => (f3 z.1; g3 z.1 z.2).

Let T2 := fun z: {x: A2 &T P2 x} => (f2 z.1; g2 z.1 z.2).

Let V1 := fun z: {x: A1 &T P1 x} => h1 z.1 z.2.

Let V3 := fun z: {x: A3 &T P3 x} => h3 z.1 z.2.

Let V2 := fun z: {x: A2 &T P2 x} => h2 z.1 z.2.

Let N1 := f_equal_eq_existT_curried f1 g1 H1 Hu1.

Let N3 := f_equal_eq_existT_curried f3 g3 H3 Hu3.

Let N2 := f_equal_eq_existT_curried f2 g2 H2' Hu2'.

Let NL := sigT_path_paste (sigT_path_paste (q := H2) (k := Hu2) N1 eq_refl) N3.

Let NR := sigT_path_paste (p := H1') (h := Hu1') eq_refl (sigT_path_paste (q := H3')
  (k := Hu3') N2 eq_refl).

Let EL := sigT_hex_pair_left_normalize f1 g1 h1 f3 g3 h3
  H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3.

Let ER := sigT_hex_pair_right_normalize f1 g1 h1 f3 g3 h3 f2 g2 h2
  H1' Hu1' Hv1' H2' Hu2' Hv2' H3' Hu3' Hv3'.

Let PairHex := eq_existT_curried_hex_dep f1 g1 h1 f3 g3 h3 f2 g2 h2
  H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3
  H1' Hu1' Hv1' H2' Hu2' Hv2' H3' Hu3' Hv3' HH HHu HHv.

Let M := fun (e: f1 x0 = f3 x3)
  (z: rew [fun b => {u: P' b &T R' b u}] e in
    (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)) =>
  sigT_map_eq (Q := QOutput) (f := MapOutput)
    (fun b (uv: {u: P' b &T R' b u}) => FiberOutput b uv.1) z.

Let L0 := (f_equal f1 H1 • H2) • f_equal f3 H3.

Let R0 := H1' • (f_equal f2 H2' • H3').

Let ML := sigT_map_eq_fst FiberOutput
  (rew [fun e: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
    rew [S] e in (h1 x0 u0 v0: S (f1 x0; g1 x0 u0)) = h3 x3 u3 v3]
    NL in ((sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙ Hv2) ⊙ sigT_map_eq (f := T3) (Q := S) V3 Hv3)).

Let MR := sigT_map_eq_fst FiberOutput
  (rew [fun e: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
    rew [S] e in (h1 x0 u0 v0: S (f1 x0; g1 x0 u0)) = h3 x3 u3 v3]
    NR in (Hv1' ⊙ (sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙ Hv3'))).

(** First projection of the selected paired hexagon, after its two
    routes have been normalized. The supplied higher hexagon is retained
    throughout the computation. *)
Local Lemma eq_existT_curried_hex_dep_fst_map_normalized:
  dpath_change
    (P := fun e => rew [QOutput] e in FiberOutput (f1 x0) (g1 x0 u0) = FiberOutput (f3 x3) (g3 x3 u3))
    (p := f_equal (fun e => f_equal MapOutput e) HH)
    (eq_sym (f_equal (M L0) EL • ML))
    (sigT_map_eq M PairHex)
    (eq_sym (f_equal (M R0) ER • MR)) =
  sigT_map_eq (fun e (z: rew [P'] e in g1 x0 u0 = g3 x3 u3) =>
    sigT_map_eq FiberOutput z) HHu.
Proof.
  change (dpath_change
    (P := fun e => rew [QOutput] e in FiberOutput (f1 x0) (g1 x0 u0) = FiberOutput (f3 x3) (g3 x3 u3))
    (p := f_equal (fun e => f_equal MapOutput e) HH)
    (eq_sym (f_equal (M L0) EL • ML))
    (sigT_map_eq (f := fun e => f_equal MapOutput e) M
      (dpath_change
        (P := fun e => rew [fun b => {u: P' b &T R' b u}] e in
          (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3))
        (p := HH) EL
          (sigT_eq_dep_normalize S HH HHu NL NR
            ((sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙ Hv2) ⊙ sigT_map_eq (f := T3) (Q := S) V3 Hv3)
            (Hv1' ⊙ (sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙ Hv3')) HHv)
          ER)) (eq_sym (f_equal (M R0) ER • MR)) =
    sigT_map_eq (fun e (z: rew [P'] e in g1 x0 u0 = g3 x3 u3) =>
      sigT_map_eq FiberOutput z) HHu).
  rewrite dpath_change_map.
  unfold L0, R0.
  rewrite (dpath_change_cancel_normalizations
    (P := fun e => rew [QOutput] e in FiberOutput (f1 x0) (g1 x0 u0) = FiberOutput (f3 x3) (g3 x3 u3))
    (f_equal (M L0) EL) ML (f_equal (M R0) ER) MR).
  now exact (sigT_eq_dep_normalize_fst_map_change S MapOutput FiberOutput HH HHu NL NR
    ((sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙ Hv2) ⊙ sigT_map_eq (f := T3) (Q := S) V3 Hv3)
    (Hv1' ⊙ (sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙ Hv3')) HHv).
Defined.

End MappedHexProjection.

Local Arguments rew_cohLayer_hex {T1 T2 T3 X} P {S2 S3} rf0 {rfF rfG} F G
  {d1 d2} E1 {m1 m2} C2 {n1 n2} D2 C1 D1 K aL aR _ _.

Local Lemma rew_coh2Painting_restr0_projection {TU TR W TL: Type}
  {P: TL -> Type} {S: TU -> Type} {SR: TR -> Type}
  {rq: TU -> TL} {rr: TR -> TL} {r0: W -> TL}
  (F: forall m, S m -> P (rq m))
  (G: forall n, SR n -> P (rr n))
  {d1 d2: W} (E1: d1 = d2)
  {m1 m2: TU} (e2: m1 = m2)
  {n1 n2: TR} (e5: n1 = n2)
  (pQ: rq m2 = r0 d1) (pR: rr n2 = r0 d2)
  (KA: rq m1 = rr n1)
  (aL: S m1) (aR: SR n1)
  (HK: rew [P] KA in F m1 aL = G n1 aR)
  (κ: hexagonal_coherence rq r0 rr e2 E1 e5 pQ KA pR)
  (A0 := rew [P] pQ in F m2 (rew [S] e2 in aL))
  (B0 := rew [P] pR in G n2 (rew [SR] e5 in aR))
  (L := rew_cohLayer_hex P r0 F G E1 e2 e5 pQ pR KA aL aR HK κ)
  (R: forall d, P (r0 d) -> Type)
  {v: R d1 A0} {w: R d2 B0}
  (Hv: rew [fun z: {d: W &T P (r0 d)} => R z.1 z.2] (= E1; L) in
    (v: (fun z: {d: W &T P (r0 d)} => R z.1 z.2) (d1; A0)) = w)
  (EM := sigT_map_eq_fst (P := fun d => P (r0 d)) (Q := P)
    (f := r0) (R := R) (fun _ a => a) Hv)
  (Canon := @rew_coh2Painting_restr0
    TU TR W TL P S SR rq rr r0 F G d1 d2 E1 m1 m2 e2 n1 n2 e5
    pQ pR KA aL aR HK κ R v w Hv):
  rew [fun middle =>
    rew [fun e => rew [P] e in F m1 aL = B0]
      κ in
    ((sigT_map_eq (Q := P) (f := rq) F (p := e2) (u := aL) eq_refl ⊙ eq_refl)
      ⊙ middle) = HK ⊙
      (sigT_map_eq (Q := P) (f := rr) G (p := e5) (u := aR) eq_refl ⊙ eq_refl)]
    EM in
  Canon =
  layer_square rq rr r0 F G e2 e5 E1 pQ pR KA HK κ.
Proof.
  unfold Canon, rew_coh2Painting_restr0.
  now exact (rew_opp_r _ EM (layer_square _ _ _ F G e2 e5 E1 pQ pR KA HK κ)).
Defined.

Section ProjectedNaturality.

Context {A B C D: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (RA: forall x, PA x -> Type) (RC: forall x, PC x -> Type)
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x))
  (DV: forall x a, RA x a -> RC (v x) (V x a))
  (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x))
  (K: forall x, f (u x) = g (v x))
  (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a))
  {x y: A} (p: x = y) {a: PA x} {b: PA y} (h: rew [PA] p in a = b)
  {r: RA x a} {s: RA y b}
  (dh: rew [fun z: {x: A &T PA x} => RA z.1 z.2] (= p; h) in
    (r: (fun z: {x: A &T PA x} => RA z.1 z.2) (x; a)) = s).

Let SR := fun z: {x: A &T PA x} => RA z.1 z.2.

Let TR := fun z: {x: C &T PC x} => RC z.1 z.2.

Let tU := fun x (uv: {a: PA x &T RA x a}) => U x uv.1.

Let tV := fun x (uv: {a: PA x &T RA x a}) => (V x uv.1; DV x uv.1 uv.2).

Let tG := fun x (uv: {a: PC x &T RC x a}) => G x uv.1.

Let tH := eq_existT_curried_dep (Q := SR) (H := p) (Hu := h) (Hv := dh).

Let EU := sigT_map_eq_fst U dh.

Let EV := sigT_dep_path_map_direct v V SR TR
  (fun z => DV z.1 z.2) dh.

Let dV := rew [fun e: (v x; V x a) = (v y; V y b) =>
    rew [TR] e in (DV x a r: TR (v x; V x a)) = DV y b s]
  f_equal_eq_existT_curried v V p h in sigT_map_eq (Q := TR)
    (f := fun z: {x: A &T PA x} => (v z.1; V z.1 z.2))
    (fun z: {x: A &T PA x} => DV z.1 z.2) dh.

Let EG := f_equal (fun hh => sigT_map_eq (Q := PD) (f := g) tG hh) EV •
  sigT_map_eq_fst G dV.

Let Lower := square_coherence_dep_reverse_fill u v f g U V F G K HK p h.

Let Upper := square_coherence_dep_reverse_fill u v f g tU tV F tG K
  (fun x a => HK x a.1) p tH.

Let Left := f_equal (fun hd => HK x a ⊙ hd) EG.

Let Right := f_equal (fun hu => sigT_map_eq F hu ⊙ HK y b) EU.
Local Lemma square_coherence_dep_reverse_fill_projection:
  dpath_change
    (P := fun e => rew [PD] e in F (u x) (U x a) = G (v y) (V y b))
    (p := eq_sym (square_coherence_fill u v f g K p))
    (eq_sym Left) Upper (eq_sym Right) = Lower.
Proof.
  destruct p, h, dh.
  cbn in *.
  unfold Left, Right, EG, EU, EV, dV, Upper, Lower.
  cbn.
  rewrite (dpath_change_id
    (P := fun e => rew [PD] e in F (u x) (U x a) = G (v x) (V x a))
    (p := eq_sym (square_coherence_fill u v f g K eq_refl))
    (square_coherence_dep_reverse_fill u v f g tU tV F tG K
      (fun x a => HK x a.1) (a := (a; r)) (b := (a; r)) eq_refl eq_refl)).
  now reflexivity.
Defined.

End ProjectedNaturality.

Local Lemma square_map_along_dep_projection {T X U Y: Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (α: forall t, f (r t) = j (g t))
  (P: X -> Type) (Q: Y -> Type) (F: forall x, P x -> Q (f x))
  {t0 t1: T} (e: t0 = t1) {x0 x1: X} {a: x0 = x1}
  {p: x0 = r t0} {q: x1 = r t1}
  (H: p • f_equal r e = a • q) (N: square_coherence r g f j α e)
  {u0: P x0} {u1: P x1} {v0: P (r t0)} {v1: P (r t1)}
  {w0: Q (j (g t0))} {w1: Q (j (g t1))}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] f_equal r e in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hα0: rew [Q] α t0 in F (r t0) v0 = w0)
  (hα1: rew [Q] α t1 in F (r t1) v1 = w1)
  (hd: rew [Q] f_equal j (f_equal g e) in w0 = w1)
  (HH: rew [fun b => rew [P] b in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (NN: rew [fun b => rew [Q] b in F (r t0) v0 = w1] (eq_sym N) in
    (hα0 ⊙ hd) = sigT_map_eq F hb ⊙ hα1)
  (hb0: rew [P] f_equal r e in v0 = v1)
  (hd0: rew [Q] f_equal j (f_equal g e) in w0 = w1)
  (Es: hb = hb0) (Et: hd = hd0)
  (HH0: rew [fun b => rew [P] b in u0 = v1] H in (hp ⊙ hb0) = ha ⊙ hq)
  (NN0: rew [fun b => rew [Q] b in F (r t0) v0 = w1] (eq_sym N) in
    (hα0 ⊙ hd0) = sigT_map_eq F hb0 ⊙ hα1)
  (EH: rew [fun hb => rew [fun b => rew [P] b in u0 = v1] H in
    (hp ⊙ hb) = ha ⊙ hq] Es in HH = HH0)
  (EN: dpath_change
    (P := fun b => rew [Q] b in F (r t0) v0 = w1) (p := eq_sym N)
    (eq_sym (f_equal (fun hd => hα0 ⊙ hd) Et)) NN
    (eq_sym (f_equal (fun hb => sigT_map_eq F hb ⊙ hα1) Es)) = NN0):
  rew [fun hd => rew [fun b => rew [Q] b in F x0 u0 = w1]
    (square_map_along r g f j α e H N) in
    ((sigT_map_eq F hp ⊙ hα0) ⊙ hd) =
      sigT_map_eq F ha ⊙ (sigT_map_eq F hq ⊙ hα1)] Et in
  square_map_along_dep r g f j α P Q F e H N ha hb hp hq hα0 hα1 hd HH NN =
  square_map_along_dep r g f j α P Q F e H N ha hb0 hp hq hα0 hα1 hd0 HH0 NN0.
Proof.
  destruct Es, Et.
  cbn [f_equal eq_sym] in EN.
  rewrite (dpath_change_id NN) in EN.
  subst HH0 NN0.
  now reflexivity.
Defined.

Section SigmaMapFace.
Context
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  (P: X -> Type) (Q: Y -> Type) (PM: M -> Type) (PN: N -> Type)
  (F: forall x, P x -> Q (f x))
  (L: forall m, PM m -> P (s m)) (R: forall n, PN n -> P (t n))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: hexagonal_coherence s r t p e q v k w)
  {a: PM m} {b: PN n} (h: rew [P] k in L m a = R n b).

Let A0 := rew [P] v in L m' (rew [PM] p in a).

Let B0 := rew [P] w in R n' (rew [PN] q in b).

Let hlower := rew_cohLayer_hex P r L R e p q v w k a b h H.

Let Source := fun dd => P (r dd).

Let Target := fun uu => Q (j uu).

Context (ExtraSource: forall dd, Source dd -> Type)
  (ExtraTarget: forall uu, Target uu -> Type).

Let G0 := fun dd x => rew [Q] α dd in F (r dd) x.

Context (Paint: forall dd x, ExtraSource dd x -> ExtraTarget (g dd) (G0 dd x))
  {aPaint: ExtraSource d A0} {bPaint: ExtraSource d' B0}
  (Hv: rew [fun z: {dd: T &T Source dd} => ExtraSource z.1 z.2]
    (= e; hlower) in
    (aPaint: (fun z: {dd: T &T Source dd} => ExtraSource z.1 z.2) (d; A0)) = bPaint).

Let SR := fun z: {dd: T &T Source dd} => ExtraSource z.1 z.2.

Let TR := fun z: {uu: U &T Target uu} => ExtraTarget z.1 z.2.

Let he := eq_existT_curried_dep (Q := SR) (H := e) (Hu := hlower) (Hv := Hv).

Let FirstSource := fun dd (uv: {x: Source dd &T ExtraSource dd x}) => uv.1.

Let PairG := fun dd (uv: {x: Source dd &T ExtraSource dd x}) =>
  (G0 dd uv.1; Paint dd uv.1 uv.2).

Let FirstTarget := fun uu (uv: {x: Target uu &T ExtraTarget uu x}) => uv.1.

Let ES := sigT_map_eq_fst (Q := P) (f := r) (R := ExtraSource) (fun _ x => x) Hv.

Let EG := sigT_dep_path_map_direct g G0 SR TR
  (fun z => Paint z.1 z.2) Hv.

Let dPaint := rew [fun ee: (g d; G0 d A0) = (g d'; G0 d' B0) =>
    rew [TR] ee in (Paint d A0 aPaint: TR (g d; G0 d A0)) = Paint d' B0 bPaint]
  f_equal_eq_existT_curried g G0 e hlower in
  sigT_map_eq (Q := TR) (f := fun z: {dd: T &T Source dd} => (g z.1; G0 z.1 z.2))
    (fun z => Paint z.1 z.2) Hv.

Let ET := f_equal (fun hh => sigT_map_eq (Q := Q) (f := j) FirstTarget hh) EG •
  sigT_map_eq_fst (Q := Q) (f := j) (R := ExtraTarget) (fun _ x => x) dPaint.

Let Canon := rew_coh2Painting_restr0 L R e p q v w k a b h H
  ExtraSource Hv.

Let Prefix := sigT_map_eq F
  (sigT_map_eq L (p := p) (u := a) eq_refl ⊙
    (eq_refl: rew [P] v in L m' (rew [PM] p in a) = A0)) ⊙
  (eq_refl: rew [Q] α d in F (r d) A0 = G0 d A0).

Let EndRoute := sigT_map_eq F h ⊙
  (sigT_map_eq F (sigT_map_eq R (p := q) (u := b) eq_refl ⊙
    (eq_refl: rew [P] w in R n' (rew [PN] q in b) = B0)) ⊙
    (eq_refl: rew [Q] α d' in F (r d') B0 = G0 d' B0)).

Let Base := layer_square_map r s t f g j α e p q v w k H
  (square_coherence_fill r g f j α e).

(** Projecting the additional middle-fibre path transports the mapped
    square along the induced equality of target paths. *)
Local Lemma layer_square_map_dep_projection:
  rew [fun middle => rew [fun ee => rew [Q] ee in F (s m) (L m a) = G0 d' B0]
    Base in (Prefix ⊙ middle) = EndRoute] ET in
  layer_square_map_coherence_dep r s t f g j FirstSource L R F PairG FirstTarget
    α (fun _ _ => eq_refl) e p q v w k H he eq_refl eq_refl eq_refl eq_refl h Canon =
  layer_square_map_dep r s t f g j α P Q PM PN F L R e p q v w k H h.
Proof.
  unfold layer_square_map_coherence_dep, layer_square_map_dep.
  unfold square_map_along_coherence_dep.
  eapply (square_map_along_dep_projection r g f j α P Q F e
    H
    (square_coherence_fill r g f j α e)
    h (sigT_map_eq (Q := P) (f := r) FirstSource he)
    (sigT_map_eq L (p := p) (u := a) eq_refl ⊙
      (eq_refl: rew [P] v in L m' (rew [PM] p in a) = A0))
    (sigT_map_eq R (p := q) (u := b) eq_refl ⊙
      (eq_refl: rew [P] w in R n' (rew [PN] q in b) = B0))
    (eq_refl: rew [Q] α d in F (r d) A0 = G0 d A0)
    (eq_refl: rew [Q] α d' in F (r d') B0 = G0 d' B0)
    (sigT_map_eq (Q := Q) (f := j) FirstTarget (sigT_map_eq PairG he))
    (Canon)
    (square_coherence_dep_reverse_fill r g f j FirstSource PairG F FirstTarget
      α (fun _ _ => eq_refl) e he)
    (sigT_map_eq (Q := P) (f := r) (fun _ x => x) hlower)
    (sigT_map_eq (Q := Q) (f := j) (fun _ x => x) (sigT_map_eq G0 hlower))
    ES ET (layer_square s t r L R p q e v w k h H)
    (square_coherence_dep_reverse_fill r g f j
      (fun _ x => x) G0 F (fun _ x => x) α (fun _ _ => eq_refl) e hlower)).
  - now exact (rew_coh2Painting_restr0_projection L R e p q v w k a b h H
      ExtraSource Hv).
  - now exact (square_coherence_dep_reverse_fill_projection ExtraSource ExtraTarget
      r g f j (fun _ x => x) G0 Paint F (fun _ x => x)
      α (fun _ _ => eq_refl) e hlower Hv).
Defined.

End SigmaMapFace.

Section NatSigma.

Context {Z V V' W X: Type} {S: Z -> Type} {QL: V -> Type} {QR: V' -> Type}
  {P: X -> Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (RL: forall z, S z -> QL (L z)) (RR: forall z, S z -> QR (R z))
  (F: forall v, QL v -> P (f v)) (G: forall v, QR v -> P (g v))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [P] k z in F (L z) (RL z a) = G (R z) (RR z a))
  {z1 z2: Z} (p: z1 = z2) {m: V} {n: V'} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2) (c: f m = d w1) (c': g n = d w2)
  (H: hexagonal_coherence f d g l e r c (k z2) c') (a: S z1).

Let a2 := rew [S] p in a.

Let am := rew [QL] l in RL z2 a2.

Let an := rew [QR] r in RR z2 a2.

Let aw1 := rew [P] c in F m am.

Let aw2 := rew [P] c' in G n an.

Let he0 := rew_cohLayer_hex P d F G e l r c c' (k z2)
  (RL z2 a2) (RR z2 a2) (hk z2 a2) H.

Let HH0 := layer_square _ _ _ F G l r e c c' (k z2) (hk z2 a2) H.

Let LeftPrefix := sigT_map_eq F
  (sigT_map_eq RL (p := p) (u := a) eq_refl ⊙
    (eq_refl: rew [QL] l in RL z2 a2 = am)) ⊙
  (eq_refl: rew [P] c in F m am = aw1).

Context (Extra: forall w, P (d w) -> Type)
  {v1: Extra w1 aw1} {v2: Extra w2 aw2}
  (Hv: rew [fun z: {w: W &T P (d w)} => Extra z.1 z.2] (= e; he0) in
    (v1: (fun z: {w: W &T P (d w)} => Extra z.1 z.2) (w1; aw1)) = v2).

Let he := eq_existT_curried_dep (Q := fun z => Extra z.1 z.2)
  (H := e) (Hu := he0) (Hv := Hv).

Let EM := sigT_map_eq_fst (P := fun w => P (d w)) (Q := P) (f := d) (R := Extra)
  (fun _ a => a) Hv.

Let Canon := rew_coh2Painting_restr0 F G e l r c c'
  (k z2) (RL z2 a2) (RR z2 a2) (hk z2 a2) H Extra Hv.

Let RightRoute := hk z1 a ⊙ (sigT_map_eq G
  (sigT_map_eq RR (p := p) (u := a) eq_refl ⊙
    (eq_refl: rew [QR] r in RR z2 a2 = an)) ⊙
  (eq_refl: rew [P] c' in G n an = aw2)).

Let Base := layer_square_nat L R f g d k p l r e c c' H
  (square_coherence_fill L R f g k p).

(** Projecting the additional middle-fibre path recovers the canonical
    naturality square after transport along its path projection. *)
Local Lemma layer_square_nat_dep_projection:
  rew [fun h => rew [fun q => rew [P] q in F (L z1) (RL z1 a) = aw2] Base in
    (LeftPrefix ⊙ h) = RightRoute] EM in
  layer_square_nat_coherence_dep L R f g d RL RR F G (fun _ a => a.1) k hk
    p l r e c c' H eq_refl eq_refl eq_refl he eq_refl eq_refl Canon =
  layer_square_nat_dep L R f g d RL RR F G k hk p l r e c c' H a.
Proof.
  unfold Canon, rew_coh2Painting_restr0.
  unfold layer_square_nat_coherence_dep, layer_square_nat_dep.
  pose (Factory := fun
    (middle: rew [P] f_equal d e in aw1 = aw2)
    (face: rew [fun h => rew [P] h in F (L z2) (RL z2 a2) = aw2] H in
      ((sigT_map_eq (Q := P) (f := f) F (p := l) (u := RL z2 a2) eq_refl ⊙ eq_refl) ⊙ middle) =
      hk z2 a2 ⊙ (sigT_map_eq (Q := P) (f := g) G
        (p := r) (u := RR z2 a2) eq_refl ⊙ eq_refl)) =>
    square_change_sides_dep P (map_compose_tail f (f_equal L p) l c)
      (square_nat_along L R f g k p
        H
        (square_coherence_fill L R f g k p))
      (map_compose_tail g (f_equal R p) r c') (hk z1 a) middle
      (sigT_map_eq F (sigT_map_eq RL (p := p) (u := a) eq_refl) ⊙
        (sigT_map_eq F (p := l) (u := RL z2 a2) eq_refl ⊙ eq_refl))
      (sigT_map_eq F (sigT_map_eq RL (p := p) (u := a) eq_refl ⊙ eq_refl) ⊙ eq_refl)
      (sigT_map_eq G (sigT_map_eq RR (p := p) (u := a) eq_refl) ⊙
        (sigT_map_eq G (p := r) (u := RR z2 a2) eq_refl ⊙ eq_refl))
      (sigT_map_eq G (sigT_map_eq RR (p := p) (u := a) eq_refl ⊙ eq_refl) ⊙ eq_refl)
      (map_compose_tail_dep f F (sigT_map_eq RL (p := p) (u := a) eq_refl)
        (p := f_equal L p) (q := l) (r := c) eq_refl eq_refl)
      (square_nat_along_coherence_dep L R f g RL RR F G k hk p
        H eq_refl
        face)
      (map_compose_tail_dep g G (sigT_map_eq RR (p := p) (u := a) eq_refl)
        (p := f_equal R p) (q := r) (r := c') eq_refl eq_refl)).
  refine (map_subst Factory EM _ • _).
  refine (f_equal (Factory _) (rew_opp_r _ EM HH0) • _).
  unfold Factory.
  unfold square_nat_along_coherence_dep.
  now f_equal.
Defined.

End NatSigma.

Local Lemma square_cube_coherence_dep_projection {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q) (K: p • b' = a' • q) (κ: b = b') (λ: a = a')
  (C: square_cube H K κ λ)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [P] b in v0 = v1) (hb': rew [P] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq)
  (Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb')
  (Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha')
  (hb0: rew [P] b in v0 = v1) (hb'0: rew [P] b' in v0 = v1)
  (EB: hb = hb0) (EB': hb' = hb'0)
  (HH0: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb0) = ha ⊙ hq)
  (KK0: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb'0) = ha' ⊙ hq)
  (DK0: rew [fun e => rew [P] e in v0 = v1] κ in hb0 = hb'0)
  (EH: rew [fun hb => rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ hb) = ha ⊙ hq] EB in HH = HH0)
  (EK: rew [fun hb => rew [fun e => rew [P] e in u0 = v1] K in
    (hp ⊙ hb) = ha' ⊙ hq] EB' in KK = KK0)
  (EDK: dpath_change
    (P := fun e => rew [P] e in v0 = v1) (p := κ)
    (eq_sym EB) Dκ (eq_sym EB') = DK0):
  square_cube_coherence_dep P H K κ λ C ha ha' hb0 hb'0 hp hq HH0 KK0 DK0 Dλ ->
  square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ.
Proof.
  destruct EB, EB'.
  cbn [f_equal eq_sym] in EDK.
  rewrite (dpath_change_id Dκ) in EDK.
  subst HH0 KK0 DK0.
  now intros E.
Defined.

Section ComposeProjection.

Context {X Y: Type} {f: Y -> X} {P: X -> Type} {Q: Y -> Type}
  {F: forall y, Q y -> P (f y)}
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {H: p • f_equal f c = a • q} {K: q • f_equal f d = b • r}
  {u0: P x0} {u1: P x1} {u2: P x2}
  {v0: Q y0} {v1: Q y1} {v2: Q y2}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in u1 = u2}
  {hc: rew [Q] c in v0 = v1}
  {hd: rew [Q] d in v1 = v2}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  {hr: rew [P] r in u2 = F y2 v2}
  {HH0: rew [fun e => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq}
  {KK0: rew [fun e => rew [P] e in u1 = F y2 v2] K in
    (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr}.

Context {S: {y: Y &T Q y} -> Type}
  {w0: S (y0; v0)} {w1: S (y1; v1)} {w2: S (y2; v2)}
  {tc: (y0; v0) = (y1; v1)} {td: (y1; v1) = (y2; v2)}
  (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (dc: rew [S] tc in w0 = w1) (dd: rew [S] td in w1 = w2)
  (Cfull: rew [fun y => {v: Q y &T S (y; v)}] c in (v0; w0) = (v1; w1))
  (Dfull: rew [fun y => {v: Q y &T S (y; v)}] d in (v1; w1) = (v2; w2))
  (Uc: Cfull = eq_existT_curried_dep (Q := S) (H := c) (Hu := hc)
    (Hv := rew [fun e => rew [S] e in w0 = w1] Nc in dc))
  (Ud: Dfull = eq_existT_curried_dep (Q := S) (H := d) (Hu := hd)
    (Hv := rew [fun e => rew [S] e in w1 = w2] Nd in dd)).

Let Full := fun y (v: {v: Q y &T S (y; v)}) => F y v.1.

Let EC := f_equal (fun h => sigT_map_eq Full h) Uc •
  sigT_map_eq_fst F (rew [fun e => rew [S] e in w0 = w1] Nc in dc).

Let ED := f_equal (fun h => sigT_map_eq Full h) Ud •
  sigT_map_eq_fst F (rew [fun e => rew [S] e in w1 = w2] Nd in dd).

Let ECD := f_equal (fun h => sigT_map_eq Full h)
  (sigT_pair_path_paste S Nc Nd dc dd Uc Ud) •
  sigT_map_eq_fst F
    (rew [fun e => rew [S] e in w0 = w2](sigT_path_paste Nc Nd) in (dc ⊙ dd)).
Context
  (HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ sigT_map_eq Full Cfull) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = F y2 v2] K in
    (hq ⊙ sigT_map_eq Full Dfull) = hb ⊙ hr)
  (EH: rew [fun (edge: rew [P] f_equal f c in F y0 v0 = F y1 v1) => rew [fun
    (e: x0 = f y1) => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ edge) = ha ⊙ hq] EC in HH = HH0)
  (EK: rew [fun (edge: rew [P] f_equal f d in F y1 v1 = F y2 v2) => rew [fun
    (e: x1 = f y2) => rew [P] e in u1 = F y2 v2] K in
    (hq ⊙ edge) = hb ⊙ hr] ED in KK = KK0).
Local Lemma square_compose_map_coherence_dep_projection:
  rew [fun (edge: rew [P] f_equal f (c • d) in F y0 v0 = F y2 v2) => rew [fun
    (e: x0 = f y2) => rew [P] e in u0 = F y2 v2]
    (square_compose_map f H K) in (hp ⊙ edge) = (ha ⊙ hb) ⊙ hr] ECD in
  square_compose_map_coherence_dep f P (fun y => {v: Q y &T S (y; v)})
    Full H K ha hb Cfull Dfull hp hq hr HH KK =
  square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH0 KK0.
Proof.
  subst tc td.
  destruct c, hc, dc, d, hd, dd.
  subst Cfull Dfull.
  cbn in *.
  subst HH0 KK0.
  now reflexivity.
Defined.

End ComposeProjection.

Section Restr0.
Context
  {X2 X1 X0: Type}
  {S2: X2 -> Type}
  {S1: X1 -> Type}
  {S0: X0 -> Type}

  {TU T: Type}
  {uf0: TU -> X1}
  {rf0: T -> X0}
  {fA fB fC: TU -> T}

  {rfq rfs rfr: X1 -> X0}
  {Fq: forall y, S1 y -> S0 (rfq y)}
  {Fs: forall y, S1 y -> S0 (rfs y)}
  {Fr: forall y, S1 y -> S0 (rfr y)}
  {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}
  {gs: forall dd, rfs (uf0 dd) = rf0 (fB dd)}
  {gr: forall dd, rfr (uf0 dd) = rf0 (fC dd)}

  {rur rus ruq1 rur1: X2 -> X1}
  {Rr: forall z, S2 z -> S1 (rur z)}
  {Rs: forall z, S2 z -> S1 (rus z)}
  {Rq1: forall z, S2 z -> S1 (ruq1 z)}
  {Rr1: forall z, S2 z -> S1 (rur1 z)}

  {KA2: forall z, rfq (rus z) = rfs (ruq1 z)}
  {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}
  {KA6: forall z, rfr (rus z) = rfs (rur1 z)}
  {HKA2: forall z (c: S2 z),
  rew [S0] KA2 z in Fq (rus z) (Rs z c) = Fs (ruq1 z) (Rq1 z c)}
  {HKA4: forall z (c: S2 z),
  rew [S0] KA4 z in Fq (rur z) (Rr z c) = Fr (ruq1 z) (Rq1 z c)}
  {HKA6: forall z (c: S2 z),
  rew [S0] KA6 z in Fr (rus z) (Rs z c) = Fs (rur1 z) (Rr1 z c)}
  (u0 u1 u2 u3 u4 u5: TU)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2: X2)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (aS: S2 zs1) (aR: S2 zr1) (aQ: S2 zq1)
  (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
  (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
  (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
  (K1: rur zs1 = rus zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rus zq1)
  (HK1: rew [S1] K1 in Rr zs1 aS = Rs zr1 aR)
  (HK3: rew [S1] K3 in Rq1 zr1 aR = Rr1 zq1 aQ)
  (HK5: rew [S1] K5 in Rq1 zs1 aS = Rs zq1 aQ)
  (HH1: hexagonal_coherence rur uf0 rus pIs eU1 pIr pV0 K1 pV1)
  (HH3: hexagonal_coherence ruq1 uf0 rur1 pIr eU2 pIq pV2 K3 pV3)
  (HH5: hexagonal_coherence ruq1 uf0 rus pIs eU3 pIq pV4 K5 pV5)
  (κ: hexagonal_coherence fA fB fC eU1 eU2 eU3 e2 e4 e6)
  (HH2: hexagonal_coherence rfq rf0 rfs pV1 e2 pV2 (gq u1) (KA2 zr2) (gs u2))
  (HH4: hexagonal_coherence rfq rf0 rfr pV0 e4 pV4 (gq u0) (KA4 zs2) (gr u4))
  (HH6: hexagonal_coherence rfr rf0 rfs pV5 e6 pV3 (gr u5) (KA6 zq2) (gs u3))
  (HHA: hexagonal_coherence rfq rfs rfr K1 K3 K5 (KA2 zr1) (KA4 zs1) (KA6 zq1))
  (Hcoh2Painting: hexagonal_coherence_dep Fq Fs Fr HHA HK1 HK3 HK5
    (HKA2 zr1 aR) (HKA4 zs1 aS) (HKA6 zq1 aQ))
  (Hcoh3Frame: permutahedral_coherence u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA).

Let aS2 := rew [S2] pIs in aS.

Let aR2 := rew [S2] pIr in aR.

Let aQ2 := rew [S2] pIq in aQ.

Let a0 := rew [S1] pV0 in Rr zs2 aS2.

Let a1 := rew [S1] pV1 in Rs zr2 aR2.

Let a2 := rew [S1] pV2 in Rq1 zr2 aR2.

Let a3 := rew [S1] pV3 in Rr1 zq2 aQ2.

Let a4 := rew [S1] pV4 in Rq1 zs2 aS2.

Let a5 := rew [S1] pV5 in Rs zq2 aQ2.

Let ULower := fun u => S1 (uf0 u).

Let TLower := fun t => S0 (rf0 t).

Let GA := fun u a => rew [S0] gq u in Fq (uf0 u) a.

Let GB := fun u a => rew [S0] gs u in Fs (uf0 u) a.

Let GC := fun u a => rew [S0] gr u in Fr (uf0 u) a.

Let he1 := rew_cohLayer_hex S1 uf0 Rr Rs eU1 pIs pIr pV0 pV1 K1 aS aR HK1 HH1.

Let he3 := rew_cohLayer_hex S1 uf0 Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 aR aQ HK3 HH3.

Let he5 := rew_cohLayer_hex S1 uf0 Rq1 Rs eU3 pIs pIq pV4 pV5 K5 aS aQ HK5 HH5.

Let he2 := rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2)
  (Rs zr2 aR2) (Rq1 zr2 aR2) (HKA2 zr2 aR2) HH2.

Let he4 := rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2)
  (Rr zs2 aS2) (Rq1 zs2 aS2) (HKA4 zs2 aS2) HH4.

Let he6 := rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2)
  (Rs zq2 aQ2) (Rr1 zq2 aQ2) (HKA6 zq2 aQ2) HH6.

Let Lowerκ := rew_coh2Layer_perm4 u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
  zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq aS aR aQ pV0 pV1 pV2 pV3 pV4 pV5
  K1 K3 K5 HK1 HK3 HK5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA Hcoh2Painting Hcoh3Frame.

Context (UExtra: forall u, ULower u -> Type) (TExtra: forall t, TLower t -> Type)
  (PaintA: forall u a, UExtra u a -> TExtra (fA u) (GA u a))
  (PaintB: forall u a, UExtra u a -> TExtra (fB u) (GB u a))
  (PaintC: forall u a, UExtra u a -> TExtra (fC u) (GC u a))
  (v0: UExtra u0 a0) (v1: UExtra u1 a1) (v2: UExtra u2 a2)
  (v3: UExtra u3 a3) (v4: UExtra u4 a4) (v5: UExtra u5 a5).

Let UR := fun z: {u: TU &T ULower u} => UExtra z.1 z.2.

Let TR := fun z: {t: T &T TLower t} => TExtra z.1 z.2.
Context
  (hV1: rew [UR] (= eU1; he1) in (v0: UR (u0; a0)) = v1)
  (hV3: rew [UR] (= eU2; he3) in (v2: UR (u2; a2)) = v3)
  (hV5: rew [UR] (= eU3; he5) in (v4: UR (u4; a4)) = v5)
  (hV2: rew [TR] (= e2; he2) in (PaintA u1 a1 v1: TR (fA u1; GA u1 a1)) = PaintB u2 a2 v2)
  (hV4: rew [TR] (= e4; he4) in (PaintA u0 a0 v0: TR (fA u0; GA u0 a0)) = PaintC u4 a4 v4)
  (hV6: rew [TR] (= e6; he6) in (PaintC u5 a5 v5: TR (fC u5; GC u5 a5)) = PaintB u3 a3 v3).

Let lifted1 := eq_existT_curried_dep (Q := UR) (H := eU1) (Hu := he1) (Hv := hV1).

Let lifted3 := eq_existT_curried_dep (Q := UR) (H := eU2) (Hu := he3) (Hv := hV3).

Let lifted5 := eq_existT_curried_dep (Q := UR) (H := eU3) (Hu := he5) (Hv := hV5).

Let lifted2 := eq_existT_curried_dep (Q := TR) (H := e2) (Hu := he2) (Hv := hV2).

Let lifted4 := eq_existT_curried_dep (Q := TR) (H := e4) (Hu := he4) (Hv := hV4).

Let lifted6 := eq_existT_curried_dep (Q := TR) (H := e6) (Hu := he6) (Hv := hV6).

Context (Higherκ: hexagonal_coherence_dep (Q := TR)
  (f1 := fun z => (fA z.1; GA z.1 z.2))
  (f2 := fun z => (fB z.1; GB z.1 z.2))
  (f3 := fun z => (fC z.1; GC z.1 z.2))
  (fun z => PaintA z.1 z.2) (fun z => PaintB z.1 z.2) (fun z => PaintC z.1 z.2)
  (eq_existT_curried_hex fA GA fC GC fB GB κ Lowerκ)
  hV1 hV3 hV5 hV2 hV4 hV6).

Let Dκ := eq_existT_curried_hex_dep fA GA PaintA fB GB PaintB fC GC PaintC
  eU1 he1 hV1 e2 he2 hV2 eU2 he3 hV3 e4 he4 hV4 eU3 he5 hV5 e6 he6 hV6 κ Lowerκ Higherκ.

Let FullA := fun u (av: {a: ULower u &T UExtra u a}) => (GA u av.1; PaintA u av.1 av.2).

Let FullB := fun u (av: {a: ULower u &T UExtra u a}) => (GB u av.1; PaintB u av.1 av.2).

Let FullC := fun u (av: {a: ULower u &T UExtra u a}) => (GC u av.1; PaintC u av.1 av.2).

Let Face1 := rew_coh2Painting_restr0 Rr Rs eU1 pIs pIr
  pV0 pV1 K1 aS aR HK1 HH1 UExtra hV1.

Let Face3 := rew_coh2Painting_restr0 Rq1 Rr1 eU2 pIr pIq
  pV2 pV3 K3 aR aQ HK3 HH3 UExtra hV3.

Let Face5 := rew_coh2Painting_restr0 Rq1 Rs eU3 pIs pIq
  pV4 pV5 K5 aS aQ HK5 HH5 UExtra hV5.

Let Face2 := rew_coh2Painting_restr0 Fq Fs e2 pV1 pV2
  (gq u1) (gs u2) (KA2 zr2) (Rs zr2 aR2) (Rq1 zr2 aR2) (HKA2 zr2 aR2) HH2 TExtra hV2.

Let Face4 := rew_coh2Painting_restr0 Fq Fr e4 pV0 pV4
  (gq u0) (gr u4) (KA4 zs2) (Rr zs2 aS2) (Rq1 zs2 aS2) (HKA4 zs2 aS2) HH4 TExtra hV4.

Let Face6 := rew_coh2Painting_restr0 Fr Fs e6 pV5 pV3
  (gr u5) (gs u3) (KA6 zq2) (Rs zq2 aQ2) (Rr1 zq2 aQ2) (HKA6 zq2 aQ2) HH6 TExtra hV6.

Lemma rew_coh3Painting_restr0:
  permutahedral_coherence_dep Hcoh3Frame
    (fun u (av: {a: ULower u &T UExtra u a}) => av.1)
    (fun t (av: {a: TLower t &T TExtra t a}) => av.1)
    FullA FullB FullC Fq Fs Fr Rr Rs Rq1 Rr1
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    HKA2 HKA4 HKA6 lifted1 lifted3 lifted5 lifted2 lifted4 lifted6
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HK1 HK3 HK5
    Face1 Face3 Face5 Dκ Face2 Face4 Face6 Hcoh2Painting.
Proof.
  pose proof (rew_coh2Layer_perm4_coherence
    u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
    zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq aS aR aQ pV0 pV1 pV2 pV3 pV4 pV5
    K1 K3 K5 HK1 HK3 HK5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA Hcoh2Painting Hcoh3Frame)
    as LowerDP.
  pose proof (eq_existT_curried_hex_dep_fst_map_normalized
    fA GA PaintA fB GB PaintB fC GC PaintC
    eU1 he1 hV1 e2 he2 hV2 eU2 he3 hV3 e4 he4 hV4 eU3 he5 hV5 e6 he6 hV6
    κ Lowerκ Higherκ rf0 (fun _ a => a)) as CapProjection.
  unfold permutahedral_coherence_dep.
  cbn zeta.
  unfold permutahedral_coherence_dep in LowerDP.
  cbn zeta in LowerDP.
  eapply square_cube_coherence_dep_projection.
  3: now exact CapProjection.
  3: now exact LowerDP.
  - rewrite sigT_hex_pair_left_normalize_paste.
    eapply (square_compose_map_coherence_dep_projection
      (f := rf0) (F := fun _ a => a) (S := TR)).
    + eapply (square_compose_map_coherence_dep_projection
        (f := rf0) (F := fun _ a => a) (S := TR)).
      * now exact (layer_square_map_dep_projection
          uf0 rur rus rfq fA rf0 gq S1 S0 S2 S2 Fq Rr Rs
          eU1 pIs pIr pV0 pV1 K1 HH1 HK1 UExtra TExtra PaintA hV1).
      * cbn [f_equal]. rewrite eq_trans_refl_l.
        now exact (layer_square_nat_dep_projection rus ruq1 rfq rfs rf0 Rs Rq1 Fq Fs KA2 HKA2
          pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 aR TExtra hV2).
    + now exact (layer_square_map_dep_projection
        uf0 ruq1 rur1 rfs fB rf0 gs S1 S0 S2 S2 Fs Rq1 Rr1
        eU2 pIr pIq pV2 pV3 K3 HH3 HK3 UExtra TExtra PaintB hV3).
  - rewrite sigT_hex_pair_right_normalize_paste.
    eapply (square_compose_map_coherence_dep_projection
      (f := rf0) (F := fun _ a => a) (S := TR)).
    + cbn [f_equal]. rewrite eq_trans_refl_l.
      now exact (layer_square_nat_dep_projection rur ruq1 rfq rfr rf0 Rr Rq1 Fq Fr KA4 HKA4
        pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 aS TExtra hV4).
    + eapply (square_compose_map_coherence_dep_projection
        (f := rf0) (F := fun _ a => a) (S := TR)).
      * now exact (layer_square_map_dep_projection
          uf0 ruq1 rus rfr fC rf0 gr S1 S0 S2 S2 Fr Rq1 Rs
          eU3 pIs pIq pV4 pV5 K5 HH5 HK5 UExtra TExtra PaintC hV5).
      * cbn [f_equal]. rewrite eq_trans_refl_l.
        now exact (layer_square_nat_dep_projection rus rur1 rfr rfs rf0 Rs Rr1 Fr Fs KA6 HKA6
          pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 aQ TExtra hV6).
Defined.

End Restr0.
