Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas νGpd.Pasting.

Set Keyed Unification.

Local Arguments rew_cohLayer_hex {T1 T2 T3 X} P {S2 S3} rf0 {rfF rfG} F G
  {d1 d2} E1 {m1 m2} C2 {n1 n2} D2 C1 D1 K aL aR _ _.

Lemma eq_existT_curried_hex {A1 A2 A3 B: Type}
  {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {Q: B -> Type}
  (f1: A1 -> B) (g1: forall a, P1 a -> Q (f1 a))
  (f2: A2 -> B) (g2: forall a, P2 a -> Q (f2 a))
  (f3: A3 -> B) (g3: forall a, P3 a -> Q (f3 a))
  {x1 y1: A1} {u1: P1 x1} {v1: P1 y1}
  {x2 y2: A2} {u2: P2 x2} {v2: P2 y2}
  {x3 y3: A3} {u3: P3 x3} {v3: P3 y3}
  {K1: x1 = y1} {W1: rew [P1] K1 in u1 = v1}
  {K2: x2 = y2} {W2: rew [P2] K2 in u2 = v2}
  {K3: x3 = y3} {W3: rew [P3] K3 in u3 = v3}
  {H2: f1 y1 = f3 x3} {U2: rew [Q] H2 in g1 y1 v1 = g3 x3 u3}
  {H1': f1 x1 = f2 x2} {U1': rew [Q] H1' in g1 x1 u1 = g2 x2 u2}
  {H3': f2 y2 = f3 y3} {U3': rew [Q] H3' in g2 y2 v2 = g3 y3 v3}
  (HH: f_equal f1 K1 • (H2 • f_equal f3 K3) =
    H1' • (f_equal f2 K2 • H3'))
  (HHu: rew [fun h => rew [Q] h in g1 x1 u1 = g3 y3 v3] HH in
    (sigT_map_eq g1 W1 ⊙ (U2 ⊙ sigT_map_eq g3 W3)) =
    U1' ⊙ (sigT_map_eq g2 W2 ⊙ U3')):
  f_equal (fun z: {a: A1 &T P1 a} => (f1 z.1; g1 z.1 z.2)) (= K1; W1)
  • ((= H2; U2)
     • f_equal (fun z: {a: A3 &T P3 a} => (f3 z.1; g3 z.1 z.2)) (= K3; W3)) =
  (= H1'; U1')
  • (f_equal (fun z: {a: A2 &T P2 a} => (f2 z.1; g2 z.1 z.2)) (= K2; W2)
     • (= H3'; U3')).
Proof.
  refine (_ • (eq_existT_curried_eq HH HHu • eq_sym _)).
  - now exact (sigT_path_paste (f_equal_eq_existT_curried f1 g1 K1 W1)
      (sigT_path_paste eq_refl (f_equal_eq_existT_curried f3 g3 K3 W3))).
  - now exact (sigT_path_paste eq_refl
      (sigT_path_paste (f_equal_eq_existT_curried f2 g2 K2 W2) eq_refl)).
Defined.

(** The hexagon first normalizes the left route, compares the resulting
    pair paths, and reverses the right normalization. Its dependent lift
    transports both routes to their normal forms. *)
Lemma eq_existT_curried_dep_hex_split
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
  (Hv1: rew [fun z => R1 z.1 z.2] (=H1; Hu1) in
    (v0: (fun z => R1 z.1 z.2) (x0; u0)) = v1)
  (H2: f1 x1 = f3 x2) (Hu2: rew [P'] H2 in g1 x1 u1 = g3 x2 u2)
  (Hv2: rew [fun z => R' z.1 z.2] (=H2; Hu2) in
    (h1 x1 u1 v1: (fun z => R' z.1 z.2) (f1 x1; g1 x1 u1)) = h3 x2 u2 v2)
  (H3: x2 = x3) (Hu3: rew [P3] H3 in u2 = u3)
  (Hv3: rew [fun z => R3 z.1 z.2] (=H3; Hu3) in
    (v2: (fun z => R3 z.1 z.2) (x2; u2)) = v3)
  (H1': f1 x0 = f2 x1') (Hu1': rew [P'] H1' in g1 x0 u0 = g2 x1' u1')
  (Hv1': rew [fun z => R' z.1 z.2] (=H1'; Hu1') in
    (h1 x0 u0 v0: (fun z => R' z.1 z.2) (f1 x0; g1 x0 u0)) = h2 x1' u1' v1')
  (H2': x1' = x2') (Hu2': rew [P2] H2' in u1' = u2')
  (Hv2': rew [fun z => R2 z.1 z.2] (=H2'; Hu2') in
    (v1': (fun z => R2 z.1 z.2) (x1'; u1')) = v2')
  (H3': f2 x2' = f3 x3) (Hu3': rew [P'] H3' in g2 x2' u2' = g3 x3 u3)
  (Hv3': rew [fun z => R' z.1 z.2] (=H3'; Hu3') in
    (h2 x2' u2' v2': (fun z => R' z.1 z.2) (f2 x2'; g2 x2' u2')) = h3 x3 u3 v3)
  (HH: f_equal f1 H1 • (H2 • f_equal f3 H3) =
    H1' • (f_equal f2 H2' • H3'))
  (HHu: rew [fun h => rew [P'] h in g1 x0 u0 = g3 x3 u3] HH in
    (sigT_map_eq g1 Hu1 ⊙ (Hu2 ⊙ sigT_map_eq g3 Hu3)) =
    Hu1' ⊙ (sigT_map_eq g2 Hu2' ⊙ Hu3'))
  (HHv:
    rew [fun p: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
        rew [fun z: {a: B &T P' a} => R' z.1 z.2] p in
        (h1 x0 u0 v0:
          (fun z: {a: B &T P' a} => R' z.1 z.2) (f1 x0; g1 x0 u0)) =
        h3 x3 u3 v3]
      eq_existT_curried_hex f1 g1 f2 g2 f3 g3 HH HHu in
    (@sigT_map_eq _ _ (fun z: {x: A1 &T P1 x} => R1 z.1 z.2)
       (fun z: {x: B &T P' x} => R' z.1 z.2)
       (fun z => (f1 z.1; g1 z.1 z.2)) (fun z => h1 z.1 z.2)
       (x0; u0) (x1; u1) v0 v1 (=H1; Hu1) Hv1
     ⊙ (Hv2
        ⊙ @sigT_map_eq _ _ (fun z: {x: A3 &T P3 x} => R3 z.1 z.2)
            (fun z: {x: B &T P' x} => R' z.1 z.2)
            (fun z => (f3 z.1; g3 z.1 z.2)) (fun z => h3 z.1 z.2)
            (x2; u2) (x3; u3) v2 v3 (=H3; Hu3) Hv3)) =
    Hv1'
    ⊙ (@sigT_map_eq _ _ (fun z: {x: A2 &T P2 x} => R2 z.1 z.2)
         (fun z: {x: B &T P' x} => R' z.1 z.2)
         (fun z => (f2 z.1; g2 z.1 z.2)) (fun z => h2 z.1 z.2)
         (x1'; u1') (x2'; u2') v1' v2' (=H2'; Hu2') Hv2' ⊙ Hv3')):
  rew [fun h => rew [fun x => {a: P' x &T R' x a}] h in
      (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)] HH in
  (sigT_map_eq (fun a uv => (g1 a uv.1; h1 a uv.1 uv.2))
     (eq_existT_curried_dep (Q := fun z => R1 z.1 z.2)
        (H := H1) (Hu := Hu1) (Hv := Hv1))
   ⊙ (eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
        (H := H2) (Hu := Hu2) (Hv := Hv2)
      ⊙ sigT_map_eq (fun a uv => (g3 a uv.1; h3 a uv.1 uv.2))
          (eq_existT_curried_dep (Q := fun z => R3 z.1 z.2)
             (H := H3) (Hu := Hu3) (Hv := Hv3)))) =
  eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
    (H := H1') (Hu := Hu1') (Hv := Hv1')
  ⊙ (sigT_map_eq (fun a uv => (g2 a uv.1; h2 a uv.1 uv.2))
       (eq_existT_curried_dep (Q := fun z => R2 z.1 z.2)
          (H := H2') (Hu := Hu2') (Hv := Hv2'))
     ⊙ eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
         (H := H3') (Hu := Hu3') (Hv := Hv3')).
Proof.
  rewrite 3 sigT_map_eq_existT_curried_dep_curried.
  rewrite 4 (sigT_trans_eq_existT_curried_dep (Q := fun z => R' z.1 z.2)).
  refine (eq_existT_curried_dep_eq (Q := fun z => R' z.1 z.2) HH HHu _).
  unfold eq_existT_curried_hex in HHv.
  cbn [projT1 projT2] in HHv |- *.
  pose (R := fun z: {a: B &T P' a} => R' z.1 z.2).
  apply (rew_conjugate (fun p: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
    @eq_rect _ (f1 x0; g1 x0 u0) R
      (h1 x0 u0 v0) (f3 x3; g3 x3 u3) p = h3 x3 u3 v3)) in HHv.
  rewrite 4 (sigT_path_paste_dep R) in HHv.
  now exact HHv.
Defined.

Lemma eq_existT_curried_dep_hex
  {A0 B: Type} {P0: A0 -> Type} {R0: forall a, P0 a -> Type}
  {P': B -> Type} {R': forall b, P' b -> Type}
  (f1: A0 -> B) (g1: forall a, P0 a -> P' (f1 a))
  (h1: forall a u, R0 a u -> R' (f1 a) (g1 a u))
  (f3: A0 -> B) (g3: forall a, P0 a -> P' (f3 a))
  (h3: forall a u, R0 a u -> R' (f3 a) (g3 a u))
  (f2: A0 -> B) (g2: forall a, P0 a -> P' (f2 a))
  (h2: forall a u, R0 a u -> R' (f2 a) (g2 a u))
  {x0 x1 x2 x3 x1' x2': A0}
  {u0: P0 x0} {v0: R0 x0 u0} {u1: P0 x1} {v1: R0 x1 u1}
  {u2: P0 x2} {v2: R0 x2 u2} {u3: P0 x3} {v3: R0 x3 u3}
  {u1': P0 x1'} {v1': R0 x1' u1'} {u2': P0 x2'} {v2': R0 x2' u2'}
  (H1: x0 = x1) (Hu1: rew [P0] H1 in u0 = u1)
  (Hv1: rew [fun z => R0 z.1 z.2] (=H1; Hu1) in
    (v0: (fun z => R0 z.1 z.2) (x0; u0)) = v1)
  (H2: f1 x1 = f3 x2) (Hu2: rew [P'] H2 in g1 x1 u1 = g3 x2 u2)
  (Hv2: rew [fun z => R' z.1 z.2] (=H2; Hu2) in
    (h1 x1 u1 v1: (fun z => R' z.1 z.2) (f1 x1; g1 x1 u1)) = h3 x2 u2 v2)
  (H3: x2 = x3) (Hu3: rew [P0] H3 in u2 = u3)
  (Hv3: rew [fun z => R0 z.1 z.2] (=H3; Hu3) in
    (v2: (fun z => R0 z.1 z.2) (x2; u2)) = v3)
  (H1': f1 x0 = f2 x1') (Hu1': rew [P'] H1' in g1 x0 u0 = g2 x1' u1')
  (Hv1': rew [fun z => R' z.1 z.2] (=H1'; Hu1') in
    (h1 x0 u0 v0: (fun z => R' z.1 z.2) (f1 x0; g1 x0 u0)) = h2 x1' u1' v1')
  (H2': x1' = x2') (Hu2': rew [P0] H2' in u1' = u2')
  (Hv2': rew [fun z => R0 z.1 z.2] (=H2'; Hu2') in
    (v1': (fun z => R0 z.1 z.2) (x1'; u1')) = v2')
  (H3': f2 x2' = f3 x3) (Hu3': rew [P'] H3' in g2 x2' u2' = g3 x3 u3)
  (Hv3': rew [fun z => R' z.1 z.2] (=H3'; Hu3') in
    (h2 x2' u2' v2': (fun z => R' z.1 z.2) (f2 x2'; g2 x2' u2')) = h3 x3 u3 v3)
  (HH: f_equal f1 H1 • (H2 • f_equal f3 H3) =
    H1' • (f_equal f2 H2' • H3'))
  (HHu: rew [fun h => rew [P'] h in g1 x0 u0 = g3 x3 u3] HH in
    (sigT_map_eq g1 Hu1 ⊙ (Hu2 ⊙ sigT_map_eq g3 Hu3)) =
    Hu1' ⊙ (sigT_map_eq g2 Hu2' ⊙ Hu3'))
  (HHv:
    rew [fun p: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
        rew [fun z: {a: B &T P' a} => R' z.1 z.2] p in
        (h1 x0 u0 v0:
          (fun z: {a: B &T P' a} => R' z.1 z.2) (f1 x0; g1 x0 u0)) =
        h3 x3 u3 v3]
      eq_existT_curried_hex f1 g1 f2 g2 f3 g3 HH HHu in
    (@sigT_map_eq _ _ (fun z: {x: A0 &T P0 x} => R0 z.1 z.2)
       (fun z: {x: B &T P' x} => R' z.1 z.2)
       (fun z => (f1 z.1; g1 z.1 z.2)) (fun z => h1 z.1 z.2)
       (x0; u0) (x1; u1) v0 v1 (=H1; Hu1) Hv1
     ⊙ (Hv2
        ⊙ @sigT_map_eq _ _ (fun z: {x: A0 &T P0 x} => R0 z.1 z.2)
            (fun z: {x: B &T P' x} => R' z.1 z.2)
            (fun z => (f3 z.1; g3 z.1 z.2)) (fun z => h3 z.1 z.2)
            (x2; u2) (x3; u3) v2 v3 (=H3; Hu3) Hv3)) =
    Hv1'
    ⊙ (@sigT_map_eq _ _ (fun z: {x: A0 &T P0 x} => R0 z.1 z.2)
         (fun z: {x: B &T P' x} => R' z.1 z.2)
         (fun z => (f2 z.1; g2 z.1 z.2)) (fun z => h2 z.1 z.2)
         (x1'; u1') (x2'; u2') v1' v2' (=H2'; Hu2') Hv2' ⊙ Hv3')):
  rew [fun h => rew [fun x => {a: P' x &T R' x a}] h in
      (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)] HH in
  (sigT_map_eq (fun a uv => (g1 a uv.1; h1 a uv.1 uv.2))
     (eq_existT_curried_dep (Q := fun z => R0 z.1 z.2)
        (H := H1) (Hu := Hu1) (Hv := Hv1))
   ⊙ (eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
        (H := H2) (Hu := Hu2) (Hv := Hv2)
      ⊙ sigT_map_eq (fun a uv => (g3 a uv.1; h3 a uv.1 uv.2))
          (eq_existT_curried_dep (Q := fun z => R0 z.1 z.2)
             (H := H3) (Hu := Hu3) (Hv := Hv3)))) =
  eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
    (H := H1') (Hu := Hu1') (Hv := Hv1')
  ⊙ (sigT_map_eq (fun a uv => (g2 a uv.1; h2 a uv.1 uv.2))
       (eq_existT_curried_dep (Q := fun z => R0 z.1 z.2)
          (H := H2') (Hu := Hu2') (Hv := Hv2'))
     ⊙ eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
         (H := H3') (Hu := Hu3') (Hv := Hv3')).
Proof.
  now exact (eq_existT_curried_dep_hex_split f1 g1 h1 f3 g3 h3 f2 g2 h2
    H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3 H1' Hu1' Hv1' H2' Hu2' Hv2'
    H3' Hu3' Hv3' HH HHu HHv).
Defined.

Section Coh2Layer.

Context {X2A X2C X1 Y1 X0: Type}.
Context {S2A: X2A -> Type}.
Context {S2C: X2C -> Type}.
Context {S1: X1 -> Type}.
Context {SY: Y1 -> Type}.
Context {S0: X0 -> Type}.

Context {TUA TUB TUC T: Type}.
Context {uf0: TUA -> Y1}.
Context {ufB: TUB -> X1}.
Context {ufC: TUC -> X1}.
Context {rf0: T -> X0}.
Context {fA: TUA -> T}.
Context {fB: TUB -> T}.
Context {fC: TUC -> T}.

Context {rfq: Y1 -> X0}.
Context {rfs rfr: X1 -> X0}.
Context {Fq: forall y, SY y -> S0 (rfq y)}.
Context {Fs: forall y, S1 y -> S0 (rfs y)}.
Context {Fr: forall y, S1 y -> S0 (rfr y)}.
Context {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}.
Context {gs: forall dd, rfs (ufB dd) = rf0 (fB dd)}.
Context {gr: forall dd, rfr (ufC dd) = rf0 (fC dd)}.

Context {rur rusY: X2A -> Y1}.
Context {ruq1: X2A -> X1}.
Context {rusX rur1: X2C -> X1}.
Context {Rr: forall z, S2A z -> SY (rur z)}.
Context {RsY: forall z, S2A z -> SY (rusY z)}.
Context {Rq1: forall z, S2A z -> S1 (ruq1 z)}.
Context {RsX: forall z, S2C z -> S1 (rusX z)}.
Context {Rr1: forall z, S2C z -> S1 (rur1 z)}.

Context {KA2: forall z, rfq (rusY z) = rfs (ruq1 z)}.
Context {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}.
Context {KA6: forall z, rfr (rusX z) = rfs (rur1 z)}.
Context {HKA2: forall z (c: S2A z),
  rew [S0] KA2 z in Fq (rusY z) (RsY z c) = Fs (ruq1 z) (Rq1 z c)}.
Context {HKA4: forall z (c: S2A z),
  rew [S0] KA4 z in Fq (rur z) (Rr z c) = Fr (ruq1 z) (Rq1 z c)}.
Context {HKA6: forall z (c: S2C z),
  rew [S0] KA6 z in Fr (rusX z) (RsX z c) = Fs (rur1 z) (Rr1 z c)}.

(** The permutahedral coherence of frames compares four hexagons on each
    side. The squares [NKA2, NKA4, NKA6] express naturality of the restriction
    coherences; [Ngq, Ngs, Ngr] express naturality of the comparison maps.
    Each side-face pasting combines one hexagon and one of these squares.
    Pasting [HHA] at the top and the image of [κ] at the bottom completes
    the two boundary paths. *)
Definition permutahedral_coherence
  (u0 u1: TUA) (u2 u3: TUB) (u4 u5: TUC)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2: X2A) (zq1 zq2: X2C)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (pV0: rur zs2 = uf0 u0) (pV1: rusY zr2 = uf0 u1)
  (pV2: ruq1 zr2 = ufB u2) (pV3: rur1 zq2 = ufB u3)
  (pV4: ruq1 zs2 = ufC u4) (pV5: rusX zq2 = ufC u5)
  (K1: rur zs1 = rusY zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rusX zq1)
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rusY pIr • pV1))
  (HH3: f_equal ruq1 pIr • (pV2 • f_equal ufB eU2)
        = K3 • (f_equal rur1 pIq • pV3))
  (HH5: f_equal ruq1 pIs • (pV4 • f_equal ufC eU3)
        = K5 • (f_equal rusX pIq • pV5))
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6))
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (HHA: f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
      = KA4 zs1 • (f_equal rfr K5 • KA6 zq1)): Type :=
  let NKA2: f_equal rfq (f_equal rusY pIr) • KA2 zr2 =
      KA2 zr1 • f_equal rfs (f_equal ruq1 pIr) :=
    f_equal_naturality rusY ruq1 rfq rfs KA2 pIr in
  let NKA4: f_equal rfq (f_equal rur pIs) • KA4 zs2 =
      KA4 zs1 • f_equal rfr (f_equal ruq1 pIs) :=
    f_equal_naturality rur ruq1 rfq rfr KA4 pIs in
  let NKA6: f_equal rfr (f_equal rusX pIq) • KA6 zq2 =
      KA6 zq1 • f_equal rfs (f_equal rur1 pIq) :=
    f_equal_naturality rusX rur1 rfr rfs KA6 pIq in
  let Ngq: f_equal rfq (f_equal uf0 eU1) • gq u1 =
      gq u0 • f_equal rf0 (f_equal fA eU1) :=
    f_equal_naturality uf0 fA rfq rf0 gq eU1 in
  let Ngs: f_equal rfs (f_equal ufB eU2) • gs u3 =
      gs u2 • f_equal rf0 (f_equal fB eU2) :=
    f_equal_naturality ufB fB rfs rf0 gs eU2 in
  let Ngr: f_equal rfr (f_equal ufC eU3) • gr u5 =
      gr u4 • f_equal rf0 (f_equal fC eU3) :=
    f_equal_naturality ufC fC rfr rf0 gr eU3 in
  let left := square_compose_map rf0
      (layer_square_map uf0 rur rusY rfq fA rf0 gq eU1 pIs pIr pV0 pV1 K1 HH1 Ngq)
      (square_compose_map rf0
        (layer_square_nat rusY ruq1 rfq rfs rf0 KA2 pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 NKA2)
        (layer_square_map ufB ruq1 rur1 rfs fB rf0 gs eU2 pIr pIq pV2 pV3 K3 HH3 Ngs)) •
    whisker_r HHA _ in
  let right := whisker_l _ (f_equal (fun e => f_equal rf0 e) κ) •
    square_compose_map rf0
      (layer_square_nat rur ruq1 rfq rfr rf0 KA4 pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 NKA4)
      (square_compose_map rf0
        (layer_square_map ufC ruq1 rusX rfr fC rf0 gr eU3 pIs pIq pV4 pV5 K5 HH5 Ngr)
        (layer_square_nat rusX rur1 rfr rfs rf0 KA6 pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 NKA6)) in
  left = right.


(** The dependent hexagon transported through the six layer-coherence cells.
    The frame premise [permutahedral_coherence] compares its two boundary pastings. *)
Lemma rew_coh2Layer_perm4
  (u0 u1: TUA) (u2 u3: TUB) (u4 u5: TUC)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2: X2A) (zq1 zq2: X2C)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (aS: S2A zs1) (aR: S2A zr1) (aQ: S2C zq1)
  (pV0: rur zs2 = uf0 u0) (pV1: rusY zr2 = uf0 u1)
  (pV2: ruq1 zr2 = ufB u2) (pV3: rur1 zq2 = ufB u3)
  (pV4: ruq1 zs2 = ufC u4) (pV5: rusX zq2 = ufC u5)
  (K1: rur zs1 = rusY zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rusX zq1)
  (HK1: rew [SY] K1 in Rr zs1 aS = RsY zr1 aR)
  (HK3: rew [S1] K3 in Rq1 zr1 aR = Rr1 zq1 aQ)
  (HK5: rew [S1] K5 in Rq1 zs1 aS = RsX zq1 aQ)
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rusY pIr • pV1))
  (HH3: f_equal ruq1 pIr • (pV2 • f_equal ufB eU2)
        = K3 • (f_equal rur1 pIq • pV3))
  (HH5: f_equal ruq1 pIs • (pV4 • f_equal ufC eU3)
        = K5 • (f_equal rusX pIq • pV5))
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6))
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (HHA: f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
        = KA4 zs1 • (f_equal rfr K5 • KA6 zq1))
  (Hcoh2Painting:
    rew [fun π: rfq (rur zs1) = rfs (rur1 zq1) =>
        rew [S0] π in Fq (rur zs1) (Rr zs1 aS)
        = Fs (rur1 zq1) (Rr1 zq1 aQ)] HHA in
    (sigT_map_eq Fq HK1 ⊙ (HKA2 zr1 aR ⊙ sigT_map_eq Fs HK3)) =
    HKA4 zs1 aS ⊙ (sigT_map_eq Fr HK5 ⊙ HKA6 zq1 aQ))
  (Hcoh3Frame: permutahedral_coherence u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA):
  rew [fun e: fA u0 = fB u3 =>
    rew [fun dd => S0 (rf0 dd)] e in
      rew [S0] gq u0 in Fq (uf0 u0)
        (rew [SY] pV0 in Rr zs2 (rew [S2A] pIs in aS)) =
      rew [S0] gs u3 in Fs (ufB u3)
        (rew [S1] pV3 in Rr1 zq2 (rew [S2C] pIq in aQ))] κ in
  (sigT_map_eq (fun dd x => rew [S0] gq dd in Fq (uf0 dd) x)
     (rew_cohLayer_hex SY uf0 Rr RsY eU1 pIs pIr pV0 pV1 K1 aS aR HK1 HH1)
   ⊙ (rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2)
        (RsY zr2 (rew [S2A] pIr in aR)) (Rq1 zr2 (rew [S2A] pIr in aR))
        (HKA2 zr2 (rew [S2A] pIr in aR)) HH2
      ⊙ sigT_map_eq (fun dd x => rew [S0] gs dd in Fs (ufB dd) x)
          (rew_cohLayer_hex S1 ufB Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 aR aQ HK3 HH3))) =
  rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2)
    (Rr zs2 (rew [S2A] pIs in aS)) (Rq1 zs2 (rew [S2A] pIs in aS))
    (HKA4 zs2 (rew [S2A] pIs in aS)) HH4
  ⊙ (sigT_map_eq (fun dd x => rew [S0] gr dd in Fr (ufC dd) x)
       (rew_cohLayer_hex S1 ufC Rq1 RsX eU3 pIs pIq pV4 pV5 K5 aS aQ HK5 HH5)
     ⊙ rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2)
         (RsX zq2 (rew [S2C] pIq in aQ)) (Rr1 zq2 (rew [S2C] pIq in aQ))
         (HKA6 zq2 (rew [S2C] pIq in aQ)) HH6).
Proof.
  refine (square_cube_map_dep rf0 S0 _ _ κ HHA Hcoh3Frame
    _ _ _ _ _ _ _ _ Hcoh2Painting).
  - eapply square_compose_map_dep.
    + now exact (layer_square_map_dep uf0 rur rusY rfq fA rf0 gq SY S0 S2A S2A
        Fq Rr RsY eU1 pIs pIr pV0 pV1 K1 HH1 HK1).
    + eapply square_compose_map_dep.
      * now exact (layer_square_nat_dep rusY ruq1 rfq rfs rf0 RsY Rq1 Fq Fs KA2 HKA2
          pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 aR).
      * now exact (layer_square_map_dep ufB ruq1 rur1 rfs fB rf0 gs S1 S0 S2A S2C
          Fs Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 HH3 HK3).
  - eapply square_compose_map_dep.
    + now exact (layer_square_nat_dep rur ruq1 rfq rfr rf0 Rr Rq1 Fq Fr KA4 HKA4
        pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 aS).
    + eapply square_compose_map_dep.
      * now exact (layer_square_map_dep ufC ruq1 rusX rfr fC rf0 gr S1 S0 S2A S2C
          Fr Rq1 RsX eU3 pIs pIq pV4 pV5 K5 HH5 HK5).
      * now exact (layer_square_nat_dep rusX rur1 rfr rfs rf0 RsX Rr1 Fr Fs KA6 HKA6
          pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 aQ).
Defined.

End Coh2Layer.

Lemma rew_coh2Painting_restr0 {TU0 TU2 TU3 TL: Type}
  {P: TL -> Type} {Sq: TU2 -> Type} {Sr: TU3 -> Type}
  {rq: TU2 -> TL} {rr: TU3 -> TL} {r0: TU0 -> TL}
  (F: forall m, Sq m -> P (rq m))
  (G: forall n, Sr n -> P (rr n))
  {d1 d2: TU0} (E1: d1 = d2)
  {m1 m2: TU2} (e2: m1 = m2)
  {n1 n2: TU3} (e5: n1 = n2)
  (pQ: rq m2 = r0 d1) (pR: rr n2 = r0 d2)
  (KA: rq m1 = rr n1)
  (aL: Sq m1) (aR: Sr n1)
  (HK: rew [P] KA in F m1 aL = G n1 aR)
  (κ: f_equal rq e2 • (pQ • f_equal r0 E1) = KA • (f_equal rr e5 • pR)):
  rew [fun π: rq m1 = r0 d2 =>
    rew [P] π in F m1 aL = rew [P] pR in G n2 (rew [Sr] e5 in aR)] κ in
  (sigT_map_eq (Q := P) F (p := e2) (u := aL) eq_refl
   ⊙ (eq_refl
      ⊙ sigT_map_eq (P := fun d => P (r0 d)) (Q := P) (f := r0) (fun _ a => a)
          (rew_cohLayer_hex P r0 F G E1 e2 e5 pQ pR KA aL aR HK κ))) =
  HK ⊙ (sigT_map_eq (Q := P) G (p := e5) (u := aR) eq_refl ⊙ eq_refl).
Proof.
  rewrite <- sigT_trans_eq_assoc.
  rewrite rew_compose.
  now exact (layer_square rq rr r0 F G e2 e5 E1 pQ pR KA HK κ).
Defined.

Section Coh2LayerSplit.

Local Arguments rew_cohLayer_hex {T1 T2 T3 X} P {S2 S3} rf0 {rfF rfG} F G
  {d1 d2} E1 {m1 m2} C2 {n1 n2} D2 C1 D1 K aL aR _ _.

Context {X2A X2C X1 Y1 X0: Type}.
Context {S2A: X2A -> Type}.
Context {S2C: X2C -> Type}.
Context {S1: X1 -> Type}.
Context {SY: Y1 -> Type}.
Context {S0: X0 -> Type}.

Context {TUA TUB TUC T: Type}.
Context {uf0: TUA -> Y1}.
Context {ufB: TUB -> X1}.
Context {ufC: TUC -> X1}.
Context {rf0: T -> X0}.
Context {fA: TUA -> T}.
Context {fB: TUB -> T}.
Context {fC: TUC -> T}.

Context {rfq: Y1 -> X0}.
Context {rfs rfr: X1 -> X0}.
Context {Fq: forall y, SY y -> S0 (rfq y)}.
Context {Fs: forall y, S1 y -> S0 (rfs y)}.
Context {Fr: forall y, S1 y -> S0 (rfr y)}.
Context {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}.
Context {gs: forall dd, rfs (ufB dd) = rf0 (fB dd)}.
Context {gr: forall dd, rfr (ufC dd) = rf0 (fC dd)}.

Context {rur rusY: X2A -> Y1}.
Context {ruq1: X2A -> X1}.
Context {rusX rur1: X2C -> X1}.
Context {Rr: forall z, S2A z -> SY (rur z)}.
Context {RsY: forall z, S2A z -> SY (rusY z)}.
Context {Rq1: forall z, S2A z -> S1 (ruq1 z)}.
Context {RsX: forall z, S2C z -> S1 (rusX z)}.
Context {Rr1: forall z, S2C z -> S1 (rur1 z)}.

Context {KA2: forall z, rfq (rusY z) = rfs (ruq1 z)}.
Context {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}.
Context {KA6: forall z, rfr (rusX z) = rfs (rur1 z)}.
Context {HKA2: forall z (c: S2A z),
  rew [S0] KA2 z in Fq (rusY z) (RsY z c) = Fs (ruq1 z) (Rq1 z c)}.
Context {HKA4: forall z (c: S2A z),
  rew [S0] KA4 z in Fq (rur z) (Rr z c) = Fr (ruq1 z) (Rq1 z c)}.
Context {HKA6: forall z (c: S2C z),
  rew [S0] KA6 z in Fr (rusX z) (RsX z c) = Fs (rur1 z) (Rr1 z c)}.

Context {A0: Type}.
Context {a: A0}.

(** Endpoint-corrected form of the permutahedral pasting. Matching
    corrections cancel at each shared vertex of its six side cells. *)
Lemma rew_coh2Layer_split
  (u0 u1: TUA) (u2 u3: TUB) (u4 u5: TUC)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2: X2A) (zq1 zq2: X2C)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (FIs: A0 -> S2A zs1) (FIr: A0 -> S2A zr1) (FIq: A0 -> S2C zq1)
  (pV0: rur zs2 = uf0 u0) (pV1: rusY zr2 = uf0 u1)
  (pV2: ruq1 zr2 = ufB u2) (pV3: rur1 zq2 = ufB u3)
  (pV4: ruq1 zs2 = ufC u4) (pV5: rusX zq2 = ufC u5)
  (K1: rur zs1 = rusY zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rusX zq1)
  (HK1: rew [SY] K1 in Rr zs1 (FIs a) = RsY zr1 (FIr a))
  (HK3: rew [S1] K3 in Rq1 zr1 (FIr a) = Rr1 zq1 (FIq a))
  (HK5: rew [S1] K5 in Rq1 zs1 (FIs a) = RsX zq1 (FIq a))
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rusY pIr • pV1))
  (HH3: f_equal ruq1 pIr • (pV2 • f_equal ufB eU2)
        = K3 • (f_equal rur1 pIq • pV3))
  (HH5: f_equal ruq1 pIs • (pV4 • f_equal ufC eU3)
        = K5 • (f_equal rusX pIq • pV5))
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (aP: S2A zs2) (kP: aP = rew [S2A] pIs in FIs a)
  (aQ: S2A zr2) (kQ: aQ = rew [S2A] pIr in FIr a)
  (aR: S2C zq2) (kR: aR = rew [S2C] pIq in FIq a)
  (bP: SY (uf0 u0)) (kbP: bP = rew [SY] pV0 in Rr zs2 aP)
  (bQ: SY (uf0 u1)) (kbQ: bQ = rew [SY] pV1 in RsY zr2 aQ)
  (bR: S1 (ufB u2)) (kbR: bR = rew [S1] pV2 in Rq1 zr2 aQ)
  (bR': S1 (ufB u3)) (kbR': bR' = rew [S1] pV3 in Rr1 zq2 aR)
  (bW: S1 (ufC u4)) (kbW: bW = rew [S1] pV4 in Rq1 zs2 aP)
  (bW': S1 (ufC u5)) (kbW': bW' = rew [S1] pV5 in RsX zq2 aR)
  (cA0: S0 (rf0 (fA u0))) (kc0: cA0 = rew [S0] gq u0 in Fq (uf0 u0) bP)
  (cA1: S0 (rf0 (fA u1))) (kc1: cA1 = rew [S0] gq u1 in Fq (uf0 u1) bQ)
  (cB2: S0 (rf0 (fB u2))) (kc2: cB2 = rew [S0] gs u2 in Fs (ufB u2) bR)
  (cB3: S0 (rf0 (fB u3))) (kc3: cB3 = rew [S0] gs u3 in Fs (ufB u3) bR')
  (cC4: S0 (rf0 (fC u4))) (kc4: cC4 = rew [S0] gr u4 in Fr (ufC u4) bW)
  (cC5: S0 (rf0 (fC u5))) (kc5: cC5 = rew [S0] gr u5 in Fr (ufC u5) bW')
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6))
  (HHA: f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
        = KA4 zs1 • (f_equal rfr K5 • KA6 zq1))
  (Hcoh2Painting:
    rew [fun π: rfq (rur zs1) = rfs (rur1 zq1) =>
        rew [S0] π in Fq (rur zs1) (Rr zs1 (FIs a))
        = Fs (rur1 zq1) (Rr1 zq1 (FIq a))] HHA in
    (sigT_map_eq Fq HK1 ⊙ (HKA2 zr1 (FIr a) ⊙ sigT_map_eq Fs HK3)) =
    HKA4 zs1 (FIs a) ⊙ (sigT_map_eq Fr HK5 ⊙ HKA6 zq1 (FIq a)))
  (Hcoh3Frame: permutahedral_coherence u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA):
  rew [fun e: fA u0 = fB u3 =>
       rew [fun dd => S0 (rf0 dd)] e in cA0 = cB3] κ in
  (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] f_equal fA eU1 in x) kc0
   • (sigT_map_eq (P := fun dd => SY (uf0 dd)) (Q := fun dd => S0 (rf0 dd))
        (f := fA) (fun dd x => rew [S0] gq dd in Fq (uf0 dd) x)
        (f_equal (fun x => rew [fun dd => SY (uf0 dd)] eU1 in x) kbP
         • (f_equal (fun x =>
              rew [fun dd => SY (uf0 dd)] eU1 in rew [SY] pV0 in Rr zs2 x) kP
            • (rew_cohLayer_hex SY uf0 Rr RsY eU1 pIs pIr pV0 pV1 K1
                 (FIs a) (FIr a) HK1 HH1
               • (eq_sym (f_equal (fun x => rew [SY] pV1 in RsY zr2 x) kQ)
                  • eq_sym kbQ))))
      • eq_sym kc1)
   ⊙[fun dd => S0 (rf0 dd)]
     (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e2 in x) kc1
      • (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e2 in
           rew [S0] gq u1 in Fq (uf0 u1) x) kbQ
         • (rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2)
              (RsY zr2 aQ) (Rq1 zr2 aQ) (HKA2 zr2 aQ) HH2
            • (eq_sym (f_equal (fun x => rew [S0] gs u2 in Fs (ufB u2) x) kbR)
               • eq_sym kc2)))
      ⊙[fun dd => S0 (rf0 dd)]
        (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] f_equal fB eU2 in x) kc2
         • (sigT_map_eq (P := fun dd => S1 (ufB dd))
              (Q := fun dd => S0 (rf0 dd)) (f := fB)
              (fun dd x => rew [S0] gs dd in Fs (ufB dd) x)
              (f_equal (fun x => rew [fun dd => S1 (ufB dd)] eU2 in x) kbR
               • (f_equal (fun x => rew [fun dd => S1 (ufB dd)] eU2 in
                    rew [S1] pV2 in Rq1 zr2 x) kQ
                  • (rew_cohLayer_hex S1 ufB Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3
                       (FIr a) (FIq a) HK3 HH3
                     • (eq_sym (f_equal (fun x =>
                          rew [S1] pV3 in Rr1 zq2 x) kR)
                        • eq_sym kbR'))))
            • eq_sym kc3))))
  = f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e4 in x) kc0
    • (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e4 in
         rew [S0] gq u0 in Fq (uf0 u0) x) kbP
       • (rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2)
            (Rr zs2 aP) (Rq1 zs2 aP) (HKA4 zs2 aP) HH4
          • (eq_sym (f_equal (fun x => rew [S0] gr u4 in Fr (ufC u4) x) kbW)
             • eq_sym kc4)))
    ⊙[fun dd => S0 (rf0 dd)]
      (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] f_equal fC eU3 in x) kc4
       • (sigT_map_eq (P := fun dd => S1 (ufC dd))
            (Q := fun dd => S0 (rf0 dd)) (f := fC)
            (fun dd x => rew [S0] gr dd in Fr (ufC dd) x)
            (f_equal (fun x => rew [fun dd => S1 (ufC dd)] eU3 in x) kbW
             • (f_equal (fun x => rew [fun dd => S1 (ufC dd)] eU3 in
                  rew [S1] pV4 in Rq1 zs2 x) kP
                • (rew_cohLayer_hex S1 ufC Rq1 RsX eU3 pIs pIq pV4 pV5 K5
                     (FIs a) (FIq a) HK5 HH5
                   • (eq_sym (f_equal (fun x => rew [S1] pV5 in RsX zq2 x) kR)
                      • eq_sym kbW'))))
          • eq_sym kc5)
       ⊙[fun dd => S0 (rf0 dd)]
         (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e6 in x) kc5
          • (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e6 in
               rew [S0] gr u5 in Fr (ufC u5) x) kbW'
             • (rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2)
                  (RsX zq2 aR) (Rr1 zq2 aR) (HKA6 zq2 aR) HH6
                • (eq_sym (f_equal (fun x =>
                     rew [S0] gs u3 in Fs (ufB u3) x) kbR')
                   • eq_sym kc3))))).
Proof.
  rewrite (dpath_change_flat_map (P := fun d => SY (uf0 d))
    (fun c => rew [SY] pV0 in Rr zs2 c) (fun c => rew [SY] pV1 in RsY zr2 c)
    kP kQ kbP kbQ).
  rewrite (dpath_change_flat_map (P := fun d => S1 (ufB d))
    (fun c => rew [S1] pV2 in Rq1 zr2 c) (fun c => rew [S1] pV3 in Rr1 zq2 c)
    kQ kR kbR kbR').
  rewrite (dpath_change_flat_map (P := fun d => S1 (ufC d))
    (fun c => rew [S1] pV4 in Rq1 zs2 c) (fun c => rew [S1] pV5 in RsX zq2 c)
    kP kR kbW kbW').
  rewrite (dpath_change_flat_map (P := fun d => S0 (rf0 d))
    (fun c => rew [S0] gq u1 in Fq (uf0 u1) c)
    (fun c => rew [S0] gs u2 in Fs (ufB u2) c) kbQ kbR kc1 kc2).
  rewrite (dpath_change_flat_map (P := fun d => S0 (rf0 d))
    (fun c => rew [S0] gq u0 in Fq (uf0 u0) c)
    (fun c => rew [S0] gr u4 in Fr (ufC u4) c) kbP kbW kc0 kc4).
  rewrite (dpath_change_flat_map (P := fun d => S0 (rf0 d))
    (fun c => rew [S0] gr u5 in Fr (ufC u5) c)
    (fun c => rew [S0] gs u3 in Fs (ufB u3) c) kbW' kbR' kc5 kc3).
  rewrite (dpath_change_fold (P := fun d => S0 (rf0 d)) kc0 _ kc1),
    (dpath_change_fold (P := fun d => S0 (rf0 d)) kc2 _ kc3),
    (dpath_change_fold (P := fun d => S0 (rf0 d)) kc4 _ kc5).
  rewrite <- (dpath_change_natural (P := fun d => S0 (rf0 d))
    (fun c => rew [S0] gq u1 in Fq (uf0 u1) (rew [SY] pV1 in RsY zr2 c))
    (fun c => rew [S0] gs u2 in Fs (ufB u2) (rew [S1] pV2 in Rq1 zr2 c))
    (fun c => rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2)
      (KA2 zr2) (RsY zr2 c) (Rq1 zr2 c) (HKA2 zr2 c) HH2) kQ).
  rewrite <- (dpath_change_natural (P := fun d => S0 (rf0 d))
    (fun c => rew [S0] gq u0 in Fq (uf0 u0) (rew [SY] pV0 in Rr zs2 c))
    (fun c => rew [S0] gr u4 in Fr (ufC u4) (rew [S1] pV4 in Rq1 zs2 c))
    (fun c => rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4)
      (KA4 zs2) (Rr zs2 c) (Rq1 zs2 c) (HKA4 zs2 c) HH4) kP).
  rewrite <- (dpath_change_natural (P := fun d => S0 (rf0 d))
    (fun c => rew [S0] gr u5 in Fr (ufC u5) (rew [S1] pV5 in RsX zq2 c))
    (fun c => rew [S0] gs u3 in Fs (ufB u3) (rew [S1] pV3 in Rr1 zq2 c))
    (fun c => rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3)
      (KA6 zq2) (RsX zq2 c) (Rr1 zq2 c) (HKA6 zq2 c) HH6) kR).
  rewrite 3 dpath_change_map, 6 dpath_change_nest.
  rewrite 6 eq_trans_map_distr.
  rewrite (f_equal_compose (fun c => rew [SY] pV0 in Rr zs2 c)
    (fun c => rew [S0] gq u0 in Fq (uf0 u0) c) kP),
    (f_equal_compose (fun c => rew [SY] pV1 in RsY zr2 c)
      (fun c => rew [S0] gq u1 in Fq (uf0 u1) c) kQ),
    (f_equal_compose (fun c => rew [S1] pV2 in Rq1 zr2 c)
      (fun c => rew [S0] gs u2 in Fs (ufB u2) c) kQ),
    (f_equal_compose (fun c => rew [S1] pV3 in Rr1 zq2 c)
      (fun c => rew [S0] gs u3 in Fs (ufB u3) c) kR),
    (f_equal_compose (fun c => rew [S1] pV4 in Rq1 zs2 c)
      (fun c => rew [S0] gr u4 in Fr (ufC u4) c) kP),
    (f_equal_compose (fun c => rew [S1] pV5 in RsX zq2 c)
      (fun c => rew [S0] gr u5 in Fr (ufC u5) c) kR).
  rewrite <- (eq_trans_assoc kc0), <- (eq_trans_assoc kc1),
    <- (eq_trans_assoc kc2), <- (eq_trans_assoc kc3),
    <- (eq_trans_assoc kc4), <- (eq_trans_assoc kc5).
  rewrite 4 dpath_change_comp.
  apply (dpath_change_cell (P := fun d => S0 (rf0 d))).
  now exact (rew_coh2Layer_perm4 u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
    (FIs a) (FIr a) (FIq a) pV0 pV1 pV2 pV3 pV4 pV5
    K1 K3 K5 HK1 HK3 HK5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA
    Hcoh2Painting Hcoh3Frame).
Defined.

(** A square of transport chains over separate intermediate carriers.
    Endpoint comparisons cancel against their dependent-path edges,
    leaving the central coherence [HK]. *)
Lemma rew_coh2Painting_restr0_split {TU0 TU2 TU3 TL B0: Type}
  {P: TL -> Type} {Sq: TU2 -> Type} {Sr: TU3 -> Type}
  {rq: TU2 -> TL} {rr: TU3 -> TL} {r0: TU0 -> TL}
  (F: forall m, Sq m -> P (rq m))
  (G: forall n, Sr n -> P (rr n))
  {d1 d2: TU0} (E1: d1 = d2)
  {m1 m2: TU2} (e2: m1 = m2)
  {n1 n2: TU3} (e5: n1 = n2)
  (pQ: rq m2 = r0 d1) (pR: rr n2 = r0 d2)
  (KA: rq m1 = rr n1)
  (b0: B0) (AR: B0 -> Sq m1) (AQ1: B0 -> Sr n1)
  (HK: rew [P] KA in F m1 (AR b0) = G n1 (AQ1 b0))
  (κ: f_equal rq e2 • (pQ • f_equal r0 E1) = KA • (f_equal rr e5 • pR))
  (u1: Sq m2) (kF: u1 = rew [Sq] e2 in AR b0)
  (u12: Sr n2) (kG: u12 = rew [Sr] e5 in AQ1 b0)
  (w3: P (r0 d1)) (kM: w3 = rew [P] pQ in F m2 u1)
  (w4: P (r0 d2)) (kM': w4 = rew [P] pR in G n2 u12):
  rew [fun π: rq m1 = r0 d2 => rew [P] π in F m1 (AR b0) = w4] κ in
  (sigT_map_eq (Q := P) F (eq_sym kF)
   ⊙ (eq_sym kM
      ⊙ (eq_sym (rew_map P r0 E1 w3)
         • (f_equal (fun x => rew [fun dd: TU0 => P (r0 dd)] E1 in x) kM
            • (f_equal (fun x =>
                 rew [fun dd: TU0 => P (r0 dd)] E1 in rew [P] pQ in F m2 x) kF
               • (rew_cohLayer_hex P r0 F G E1 e2 e5 pQ pR KA
                    (AR b0) (AQ1 b0) HK κ
                  • (eq_sym (f_equal (fun x =>
                       rew [P] pR in G n2 x) kG)
                     • eq_sym kM'))))))) =
  HK ⊙ (sigT_map_eq (Q := P) G (eq_sym kG) ⊙ eq_sym kM').
Proof.
  rewrite (dpath_change_flat_map (P := fun d => P (r0 d))
    (fun c => rew [P] pQ in F m2 c) (fun c => rew [P] pR in G n2 c)
    kF kG kM kM').
  rewrite <- (sigT_map_eq_id (P := P) r0).
  rewrite <- (dpath_change_refl (P := Sq) e2 (AR b0) kF),
    <- (dpath_change_refl (P := Sr) e5 (AQ1 b0) kG).
  rewrite <- (dpath_change_transport (P := P) pQ (f_equal (F m2) kF) kM),
    <- (dpath_change_transport (P := P) pR (f_equal (G n2) kG) kM').
  rewrite 3 dpath_change_map.
  cbn [f_equal].
  rewrite 2 f_equal_id.
  rewrite (f_equal_compose (F m2) (fun c => rew [P] pQ in c) kF),
    (f_equal_compose (G n2) (fun c => rew [P] pR in c) kG).
  rewrite <- (dpath_change_id (P := P) HK).
  rewrite 4 dpath_change_comp.
  apply (dpath_change_cell (P := P)).
  rewrite dpath_change_id.
  now exact (rew_coh2Painting_restr0 F G E1 e2 e5 pQ pR KA (AR b0) (AQ1 b0) HK κ).
Defined.

(** Present the four dependent-path edges of the square as parameters,
    with equations identifying them with the endpoint corrections. This
    allows their presentations to be checked separately. [kF] points
    from the transported source to its endpoint. *)

Lemma rew_coh2Painting_restr0_edges {TU0 TU2 TU3 TL: Type}
  {P: TL -> Type} {Sq: TU2 -> Type} {Sr: TU3 -> Type}
  {rq: TU2 -> TL} {rr: TU3 -> TL} {r0: TU0 -> TL}
  (F: forall m, Sq m -> P (rq m))
  (G: forall n, Sr n -> P (rr n))
  {d1 d2: TU0} (E1: d1 = d2)
  {m1 m2: TU2} (e2: m1 = m2)
  {n1 n2: TU3} (e5: n1 = n2)
  (pQ: rq m2 = r0 d1) (pR: rr n2 = r0 d2)
  (KA: rq m1 = rr n1)
  (aL: Sq m1) (aR: Sr n1)
  (HK: rew [P] KA in F m1 aL = G n1 aR)
  (κ: f_equal rq e2 • (pQ • f_equal r0 E1) = KA • (f_equal rr e5 • pR))
  (u1: Sq m2) (kF: rew [Sq] e2 in aL = u1)
  (u12: Sr n2) (kG: u12 = rew [Sr] e5 in aR)
  (w3: P (r0 d1)) (kM: w3 = rew [P] pQ in F m2 u1)
  (w4: P (r0 d2)) (kM': w4 = rew [P] pR in G n2 u12)
  (EA: rew [P] f_equal rq e2 in F m1 aL = F m2 u1)
  (hEA: EA = sigT_map_eq (Q := P) F kF)
  (EB: rew [P] pQ in F m2 u1 = w3)
  (hEB: EB = eq_sym kM)
  (EG: rew [P] f_equal rr e5 in G n1 aR = G n2 u12)
  (hEG: EG = sigT_map_eq (Q := P) G (eq_sym kG))
  (EM: rew [P] pR in G n2 u12 = w4)
  (hEM: EM = eq_sym kM'):
  rew [fun π: rq m1 = r0 d2 => rew [P] π in F m1 aL = w4] κ in
  (EA
   ⊙ (EB
      ⊙ (eq_sym (rew_map P r0 E1 w3)
         • (f_equal (fun x => rew [fun dd: TU0 => P (r0 dd)] E1 in x) kM
            • (f_equal (fun x =>
                 rew [fun dd: TU0 => P (r0 dd)] E1 in rew [P] pQ in F m2 x)
                 (eq_sym kF)
               • (rew_cohLayer_hex P r0 F G E1 e2 e5 pQ pR KA aL aR HK κ
                  • (eq_sym (f_equal (fun x =>
                       rew [P] pR in G n2 x) kG)
                     • eq_sym kM'))))))) =
  HK ⊙ (EG ⊙ EM).
Proof.
  rewrite hEA, hEB, hEG, hEM.
  pose proof (rew_coh2Painting_restr0_split F G E1 e2 e5 pQ pR KA
    tt (fun _: unit => aL) (fun _: unit => aR) HK κ
    u1 (eq_sym kF) u12 kG w3 kM w4 kM') as H.
  now rewrite eq_sym_involutive in H.
Defined.

End Coh2LayerSplit.
