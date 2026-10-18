(** Permutahedral and hexagonal-prism coherences. *)

From Bonak.Lib Require Import Notation RewLemmas SigT Coh2Shapes.
From Bonak.SSGpd Require Import Pasting.

(** Permutahedral coherence compares four hexagons on each side.
    The squares [NKA2, NKA4, NKA6] express naturality of [KA2, KA4, KA6];
    [Ngq, Ngs, Ngr] express naturality of [gq, gs, gr].
    Each side-face pasting combines one hexagon and one of these squares.
    Pasting [HHA] at the top and the image of [κ] at the bottom completes
    the two boundary paths. *)
Definition permutahedral_coherence
  {X2 X1 X0 TU T: Type}
  {uf0: TU -> X1} {rf0: T -> X0} {fA fB fC: TU -> T}
  {rfq rfs rfr: X1 -> X0}
  {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}
  {gs: forall dd, rfs (uf0 dd) = rf0 (fB dd)}
  {gr: forall dd, rfr (uf0 dd) = rf0 (fC dd)}
  {rur rus ruq1 rur1: X2 -> X1}
  {KA2: forall z, rfq (rus z) = rfs (ruq1 z)}
  {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}
  {KA6: forall z, rfr (rus z) = rfs (rur1 z)}
  (u0 u1 u2 u3 u4 u5: TU)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2: X2)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
  (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
  (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
  (K1: rur zs1 = rus zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rus zq1)
  (HH1: hexagonal_coherence rur uf0 rus pIs eU1 pIr pV0 K1 pV1)
  (HH3: hexagonal_coherence ruq1 uf0 rur1 pIr eU2 pIq pV2 K3 pV3)
  (HH5: hexagonal_coherence ruq1 uf0 rus pIs eU3 pIq pV4 K5 pV5)
  (κ: hexagonal_coherence fA fB fC eU1 eU2 eU3 e2 e4 e6)
  (HH2: hexagonal_coherence rfq rf0 rfs pV1 e2 pV2 (gq u1) (KA2 zr2) (gs u2))
  (HH4: hexagonal_coherence rfq rf0 rfr pV0 e4 pV4 (gq u0) (KA4 zs2) (gr u4))
  (HH6: hexagonal_coherence rfr rf0 rfs pV5 e6 pV3 (gr u5) (KA6 zq2) (gs u3))
  (HHA: hexagonal_coherence rfq rfs rfr K1 K3 K5 (KA2 zr1) (KA4 zs1) (KA6 zq1)):
  Prop :=
  let NKA2 := square_coherence_fill rus ruq1 rfq rfs KA2 pIr in
  let NKA4 := square_coherence_fill rur ruq1 rfq rfr KA4 pIs in
  let NKA6 := square_coherence_fill rus rur1 rfr rfs KA6 pIq in
  let Ngq := square_coherence_fill uf0 fA rfq rf0 gq eU1 in
  let Ngs := square_coherence_fill uf0 fB rfs rf0 gs eU2 in
  let Ngr := square_coherence_fill uf0 fC rfr rf0 gr eU3 in
  let left := square_compose_map rf0
      (square_compose_map rf0
        (layer_square_map uf0 rur rus rfq fA rf0 gq eU1 pIs pIr pV0 pV1 K1 HH1 Ngq)
        (layer_square_nat rus ruq1 rfq rfs rf0 KA2 pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 NKA2))
      (layer_square_map uf0 ruq1 rur1 rfs fB rf0 gs eU2 pIr pIq pV2 pV3 K3 HH3 Ngs) in
  let right := square_compose_map rf0
      (layer_square_nat rur ruq1 rfq rfr rf0 KA4 pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 NKA4)
      (square_compose_map rf0
        (layer_square_map uf0 ruq1 rus rfr fC rf0 gr eU3 pIs pIq pV4 pV5 K5 HH5 Ngr)
        (layer_square_nat rus rur1 rfr rfs rf0 KA6 pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 NKA6)) in
  square_cube left right (f_equal (fun e => f_equal rf0 e) κ) HHA.

(** Lift all eight hexagonal faces and the six canonical naturality
    squares of a permutahedral boundary. Their two pasted routes are
    compared after transport along the supplied base permutahedron.
    All five fiber families and all dependent maps are independent. *)
Definition permutahedral_coherence_dep
  {X2 X1 X0 TU T: Type}
  {S2: X2 -> Type} {S1: X1 -> Type} {S0: X0 -> Type}
  {PU: TU -> Type} {PT: T -> Type}
  {uf0: TU -> X1} {rf0: T -> X0} {fA fB fC: TU -> T}
  {rfq rfs rfr: X1 -> X0}
  {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}
  {gs: forall dd, rfs (uf0 dd) = rf0 (fB dd)}
  {gr: forall dd, rfr (uf0 dd) = rf0 (fC dd)}
  {rur rus ruq1 rur1: X2 -> X1}
  {KA2: forall z, rfq (rus z) = rfs (ruq1 z)}
  {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}
  {KA6: forall z, rfr (rus z) = rfs (rur1 z)}
  {u0 u1 u2 u3 u4 u5: TU}
  {eU1: u0 = u1} {eU2: u2 = u3} {eU3: u4 = u5}
  {e2: fA u1 = fB u2} {e4: fA u0 = fC u4} {e6: fC u5 = fB u3}
  {zs1 zs2 zr1 zr2 zq1 zq2: X2}
  {pIs: zs1 = zs2} {pIr: zr1 = zr2} {pIq: zq1 = zq2}
  {pV0: rur zs2 = uf0 u0} {pV1: rus zr2 = uf0 u1}
  {pV2: ruq1 zr2 = uf0 u2} {pV3: rur1 zq2 = uf0 u3}
  {pV4: ruq1 zs2 = uf0 u4} {pV5: rus zq2 = uf0 u5}
  {K1: rur zs1 = rus zr1} {K3: ruq1 zr1 = rur1 zq1} {K5: ruq1 zs1 = rus zq1}
  {HH1: hexagonal_coherence rur uf0 rus pIs eU1 pIr pV0 K1 pV1}
  {HH3: hexagonal_coherence ruq1 uf0 rur1 pIr eU2 pIq pV2 K3 pV3}
  {HH5: hexagonal_coherence ruq1 uf0 rus pIs eU3 pIq pV4 K5 pV5}
  {κ: hexagonal_coherence fA fB fC eU1 eU2 eU3 e2 e4 e6}
  {HH2: hexagonal_coherence rfq rf0 rfs pV1 e2 pV2 (gq u1) (KA2 zr2) (gs u2)}
  {HH4: hexagonal_coherence rfq rf0 rfr pV0 e4 pV4 (gq u0) (KA4 zs2) (gr u4)}
  {HH6: hexagonal_coherence rfr rf0 rfs pV5 e6 pV3 (gr u5) (KA6 zq2) (gs u3)}
  {HHA: hexagonal_coherence rfq rfs rfr K1 K3 K5 (KA2 zr1) (KA4 zs1) (KA6 zq1)}
  (P: permutahedral_coherence u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
    zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq pV0 pV1 pV2 pV3 pV4 pV5
    K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA)
  (U: forall u, PU u -> S1 (uf0 u)) (F0: forall t, PT t -> S0 (rf0 t))
  (FA: forall u, PU u -> PT (fA u)) (FB: forall u, PU u -> PT (fB u))
  (FC: forall u, PU u -> PT (fC u))
  (Fq: forall x, S1 x -> S0 (rfq x)) (Fs: forall x, S1 x -> S0 (rfs x))
  (Fr: forall x, S1 x -> S0 (rfr x))
  (Rr: forall z, S2 z -> S1 (rur z)) (Rs: forall z, S2 z -> S1 (rus z))
  (Rq1: forall z, S2 z -> S1 (ruq1 z)) (Rr1: forall z, S2 z -> S1 (rur1 z))
  (Hgq: forall u a, rew [S0] gq u in Fq (uf0 u) (U u a) = F0 (fA u) (FA u a))
  (Hgs: forall u a, rew [S0] gs u in Fs (uf0 u) (U u a) = F0 (fB u) (FB u a))
  (Hgr: forall u a, rew [S0] gr u in Fr (uf0 u) (U u a) = F0 (fC u) (FC u a))
  (HKA2: forall z a, rew [S0] KA2 z in Fq (rus z) (Rs z a) = Fs (ruq1 z) (Rq1 z a))
  (HKA4: forall z a, rew [S0] KA4 z in Fq (rur z) (Rr z a) = Fr (ruq1 z) (Rq1 z a))
  (HKA6: forall z a, rew [S0] KA6 z in Fr (rus z) (Rs z a) = Fs (rur1 z) (Rr1 z a))
  {a0: PU u0} {a1: PU u1} {a2: PU u2} {a3: PU u3} {a4: PU u4} {a5: PU u5}
  {aS1: S2 zs1} {aS2: S2 zs2} {aR1: S2 zr1} {aR2: S2 zr2}
  {aQ1: S2 zq1} {aQ2: S2 zq2}
  (heU1: rew [PU] eU1 in a0 = a1) (heU2: rew [PU] eU2 in a2 = a3)
  (heU3: rew [PU] eU3 in a4 = a5)
  (he2: rew [PT] e2 in FA u1 a1 = FB u2 a2)
  (he4: rew [PT] e4 in FA u0 a0 = FC u4 a4)
  (he6: rew [PT] e6 in FC u5 a5 = FB u3 a3)
  (hpIs: rew [S2] pIs in aS1 = aS2) (hpIr: rew [S2] pIr in aR1 = aR2)
  (hpIq: rew [S2] pIq in aQ1 = aQ2)
  (hpV0: rew [S1] pV0 in Rr zs2 aS2 = U u0 a0)
  (hpV1: rew [S1] pV1 in Rs zr2 aR2 = U u1 a1)
  (hpV2: rew [S1] pV2 in Rq1 zr2 aR2 = U u2 a2)
  (hpV3: rew [S1] pV3 in Rr1 zq2 aQ2 = U u3 a3)
  (hpV4: rew [S1] pV4 in Rq1 zs2 aS2 = U u4 a4)
  (hpV5: rew [S1] pV5 in Rs zq2 aQ2 = U u5 a5)
  (HK1: rew [S1] K1 in Rr zs1 aS1 = Rs zr1 aR1)
  (HK3: rew [S1] K3 in Rq1 zr1 aR1 = Rr1 zq1 aQ1)
  (HK5: rew [S1] K5 in Rq1 zs1 aS1 = Rs zq1 aQ1)
  (DHH1: hexagonal_coherence_dep Rr U Rs HH1 hpIs heU1 hpIr hpV0 HK1 hpV1)
  (DHH3: hexagonal_coherence_dep Rq1 U Rr1 HH3 hpIr heU2 hpIq hpV2 HK3 hpV3)
  (DHH5: hexagonal_coherence_dep Rq1 U Rs HH5 hpIs heU3 hpIq hpV4 HK5 hpV5)
  (Dκ: hexagonal_coherence_dep FA FB FC κ heU1 heU2 heU3 he2 he4 he6)
  (DHH2: hexagonal_coherence_dep Fq F0 Fs HH2 hpV1 he2 hpV2
    (Hgq u1 a1) (HKA2 zr2 aR2) (Hgs u2 a2))
  (DHH4: hexagonal_coherence_dep Fq F0 Fr HH4 hpV0 he4 hpV4
    (Hgq u0 a0) (HKA4 zs2 aS2) (Hgr u4 a4))
  (DHH6: hexagonal_coherence_dep Fr F0 Fs HH6 hpV5 he6 hpV3
    (Hgr u5 a5) (HKA6 zq2 aQ2) (Hgs u3 a3))
  (DHHA: hexagonal_coherence_dep Fq Fs Fr HHA HK1 HK3 HK5
    (HKA2 zr1 aR1) (HKA4 zs1 aS1) (HKA6 zq1 aQ1)): Prop :=
  let NKA2 := square_coherence_fill rus ruq1 rfq rfs KA2 pIr in
  let NKA4 := square_coherence_fill rur ruq1 rfq rfr KA4 pIs in
  let NKA6 := square_coherence_fill rus rur1 rfr rfs KA6 pIq in
  let Ngq := square_coherence_fill uf0 fA rfq rf0 gq eU1 in
  let Ngs := square_coherence_fill uf0 fB rfs rf0 gs eU2 in
  let Ngr := square_coherence_fill uf0 fC rfr rf0 gr eU3 in
  let left := square_compose_map rf0
      (square_compose_map rf0
        (layer_square_map uf0 rur rus rfq fA rf0 gq eU1 pIs pIr pV0 pV1 K1 HH1 Ngq)
        (layer_square_nat rus ruq1 rfq rfs rf0 KA2 pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 NKA2))
      (layer_square_map uf0 ruq1 rur1 rfs fB rf0 gs eU2 pIr pIq pV2 pV3 K3 HH3 Ngs) in
  let right := square_compose_map rf0
      (layer_square_nat rur ruq1 rfq rfr rf0 KA4 pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 NKA4)
      (square_compose_map rf0
        (layer_square_map uf0 ruq1 rus rfr fC rf0 gr eU3 pIs pIq pV4 pV5 K5 HH5 Ngr)
        (layer_square_nat rus rur1 rfr rfs rf0 KA6 pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 NKA6)) in
  let h1 := layer_square_map_coherence_dep uf0 rur rus rfq fA rf0
    U Rr Rs Fq FA F0 gq Hgq eU1 pIs pIr pV0 pV1 K1 HH1
    heU1 hpIs hpIr hpV0 hpV1 HK1 DHH1 in
  let h3 := layer_square_map_coherence_dep uf0 ruq1 rur1 rfs fB rf0
    U Rq1 Rr1 Fs FB F0 gs Hgs eU2 pIr pIq pV2 pV3 K3 HH3
    heU2 hpIr hpIq hpV2 hpV3 HK3 DHH3 in
  let h5 := layer_square_map_coherence_dep uf0 ruq1 rus rfr fC rf0
    U Rq1 Rs Fr FC F0 gr Hgr eU3 pIs pIq pV4 pV5 K5 HH5
    heU3 hpIs hpIq hpV4 hpV5 HK5 DHH5 in
  let h2 := layer_square_nat_coherence_dep rus ruq1 rfq rfs rf0
    Rs Rq1 Fq Fs F0 KA2 HKA2 pIr pV1 pV2 e2 (gq u1) (gs u2) HH2
    hpIr hpV1 hpV2 he2 (Hgq u1 a1) (Hgs u2 a2) DHH2 in
  let h4 := layer_square_nat_coherence_dep rur ruq1 rfq rfr rf0
    Rr Rq1 Fq Fr F0 KA4 HKA4 pIs pV0 pV4 e4 (gq u0) (gr u4) HH4
    hpIs hpV0 hpV4 he4 (Hgq u0 a0) (Hgr u4 a4) DHH4 in
  let h6 := layer_square_nat_coherence_dep rus rur1 rfr rfs rf0
    Rs Rr1 Fr Fs F0 KA6 HKA6 pIq pV5 pV3 e6 (gr u5) (gs u3) HH6
    hpIq hpV5 hpV3 he6 (Hgr u5 a5) (Hgs u3 a3) DHH6 in
  let hleft := square_compose_map_coherence_dep rf0 S0 PT F0 _ _ _ _ _ _ _ _ _
    (square_compose_map_coherence_dep rf0 S0 PT F0 _ _ _ _ _ _ _ _ _ h1 h2) h3 in
  let hright := square_compose_map_coherence_dep rf0 S0 PT F0 _ _ _ _ _ _ _ _ _
    h4 (square_compose_map_coherence_dep rf0 S0 PT F0 _ _ _ _ _ _ _ _ _ h5 h6) in
  square_cube_coherence_dep S0 left right (f_equal (fun e => f_equal rf0 e) κ) HHA P
    _ _ _ _ _ _ hleft hright
    (sigT_map_eq
      (fun (e: fA u0 = fB u3) (h: rew [PT] e in FA u0 a0 = FB u3 a3) =>
        sigT_map_eq F0 h) Dκ) DHHA.

(** A filler for every permutahedral boundary is equivalent to GUIP.
    For the converse, take all source types to be [unit], all maps constant,
    and all edges and faces reflexive except [HHA]. The boundary equation
    forces this arbitrary 2-loop to be reflexivity. *)
Theorem permutahedron_iff_guip:
  (forall (X2 X1 X0 TU T: Type)
    (uf0: TU -> X1) (rf0: T -> X0) (fA fB fC: TU -> T)
    (rfq rfs rfr: X1 -> X0)
    (gq: forall dd, rfq (uf0 dd) = rf0 (fA dd))
    (gs: forall dd, rfs (uf0 dd) = rf0 (fB dd))
    (gr: forall dd, rfr (uf0 dd) = rf0 (fC dd))
    (rur rus ruq1 rur1: X2 -> X1)
    (KA2: forall z, rfq (rus z) = rfs (ruq1 z))
    (KA4: forall z, rfq (rur z) = rfr (ruq1 z))
    (KA6: forall z, rfr (rus z) = rfs (rur1 z))
    (u0 u1 u2 u3 u4 u5: TU)
    (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
    (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
    (zs1 zs2 zr1 zr2 zq1 zq2: X2)
    (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
    (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
    (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
    (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
    (K1: rur zs1 = rus zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rus zq1)
    (HH1: hexagonal_coherence rur uf0 rus pIs eU1 pIr pV0 K1 pV1)
    (HH3: hexagonal_coherence ruq1 uf0 rur1 pIr eU2 pIq pV2 K3 pV3)
    (HH5: hexagonal_coherence ruq1 uf0 rus pIs eU3 pIq pV4 K5 pV5)
    (κ: hexagonal_coherence fA fB fC eU1 eU2 eU3 e2 e4 e6)
    (HH2: hexagonal_coherence rfq rf0 rfs pV1 e2 pV2 (gq u1) (KA2 zr2) (gs u2))
    (HH4: hexagonal_coherence rfq rf0 rfr pV0 e4 pV4 (gq u0) (KA4 zs2) (gr u4))
    (HH6: hexagonal_coherence rfr rf0 rfs pV5 e6 pV3 (gr u5) (KA6 zq2) (gs u3))
    (HHA: hexagonal_coherence rfq rfs rfr K1 K3 K5 (KA2 zr1) (KA4 zs1) (KA6 zq1)),
    @permutahedral_coherence X2 X1 X0 TU T uf0 rf0 fA fB fC rfq rfs rfr
      gq gs gr rur rus ruq1 rur1 KA2 KA4 KA6
      u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
      zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq pV0 pV1 pV2 pV3 pV4 pV5
      K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA) <->
  (forall (X: Type) (x y: X) (h g: x = y) (p q: h = g), p = q).
Proof.
  split.
  - intros perm X x y h g p q.
    destruct q, h.
    pose proof (perm unit unit X unit unit
      (fun _ => tt) (fun _ => x)
      (fun _ => tt) (fun _ => tt) (fun _ => tt)
      (fun _ => x) (fun _ => x) (fun _ => x)
      (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)
      (fun _ => tt) (fun _ => tt) (fun _ => tt) (fun _ => tt)
      (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)
      tt tt tt tt tt tt eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      tt tt tt tt tt tt eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl p) as H.
    unfold permutahedral_coherence, square_cube, whisker_r in H.
    cbn in H.
    rewrite eq_trans_refl_l, f_equal_id in H.
    now exact H.
  - intros guip *.
    now apply guip.
Qed.

(** A hexagonal prism has two caps [H0, H1] and six square side faces.
    Each cap has a left-associated first route and a right-associated
    second route. Paste the squares along each route and compare the boundary
    pastings. All faces are supplied independently, with shared edges;
    no naturality hypothesis is imposed on this boundary type. *)
Definition hexagonal_prism_coherence {X: Type}
  {x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5: X}
  {p1: x0 = x1} {p2: x1 = x2} {p3: x2 = x3}
  {q1: x0 = x4} {q2: x4 = x5} {q3: x5 = x3}
  {p1': y0 = y1} {p2': y1 = y2} {p3': y2 = y3}
  {q1': y0 = y4} {q2': y4 = y5} {q3': y5 = y3}
  {v0: x0 = y0} {v1: x1 = y1} {v2: x2 = y2}
  {v3: x3 = y3} {v4: x4 = y4} {v5: x5 = y5}
  (H0: (p1 • p2) • p3 = q1 • (q2 • q3))
  (H1: (p1' • p2') • p3' = q1' • (q2' • q3'))
  (S1: v0 • p1' = p1 • v1) (S2: v1 • p2' = p2 • v2) (S3: v2 • p3' = p3 • v3)
  (T1: v0 • q1' = q1 • v4) (T2: v4 • q2' = q2 • v5) (T3: v5 • q3' = q3 • v3):
  Prop :=
  square_cube
    (square_compose (square_compose S1 S2) S3)
    (square_compose T1 (square_compose T2 T3)) H1 H0.

(** A filler for every abstract hexagonal prism is equivalent to GUIP.
    For the converse, make all edges and side faces reflexive and take
    [H1] to be reflexivity. The prism equation forces the arbitrary
    2-loop [H0] to be reflexivity. *)
Theorem hexagonal_prism_iff_guip:
  (forall (X: Type)
    (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5: X)
    (p1: x0 = x1) (p2: x1 = x2) (p3: x2 = x3)
    (q1: x0 = x4) (q2: x4 = x5) (q3: x5 = x3)
    (p1': y0 = y1) (p2': y1 = y2) (p3': y2 = y3)
    (q1': y0 = y4) (q2': y4 = y5) (q3': y5 = y3)
    (v0: x0 = y0) (v1: x1 = y1) (v2: x2 = y2)
    (v3: x3 = y3) (v4: x4 = y4) (v5: x5 = y5)
    (H0: (p1 • p2) • p3 = q1 • (q2 • q3))
    (H1: (p1' • p2') • p3' = q1' • (q2' • q3'))
    (S1: v0 • p1' = p1 • v1) (S2: v1 • p2' = p2 • v2)
    (S3: v2 • p3' = p3 • v3)
    (T1: v0 • q1' = q1 • v4) (T2: v4 • q2' = q2 • v5)
    (T3: v5 • q3' = q3 • v3),
    @hexagonal_prism_coherence X x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5
      p1 p2 p3 q1 q2 q3 p1' p2' p3' q1' q2' q3'
      v0 v1 v2 v3 v4 v5 H0 H1 S1 S2 S3 T1 T2 T3) <->
  (forall (X: Type) (x y: X) (h g: x = y) (p q: h = g), p = q).
Proof.
  split.
  - intros prism X x y h g p q.
    destruct q, h.
    pose proof (prism X x x x x x x x x x x x x
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      p eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as H.
    change (eq_refl • f_equal (fun e => e) p = eq_refl) in H.
    rewrite eq_trans_refl_l, f_equal_id in H.
    now exact H.
  - intros guip *.
    now apply guip.
Qed.

(** A family of [hexagonal_coherence] proofs and a path [e] determine
    the two hexagonal faces [H a, H b] of a prism. Its six side faces are
    constructed with [square_coherence_fill], alternating between mapped
    edges and connecting edges. Vertical edges retain both path actions
    through the vertex maps. Paste the three squares along each route,
    then compare the two boundary pastings. *)
Definition hexagonal_prism_coherence_nat {A A1 A2 A3 B: Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (x0 x1: A -> A1) (x2 x3: A -> A2) (x4 x5: A -> A3)
  (p1: forall a, x0 a = x1 a) (p2: forall a, x2 a = x3 a)
  (p3: forall a, x4 a = x5 a)
  (h1: forall a, f1 (x1 a) = f2 (x2 a))
  (h2: forall a, f1 (x0 a) = f3 (x4 a))
  (h3: forall a, f3 (x5 a) = f2 (x3 a))
  (H: forall a, hexagonal_coherence f1 f2 f3
    (p1 a) (p2 a) (p3 a) (h1 a) (h2 a) (h3 a))
  {a b: A} (e: a = b): Prop :=
  let S1 := square_coherence_fill x0 x1 f1 f1 (fun a => f_equal f1 (p1 a)) e in
  let S2 := square_coherence_fill x1 x2 f1 f2 h1 e in
  let S3 := square_coherence_fill x2 x3 f2 f2 (fun a => f_equal f2 (p2 a)) e in
  let T1 := square_coherence_fill x0 x4 f1 f3 h2 e in
  let T2 := square_coherence_fill x4 x5 f3 f3 (fun a => f_equal f3 (p3 a)) e in
  let T3 := square_coherence_fill x5 x3 f3 f2 h3 e in
  hexagonal_prism_coherence (H a) (H b) S1 S2 S3 T1 T2 T3.

(** A homotopy between composites determines the six vertical edges of
    a prism over a hexagon. The hexagonal faces are the images under the
    two composites. The square faces are canonical naturality fillers of
    the homotopy along each edge, reversed for square pasting. *)
Definition hexagonal_prism_coherence_map {A1 A2 A3 B U V C: Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (u: B -> U) (v: B -> V) (f: U -> C) (g: V -> C)
  (K: forall b, f (u b) = g (v b))
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  (p1: x0 = x1) (p2: x2 = x3) (p3: x4 = x5)
  (h1: f1 x1 = f2 x2) (h2: f1 x0 = f3 x4) (h3: f3 x5 = f2 x3)
  (H: hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3): Prop :=
  let S1 := square_coherence_fill u v f g K (f_equal f1 p1) in
  let S2 := square_coherence_fill u v f g K h1 in
  let S3 := square_coherence_fill u v f g K (f_equal f2 p2) in
  let T1 := square_coherence_fill u v f g K h2 in
  let T2 := square_coherence_fill u v f g K (f_equal f3 p3) in
  let T3 := square_coherence_fill u v f g K h3 in
  hexagonal_prism_coherence
    (hexagon_map f (hexagon_map u H)) (hexagon_map g (hexagon_map v H))
    (eq_sym S1) (eq_sym S2) (eq_sym S3) (eq_sym T1) (eq_sym T2) (eq_sym T3).

(** Naturality of a family of hexagon proofs along a path. The side faces
    are the canonical naturality squares of its six edge homotopies. *)
Lemma hexagonal_prism_coherence_nat_fill {A A1 A2 A3 B: Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (x0 x1: A -> A1) (x2 x3: A -> A2) (x4 x5: A -> A3)
  (p1: forall a, x0 a = x1 a) (p2: forall a, x2 a = x3 a)
  (p3: forall a, x4 a = x5 a)
  (h1: forall a, f1 (x1 a) = f2 (x2 a))
  (h2: forall a, f1 (x0 a) = f3 (x4 a))
  (h3: forall a, f3 (x5 a) = f2 (x3 a))
  (H: forall a, hexagonal_coherence f1 f2 f3
    (p1 a) (p2 a) (p3 a) (h1 a) (h2 a) (h3 a))
  {a b: A} (e: a = b):
  hexagonal_prism_coherence_nat f1 f2 f3 x0 x1 x2 x3 x4 x5
    p1 p2 p3 h1 h2 h3 H e.
Proof.
  destruct e.
  unfold hexagonal_prism_coherence_nat, hexagonal_prism_coherence, square_cube.
  cbn.
  (* Expose the hexagon at the remaining endpoint. *)
  generalize (H a).
  unfold hexagonal_coherence.
  generalize (f_equal f1 (p1 a)), (h1 a), (f_equal f2 (p2 a)),
    (h2 a), (f_equal f3 (p3 a)), (h3 a).
  generalize (f1 (x0 a)), (f1 (x1 a)), (f2 (x2 a)),
    (f2 (x3 a)), (f3 (x4 a)), (f3 (x5 a)).
  intros y0 y1 y2 y3 y4 y5 r1 r2 r3 s1 s2 s3 h.
  destruct r2, r3, s2, s3, s1.
  cbn in h.
  subst r1.
  now reflexivity.
Defined.

(** Naturality of a comparison homotopy with respect to a hexagon. *)
Lemma hexagonal_prism_coherence_map_fill {A1 A2 A3 B U V C: Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (u: B -> U) (v: B -> V) (f: U -> C) (g: V -> C)
  (K: forall b, f (u b) = g (v b))
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  (p1: x0 = x1) (p2: x2 = x3) (p3: x4 = x5)
  (h1: f1 x1 = f2 x2) (h2: f1 x0 = f3 x4) (h3: f3 x5 = f2 x3)
  (H: hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3):
  hexagonal_prism_coherence_map f1 f2 f3 u v f g K p1 p2 p3 h1 h2 h3 H.
Proof.
  unfold hexagonal_prism_coherence_map, hexagonal_prism_coherence, square_cube.
  generalize H. unfold hexagonal_coherence.
  generalize (f_equal f1 p1), h1, (f_equal f2 p2), h2, (f_equal f3 p3), h3.
  generalize (f1 x0), (f1 x1), (f2 x2), (f2 x3), (f3 x4), (f3 x5).
  intros y0 y1 y2 y3 y4 y5 r1 r2 r3 s1 s2 s3 h.
  destruct r2, r3, s2, s3, s1.
  cbn in h. subst r1.
  cbn.
  generalize (K y0).
  generalize (g (v y0)).
  intros z k.
  now destruct k.
Defined.

(** Canonical map prism in the whole-route presentation. The two square
    faces are naturality along the complete routes of the hexagon. *)
Definition hexagonal_prism_map_route_fill {A1 A2 A3 B U V C: Type}
  {f1: A1 -> B} {f2: A2 -> B} {f3: A3 -> B}
  (u: B -> U) (v: B -> V) (f: U -> C) (g: V -> C)
  (K: forall b, f (u b) = g (v b))
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  {p1: x0 = x1} {p2: x2 = x3} {p3: x4 = x5}
  {h1: f1 x1 = f2 x2} {h2: f1 x0 = f3 x4} {h3: f3 x5 = f2 x3}
  (H: hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3) :=
  square_coherence_cube u v f g K H.

(** Canonical source prism in the whole-route presentation. Its square
    faces are naturality of the two complete route families. *)
Definition hexagonal_prism_nat_route_fill {A A1 A2 A3 B: Type}
  {f1: A1 -> B} {f2: A2 -> B} {f3: A3 -> B}
  {x0 x1: A -> A1} {x2 x3: A -> A2} {x4 x5: A -> A3}
  {p1: forall a, x0 a = x1 a} {p2: forall a, x2 a = x3 a}
  {p3: forall a, x4 a = x5 a}
  {h1: forall a, f1 (x1 a) = f2 (x2 a)}
  {h2: forall a, f1 (x0 a) = f3 (x4 a)}
  {h3: forall a, f3 (x5 a) = f2 (x3 a)}
  (H: forall a, hexagonal_coherence f1 f2 f3
    (p1 a) (p2 a) (p3 a) (h1 a) (h2 a) (h3 a))
  {a b: A} (e: a = b) :=
  square_coherence_family_cube x0 x3 f1 f2
    (fun a => (f_equal f1 (p1 a) • h1 a) • f_equal f2 (p2 a))
    (fun a => h2 a • (f_equal f3 (p3 a) • h3 a)) H e.
