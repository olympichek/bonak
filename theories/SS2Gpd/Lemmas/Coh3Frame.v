Set Warnings "-notation-overridden".

From Bonak.Lib Require Import SigT Notation RewLemmas Coh2Shapes.
From Bonak.SSGpd Require Import Pasting Coh3Shapes Lemmas.
From Bonak.SS2Gpd Require Import Pasting SigmaPasting.

Set Keyed Unification.

(** Assemble the base and dependent permutahedral coherences into a
    permutahedron of dependent pairs. The eight hexagonal faces use the
    chosen sigma assembly of their base and fiber witnesses. *)

Lemma eq_existT_curried_perm4
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
    (HKA2 zr1 aR1) (HKA4 zs1 aS1) (HKA6 zq1 aQ1))
  (DP: permutahedral_coherence_dep P U F0 FA FB FC Fq Fs Fr Rr Rs Rq1 Rr1 Hgq Hgs Hgr HKA2
    HKA4 HKA6 heU1 heU2 heU3 he2 he4 he6 hpIs hpIr hpIq hpV0 hpV1 hpV2 hpV3 hpV4 hpV5 HK1
    HK3 HK5 DHH1 DHH3 DHH5 Dκ DHH2 DHH4 DHH6 DHHA):
  let tuf0 := (fun z: {x: TU &T PU x} => (uf0 z.1; U z.1 z.2)) in
  let trf0 := (fun z: {x: T &T PT x} => (rf0 z.1; F0 z.1 z.2)) in
  let tfA := (fun z: {x: TU &T PU x} => (fA z.1; FA z.1 z.2)) in
  let tfB := (fun z: {x: TU &T PU x} => (fB z.1; FB z.1 z.2)) in
  let tfC := (fun z: {x: TU &T PU x} => (fC z.1; FC z.1 z.2)) in
  let trfq := (fun z: {x: X1 &T S1 x} => (rfq z.1; Fq z.1 z.2)) in
  let trfs := (fun z: {x: X1 &T S1 x} => (rfs z.1; Fs z.1 z.2)) in
  let trfr := (fun z: {x: X1 &T S1 x} => (rfr z.1; Fr z.1 z.2)) in
  let trur := (fun z: {x: X2 &T S2 x} => (rur z.1; Rr z.1 z.2)) in
  let trus := (fun z: {x: X2 &T S2 x} => (rus z.1; Rs z.1 z.2)) in
  let truq1 := (fun z: {x: X2 &T S2 x} => (ruq1 z.1; Rq1 z.1 z.2)) in
  let trur1 := (fun z: {x: X2 &T S2 x} => (rur1 z.1; Rr1 z.1 z.2)) in
  let tgq := fun z => (= gq z.1; Hgq z.1 z.2) in
  let tgs := fun z => (= gs z.1; Hgs z.1 z.2) in
  let tgr := fun z => (= gr z.1; Hgr z.1 z.2) in
  let tKA2 := fun z => (= KA2 z.1; HKA2 z.1 z.2) in
  let tKA4 := fun z => (= KA4 z.1; HKA4 z.1 z.2) in
  let tKA6 := fun z => (= KA6 z.1; HKA6 z.1 z.2) in
  @permutahedral_coherence _ _ _ _ _ tuf0 trf0 tfA tfB tfC trfq trfs trfr
    tgq tgs tgr trur trus truq1 trur1 tKA2 tKA4 tKA6
    (u0; a0) (u1; a1) (u2; a2) (u3; a3) (u4; a4) (u5; a5)
    (= eU1; heU1) (= eU2; heU2) (= eU3; heU3) (= e2; he2) (= e4; he4) (= e6; he6)
    (zs1; aS1) (zs2; aS2) (zr1; aR1) (zr2; aR2) (zq1; aQ1) (zq2; aQ2)
    (= pIs; hpIs) (= pIr; hpIr) (= pIq; hpIq)
    (= pV0; hpV0) (= pV1; hpV1) (= pV2; hpV2)
    (= pV3; hpV3) (= pV4; hpV4) (= pV5; hpV5)
    (= K1; HK1) (= K3; HK3) (= K5; HK5)
    (eq_existT_curried_hex rur Rr rus Rs uf0 U HH1 DHH1)
    (eq_existT_curried_hex ruq1 Rq1 rur1 Rr1 uf0 U HH3 DHH3)
    (eq_existT_curried_hex ruq1 Rq1 rus Rs uf0 U HH5 DHH5)
    (eq_existT_curried_hex fA FA fC FC fB FB κ Dκ)
    (eq_existT_curried_hex rfq Fq rfs Fs rf0 F0 HH2 DHH2)
    (eq_existT_curried_hex rfq Fq rfr Fr rf0 F0 HH4 DHH4)
    (eq_existT_curried_hex rfr Fr rfs Fs rf0 F0 HH6 DHH6)
    (eq_existT_curried_hex rfq Fq rfr Fr rfs Fs HHA DHHA).

Proof.
  cbn zeta. unfold permutahedral_coherence at 1. cbn zeta.
  pose (trf0 := fun z: {x: T &T PT x} => (rf0 z.1; F0 z.1 z.2)).
  pose proof (sigT_layer_square_nat rus ruq1 rfq rfs rf0 Rs Rq1 Fq Fs F0 KA2 HKA2
    pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 hpIr hpV1 hpV2 he2
    (Hgq u1 a1) (Hgs u2 a2) DHH2) as N2.
  pose proof (sigT_layer_square_nat rur ruq1 rfq rfr rf0 Rr Rq1 Fq Fr F0 KA4 HKA4
    pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 hpIs hpV0 hpV4 he4
    (Hgq u0 a0) (Hgr u4 a4) DHH4) as N4.
  pose proof (sigT_layer_square_nat rus rur1 rfr rfs rf0 Rs Rr1 Fr Fs F0 KA6 HKA6
    pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 hpIq hpV5 hpV3 he6
    (Hgr u5 a5) (Hgs u3 a3) DHH6) as N6.
  pose proof (sigT_layer_square_map uf0 rur rus rfq fA rf0 U Rr Rs Fq FA F0 gq Hgq
    eU1 pIs pIr pV0 pV1 K1 HH1 heU1 hpIs hpIr hpV0 hpV1 HK1 DHH1) as N1.
  pose proof (sigT_layer_square_map uf0 ruq1 rur1 rfs fB rf0 U Rq1 Rr1 Fs FB F0 gs Hgs
    eU2 pIr pIq pV2 pV3 K3 HH3 heU2 hpIr hpIq hpV2 hpV3 HK3 DHH3) as N3.
  pose proof (sigT_layer_square_map uf0 ruq1 rus rfr fC rf0 U Rq1 Rs Fr FC F0 gr Hgr
    eU3 pIs pIq pV4 pV5 K5 HH5 heU3 hpIs hpIq hpV4 hpV5 HK5 DHH5) as N5.

  eassert (N12: square_compose_map trf0 _ _ = _).
  { refine (path_map2 (fun h k => square_compose_map trf0 h k) N1 N2 • _).
    now apply sigT_square_compose_map_normalize. }
  eassert (N56: square_compose_map trf0 _ _ = _).
  { refine (path_map2 (fun h k => square_compose_map trf0 h k) N5 N6 • _).
    now apply sigT_square_compose_map_normalize. }
  eassert (Nleft: square_compose_map trf0 _ _ = _).
  { refine (path_map2 (fun h k => square_compose_map trf0 h k) N12 N3 • _).
    now apply sigT_square_compose_map_normalize. }
  eassert (Nright: square_compose_map trf0 _ _ = _).
  { refine (path_map2 (fun h k => square_compose_map trf0 h k) N4 N56 • _).
    now apply sigT_square_compose_map_normalize. }
  eassert (Ncap: f_equal (fun e => f_equal trf0 e)
    (eq_existT_curried_hex fA FA fC FC fB FB κ Dκ) = _).
  { unfold eq_existT_curried_hex.
    now apply sigT_eq_map_normalized. }
  refine (square_cube_transport Nleft Nright Ncap eq_refl _).
  eapply (sigT_square_cube_normalize S0 _ _ _ _ P).
  now exact DP.
Defined.
