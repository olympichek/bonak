Set Warnings "-notation-overridden".

From Bonak.Lib Require Import SigT Notation RewLemmas Coh2Shapes.
From Bonak.SSGpd Require Import Pasting Coh3Shapes Lemmas.
From Bonak.SS2Gpd Require Import Pasting SigmaPasting.

From Bonak.SS2Gpd.Lemmas Require Import Coh3Frame.

Set Keyed Unification.

(** Rewrite a compose node once both children have mapped-square factories. *)
Local Ltac normalize_parent_compose_factory map paint source_paint map_paint
  higher_paint source_higher_paint map_higher :=
  match goal with
  | |- context[square_compose_map_coherence_dep map _ _ _ ?H0 ?K0
      ?aa ?bb ?cc ?dd ?pp ?qq ?rr ?CH ?CK] =>
    let ChildH := eval cbv beta iota zeta
      delta [layer_map_square_factory compose_map_parent_factory] in CH in
    let ChildK := eval cbv beta iota zeta
      delta [layer_map_square_factory compose_map_parent_factory] in CK in
    lazymatch constr: (pair ChildH ChildK) with
    | pair (f_equal _ (path_map2 _ ?Ep2 ?Ec2) •
         (sigT_square_map_dep_normalize map paint source_paint
            higher_paint source_higher_paint map_paint map_higher
            ?BH2 ?FH2 ?Na2 ?Nc2 ?Np2 ?Nq2 ?Da2 ?Dc2 ?Dp2 ?Dq2 ?DH2 •
          eq_sym (path_map2 _ ?Ea2 ?Eq2)))
      (f_equal _ (path_map2 _ ?Ep3 ?Ec3) •
         (sigT_square_map_dep_normalize map paint source_paint
            higher_paint source_higher_paint map_paint map_higher
            ?BH3 ?FH3 ?Na3 ?Nc3 ?Np3 ?Nq3 ?Da3 ?Dc3 ?Dp3 ?Dq3 ?DH3 •
          eq_sym (path_map2 _ ?Ea3 ?Eq3))) =>
      let TH2 := type of FH2 in
      let TH2 := eval cbv beta iota zeta in TH2 in
      let TH3 := type of FH3 in
      let TH3 := eval cbv beta iota zeta in TH3 in
      lazymatch TH2 with
      | @eq _ (@eq_rect _ _ _ (?Hp2 ⊙ sigT_map_eq map_paint ?Hc2) _ _)
          (?Ha2 ⊙ ?Hq2) =>
        lazymatch TH3 with
        | @eq _ (@eq_rect _ _ _ (?Hp3 ⊙ sigT_map_eq map_paint ?Hc3) _ _)
            (?Ha3 ⊙ ?Hq3) =>
          let N := constr: (sigT_square_compose_map_pair_parent_factory
            map paint source_paint map_paint higher_paint source_higher_paint
            map_higher H0 K0 Ha2 Ha3 Hc2 Hc3 Hp2 Hq2 Hq3
            FH2 FH3 Na2 Na3 Nc2 Nc3 Np2 Nq2 Nq3
            Da2 Da3 Dc2 Dc3 Dp2 Dq2 Dq3 DH2 DH3
            aa bb cc dd pp qq rr Ea2 Ea3 Ec2 Ec3 Ep2 Eq2 Eq3) in
          rewrite N
        end
      end
    end
  end.

Section DependentPerm4.

Context
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
  {P: permutahedral_coherence u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
    zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq pV0 pV1 pV2 pV3 pV4 pV5
    K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA}
  {U: forall u, PU u -> S1 (uf0 u)} {F0: forall t, PT t -> S0 (rf0 t)}
  {FA: forall u, PU u -> PT (fA u)} {FB: forall u, PU u -> PT (fB u)}
  {FC: forall u, PU u -> PT (fC u)}
  {Fq: forall x, S1 x -> S0 (rfq x)} {Fs: forall x, S1 x -> S0 (rfs x)}
  {Fr: forall x, S1 x -> S0 (rfr x)}
  {Rr: forall z, S2 z -> S1 (rur z)} {Rs: forall z, S2 z -> S1 (rus z)}
  {Rq1: forall z, S2 z -> S1 (ruq1 z)} {Rr1: forall z, S2 z -> S1 (rur1 z)}
  {Hgq: forall u a, rew [S0] gq u in Fq (uf0 u) (U u a) = F0 (fA u) (FA u a)}
  {Hgs: forall u a, rew [S0] gs u in Fs (uf0 u) (U u a) = F0 (fB u) (FB u a)}
  {Hgr: forall u a, rew [S0] gr u in Fr (uf0 u) (U u a) = F0 (fC u) (FC u a)}
  {HKA2: forall z a, rew [S0] KA2 z in Fq (rus z) (Rs z a) = Fs (ruq1 z) (Rq1 z a)}
  {HKA4: forall z a, rew [S0] KA4 z in Fq (rur z) (Rr z a) = Fr (ruq1 z) (Rq1 z a)}
  {HKA6: forall z a, rew [S0] KA6 z in Fr (rus z) (Rs z a) = Fs (rur1 z) (Rr1 z a)}
  {a0: PU u0} {a1: PU u1} {a2: PU u2} {a3: PU u3} {a4: PU u4} {a5: PU u5}
  {aS1: S2 zs1} {aS2: S2 zs2} {aR1: S2 zr1} {aR2: S2 zr2}
  {aQ1: S2 zq1} {aQ2: S2 zq2}
  {heU1: rew [PU] eU1 in a0 = a1} {heU2: rew [PU] eU2 in a2 = a3}
  {heU3: rew [PU] eU3 in a4 = a5}
  {he2: rew [PT] e2 in FA u1 a1 = FB u2 a2}
  {he4: rew [PT] e4 in FA u0 a0 = FC u4 a4}
  {he6: rew [PT] e6 in FC u5 a5 = FB u3 a3}
  {hpIs: rew [S2] pIs in aS1 = aS2} {hpIr: rew [S2] pIr in aR1 = aR2}
  {hpIq: rew [S2] pIq in aQ1 = aQ2}
  {hpV0: rew [S1] pV0 in Rr zs2 aS2 = U u0 a0}
  {hpV1: rew [S1] pV1 in Rs zr2 aR2 = U u1 a1}
  {hpV2: rew [S1] pV2 in Rq1 zr2 aR2 = U u2 a2}
  {hpV3: rew [S1] pV3 in Rr1 zq2 aQ2 = U u3 a3}
  {hpV4: rew [S1] pV4 in Rq1 zs2 aS2 = U u4 a4}
  {hpV5: rew [S1] pV5 in Rs zq2 aQ2 = U u5 a5}
  {HK1: rew [S1] K1 in Rr zs1 aS1 = Rs zr1 aR1}
  {HK3: rew [S1] K3 in Rq1 zr1 aR1 = Rr1 zq1 aQ1}
  {HK5: rew [S1] K5 in Rq1 zs1 aS1 = Rs zq1 aQ1}
  {DHH1: hexagonal_coherence_dep Rr U Rs HH1 hpIs heU1 hpIr hpV0 HK1 hpV1}
  {DHH3: hexagonal_coherence_dep Rq1 U Rr1 HH3 hpIr heU2 hpIq hpV2 HK3 hpV3}
  {DHH5: hexagonal_coherence_dep Rq1 U Rs HH5 hpIs heU3 hpIq hpV4 HK5 hpV5}
  {Dκ: hexagonal_coherence_dep FA FB FC κ heU1 heU2 heU3 he2 he4 he6}
  {DHH2: hexagonal_coherence_dep Fq F0 Fs HH2 hpV1 he2 hpV2
    (Hgq u1 a1) (HKA2 zr2 aR2) (Hgs u2 a2)}
  {DHH4: hexagonal_coherence_dep Fq F0 Fr HH4 hpV0 he4 hpV4
    (Hgq u0 a0) (HKA4 zs2 aS2) (Hgr u4 a4)}
  {DHH6: hexagonal_coherence_dep Fr F0 Fs HH6 hpV5 he6 hpV3
    (Hgr u5 a5) (HKA6 zq2 aQ2) (Hgs u3 a3)}
  {DHHA: hexagonal_coherence_dep Fq Fs Fr HHA HK1 HK3 HK5
    (HKA2 zr1 aR1) (HKA4 zs1 aS1) (HKA6 zq1 aQ1)}
  (DP: permutahedral_coherence_dep P U F0 FA FB FC Fq Fs Fr Rr Rs Rq1 Rr1 Hgq Hgs Hgr HKA2
    HKA4 HKA6 heU1 heU2 heU3 he2 he4 he6 hpIs hpIr hpIq hpV0 hpV1 hpV2 hpV3 hpV4 hpV5 HK1
    HK3 HK5 DHH1 DHH3 DHH5 Dκ DHH2 DHH4 DHH6 DHHA).

Let tuf0 := (fun z: {x: TU &T PU x} => (uf0 z.1; U z.1 z.2)).

Let trf0 := (fun z: {x: T &T PT x} => (rf0 z.1; F0 z.1 z.2)).

Let tfA := (fun z: {x: TU &T PU x} => (fA z.1; FA z.1 z.2)).

Let tfB := (fun z: {x: TU &T PU x} => (fB z.1; FB z.1 z.2)).

Let tfC := (fun z: {x: TU &T PU x} => (fC z.1; FC z.1 z.2)).

Let trfq := (fun z: {x: X1 &T S1 x} => (rfq z.1; Fq z.1 z.2)).

Let trfs := (fun z: {x: X1 &T S1 x} => (rfs z.1; Fs z.1 z.2)).

Let trfr := (fun z: {x: X1 &T S1 x} => (rfr z.1; Fr z.1 z.2)).

Let trur := (fun z: {x: X2 &T S2 x} => (rur z.1; Rr z.1 z.2)).

Let trus := (fun z: {x: X2 &T S2 x} => (rus z.1; Rs z.1 z.2)).

Let truq1 := (fun z: {x: X2 &T S2 x} => (ruq1 z.1; Rq1 z.1 z.2)).

Let trur1 := (fun z: {x: X2 &T S2 x} => (rur1 z.1; Rr1 z.1 z.2)).

Let tgq := fun z => (= gq z.1; Hgq z.1 z.2).

Let tgs := fun z => (= gs z.1; Hgs z.1 z.2).

Let tgr := fun z => (= gr z.1; Hgr z.1 z.2).

Let tKA2 := fun z => (= KA2 z.1; HKA2 z.1 z.2).

Let tKA4 := fun z => (= KA4 z.1; HKA4 z.1 z.2).

Let tKA6 := fun z => (= KA6 z.1; HKA6 z.1 z.2).

Let tHH1 := eq_existT_curried_hex rur Rr rus Rs uf0 U HH1 DHH1.

Let tHH3 := eq_existT_curried_hex ruq1 Rq1 rur1 Rr1 uf0 U HH3 DHH3.

Let tHH5 := eq_existT_curried_hex ruq1 Rq1 rus Rs uf0 U HH5 DHH5.

Let tκ := eq_existT_curried_hex fA FA fC FC fB FB κ Dκ.

Let tHH2 := eq_existT_curried_hex rfq Fq rfs Fs rf0 F0 HH2 DHH2.

Let tHH4 := eq_existT_curried_hex rfq Fq rfr Fr rf0 F0 HH4 DHH4.

Let tHH6 := eq_existT_curried_hex rfr Fr rfs Fs rf0 F0 HH6 DHH6.

Let tHHA := eq_existT_curried_hex rfq Fq rfr Fr rfs Fs HHA DHHA.

Let TP := eq_existT_curried_perm4 P U F0 FA FB FC Fq Fs Fr Rr Rs Rq1 Rr1 Hgq Hgs Hgr HKA2
  HKA4 HKA6 heU1 heU2 heU3 he2 he4 he6 hpIs hpIr hpIq hpV0 hpV1 hpV2 hpV3 hpV4 hpV5 HK1
  HK3 HK5 DHH1 DHH3 DHH5 Dκ DHH2 DHH4 DHH6 DHHA DP.

Context
  {RS2: {x: X2 &T S2 x} -> Type}
  {RS1: {x: X1 &T S1 x} -> Type}
  {RS0: {x: X0 &T S0 x} -> Type}
  {RPU: {x: TU &T PU x} -> Type}
  {RPT: {x: T &T PT x} -> Type}.

Context
  (dU: forall u, RPU u -> RS1 (tuf0 u)) (dF0: forall t, RPT t -> RS0 (trf0 t))
  (dFA: forall u, RPU u -> RPT (tfA u)) (dFB: forall u, RPU u -> RPT (tfB u))
  (dFC: forall u, RPU u -> RPT (tfC u))
  (dFq: forall x, RS1 x -> RS0 (trfq x)) (dFs: forall x, RS1 x -> RS0 (trfs x))
  (dFr: forall x, RS1 x -> RS0 (trfr x))
  (dRr: forall z, RS2 z -> RS1 (trur z)) (dRs: forall z, RS2 z -> RS1 (trus z))
  (dRq1: forall z, RS2 z -> RS1 (truq1 z)) (dRr1: forall z, RS2 z -> RS1 (trur1 z))
  (dHgq: forall u a, rew [RS0] tgq u in dFq (tuf0 u) (dU u a) = dF0 (tfA u) (dFA u a))
  (dHgs: forall u a, rew [RS0] tgs u in dFs (tuf0 u) (dU u a) = dF0 (tfB u) (dFB u a))
  (dHgr: forall u a, rew [RS0] tgr u in dFr (tuf0 u) (dU u a) = dF0 (tfC u) (dFC u a))
  (dHKA2: forall z a, rew [RS0] tKA2 z in dFq (trus z) (dRs z a) = dFs (truq1 z) (dRq1 z a))
  (dHKA4: forall z a, rew [RS0] tKA4 z in dFq (trur z) (dRr z a) = dFr (truq1 z) (dRq1 z a))
  (dHKA6: forall z a, rew [RS0] tKA6 z in dFr (trus z) (dRs z a) = dFs (trur1 z) (dRr1 z a))
  {da0: RPU (u0; a0)} {da1: RPU (u1; a1)} {da2: RPU (u2; a2)} {da3: RPU (u3; a3)}
  {da4: RPU (u4; a4)} {da5: RPU (u5; a5)}
  {daS1: RS2 (zs1; aS1)} {daS2: RS2 (zs2; aS2)} {daR1: RS2 (zr1; aR1)}
  {daR2: RS2 (zr2; aR2)}
  {daQ1: RS2 (zq1; aQ1)} {daQ2: RS2 (zq2; aQ2)}
  (dheU1: rew [RPU] (= eU1; heU1) in da0 = da1)
  (dheU2: rew [RPU] (= eU2; heU2) in da2 = da3)
  (dheU3: rew [RPU] (= eU3; heU3) in da4 = da5)
  (dhe2: rew [RPT] (= e2; he2) in dFA (u1; a1) da1 = dFB (u2; a2) da2)
  (dhe4: rew [RPT] (= e4; he4) in dFA (u0; a0) da0 = dFC (u4; a4) da4)
  (dhe6: rew [RPT] (= e6; he6) in dFC (u5; a5) da5 = dFB (u3; a3) da3)
  (dhpIs: rew [RS2] (= pIs; hpIs) in daS1 = daS2)
  (dhpIr: rew [RS2] (= pIr; hpIr) in daR1 = daR2)
  (dhpIq: rew [RS2] (= pIq; hpIq) in daQ1 = daQ2)
  (dhpV0: rew [RS1] (= pV0; hpV0) in dRr (zs2; aS2) daS2 = dU (u0; a0) da0)
  (dhpV1: rew [RS1] (= pV1; hpV1) in dRs (zr2; aR2) daR2 = dU (u1; a1) da1)
  (dhpV2: rew [RS1] (= pV2; hpV2) in dRq1 (zr2; aR2) daR2 = dU (u2; a2) da2)
  (dhpV3: rew [RS1] (= pV3; hpV3) in dRr1 (zq2; aQ2) daQ2 = dU (u3; a3) da3)
  (dhpV4: rew [RS1] (= pV4; hpV4) in dRq1 (zs2; aS2) daS2 = dU (u4; a4) da4)
  (dhpV5: rew [RS1] (= pV5; hpV5) in dRs (zq2; aQ2) daQ2 = dU (u5; a5) da5)
  (dHK1: rew [RS1] (= K1; HK1) in dRr (zs1; aS1) daS1 = dRs (zr1; aR1) daR1)
  (dHK3: rew [RS1] (= K3; HK3) in dRq1 (zr1; aR1) daR1 = dRr1 (zq1; aQ1) daQ1)
  (dHK5: rew [RS1] (= K5; HK5) in dRq1 (zs1; aS1) daS1 = dRs (zq1; aQ1) daQ1)
  (dDHH1: hexagonal_coherence_dep dRr dU dRs tHH1 dhpIs dheU1 dhpIr dhpV0 dHK1 dhpV1)
  (dDHH3: hexagonal_coherence_dep dRq1 dU dRr1 tHH3 dhpIr dheU2 dhpIq dhpV2 dHK3 dhpV3)
  (dDHH5: hexagonal_coherence_dep dRq1 dU dRs tHH5 dhpIs dheU3 dhpIq dhpV4 dHK5 dhpV5)
  (dDκ: hexagonal_coherence_dep dFA dFB dFC tκ dheU1 dheU2 dheU3 dhe2 dhe4 dhe6)
  (dDHH2: hexagonal_coherence_dep dFq dF0 dFs tHH2 dhpV1 dhe2 dhpV2
    (dHgq (u1; a1) da1) (dHKA2 (zr2; aR2) daR2) (dHgs (u2; a2) da2))
  (dDHH4: hexagonal_coherence_dep dFq dF0 dFr tHH4 dhpV0 dhe4 dhpV4
    (dHgq (u0; a0) da0) (dHKA4 (zs2; aS2) daS2) (dHgr (u4; a4) da4))
  (dDHH6: hexagonal_coherence_dep dFr dF0 dFs tHH6 dhpV5 dhe6 dhpV3
    (dHgr (u5; a5) da5) (dHKA6 (zq2; aQ2) daQ2) (dHgs (u3; a3) da3))
  (dDHHA: hexagonal_coherence_dep dFq dFs dFr tHHA dHK1 dHK3 dHK5
    (dHKA2 (zr1; aR1) daR1) (dHKA4 (zs1; aS1) daS1) (dHKA6 (zq1; aQ1) daQ1))
  (DDP: permutahedral_coherence_dep TP dU dF0 dFA dFB dFC dFq dFs dFr dRr dRs dRq1 dRr1
    dHgq dHgs dHgr dHKA2 dHKA4 dHKA6 dheU1 dheU2 dheU3 dhe2 dhe4 dhe6 dhpIs dhpIr dhpIq
    dhpV0 dhpV1 dhpV2 dhpV3 dhpV4 dhpV5 dHK1 dHK3 dHK5 dDHH1 dDHH3 dDHH5 dDκ dDHH2 dDHH4
    dDHH6 dDHHA).

(** Assemble a second dependent painting into the fibers of the first one.
    The higher premise lies over the chosen ordinary sigma permutahedron,
    and the eight paired faces use the corresponding dependent hexagons.
    The lower boundary is inferred from the first coherence witness. *)
Lemma eq_existT_curried_perm4_dep:
  permutahedral_coherence_dep P
    (fun x (uv: {u: PU x &T RPU (x; u)}) => (U x uv.1; dU (x; uv.1) uv.2))
    (fun x (uv: {u: PT x &T RPT (x; u)}) => (F0 x uv.1; dF0 (x; uv.1) uv.2))
    (fun x (uv: {u: PU x &T RPU (x; u)}) => (FA x uv.1; dFA (x; uv.1) uv.2))
    (fun x (uv: {u: PU x &T RPU (x; u)}) => (FB x uv.1; dFB (x; uv.1) uv.2))
    (fun x (uv: {u: PU x &T RPU (x; u)}) => (FC x uv.1; dFC (x; uv.1) uv.2))
    (fun x (uv: {u: S1 x &T RS1 (x; u)}) => (Fq x uv.1; dFq (x; uv.1) uv.2))
    (fun x (uv: {u: S1 x &T RS1 (x; u)}) => (Fs x uv.1; dFs (x; uv.1) uv.2))
    (fun x (uv: {u: S1 x &T RS1 (x; u)}) => (Fr x uv.1; dFr (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) => (Rr x uv.1; dRr (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) => (Rs x uv.1; dRs (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) => (Rq1 x uv.1; dRq1 (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) => (Rr1 x uv.1; dRr1 (x; uv.1) uv.2))
    (fun x (uv: {u: PU x &T RPU (x; u)}) =>
      eq_existT_curried_dep (Q := RS0) (H := gq x) (Hu := Hgq x uv.1)
        (Hv := dHgq (x; uv.1) uv.2))
    (fun x (uv: {u: PU x &T RPU (x; u)}) =>
      eq_existT_curried_dep (Q := RS0) (H := gs x) (Hu := Hgs x uv.1)
        (Hv := dHgs (x; uv.1) uv.2))
    (fun x (uv: {u: PU x &T RPU (x; u)}) =>
      eq_existT_curried_dep (Q := RS0) (H := gr x) (Hu := Hgr x uv.1)
        (Hv := dHgr (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) =>
      eq_existT_curried_dep (Q := RS0) (H := KA2 x) (Hu := HKA2 x uv.1)
        (Hv := dHKA2 (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) =>
      eq_existT_curried_dep (Q := RS0) (H := KA4 x) (Hu := HKA4 x uv.1)
        (Hv := dHKA4 (x; uv.1) uv.2))
    (fun x (uv: {u: S2 x &T RS2 (x; u)}) =>
      eq_existT_curried_dep (Q := RS0) (H := KA6 x) (Hu := HKA6 x uv.1)
        (Hv := dHKA6 (x; uv.1) uv.2))
    (eq_existT_curried_dep (Q := RPU) (H := eU1) (Hu := heU1) (Hv := dheU1))
    (eq_existT_curried_dep (Q := RPU) (H := eU2) (Hu := heU2) (Hv := dheU2))
    (eq_existT_curried_dep (Q := RPU) (H := eU3) (Hu := heU3) (Hv := dheU3))
    (eq_existT_curried_dep (Q := RPT) (H := e2) (Hu := he2) (Hv := dhe2))
    (eq_existT_curried_dep (Q := RPT) (H := e4) (Hu := he4) (Hv := dhe4))
    (eq_existT_curried_dep (Q := RPT) (H := e6) (Hu := he6) (Hv := dhe6))
    (eq_existT_curried_dep (Q := RS2) (H := pIs) (Hu := hpIs) (Hv := dhpIs))
    (eq_existT_curried_dep (Q := RS2) (H := pIr) (Hu := hpIr) (Hv := dhpIr))
    (eq_existT_curried_dep (Q := RS2) (H := pIq) (Hu := hpIq) (Hv := dhpIq))
    (eq_existT_curried_dep (Q := RS1) (H := pV0) (Hu := hpV0) (Hv := dhpV0))
    (eq_existT_curried_dep (Q := RS1) (H := pV1) (Hu := hpV1) (Hv := dhpV1))
    (eq_existT_curried_dep (Q := RS1) (H := pV2) (Hu := hpV2) (Hv := dhpV2))
    (eq_existT_curried_dep (Q := RS1) (H := pV3) (Hu := hpV3) (Hv := dhpV3))
    (eq_existT_curried_dep (Q := RS1) (H := pV4) (Hu := hpV4) (Hv := dhpV4))
    (eq_existT_curried_dep (Q := RS1) (H := pV5) (Hu := hpV5) (Hv := dhpV5))
    (eq_existT_curried_dep (Q := RS1) (H := K1) (Hu := HK1) (Hv := dHK1))
    (eq_existT_curried_dep (Q := RS1) (H := K3) (Hu := HK3) (Hv := dHK3))
    (eq_existT_curried_dep (Q := RS1) (H := K5) (Hu := HK5) (Hv := dHK5))
    (eq_existT_curried_hex_dep rur Rr (fun x u => dRr (x; u)) uf0 U (fun x u => dU (x; u))
      rus Rs (fun x u => dRs (x; u)) pIs hpIs dhpIs pV0 hpV0 dhpV0 eU1 heU1 dheU1 K1 HK1
      dHK1 pIr hpIr dhpIr pV1 hpV1 dhpV1 HH1 DHH1 dDHH1)
    (eq_existT_curried_hex_dep ruq1 Rq1 (fun x u => dRq1 (x; u)) uf0 U
      (fun x u => dU (x; u)) rur1 Rr1 (fun x u => dRr1 (x; u)) pIr hpIr dhpIr pV2 hpV2
      dhpV2 eU2 heU2 dheU2 K3 HK3 dHK3 pIq hpIq dhpIq pV3 hpV3 dhpV3 HH3 DHH3 dDHH3)
    (eq_existT_curried_hex_dep ruq1 Rq1 (fun x u => dRq1 (x; u)) uf0 U
      (fun x u => dU (x; u)) rus Rs (fun x u => dRs (x; u)) pIs hpIs dhpIs pV4 hpV4 dhpV4
      eU3 heU3 dheU3 K5 HK5 dHK5 pIq hpIq dhpIq pV5 hpV5 dhpV5 HH5 DHH5 dDHH5)
    (eq_existT_curried_hex_dep fA FA (fun x u => dFA (x; u)) fB FB (fun x u => dFB (x; u))
      fC FC (fun x u => dFC (x; u)) eU1 heU1 dheU1 e2 he2 dhe2 eU2 heU2 dheU2 e4 he4 dhe4
      eU3 heU3 dheU3 e6 he6 dhe6 κ Dκ dDκ)
    (eq_existT_curried_hex_dep rfq Fq (fun x u => dFq (x; u)) rf0 F0
      (fun x u => dF0 (x; u)) rfs Fs (fun x u => dFs (x; u)) pV1 hpV1 dhpV1 (gq u1)
      (Hgq u1 a1) (dHgq (u1; a1) da1) e2 he2 dhe2 (KA2 zr2) (HKA2 zr2 aR2)
      (dHKA2 (zr2; aR2) daR2) pV2 hpV2 dhpV2 (gs u2) (Hgs u2 a2) (dHgs (u2; a2) da2) HH2
      DHH2 dDHH2)
    (eq_existT_curried_hex_dep rfq Fq (fun x u => dFq (x; u)) rf0 F0
      (fun x u => dF0 (x; u)) rfr Fr (fun x u => dFr (x; u)) pV0 hpV0 dhpV0 (gq u0)
      (Hgq u0 a0) (dHgq (u0; a0) da0) e4 he4 dhe4 (KA4 zs2) (HKA4 zs2 aS2)
      (dHKA4 (zs2; aS2) daS2) pV4 hpV4 dhpV4 (gr u4) (Hgr u4 a4) (dHgr (u4; a4) da4) HH4
      DHH4 dDHH4)
    (eq_existT_curried_hex_dep rfr Fr (fun x u => dFr (x; u)) rf0 F0
      (fun x u => dF0 (x; u)) rfs Fs (fun x u => dFs (x; u)) pV5 hpV5 dhpV5 (gr u5)
      (Hgr u5 a5) (dHgr (u5; a5) da5) e6 he6 dhe6 (KA6 zq2) (HKA6 zq2 aQ2)
      (dHKA6 (zq2; aQ2) daQ2) pV3 hpV3 dhpV3 (gs u3) (Hgs u3 a3) (dHgs (u3; a3) da3) HH6
      DHH6 dDHH6)
    (eq_existT_curried_hex_dep rfq Fq (fun x u => dFq (x; u)) rfs Fs
      (fun x u => dFs (x; u)) rfr Fr (fun x u => dFr (x; u)) K1 HK1 dHK1 (KA2 zr1)
      (HKA2 zr1 aR1) (dHKA2 (zr1; aR1) daR1) K3 HK3 dHK3 (KA4 zs1) (HKA4 zs1 aS1)
      (dHKA4 (zs1; aS1) daS1) K5 HK5 dHK5 (KA6 zq1) (HKA6 zq1 aQ1) (dHKA6 (zq1; aQ1) daQ1)
      HHA DHHA dDHHA).
Proof.
  unfold permutahedral_coherence_dep at 1. cbn zeta.
  rewrite (sigT_layer_square_map_pair_factory uf0 rur rus rfq fA rf0
    U Rr Rs Fq FA F0 gq Hgq eU1 pIs pIr pV0 pV1 K1 HH1
    heU1 hpIs hpIr hpV0 hpV1 HK1 DHH1
    RPU RS2 RS2 RS1 RS0 RPT dU dRr dRs dFq dFA dF0 dHgq
    dheU1 dhpIs dhpIr dhpV0 dhpV1 dHK1 dDHH1).
  rewrite (sigT_layer_square_map_pair_factory uf0 ruq1 rur1 rfs fB rf0
    U Rq1 Rr1 Fs FB F0 gs Hgs eU2 pIr pIq pV2 pV3 K3 HH3
    heU2 hpIr hpIq hpV2 hpV3 HK3 DHH3
    RPU RS2 RS2 RS1 RS0 RPT dU dRq1 dRr1 dFs dFB dF0 dHgs
    dheU2 dhpIr dhpIq dhpV2 dhpV3 dHK3 dDHH3).
  rewrite (sigT_layer_square_map_pair_factory uf0 ruq1 rus rfr fC rf0
    U Rq1 Rs Fr FC F0 gr Hgr eU3 pIs pIq pV4 pV5 K5 HH5
    heU3 hpIs hpIq hpV4 hpV5 HK5 DHH5
    RPU RS2 RS2 RS1 RS0 RPT dU dRq1 dRs dFr dFC dF0 dHgr
    dheU3 dhpIs dhpIq dhpV4 dhpV5 dHK5 dDHH5).
  rewrite (sigT_layer_square_nat_pair_factory rus ruq1 rfq rfs rf0
    Rs Rq1 Fq Fs F0 KA2 HKA2 pIr pV1 pV2 e2 (gq u1) (gs u2) HH2
    hpIr hpV1 hpV2 he2 (Hgq u1 a1) (Hgs u2 a2) DHH2
    RS2 RS1 RS1 RPT RS0 dRs dRq1 dFq dFs dF0 dHKA2
    dhpIr dhpV1 dhpV2 dhe2 (dHgq (u1; a1) da1) (dHgs (u2; a2) da2) dDHH2).
  rewrite (sigT_layer_square_nat_pair_factory rur ruq1 rfq rfr rf0
    Rr Rq1 Fq Fr F0 KA4 HKA4 pIs pV0 pV4 e4 (gq u0) (gr u4) HH4
    hpIs hpV0 hpV4 he4 (Hgq u0 a0) (Hgr u4 a4) DHH4
    RS2 RS1 RS1 RPT RS0 dRr dRq1 dFq dFr dF0 dHKA4
    dhpIs dhpV0 dhpV4 dhe4 (dHgq (u0; a0) da0) (dHgr (u4; a4) da4) dDHH4).
  rewrite (sigT_layer_square_nat_pair_factory rus rur1 rfr rfs rf0
    Rs Rr1 Fr Fs F0 KA6 HKA6 pIq pV5 pV3 e6 (gr u5) (gs u3) HH6
    hpIq hpV5 hpV3 he6 (Hgr u5 a5) (Hgs u3 a3) DHH6
    RS2 RS1 RS1 RPT RS0 dRs dRr1 dFr dFs dF0 dHKA6
    dhpIq dhpV5 dhpV3 dhe6 (dHgr (u5; a5) da5) (dHgs (u3; a3) da3) dDHH6).
  pose (Ea := sigT_hex_pair_left_normalize
    (R1 := fun x u => RS1 (x; u)) (R3 := fun x u => RS1 (x; u)) (R' := fun x u => RS0 (x; u))
    rfq Fq (fun x u => dFq (x; u)) rfs Fs (fun x u => dFs (x; u))
    K1 HK1 dHK1 (KA2 zr1) (HKA2 zr1 aR1) (dHKA2 (zr1; aR1) daR1) K3 HK3 dHK3).
  pose (Ea' := sigT_hex_pair_right_normalize
    (R1 := fun x u => RS1 (x; u)) (R2 := fun x u => RS1 (x; u)) (R3 := fun x u => RS1 (x; u))
    (R' := fun x u => RS0 (x; u))
    rfq Fq (fun x u => dFq (x; u)) rfs Fs (fun x u => dFs (x; u)) rfr Fr (fun x u => dFr (x; u))
    (KA4 zs1) (HKA4 zs1 aS1) (dHKA4 (zs1; aS1) daS1) K5 HK5 dHK5
    (KA6 zq1) (HKA6 zq1 aQ1) (dHKA6 (zq1; aQ1) daQ1)).
  pose (Eb := sigT_hex_map_pair_left_normalize
    (R1 := fun x u => RPU (x; u)) (R3 := fun x u => RPU (x; u)) (R' := fun x u => RPT (x; u))
    fA FA (fun x u => dFA (x; u)) fB FB (fun x u => dFB (x; u))
    eU1 heU1 dheU1 e2 he2 dhe2 eU2 heU2 dheU2 RS0 rf0 F0 (fun z => dF0 (z.1; z.2))).
  pose (Eb' := sigT_hex_map_pair_right_normalize
    (R1 := fun x u => RPU (x; u)) (R2 := fun x u => RPU (x; u)) (R3 := fun x u => RPU (x; u))
    (R' := fun x u => RPT (x; u))
    fA FA (fun x u => dFA (x; u)) fB FB (fun x u => dFB (x; u)) fC FC (fun x u => dFC (x; u))
    e4 he4 dhe4 eU3 heU3 dheU3 e6 he6 dhe6 RS0 rf0 F0 (fun z => dF0 (z.1; z.2))).
  pose (EpS := sigT_dep_path_map_direct rur Rr RS2 RS1 dRr dhpIs).
  pose (EpSV := sigT_pair_path_paste RS1
    (f_equal_eq_existT_curried rur Rr pIs hpIs) eq_refl
    (sigT_map_eq dRr dhpIs) dhpV0 EpS eq_refl).
  pose (EpF := sigT_pair_path_map rfq Fq RS1 RS0 dFq
    (sigT_path_paste (f_equal_eq_existT_curried rur Rr pIs hpIs) eq_refl)
    (sigT_map_eq dRr dhpIs ⊙ dhpV0) EpSV).
  pose (Ep := sigT_pair_path_paste RS0
    (sigT_path_map rfq Fq (sigT_path_paste (f_equal_eq_existT_curried rur Rr pIs hpIs) eq_refl))
    eq_refl (sigT_map_eq dFq (sigT_map_eq dRr dhpIs ⊙ dhpV0))
    (dHgq (u0; a0) da0) EpF eq_refl).
  pose (EqS := sigT_dep_path_map_direct rur1 Rr1 RS2 RS1 dRr1 dhpIq).
  pose (EqSV := sigT_pair_path_paste RS1
    (f_equal_eq_existT_curried rur1 Rr1 pIq hpIq) eq_refl
    (sigT_map_eq dRr1 dhpIq) dhpV3 EqS eq_refl).
  pose (EqF := sigT_pair_path_map rfs Fs RS1 RS0 dFs
    (sigT_path_paste (f_equal_eq_existT_curried rur1 Rr1 pIq hpIq) eq_refl)
    (sigT_map_eq dRr1 dhpIq ⊙ dhpV3) EqSV).
  pose (Eq := sigT_pair_path_paste RS0
    (sigT_path_map rfs Fs (sigT_path_paste (f_equal_eq_existT_curried rur1 Rr1 pIq hpIq) eq_refl))
    eq_refl (sigT_map_eq dFs (sigT_map_eq dRr1 dhpIq ⊙ dhpV3))
    (dHgs (u3; a3) da3) EqF eq_refl).
  do 4 normalize_parent_compose_factory rf0 S0 PT F0 RS0 RPT dF0.
  cbv beta iota zeta delta [compose_map_parent_factory].
  rewrite 2 (sigT_square_map_dep_paint_computation rf0 S0 PT RS0 RPT F0 dF0).
  pose proof DDP as D.
  unfold permutahedral_coherence_dep in D.
  cbn zeta in D.
  unfold TP, eq_existT_curried_perm4 in D.
  cbn zeta in D.
  apply (square_cube_coherence_dep_transport RS0) in D.
  cbn zeta in D.
  do 4 (
    lazymatch type of D with
    | context [@eq_rect ?A ?x ?F ?u ?z
        (@eq_trans _ _ _ _ (path_map2 ?f ?N1 ?N2) ?M)] =>
      rewrite <- (@rew_compose A F x _ z (path_map2 f N1 N2) M u) in D
    end;
    rewrite (square_compose_map_coherence_dep_transport trf0 RS0 RPT dF0) in D).
  apply (sigT_square_cube_dep_normalize S0 RS0) in D.
  pose proof (square_cube_coherence_dep_change_lifts D Ea Ea' Eb Eb' Ep Eq) as Draw.
  cbn zeta in Draw.
  rewrite 2 (sigT_square_dep_paint_computation RS0) in Draw.
  lazymatch goal with
  | |- square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ ?LT _ _ _ =>
    lazymatch type of Draw with
    | square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ ?LD _ _ _ =>
      assert (LeftFaces : LT = LD)
    end
  end.
  { unfold Ea, Eb, Ep, EpF, EpSV, EpS, Eq, EqF, EqSV, EqS.
    unfold sigT_hex_map_pair_left_normalize.
    rewrite 2 sigT_hex_pair_left_normalize_paste.
    unfold paired_map_prefix_left, paired_map_prefix_right.
    cbn beta iota zeta.
    lazymatch goal with
    | |- f_equal _ ?EL • (?M • eq_sym ?ER) = f_equal _ ?ELD • (?MD • eq_sym ?ERD) =>
      assert (LeftCoefficient: EL = ELD) by reflexivity;
      assert (RightCoefficient: ER = ERD) by reflexivity;
      rewrite LeftCoefficient, RightCoefficient
    end.
    now reflexivity. }
  match goal with
  | |- square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ ?GL ?GR ?GB ?GT =>
    let td := type of Draw in
    lazymatch td with
    | square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ ?DL ?DR ?DB ?DT =>
      assert (RightFace: GR = DR)
    end
  end.
  { unfold Ea', Eb', Ep, EpF, EpSV, EpS, Eq, EqF, EqSV, EqS.
    unfold sigT_hex_map_pair_right_normalize.
    rewrite 2 sigT_hex_pair_right_normalize_paste.
    unfold paired_map_prefix_left, paired_map_prefix_right.
    cbn beta iota zeta.
    now reflexivity.
  }
  cbn zeta in Draw.
  lazymatch type of Draw with
  | square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?BottomDraw ?TopDraw =>
    lazymatch goal with
    | |- square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?BottomTarget ?TopTarget =>
      assert (TopCap: TopTarget = TopDraw)
    end
  end.
  { unfold Ea, Ea'.
    unfold eq_existT_curried_hex_dep.
    cbn beta iota zeta.
    now reflexivity. }
  cbn zeta in Draw.
  lazymatch type of Draw with
  | square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?BottomDraw ?TopDraw =>
    lazymatch goal with
    | |- square_cube_coherence_dep _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?BottomTarget ?TopTarget =>
      assert (BottomCap: BottomTarget = BottomDraw)
    end
  end.
  { rewrite (sigT_hex_map_pair_dep_normalize
      (R1 := fun x u => RPU (x; u)) (R2 := fun x u => RPU (x; u)) (R3 := fun x u => RPU (x; u))
      (R' := fun x u => RPT (x; u))
      fA FA (fun x u => dFA (x; u)) fB FB (fun x u => dFB (x; u)) fC FC (fun x u => dFC (x; u))
      eU1 heU1 dheU1 e2 he2 dhe2 eU2 heU2 dheU2 e4 he4 dhe4 eU3 heU3 dheU3
      e6 he6 dhe6 κ Dκ dDκ RS0 rf0 F0 (fun z => dF0 (z.1; z.2))).
    unfold Eb, Eb'. cbn beta iota zeta.
    now reflexivity. }
  rewrite LeftFaces, RightFace, TopCap, BottomCap.
  now exact Draw.
Defined.

End DependentPerm4.
