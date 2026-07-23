Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation.

Set Keyed Unification.

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
  rewrite 3 f_equal_eq_existT_curried.
  rewrite 4 eq_trans_eq_existT_curried.
  now exact (eq_existT_curried_eq HH HHu).
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
  rewrite !sigT_map_eq_existT_curried_dep_curried.
  rewrite !(sigT_trans_eq_existT_curried_dep (Q := fun z => R' z.1 z.2)).
  refine (eq_existT_curried_dep_eq (Q := fun z => R' z.1 z.2) HH HHu _).
  unfold eq_existT_curried_hex in HHv.
  cbn [projT1 projT2] in HHv |- *.
  revert HHv.
  generalize (eq_existT_curried_eq HH HHu).
  do 4 lazymatch goal with
  | |- context [ @eq_trans_eq_existT_curried ?A ?P ?x ?y ?z ?u ?v ?w
        ?p ?q ?p' ?q' ] =>
      generalize (@eq_trans_eq_existT_curried A P x y z u v w p q p' q')
  end.
  generalize (f_equal_eq_existT_curried f2 g2 H2' Hu2').
  generalize (f_equal_eq_existT_curried f3 g3 H3 Hu3).
  generalize (f_equal_eq_existT_curried f1 g1 H1 Hu1).
  generalize (= f_equal f1 H1; sigT_map_eq g1 Hu1).
  generalize (= f_equal f3 H3; sigT_map_eq g3 Hu3).
  generalize (= f_equal f2 H2'; sigT_map_eq g2 Hu2').
  generalize (= H2 • f_equal f3 H3; Hu2 ⊙ sigT_map_eq g3 Hu3).
  generalize (= f_equal f2 H2' • H3'; sigT_map_eq g2 Hu2' ⊙ Hu3').
  generalize (= f_equal f1 H1 • (H2 • f_equal f3 H3);
    sigT_map_eq g1 Hu1 ⊙ (Hu2 ⊙ sigT_map_eq g3 Hu3)).
  generalize (= H1' • (f_equal f2 H2' • H3');
    Hu1' ⊙ (sigT_map_eq g2 Hu2' ⊙ Hu3')).
  intros qR qL q23' q23 q2' q3 q1 e e0 e1 e2 e3 e4 e5 e6.
  destruct e, e0, e1, e2, e3, e4, e5.
  intros HHv'; exact HHv'.
Qed.

Lemma rew_cohLayer {T1 T2 T3 X: Type} (P: X -> Type)
  {S2: T2 -> Type} {S3: T3 -> Type}
  (rf0: T1 -> X) {rfF: T2 -> X} {rfG: T3 -> X}
  (F: forall m, S2 m -> P (rfF m))
  (G: forall n, S3 n -> P (rfG n))
  {d1 d2: T1} (E1: d1 = d2)
  {m1 m2: T2} (C2: m1 = m2)
  {n1 n2: T3} (D2: n1 = n2)
  (C1: rfF m2 = rf0 d1) (D1: rfG n2 = rf0 d2)
  (K: rfF m1 = rfG n1)
  (aL: S2 m1) (aR: S3 n1):
  rew [P] K in F m1 aL = G n1 aR ->
  f_equal rfF C2 • (C1 • f_equal rf0 E1) =
  K • (f_equal rfG D2 • D1) ->
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  destruct E1, C2, D2. cbn in *.
  rewrite <- HC.
  rewrite rew_compose.
  rewrite !eq_trans_refl_l in Hpath.
  now rewrite Hpath.
Defined.

Lemma rew_coh2Painting_restr0 {Tp Td: Type} {S: Tp -> Type} (P: Td -> Type)
  (rf0: Tp -> Td) {rfF rfG: Tp -> Td}
  (F: forall m, S m -> P (rfF m))
  (G: forall n, S n -> P (rfG n))
  {d1 d2: Tp} (E1: d1 = d2)
  {m1 m2: Tp} (C2: m1 = m2)
  {n1 n2: Tp} (D2: n1 = n2)
  (C1: rfF m2 = rf0 d1) (D1: rfG n2 = rf0 d2)
  (K: rfF m1 = rfG n1)
  (aL: S m1) (aR: S n1)
  (HK: rew [P] K in F m1 aL = G n1 aR)
  (HH: f_equal rfF C2 • (C1 • f_equal rf0 E1) =
       K • (f_equal rfG D2 • D1))
  (R0: {a: Tp &T P (rf0 a)} -> Type)
  {v0: R0 (d1; rew [P] C1 in F m2 (rew [S] C2 in aL))}
  {v1: R0 (d2; rew [P] D1 in G n2 (rew [S] D2 in aR))}
  (Hv: rew [R0] (= E1; rew_cohLayer P rf0 F G E1 C2 D2 C1 D1 K aL aR HK HH)
    in v0 = v1):
  rew [fun π: rfF m1 = rf0 d2 =>
      rew [P] π in F m1 aL = rew [P] D1 in G n2 (rew [S] D2 in aR)] HH in
  (sigT_map_eq (Q := P) F (eq_refl (x := rew [S] C2 in aL))
   ⊙ ((eq_refl : rew [P] C1 in F m2 (rew [S] C2 in aL)
       = rew [P] C1 in F m2 (rew [S] C2 in aL))
      ⊙ sigT_map_eq (P := fun a => {u: P (rf0 a) &T R0 (a; u)}) (Q := P)
          (f := rf0) (fun a uv => uv.1)
          (eq_existT_curried_dep (Q := R0) (H := E1)
            (Hu := rew_cohLayer P rf0 F G E1 C2 D2 C1 D1 K aL aR HK HH)
            (Hv := Hv)))) =
  HK ⊙ (sigT_map_eq (Q := P) G (eq_refl (x := rew [S] D2 in aR)) ⊙ eq_refl).
Proof.
  rewrite (sigT_map_eq_existT_curried_dep_fst rf0 (fun a u => u) E1
    (rew_cohLayer P rf0 F G E1 C2 D2 C1 D1 K aL aR HK HH) Hv).
  cbn [projT1].
  clear Hv v0 v1 R0.
  destruct E1, C2, D2.
  cbn in HH |- *.
  revert HH. revert HK. revert C1. revert D1.
  generalize (G n1 aR) as gb.
  intros gb D1 C1 HK HH.
  rewrite (sigT_map_eq_id_refl rf0).
  revert HH. revert HK. revert C1. revert D1.
  generalize (rf0 d1) as X.
  intros X D1.
  destruct D1.
  intros C1 HK HH.
  cbn in HH.
  revert HK.
  destruct HH.
  intros HK.
  cbn in HK |- *.
  destruct HK.
  revert C1.
  generalize (rfG n1) as Y.
  intros Y C1.
  destruct C1.
  reflexivity.
Defined.
