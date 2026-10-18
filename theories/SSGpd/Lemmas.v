Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas Lib.Coh2Shapes SSGpd.Pasting SSGpd.Coh3Shapes.

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
  (HH: hexagonal_coherence f1 f3 f2 K1 K3 K2 H2 H1' H3')
  (HHu: hexagonal_coherence_dep g1 g3 g2 HH W1 W3 W2 U2 U1' U3'):
  hexagonal_coherence
    (fun z: {a: A1 &T P1 a} => (f1 z.1; g1 z.1 z.2))
    (fun z: {a: A3 &T P3 a} => (f3 z.1; g3 z.1 z.2))
    (fun z: {a: A2 &T P2 a} => (f2 z.1; g2 z.1 z.2))
    (= K1; W1) (= K3; W3) (= K2; W2) (= H2; U2) (= H1'; U1') (= H3'; U3').
Proof.
  refine (_ • (eq_existT_curried_eq HH HHu • eq_sym _)).
  - now exact (sigT_path_paste
      (sigT_path_paste (f_equal_eq_existT_curried f1 g1 K1 W1) eq_refl)
      (f_equal_eq_existT_curried f3 g3 K3 W3)).
  - now exact (sigT_path_paste eq_refl
      (sigT_path_paste (f_equal_eq_existT_curried f2 g2 K2 W2) eq_refl)).
Defined.

(** Pair the two normalized routes of a hexagonal boundary. *)
Local Lemma path_map2_compose_l_prefix {A B C: Type} (f: A -> B -> C)
  {a a' a'': A} {b b': B} {c: C}
  (p: a = a') (q: a' = a'') (r: b = b') (s: f a'' b' = c):
  path_map2 f p r • (f_equal (fun a => f a b') q • s) =
  path_map2 f (p • q) r • s.
Proof. now destruct p, q, r, s. Defined.

Section PairedHexRoutes.
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
    (h2 x2' u2' v2': (fun z => R' z.1 z.2) (f2 x2'; g2 x2' u2')) = h3 x3 u3 v3).

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
Let PL :=
  (sigT_map_eq (fun a (uv: {u: P1 a &T R1 a u}) => (g1 a uv.1; h1 a uv.1 uv.2))
    (eq_existT_curried_dep (Q := fun z => R1 z.1 z.2) (H := H1) (Hu := Hu1) (Hv := Hv1)) ⊙
    eq_existT_curried_dep (Q := S) (H := H2) (Hu := Hu2) (Hv := Hv2)) ⊙
  sigT_map_eq (fun a (uv: {u: P3 a &T R3 a u}) => (g3 a uv.1; h3 a uv.1 uv.2))
    (eq_existT_curried_dep (Q := fun z => R3 z.1 z.2) (H := H3) (Hu := Hu3) (Hv := Hv3)).
Let PR := eq_existT_curried_dep (Q := S) (H := H1') (Hu := Hu1') (Hv := Hv1') ⊙
  (sigT_map_eq (fun a (uv: {u: P2 a &T R2 a u}) => (g2 a uv.1; h2 a uv.1 uv.2))
      (eq_existT_curried_dep (Q := fun z => R2 z.1 z.2) (H := H2') (Hu := Hu2') (Hv := Hv2')) ⊙
   eq_existT_curried_dep (Q := S) (H := H3') (Hu := Hu3') (Hv := Hv3')).
Lemma sigT_hex_pair_left_normalize:
  PL = eq_existT_curried_dep(Q:=S)
    (H:=(f_equal f1 H1 •H2) •f_equal f3 H3)
    (Hu:=(sigT_map_eq g1 Hu1 ⊙Hu2) ⊙sigT_map_eq g3 Hu3)
    (Hv := rew [fun e: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) => rew [S] e in (h1 x0 u0 v0: S
      (f1 x0; g1 x0 u0)) = h3 x3 u3 v3] NL in
      ((sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙Hv2) ⊙sigT_map_eq (f := T3) (Q := S) V3 Hv3)).
Proof.
  unfold PL.
  pose (E1 := sigT_dep_path_map_direct f1 g1 (fun z => R1 z.1 z.2) S V1 (p := H1) (hp := Hu1) Hv1).
  pose (E3 := sigT_dep_path_map_direct f3 g3 (fun z => R3 z.1 z.2) S V3 (p := H3) (hp := Hu3) Hv3).
  refine (path_map2 (fun h k => h ⊙ k)
    (path_map2 (fun h k => h ⊙ k) E1
      (eq_refl: eq_existT_curried_dep (Q := S) (H := H2) (Hu := Hu2) (Hv := Hv2) = _)) E3 • _).
  refine (f_equal (fun h => h ⊙ _)
    (sigT_dep_path_paste_normalize S N1 eq_refl
      (sigT_map_eq (f := T1) (Q := S) V1 Hv1) Hv2) • _).
  now exact (sigT_dep_path_paste_normalize S
    (sigT_path_paste N1 (eq_refl: (= H2; Hu2) = (= H2; Hu2))) N3
    (sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙ Hv2)
    (sigT_map_eq (f := T3) (Q := S) V3 Hv3)).
Defined.
Lemma sigT_hex_pair_right_normalize:
  PR = eq_existT_curried_dep(Q:=S)
    (H:=H1' •(f_equal f2 H2' •H3'))
    (Hu:=Hu1' ⊙(sigT_map_eq g2 Hu2' ⊙Hu3'))
    (Hv := rew [fun e: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) => rew [S] e in (h1 x0 u0 v0: S
      (f1 x0; g1 x0 u0)) = h3 x3 u3 v3] NR in
      (Hv1' ⊙(sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙Hv3'))).
Proof.
  unfold PR.
  pose (E2 := sigT_dep_path_map_direct f2 g2 (fun z => R2 z.1 z.2) S V2 (p := H2') (hp := Hu2') Hv2').
  refine(path_map2
    (fun (h1': rew [fun x => {u: P' x &T R' x u}] H1' in
      (g1 x0 u0; h1 x0 u0 v0) = (g2 x1' u1'; h2 x1' u1' v1'))
      (h23: rew [fun x => {u: P' x &T R' x u}](f_equal f2 H2' •H3') in
      (g2 x1' u1'; h2 x1' u1' v1') = (g3 x3 u3; h3 x3 u3 v3)) => h1' ⊙h23)
    eq_refl (path_map2
      (fun (h2': rew [fun x => {u: P' x &T R' x u}] f_equal f2 H2' in
        (g2 x1' u1'; h2 x1' u1' v1') = (g2 x2' u2'; h2 x2' u2' v2'))
        (h3': rew [fun x => {u: P' x &T R' x u}] H3' in
        (g2 x2' u2'; h2 x2' u2' v2') = (g3 x3 u3; h3 x3 u3 v3)) => h2' ⊙h3')
      E2 eq_refl) •_).
  refine(f_equal
    (fun h23: rew [fun x => {u: P' x &T R' x u}](f_equal f2 H2' •H3') in
      (g2 x1' u1'; h2 x1' u1' v1') = (g3 x3 u3; h3 x3 u3 v3) =>
      eq_existT_curried_dep (Q := S) (H := H1') (Hu := Hu1') (Hv := Hv1') ⊙h23)
    (sigT_dep_path_paste_normalize S N2 eq_refl
      (sigT_map_eq (f := T2) (Q := S) V2 Hv2') Hv3') •_).
  now exact(sigT_dep_path_paste_normalize S eq_refl
    (sigT_path_paste (q := H3') (k := Hu3') N2 eq_refl) Hv1'
    (sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙Hv3')).
Defined.


Lemma sigT_hex_pair_left_normalize_paste:
  sigT_hex_pair_left_normalize =
  sigT_pair_path_paste S (sigT_path_paste N1 (eq_refl: (= H2; Hu2) = (= H2; Hu2))) N3
    (sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙ Hv2) (sigT_map_eq (f := T3) (Q := S) V3 Hv3)
    (sigT_pair_path_paste S N1 (eq_refl: (= H2; Hu2) = (= H2; Hu2))
      (sigT_map_eq (f := T1) (Q := S) V1 Hv1) Hv2
      (sigT_dep_path_map_direct f1 g1 (fun z => R1 z.1 z.2) S V1 Hv1) eq_refl)
    (sigT_dep_path_map_direct f3 g3 (fun z => R3 z.1 z.2) S V3 Hv3).
Proof.
  unfold sigT_hex_pair_left_normalize, sigT_pair_path_paste.
  cbn beta iota zeta.
  lazymatch goal with
  | |- _ = path_map2 ?F (?E1 • ?N1) ?E2 • ?N =>
    now exact (path_map2_compose_l_prefix F E1 N1 E2 N)
  end.
Defined.

Lemma sigT_hex_pair_right_normalize_paste:
  sigT_hex_pair_right_normalize =
  sigT_pair_path_paste S (eq_refl: (= H1'; Hu1') = (= H1'; Hu1'))
    (sigT_path_paste (q := H3') (k := Hu3') N2 eq_refl)
    Hv1' (sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙ Hv3') eq_refl
    (sigT_pair_path_paste S N2 (eq_refl: (= H3'; Hu3') = (= H3'; Hu3'))
      (sigT_map_eq (f := T2) (Q := S) V2 Hv2') Hv3'
      (sigT_dep_path_map_direct f2 g2 (fun z => R2 z.1 z.2) S V2 Hv2') eq_refl).
Proof.
  unfold sigT_hex_pair_right_normalize, sigT_pair_path_paste.
  cbn beta iota zeta.
  lazymatch goal with
  | |- _ = path_map2 ?F ?E1 (?E2 • ?N2) • ?N =>
    now exact (path_map2_compose_r_prefix F E1 E2 N2 N)
  end.
Defined.

End PairedHexRoutes.

(** The hexagon first normalizes the left route, compares the resulting
    pair paths, and reverses the right normalization. Its dependent lift
    transports both routes to their normal forms. *)
Lemma eq_existT_curried_hex_dep
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
    Hv1 Hv3 Hv2' Hv2 Hv1' Hv3'):
  hexagonal_coherence_dep
    (Q := fun x => {a: P' x &T R' x a})
    (fun a (uv: {u: P1 a &T R1 a u}) => (g1 a uv.1; h1 a uv.1 uv.2))
    (fun a (uv: {u: P3 a &T R3 a u}) => (g3 a uv.1; h3 a uv.1 uv.2))
    (fun a (uv: {u: P2 a &T R2 a u}) => (g2 a uv.1; h2 a uv.1 uv.2))
    HH
    (eq_existT_curried_dep (Q := fun z => R1 z.1 z.2)
      (H := H1) (Hu := Hu1) (Hv := Hv1))
    (eq_existT_curried_dep (Q := fun z => R3 z.1 z.2)
      (H := H3) (Hu := Hu3) (Hv := Hv3))
    (eq_existT_curried_dep (Q := fun z => R2 z.1 z.2)
      (H := H2') (Hu := Hu2') (Hv := Hv2'))
    (eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
      (H := H2) (Hu := Hu2) (Hv := Hv2))
    (eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
      (H := H1') (Hu := Hu1') (Hv := Hv1'))
    (eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
      (H := H3') (Hu := Hu3') (Hv := Hv3')).
Proof.
  pose (S := fun z: {x: B &T P' x} => R' z.1 z.2).
  pose (T1 := fun z: {x: A1 &T P1 x} => (f1 z.1; g1 z.1 z.2)).
  pose (T3 := fun z: {x: A3 &T P3 x} => (f3 z.1; g3 z.1 z.2)).
  pose (T2 := fun z: {x: A2 &T P2 x} => (f2 z.1; g2 z.1 z.2)).
  pose (V1 := fun z: {x: A1 &T P1 x} => h1 z.1 z.2).
  pose (V3 := fun z: {x: A3 &T P3 x} => h3 z.1 z.2).
  pose (V2 := fun z: {x: A2 &T P2 x} => h2 z.1 z.2).
  pose (NL:=sigT_path_paste
    (sigT_path_paste (q := H2) (k := Hu2) (f_equal_eq_existT_curried f1 g1 H1 Hu1) eq_refl)
    (f_equal_eq_existT_curried f3 g3 H3 Hu3)).
  pose (NR := sigT_path_paste (p := H1') (h := Hu1') eq_refl
    (sigT_path_paste (q := H3') (k := Hu3') (f_equal_eq_existT_curried f2 g2 H2' Hu2') eq_refl)).
  pose (EL:=sigT_hex_pair_left_normalize f1 g1 h1 f3 g3 h3
    H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3).
  pose (ER:=sigT_hex_pair_right_normalize f1 g1 h1 f3 g3 h3 f2 g2 h2
    H1' Hu1' Hv1' H2' Hu2' Hv2' H3' Hu3' Hv3').
  now exact (f_equal (fun h => rew [fun e => rew [fun x => {u: P' x &T R' x u}] e in
    (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)] HH in h) EL •
    (sigT_eq_dep_normalize S HH HHu NL NR
      ((sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙Hv2) ⊙sigT_map_eq (f := T3) (Q := S) V3 Hv3)
      (Hv1' ⊙(sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙Hv3')) HHv •eq_sym ER)).
Defined.

Section Coh2Layer.

Context {X2 X1 X0: Type}.
Context {S2: X2 -> Type}.
Context {S1: X1 -> Type}.
Context {S0: X0 -> Type}.

Context {TU T: Type}.
Context {uf0: TU -> X1}.
Context {rf0: T -> X0}.
Context {fA fB fC: TU -> T}.

Context {rfq rfs rfr: X1 -> X0}.
Context {Fq: forall y, S1 y -> S0 (rfq y)}.
Context {Fs: forall y, S1 y -> S0 (rfs y)}.
Context {Fr: forall y, S1 y -> S0 (rfr y)}.
Context {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}.
Context {gs: forall dd, rfs (uf0 dd) = rf0 (fB dd)}.
Context {gr: forall dd, rfr (uf0 dd) = rf0 (fC dd)}.

Context {rur rus ruq1 rur1: X2 -> X1}.
Context {Rr: forall z, S2 z -> S1 (rur z)}.
Context {Rs: forall z, S2 z -> S1 (rus z)}.
Context {Rq1: forall z, S2 z -> S1 (ruq1 z)}.
Context {Rr1: forall z, S2 z -> S1 (rur1 z)}.

Context {KA2: forall z, rfq (rus z) = rfs (ruq1 z)}.
Context {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}.
Context {KA6: forall z, rfr (rus z) = rfs (rur1 z)}.
Context {HKA2: forall z (c: S2 z),
  rew [S0] KA2 z in Fq (rus z) (Rs z c) = Fs (ruq1 z) (Rq1 z c)}.
Context {HKA4: forall z (c: S2 z),
  rew [S0] KA4 z in Fq (rur z) (Rr z c) = Fr (ruq1 z) (Rq1 z c)}.
Context {HKA6: forall z (c: S2 z),
  rew [S0] KA6 z in Fr (rus z) (Rs z c) = Fs (rur1 z) (Rr1 z c)}.

(** The dependent hexagon transported through the six layer-coherence cells.
    The frame premise [permutahedral_coherence] compares its two boundary pastings. *)
Lemma rew_coh2Layer_perm4
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
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA):
  hexagonal_coherence_dep (Q := fun dd => S0 (rf0 dd))
    (fun dd x => rew [S0] gq dd in Fq (uf0 dd) x)
    (fun dd x => rew [S0] gs dd in Fs (uf0 dd) x)
    (fun dd x => rew [S0] gr dd in Fr (uf0 dd) x) κ
    (rew_cohLayer_hex S1 uf0 Rr Rs eU1 pIs pIr pV0 pV1 K1 aS aR HK1 HH1)
    (rew_cohLayer_hex S1 uf0 Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 aR aQ HK3 HH3)
    (rew_cohLayer_hex S1 uf0 Rq1 Rs eU3 pIs pIq pV4 pV5 K5 aS aQ HK5 HH5)
    (rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2)
      (Rs zr2 (rew [S2] pIr in aR)) (Rq1 zr2 (rew [S2] pIr in aR))
      (HKA2 zr2 (rew [S2] pIr in aR)) HH2)
    (rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2)
      (Rr zs2 (rew [S2] pIs in aS)) (Rq1 zs2 (rew [S2] pIs in aS))
      (HKA4 zs2 (rew [S2] pIs in aS)) HH4)
    (rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2)
      (Rs zq2 (rew [S2] pIq in aQ)) (Rr1 zq2 (rew [S2] pIq in aQ))
      (HKA6 zq2 (rew [S2] pIq in aQ)) HH6).
Proof.
  apply (pullback_comparison_retract rf0 S0 κ).
  refine (square_cube_dep S0 _ _ _ HHA Hcoh3Frame
    _ _ _ _ _ _ _ _ Hcoh2Painting).
  - eapply square_compose_map_dep.
    + eapply square_compose_map_dep.
      * now exact (layer_square_map_dep uf0 rur rus rfq fA rf0 gq S1 S0 S2 S2
          Fq Rr Rs eU1 pIs pIr pV0 pV1 K1 HH1 HK1).
      * now exact (layer_square_nat_dep rus ruq1 rfq rfs rf0 Rs Rq1 Fq Fs KA2 HKA2
          pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 aR).
    + now exact (layer_square_map_dep uf0 ruq1 rur1 rfs fB rf0 gs S1 S0 S2 S2
        Fs Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 HH3 HK3).
  - eapply square_compose_map_dep.
    + now exact (layer_square_nat_dep rur ruq1 rfq rfr rf0 Rr Rq1 Fq Fr KA4 HKA4
        pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 aS).
    + eapply square_compose_map_dep.
      * now exact (layer_square_map_dep uf0 ruq1 rus rfr fC rf0 gr S1 S0 S2 S2
          Fr Rq1 Rs eU3 pIs pIq pV4 pV5 K5 HH5 HK5).
      * now exact (layer_square_nat_dep rus rur1 rfr rfs rf0 Rs Rr1 Fr Fs KA6 HKA6
          pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 aQ).
Defined.

End Coh2Layer.

(** The canonical lifted faces of a layer permutahedron satisfy its
    dependent boundary equation. The lower face is precisely the
    transported hexagon returned by [rew_coh2Layer_perm4]. *)
Lemma rew_coh2Layer_perm4_coherence
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
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA):
  permutahedral_coherence_dep Hcoh3Frame
    (fun _ u => u) (fun _ u => u)
    (fun dd x => rew [S0] gq dd in Fq (uf0 dd) x)
    (fun dd x => rew [S0] gs dd in Fs (uf0 dd) x)
    (fun dd x => rew [S0] gr dd in Fr (uf0 dd) x)
    Fq Fs Fr Rr Rs Rq1 Rr1
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    HKA2 HKA4 HKA6
    (rew_cohLayer_hex S1 uf0 Rr Rs eU1 pIs pIr pV0 pV1 K1 aS aR HK1 HH1)
    (rew_cohLayer_hex S1 uf0 Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 aR aQ HK3 HH3)
    (rew_cohLayer_hex S1 uf0 Rq1 Rs eU3 pIs pIq pV4 pV5 K5 aS aQ HK5 HH5)
    (rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2) (Rs zr2 (rew [S2] pIr in aR)) (Rq1 zr2 (rew [S2] pIr in aR)) (HKA2 zr2 (rew [S2] pIr in aR)) HH2)
    (rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2) (Rr zs2 (rew [S2] pIs in aS)) (Rq1 zs2 (rew [S2] pIs in aS)) (HKA4 zs2 (rew [S2] pIs in aS)) HH4)
    (rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2) (Rs zq2 (rew [S2] pIq in aQ)) (Rr1 zq2 (rew [S2] pIq in aQ)) (HKA6 zq2 (rew [S2] pIq in aQ)) HH6)
    eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HK1 HK3 HK5
    (layer_square _ _ _ Rr Rs pIs pIr eU1 pV0 pV1 K1 HK1 HH1)
    (layer_square _ _ _ Rq1 Rr1 pIr pIq eU2 pV2 pV3 K3 HK3 HH3)
    (layer_square _ _ _ Rq1 Rs pIs pIq eU3 pV4 pV5 K5 HK5 HH5)
    (rew_coh2Layer_perm4 u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq aS aR aQ pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HK1 HK3 HK5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA Hcoh2Painting Hcoh3Frame)
    (layer_square _ _ _ Fq Fs pV1 pV2 e2 (gq u1) (gs u2) (KA2 zr2) (HKA2 zr2 (rew [S2] pIr in aR)) HH2)
    (layer_square _ _ _ Fq Fr pV0 pV4 e4 (gq u0) (gr u4) (KA4 zs2) (HKA4 zs2 (rew [S2] pIs in aS)) HH4)
    (layer_square _ _ _ Fr Fs pV5 pV3 e6 (gr u5) (gs u3) (KA6 zq2) (HKA6 zq2 (rew [S2] pIq in aQ)) HH6)
    Hcoh2Painting.
Proof.
  unfold permutahedral_coherence_dep.
  unfold rew_coh2Layer_perm4.
  now apply square_cube_map_dep_coherence.
Defined.

Section CurriedSigmaMiddleRestr0.

Context {TU TR W TL: Type}
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
  (κ: hexagonal_coherence rq r0 rr e2 E1 e5 pQ KA pR).

Let A0 := rew [P] pQ in F m2 (rew [S] e2 in aL).

Let B0 := rew [P] pR in G n2 (rew [SR] e5 in aR).

Let L := rew_cohLayer_hex P r0 F G E1 e2 e5 pQ pR KA aL aR HK κ.

Context (R: forall d, P (r0 d) -> Type)
  {v: R d1 A0} {w: R d2 B0}
  (Hv: rew [fun z: {d: W &T P (r0 d)} => R z.1 z.2] (= E1; L) in
    (v: (fun z: {d: W &T P (r0 d)} => R z.1 z.2) (d1; A0)) = w).
(** A canonical dependent hexagon when the middle fiber has an
    additional component which its comparison map forgets. *)
Lemma rew_coh2Painting_restr0:
  hexagonal_coherence_dep
    (P2 := fun d => {a: P (r0 d) &T R d a})
    (Q := P) (f2 := r0) F (fun _ a => a.1) G κ
    eq_refl (eq_existT_curried_dep (Q := fun z => R z.1 z.2) (H := E1) (Hu := L) (Hv := Hv))
    eq_refl eq_refl HK eq_refl.
Proof.
  unfold hexagonal_coherence_dep.
  rewrite (sigT_map_eq_fst (P := fun d => P (r0 d)) (Q := P) (f := r0)
    (R := R) (fun _ a => a)).
  now exact (layer_square _ _ _ F G e2 e5 E1 pQ pR KA HK κ).
Defined.

End CurriedSigmaMiddleRestr0.
