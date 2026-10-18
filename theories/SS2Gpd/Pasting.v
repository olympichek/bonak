(** Pasting 3-cells, with interchange, reassociation, and boundary changes. *)

From Bonak.Lib Require Import Notation RewLemmas SigT.
From Bonak.SSGpd Require Import Pasting Coh3Shapes.

Local Lemma f_equal_id_loop {A: Type} {x: A}
  (p: (eq_refl: x = x) = eq_refl):
  f_equal (fun q: x = x => f_equal (fun v => v) q) p = p.
Proof.
  now exact (homotopy_path_normalize
    (fun q: x = x => f_equal (fun v => v) q) (fun q => f_equal_id q) (x := eq_refl) (t := eq_refl) p).
Defined.

Local Lemma square_compose_dep_left_unit {X: Type} {P: X -> Type} {x: X} {u: P x}
  (H: (eq_refl: u = u) = eq_refl):
  @square_compose_dep X P x x x x x x eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl u u u u u u eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl H = H.
Proof.
  cbv in *.
  pose (I := fun q: (eq_refl: u = u) = eq_refl =>
    f_equal (fun p: u = u => p) q).
  pose (J := fun q: (eq_refl: u = u) = eq_refl =>
    f_equal (fun p: u = u => f_equal (fun v => v) p) q).
  change (I (I (I (I (J H)))) = H).
  unfold I. rewrite 4 f_equal_id.
  unfold J. now exact (homotopy_path_normalize
    (fun q: u = u => f_equal (fun v => v) q) (fun q => f_equal_id q)
    (x := eq_refl) (t := eq_refl) H).
Defined.

(** Compose two path comparisons, changing the left path first. *)
Definition path_paste {X: Type} {x y z: X}
  {p p': x = y} {q q': y = z} (H: p = p') (K: q = q'):
  p • q = p' • q' :=
  whisker_r H q • whisker_l p' K.

Definition path_paste_dep {X: Type} (P: X -> Type) {x y z: X}
  {p p': x = y} {q q': y = z} {H: p = p'} {K: q = q'}
  {u: P x} {v: P y} {w: P z}
  {hp: rew [P] p in u = v} {hp': rew [P] p' in u = v}
  {hq: rew [P] q in v = w} {hq': rew [P] q' in v = w}
  (HH: rew [fun e => rew [P] e in u = v] H in hp = hp')
  (KK: rew [fun e => rew [P] e in v = w] K in hq = hq'):
  rew [fun e => rew [P] e in u = w] path_paste H K in (hp ⊙ hq) = hp' ⊙ hq' :=
  sigT_map_eq (Q := fun e: x = z => rew [P] e in u = w)
    (f := fun e => e • q) (fun e h => h ⊙ hq) HH ⊙
  sigT_map_eq (Q := fun e: x = z => rew [P] e in u = w)
    (f := fun e => p' • e) (fun e h => hp' ⊙ h) KK.

(** Stack cubes along a shared horizontal edge of their square faces.
    The comparison of the middle edges is shared. *)
Lemma square_cube_stack {X: Type} {x0 x1 y0 y1 z0 z1: X}
  {a a': x0 = x1} {b b': y0 = y1} {c c': z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  {H: p • b = a • q} {H': p • b' = a' • q}
  {K: r • c = b • s} {K': r • c' = b' • s}
  {κ: b = b'} {λ: a = a'} {μ: c = c'}
  (C: square_cube H H' κ λ) (D: square_cube K K' μ κ):
  square_cube (square_stack H K) (square_stack H' K') μ λ.
Proof.
  destruct κ, λ, μ.
  unfold square_cube in *.
  cbn [whisker_l whisker_r f_equal eq_trans] in *.
  rewrite eq_trans_refl_l in C, D. subst H' K'.
  now rewrite eq_trans_refl_l.
Defined.

Lemma square_cube_stack_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1 z0 z1: X}
  {a a': x0 = x1} {b b': y0 = y1} {c c': z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  {H: p • b = a • q} {H': p • b' = a' • q}
  {K: r • c = b • s} {K': r • c' = b' • s}
  {κ: b = b'} {λ: a = a'} {μ: c = c'}
  (C: square_cube H H' κ λ) (D: square_cube K K' μ κ)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1} {w0: P z0} {w1: P z1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hc: rew [P] c in w0 = w1} {hc': rew [P] c' in w0 = w1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {hr: rew [P] r in v0 = w0} {hs: rew [P] s in v1 = w1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {HH': rew [fun e => rew [P] e in u0 = v1] H' in (hp ⊙ hb') = ha' ⊙ hq}
  {KK: rew [fun e => rew [P] e in v0 = w1] K in (hr ⊙ hc) = hb ⊙ hs}
  {KK': rew [fun e => rew [P] e in v0 = w1] K' in (hr ⊙ hc') = hb' ⊙ hs}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  {Dμ: rew [fun e => rew [P] e in w0 = w1] μ in hc = hc'}
  (CC: square_cube_coherence_dep P H H' κ λ C ha ha' hb hb' hp hq HH HH' Dκ Dλ)
  (DD: square_cube_coherence_dep P K K' μ κ D hb hb' hc hc' hr hs KK KK' Dμ Dκ):
  square_cube_coherence_dep P (square_stack H K) (square_stack H' K') μ λ
    (square_cube_stack C D) ha ha' hc hc' (hp ⊙ hr) (hq ⊙ hs)
    (square_stack_dep P H K ha hb hc hp hq hr hs HH KK)
    (square_stack_dep P H' K' ha' hb' hc' hp hq hr hs HH' KK') Dμ Dλ.
Proof.
  destruct κ, Dκ, λ, Dλ, μ, Dμ.
  unfold square_cube_coherence_dep, square_cube_stack, square_cube,
    whisker_l, whisker_r in *.
  cbn [f_equal eq_trans] in C, D |- *.
  subst H K.
  destruct p, q, r, s, hp, hq, hr, hs.
  cbn in H', K'. destruct K', H', c.
  destruct ha. cbn in *.
  pose proof (eq_sym (f_equal_id HH) • CC • f_equal_id HH') as E.
  destruct E.
  pose proof (eq_sym (f_equal_id KK) • DD • f_equal_id KK') as E.
  destruct E.
  now reflexivity.
Defined.

(** Map a cube, normalizing the mapped composites in its square faces. *)
Lemma square_cube_map {X Y: Type} (f: X -> Y)
  {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ: b = b'} {λ: a = a'} (C: square_cube H K κ λ):
  square_cube (square_map f H) (square_map f K)
    (f_equal (fun e => f_equal f e) κ) (f_equal (fun e => f_equal f e) λ).
Proof.
  destruct κ, λ.
  unfold square_cube in *.
  cbn [whisker_l whisker_r f_equal eq_trans] in *.
  rewrite eq_trans_refl_l in C. subst K.
  now rewrite eq_trans_refl_l.
Defined.

Lemma square_cube_map_coherence_dep {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ: b = b'} {λ: a = a'} (C: square_cube H K κ λ)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (CC: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ):
  square_cube_coherence_dep Q (square_map f H) (square_map f K)
    (f_equal (fun e => f_equal f e) κ) (f_equal (fun e => f_equal f e) λ)
    (square_cube_map f C)
    (sigT_map_eq F ha) (sigT_map_eq F ha') (sigT_map_eq F hb) (sigT_map_eq F hb')
    (sigT_map_eq F hp) (sigT_map_eq F hq)
    (square_map_dep f F H ha hb hp hq HH)
    (square_map_dep f F K ha' hb' hp hq KK) (sigT_map_eq
      (fun (e: y0 = y1) (h: rew [P] e in v0 = v1) => sigT_map_eq F h) Dκ) (sigT_map_eq
      (fun (e: x0 = x1) (h: rew [P] e in u0 = u1) => sigT_map_eq F h) Dλ).
Proof.
  destruct κ, Dκ, λ, Dλ.
  unfold square_cube_coherence_dep, square_cube_map, square_cube,
    whisker_l, whisker_r in *.
  cbn [f_equal eq_trans] in C |- *.
  subst H.
  destruct p, q, hp, hq. cbn in K. destruct K, b.
  destruct ha.
  cbn in *.
  pose proof (eq_sym (f_equal_id HH) • CC • f_equal_id KK) as E.
  destruct E.
  now reflexivity.
Defined.

(** Join cubes along their common square face. *)
Definition square_cube_trans {X: Type} {x0 x1 y0 y1: X}
  {a a' a'': x0 = x1} {b b' b'': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q} {L: p • b'' = a'' • q}
  {κ: b = b'} {λ: a = a'} {μ: b' = b''} {ν: a' = a''}
  (C: square_cube H K κ λ) (D: square_cube K L μ ν):
  square_cube H L (κ • μ) (λ • ν) :=
  square_change_horizontal
    (eq_trans_map_distr (fun e => p • e) κ μ)
    (square_compose C D)
    (eq_trans_map_distr (fun e => e • q) λ ν).

Lemma square_cube_trans_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a' a'': x0 = x1} {b b' b'': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q} {L: p • b'' = a'' • q}
  {κ: b = b'} {λ: a = a'} {μ: b' = b''} {ν: a' = a''}
  (C: square_cube H K κ λ) (D: square_cube K L μ ν)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {ha'': rew [P] a'' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hb'': rew [P] b'' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {LL: rew [fun e => rew [P] e in u0 = v1] L in (hp ⊙ hb'') = ha'' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  {Dμ: rew [fun e => rew [P] e in v0 = v1] μ in hb' = hb''}
  {Dν: rew [fun e => rew [P] e in u0 = u1] ν in ha' = ha''}
  (CC: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ)
  (DD: square_cube_coherence_dep P K L μ ν D ha' ha'' hb' hb'' hp hq KK LL Dμ Dν):
  square_cube_coherence_dep P H L (κ • μ) (λ • ν) (square_cube_trans C D)
    ha ha'' hb hb'' hp hq HH LL (Dκ ⊙ Dμ) (Dλ ⊙ Dν).
Proof.
  unfold square_cube_coherence_dep, square_cube_trans.
  eapply (square_change_horizontal_dep (fun e => rew [P] e in u0 = v1)
    (eq_trans_map_distr (fun e => p • e) κ μ) (square_compose C D)
    (eq_trans_map_distr (fun e => e • q) λ ν)).
  - now exact (sigT_map_eq_comp
      (fun (e: y0 = y1) (h: rew [P] e in v0 = v1) => hp ⊙ h) Dκ Dμ).
  - now exact (square_compose_dep (fun e => rew [P] e in u0 = v1) C D
      _ _ _ _ _ _ _ CC DD).
  - now exact (sigT_map_eq_comp
      (fun (e: x0 = x1) (h: rew [P] e in u0 = u1) => h ⊙ hq) Dλ Dν).
Defined.

(** Replace the two square faces of a cube by equal squares. *)
Definition square_cube_change_faces {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H H': p • b = a • q} {K K': p • b' = a' • q}
  {κ: b = b'} {λ: a = a'}
  (E: H' = H) (C: square_cube H K κ λ) (F: K' = K):
  square_cube H' K' κ λ :=
  square_change_sides E C F.

Lemma square_cube_change_faces_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H H': p • b = a • q} {K K': p • b' = a' • q}
  {κ: b = b'} {λ: a = a'}
  {E: H' = H} {C: square_cube H K κ λ} {F: K' = K}
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {HH': rew [fun e => rew [P] e in u0 = v1] H' in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {KK': rew [fun e => rew [P] e in u0 = v1] K' in (hp ⊙ hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (EE: rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in
    (hp ⊙ hb) = ha ⊙ hq] E in HH' = HH)
  (CC: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ)
  (FF: rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in
    (hp ⊙ hb') = ha' ⊙ hq] F in KK' = KK):
  square_cube_coherence_dep P H' K' κ λ (square_cube_change_faces E C F)
    ha ha' hb hb' hp hq HH' KK' Dκ Dλ.
Proof.
  now exact (square_change_sides_dep (fun e => rew [P] e in u0 = v1)
    E C F _ _ HH HH' KK KK' EE CC FF).
Defined.

(** Paste cubes whose lower edges are mapped paths, retaining the action
    on the composite lower comparison. *)
Lemma square_cube_compose_map {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a a': x0 = x1} {b b': x1 = x2}
  {c c': y0 = y1} {d d': y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {H: p • f_equal f c = a • q} {H': p • f_equal f c' = a' • q}
  {K: q • f_equal f d = b • r} {K': q • f_equal f d' = b' • r}
  {κ: c = c'} {λ: a = a'} {μ: d = d'} {ν: b = b'}
  (C: square_cube H H' (f_equal (fun e => f_equal f e) κ) λ)
  (D: square_cube K K' (f_equal (fun e => f_equal f e) μ) ν):
  square_cube (square_compose_map f H K) (square_compose_map f H' K')
    (f_equal (fun e => f_equal f e) (path_paste κ μ)) (path_paste λ ν).
Proof.
  destruct κ, λ, μ, ν.
  unfold square_cube in *.
  cbn [whisker_l whisker_r f_equal eq_trans path_paste] in *.
  rewrite eq_trans_refl_l in C, D. subst H' K'.
  now rewrite eq_trans_refl_l.
Defined.

Lemma square_cube_compose_map_coherence_dep {X Y: Type}
  (f: Y -> X) (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a a': x0 = x1} {b b': x1 = x2} {c c': y0 = y1} {d d': y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {H: p • f_equal f c = a • q} {H': p • f_equal f c' = a' • q}
  {K: q • f_equal f d = b • r} {K': q • f_equal f d' = b' • r}
  {κ: c = c'} {λ: a = a'} {μ: d = d'} {ν: b = b'}
  (C: square_cube H H' (f_equal (fun e => f_equal f e) κ) λ) (D: square_cube K K' (f_equal (fun e
    => f_equal f e) μ) ν)
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: Q y0} {v1: Q y1} {v2: Q y2}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in u1 = u2} {hb': rew [P] b' in u1 = u2}
  {hc: rew [Q] c in v0 = v1} {hc': rew [Q] c' in v0 = v1}
  {hd: rew [Q] d in v1 = v2} {hd': rew [Q] d' in v1 = v2}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  {hr: rew [P] r in u2 = F y2 v2}
  {HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq}
  {HH': rew [fun e => rew [P] e in u0 = F y1 v1] H' in (hp ⊙ sigT_map_eq F hc') = ha' ⊙ hq}
  {KK: rew [fun e => rew [P] e in u1 = F y2 v2] K in (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr}
  {KK': rew [fun e => rew [P] e in u1 = F y2 v2] K' in (hq ⊙ sigT_map_eq F hd') = hb' ⊙ hr}
  {Dκ: rew [fun e => rew [Q] e in v0 = v1] κ in hc = hc'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  {Dμ: rew [fun e => rew [Q] e in v1 = v2] μ in hd = hd'}
  {Dν: rew [fun e => rew [P] e in u1 = u2] ν in hb = hb'}
  (CC: square_cube_coherence_dep P H H' (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq F hc) (sigT_map_eq F hc') hp hq HH HH'
    (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dκ) Dλ)
  (DD: square_cube_coherence_dep P K K' (f_equal (fun e => f_equal f e) μ) ν D
    hb hb' (sigT_map_eq F hd) (sigT_map_eq F hd') hq hr KK KK'
    (sigT_map_eq (fun (e: y1 = y2) (h: rew [Q] e in v1 = v2) => sigT_map_eq F h) Dμ) Dν):
  square_cube_coherence_dep P (square_compose_map f H K) (square_compose_map f H' K')
    (f_equal (fun e => f_equal f e) (path_paste κ μ))
    (path_paste λ ν) (square_cube_compose_map f C D)
    (ha ⊙ hb) (ha' ⊙ hb') (sigT_map_eq F (hc ⊙ hd)) (sigT_map_eq F (hc' ⊙ hd')) hp hr
    (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK)
    (square_compose_map_coherence_dep f P Q F H' K' ha' hb' hc' hd' hp hq hr HH' KK')
    (sigT_map_eq (fun (e: y0 = y2) (h: rew [Q] e in v0 = v2) => sigT_map_eq F h) (path_paste_dep Q
      Dκ Dμ)) (path_paste_dep P Dλ Dν).
Proof.
  destruct κ, Dκ, λ, Dλ, μ, Dμ, ν, Dν.
  unfold square_cube_coherence_dep, square_cube_compose_map, square_cube,
    whisker_l, whisker_r, path_paste, path_paste_dep in *.
  cbn [f_equal eq_trans] in C, D |- *.
  subst H K.
  destruct c, d, hc, hd.
  cbn in *.
  subst p q. destruct a, b, ha, hb.
  unfold square_compose_map_coherence_dep, square_compose_map. cbn.
  generalize dependent r.
  generalize (F y0 v0). generalize (f y0).
  intros z vz r hq hp hr KK' KK DD HH HH' CC.
  destruct r, hr. cbn in *.
  pose proof (eq_sym (f_equal_id HH) • CC • f_equal_id HH') as E.
  destruct E.
  pose proof (eq_sym (f_equal_id KK) • DD • f_equal_id KK') as E.
  destruct E.
  now reflexivity.
Defined.

(** Change the shared vertical edges of a cube using the same comparisons
    on both square faces. *)
Lemma square_cube_change_sides {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1}
  {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (Hq: q' = q)
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ: b = b'} {λ: a = a'} (C: square_cube H K κ λ):
  square_cube (square_change_sides Hp H Hq) (square_change_sides Hp K Hq) κ λ.
Proof.
  destruct Hp, Hq.
  unfold square_change_sides.
  cbn [whisker_l whisker_r f_equal eq_sym eq_trans].
  rewrite 2 eq_trans_refl_l.
  now exact C.
Defined.

Lemma square_cube_change_sides_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (Hq: q' = q)
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ: b = b'} {λ: a = a'} (C: square_cube H K κ λ)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hp': rew [P] p' in u0 = v0}
  {hq: rew [P] q in u1 = v1} {hq': rew [P] q' in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (HHp: rew [fun e => rew [P] e in u0 = v0] Hp in hp' = hp)
  (HHq: rew [fun e => rew [P] e in u1 = v1] Hq in hq' = hq)
  (CC: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ):
  square_cube_coherence_dep P (square_change_sides Hp H Hq)
    (square_change_sides Hp K Hq) κ λ (square_cube_change_sides Hp Hq C)
    ha ha' hb hb' hp' hq'
    (square_change_sides_dep P Hp H Hq ha hb hp hp' hq hq' HHp HH HHq)
    (square_change_sides_dep P Hp K Hq ha' hb' hp hp' hq hq' HHp KK HHq) Dκ Dλ.
Proof.
  destruct Hp, HHp, Hq, HHq, κ, Dκ, λ, Dλ.
  unfold square_cube_coherence_dep, square_cube_change_sides, square_cube,
    whisker_l, whisker_r in *.
  cbn [f_equal eq_trans] in C |- *.
  subst H.
  destruct p', q', hp', hq'. cbn in K. destruct K, b.
  destruct ha. cbn in *.
  pose proof (eq_sym (f_equal_id HH) • CC • f_equal_id KK) as E.
  destruct E. now reflexivity.
Defined.

(** Normalize a source path prefixed to a layer boundary. *)
Lemma layer_cube_nat_side {Z A B C: Type}
  (s: Z -> A) (r: A -> B) (f: B -> C)
  {z0 z1: Z} (e: z0 = z1) {a: A} (p: s z1 = a)
  {b: B} (q: r a = b) {c: C} (k: f b = c):
  f_equal f (f_equal r (f_equal s e • p) • q) • k =
  f_equal f (f_equal (fun z => r (s z)) e) •
    (f_equal f (f_equal r p • q) • k).
Proof.
  destruct e, p, q. cbn.
  now rewrite 2 eq_trans_refl_l.
Defined.

Lemma layer_cube_nat_side_coherence_dep {Z A B C: Type}
  {PZ: Z -> Type} {PA: A -> Type} {PB: B -> Type} {PC: C -> Type}
  (s: Z -> A) (r: A -> B) (f: B -> C)
  (S: forall z, PZ z -> PA (s z))
  (R: forall a, PA a -> PB (r a)) (F: forall b, PB b -> PC (f b))
  {z0 z1: Z} (e: z0 = z1) {a: A} (p: s z1 = a)
  {b: B} (q: r a = b) {c: C} (k: f b = c)
  {v0: PZ z0} {v1: PZ z1} {va: PA a} {vb: PB b} {vc: PC c}
  (he: rew [PZ] e in v0 = v1) (hp: rew [PA] p in S z1 v1 = va)
  (hq: rew [PB] q in R a va = vb) (hk: rew [PC] k in F b vb = vc):
  rew [fun h => rew [PC] h in F (r (s z0)) (R (s z0) (S z0 v0)) = vc]
    layer_cube_nat_side s r f e p q k in
    (sigT_map_eq F (sigT_map_eq R (sigT_map_eq S he ⊙ hp) ⊙ hq) ⊙ hk) =
  sigT_map_eq F (sigT_map_eq (fun z v => R (s z) (S z v)) he) ⊙
    (sigT_map_eq F (sigT_map_eq R hp ⊙ hq) ⊙ hk).
Proof.
  destruct e, he, p, hp, q, hq.
  cbn [layer_cube_nat_side sigT_map_eq f_equal eq_trans] in *.
  rewrite sigT_trans_eq_refl.
  cbn.
  destruct k, hk. cbn.
  now reflexivity.
Defined.

(** Extend a permutahedral cell along a path in its source. A supplied
    naturality prism moves its upper hexagon from [z1] to [z0]. The vertical
    boundaries are normalized using [f_equal zS e • pIs] and
    [f_equal zQ e • pIq]. *)
Definition layer_cube_nat
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
  {Z: Type} (zS zR zQ: Z -> X2)
  (K1: forall z, rur (zS z) = rus (zR z))
  (K3: forall z, ruq1 (zR z) = rur1 (zQ z))
  (K5: forall z, ruq1 (zS z) = rus (zQ z))
  (HHA: forall z, hexagonal_coherence rfq rfs rfr
    (K1 z) (K3 z) (K5 z) (KA2 (zR z)) (KA4 (zS z)) (KA6 (zQ z)))
  {z0 z1: Z} (e: z0 = z1)
  (u0 u1 u2 u3 u4 u5: TU)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs2 zr2 zq2: X2)
  (pIs: zS z1 = zs2) (pIr: zR z1 = zr2) (pIq: zQ z1 = zq2)
  (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
  (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
  (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
  (HH1: hexagonal_coherence rur uf0 rus pIs eU1 pIr pV0 (K1 z1) pV1)
  (HH3: hexagonal_coherence ruq1 uf0 rur1 pIr eU2 pIq pV2 (K3 z1) pV3)
  (HH5: hexagonal_coherence ruq1 uf0 rus pIs eU3 pIq pV4 (K5 z1) pV5)
  (κ: hexagonal_coherence fA fB fC eU1 eU2 eU3 e2 e4 e6)
  (HH2: hexagonal_coherence rfq rf0 rfs pV1 e2 pV2 (gq u1) (KA2 zr2) (gs u2))
  (HH4: hexagonal_coherence rfq rf0 rfr pV0 e4 pV4 (gq u0) (KA4 zs2) (gr u4))
  (HH6: hexagonal_coherence rfr rf0 rfs pV5 e6 pV3 (gr u5) (KA6 zq2) (gs u3))
  (P: permutahedral_coherence u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 (zS z1) zs2 (zR z1) zr2 (zQ z1) zq2 pIs pIr pIq
    pV0 pV1 pV2 pV3 pV4 pV5 (K1 z1) (K3 z1) (K5 z1) HH1 HH3 HH5 κ HH2 HH4 HH6 (HHA z1))
  (S1: square_coherence
    (fun z => rur (zS z)) (fun z => rus (zR z)) rfq rfq
    (fun z => f_equal rfq (K1 z)) e)
  (S2: square_coherence
    (fun z => rus (zR z)) (fun z => ruq1 (zR z)) rfq rfs
    (fun z => KA2 (zR z)) e)
  (S3: square_coherence
    (fun z => ruq1 (zR z)) (fun z => rur1 (zQ z)) rfs rfs
    (fun z => f_equal rfs (K3 z)) e)
  (T1: square_coherence
    (fun z => rur (zS z)) (fun z => ruq1 (zS z)) rfq rfr
    (fun z => KA4 (zS z)) e)
  (T2: square_coherence
    (fun z => ruq1 (zS z)) (fun z => rus (zQ z)) rfr rfr
    (fun z => f_equal rfr (K5 z)) e)
  (T3: square_coherence
    (fun z => rus (zQ z)) (fun z => rur1 (zQ z)) rfr rfs
    (fun z => KA6 (zQ z)) e)
  (N: hexagonal_prism_coherence (HHA z0) (HHA z1) S1 S2 S3 T1 T2 T3) :=
  square_cube_change_sides
    (layer_cube_nat_side zS rur rfq e pIs pV0 (gq u0))
    (layer_cube_nat_side zQ rur1 rfs e pIq pV3 (gs u3))
    (square_cube_stack N P).

(** Compatibility of source extension, mapping and square pasting. *)
Lemma layer_square_nat_source {Z V W W' X B: Type}
  (u: Z -> V) (L: V -> W) (R: V -> W') (f: W -> X) (g: W' -> X) (d: B -> X)
  (k: forall v, f (L v) = g (R v))
  {z0 z1: Z} (e: z0 = z1) {v: V} (p: u z1 = v)
  {m: W} {n: W'} (l: L v = m) (r: R v = n)
  {w0 w1: B} (b: w0 = w1) (c: f m = d w0) (c': g n = d w1)
  (H: hexagonal_coherence f d g l b r c (k v) c'):
  layer_square_nat L R f g d k (f_equal u e • p) l r b c c' H
    (square_coherence_fill L R f g k (f_equal u e • p)) =
  square_change_sides (layer_cube_nat_side u L f e p l c) (square_stack
      (square_coherence_fill (fun z => L (u z)) (fun z => R (u z))
        f g (fun z => k (u z)) e)
      (layer_square_nat L R f g d k p l r b c c' H
        (square_coherence_fill L R f g k p)))
    (layer_cube_nat_side u R g e p r c').
Proof.
  destruct e, p, l, r, b.
  unfold layer_square_nat, square_nat_along, layer_cube_nat_side, map_compose_tail.
  cbn.
  generalize H. unfold hexagonal_coherence. cbn [f_equal].
  generalize (k (u z0)).
  generalize c', c.
  generalize (g (R (u z0))), (d w0).
  intros y z s q t J.
  destruct q. subst y. cbn in J. destruct J.
  now reflexivity.
Defined.

Lemma layer_square_nat_source_coherence_dep {Z V W W' X B: Type}
  {PZ: Z -> Type} {PV: V -> Type} {PW: W -> Type} {PW': W' -> Type}
  {PX: X -> Type} {PB: B -> Type}
  (u: Z -> V) (L: V -> W) (R: V -> W') (f: W -> X) (g: W' -> X) (d: B -> X)
  (U: forall z, PZ z -> PV (u z))
  (DL: forall v, PV v -> PW (L v)) (DR: forall v, PV v -> PW' (R v))
  (F: forall w, PW w -> PX (f w)) (G: forall w, PW' w -> PX (g w))
  (D: forall b, PB b -> PX (d b))
  (k: forall v, f (L v) = g (R v))
  (hk: forall v a, rew [PX] k v in F (L v) (DL v a) = G (R v) (DR v a))
  {z0 z1: Z} (e: z0 = z1) {v: V} (p: u z1 = v)
  {m: W} {n: W'} (l: L v = m) (r: R v = n)
  {w0 w1: B} (b: w0 = w1) (c: f m = d w0) (c': g n = d w1)
  (H: hexagonal_coherence f d g l b r c (k v) c')
  {az0: PZ z0} {az1: PZ z1} {av: PV v} {am: PW m} {an: PW' n}
  {aw0: PB w0} {aw1: PB w1}
  (he: rew [PZ] e in az0 = az1) (hp: rew [PV] p in U z1 az1 = av)
  (hl: rew [PW] l in DL v av = am) (hr: rew [PW'] r in DR v av = an)
  (hb: rew [PB] b in aw0 = aw1) (hc: rew [PX] c in F m am = D w0 aw0)
  (hc': rew [PX] c' in G n an = D w1 aw1)
  (HH: hexagonal_coherence_dep F D G H hl hb hr hc (hk v av) hc'):
  let dfull := layer_square_nat_coherence_dep L R f g d DL DR F G D k hk
    (f_equal u e • p) l r b c c' H (sigT_map_eq U he ⊙ hp) hl hr hb hc hc' HH in
  let npart := layer_square_nat L R f g d k p l r b c c' H
    (square_coherence_fill L R f g k p) in
  let dpart := layer_square_nat_coherence_dep L R f g d DL DR F G D k hk
    p l r b c c' H hp hl hr hb hc hc' HH in
  let ne := square_coherence_fill (fun z => L (u z)) (fun z => R (u z))
    f g (fun z => k (u z)) e in
  let de := square_coherence_dep_fill (fun z => L (u z)) (fun z => R (u z)) f g
    (fun z a => DL (u z) (U z a)) (fun z a => DR (u z) (U z a)) F G
    (fun z => k (u z)) (fun z a => hk (u z) (U z a)) e he in
  let left0 := sigT_map_eq F
    (sigT_map_eq (fun z a => DL (u z) (U z a)) he) in
  let right0 := sigT_map_eq G
    (sigT_map_eq (fun z a => DR (u z) (U z a)) he) in
  let left1 := sigT_map_eq F (sigT_map_eq DL hp ⊙ hl) ⊙ hc in
  let right1 := sigT_map_eq G (sigT_map_eq DR hp ⊙ hr) ⊙ hc' in
  let leftfull := sigT_map_eq F
    (sigT_map_eq DL (sigT_map_eq U he ⊙ hp) ⊙ hl) ⊙ hc in
  let rightfull := sigT_map_eq G
    (sigT_map_eq DR (sigT_map_eq U he ⊙ hp) ⊙ hr) ⊙ hc' in
  let dstack := square_stack_dep PX ne npart
    (hk (u z0) (U z0 az0)) (hk (u z1) (U z1 az1)) (sigT_map_eq D hb)
    left0 right0 left1 right1 de dpart in
  let dnormal := square_change_sides_dep PX
    (layer_cube_nat_side u L f e p l c) (square_stack ne npart)
    (layer_cube_nat_side u R g e p r c')
    (hk (u z0) (U z0 az0)) (sigT_map_eq D hb)
    (left0 ⊙ left1) leftfull (right0 ⊙ right1) rightfull
    (layer_cube_nat_side_coherence_dep u L f U DL F e p l c he hp hl hc)
    dstack (layer_cube_nat_side_coherence_dep u R g U DR G e p r c' he hp hr hc') in
  rew [fun h => rew [fun q => rew [PX] q in F (L (u z0)) (DL (u z0) (U z0 az0)) = D w1 aw1]
    h in (leftfull ⊙ sigT_map_eq D hb) = hk (u z0) (U z0 az0) ⊙ rightfull]
    layer_square_nat_source u L R f g d k e p l r b c c' H in dfull = dnormal.
Proof.
  destruct e, he, p, hp, l, hl, r, hr, b, hb.
  unfold hexagonal_coherence, hexagonal_coherence_dep in *.
  cbv in *.
  revert c c' H hc hc' HH.
  generalize (hk (u z0) (U z0 az0)).
  generalize (k (u z0)).
  generalize (G (R (u z0)) (DR (u z0) (U z0 az0))).
  generalize (g (R (u z0))).
  generalize (D w0 aw0).
  generalize (d w0).
  intros xd ad yg ag κ hκ c c' H hc hc' HH.
  destruct c, hc.
  revert κ hκ H HH. subst yg. intros κ hκ H HH.
  cbn in H. destruct H.
  revert hκ HH. destruct hc'. intros hκ HH.
  cbn in HH.
  change (eq_refl = f_equal (fun v => v) hκ) in HH.
  pose proof (HH • f_equal_id hκ) as K.
  revert HH. destruct K. intro HH. cbn.
  pose (I := fun q: (eq_refl: ag = ag) = eq_refl =>
    f_equal (fun p: ag = ag => p) q).
  pose (J := fun q: (eq_refl: ag = ag) = eq_refl =>
    f_equal (fun p: ag = ag => f_equal (fun v => v) p) q).
  change (I (I (I (I (J HH)))) = I (I (I (I (J (I (I (I (I (J HH)))))))))).
  unfold I. rewrite 8 f_equal_id.
  unfold J. now rewrite 2 f_equal_id_loop.
Defined.

Lemma square_interchange_map {X Y: Type} (f: Y -> X)
  {x0 x1 x2 y0 y1 y2: X} {z0 z1 z2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {e: z0 = z1} {g: z1 = z2}
  {p0: x0 = y0} {p1: x1 = y1} {p2: x2 = y2}
  {q0: y0 = f z0} {q1: y1 = f z1} {q2: y2 = f z2}
  (H00: p0 • c = a • p1) (H01: p1 • d = b • p2)
  (H10: q0 • f_equal f e = c • q1) (H11: q1 • f_equal f g = d • q2):
  square_compose_map f (square_stack H00 H10) (square_stack H01 H11) =
  square_stack (square_compose H00 H01) (square_compose_map f H10 H11).
Proof.
  destruct e, g.
  generalize H00, H01, H10, H11.
  generalize a, b, c, d.
  generalize p0, p1, p2.
  generalize q0, q1, q2.
  generalize x0, x1, x2, y0, y1, y2.
  intros u0 u1 u2 v0 v1 v2 r0 r1 r2.
  subst v0 v1 v2.
  intros s0 s1 s2. subst u0 u1 u2.
  intros a' b' c' d' K00 K01 K10 K11.
  cbn in K10, K11. destruct K10, K11.
  cbn in K00, K01. destruct K00, K01.
  now reflexivity.
Defined.

Lemma square_interchange_map_coherence_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2 y0 y1 y2: X} {z0 z1 z2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {e: z0 = z1} {g: z1 = z2}
  {p0: x0 = y0} {p1: x1 = y1} {p2: x2 = y2}
  {q0: y0 = f z0} {q1: y1 = f z1} {q2: y2 = f z2}
  (H00: p0 • c = a • p1) (H01: p1 • d = b • p2)
  (H10: q0 • f_equal f e = c • q1) (H11: q1 • f_equal f g = d • q2)
  {u0: P x0} {u1: P x1} {u2: P x2}
  {v0: P y0} {v1: P y1} {v2: P y2}
  {w0: Q z0} {w1: Q z1} {w2: Q z2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [P] c in v0 = v1) (hd: rew [P] d in v1 = v2)
  (he: rew [Q] e in w0 = w1) (hg: rew [Q] g in w1 = w2)
  (hp0: rew [P] p0 in u0 = v0) (hp1: rew [P] p1 in u1 = v1)
  (hp2: rew [P] p2 in u2 = v2)
  (hq0: rew [P] q0 in v0 = F z0 w0) (hq1: rew [P] q1 in v1 = F z1 w1)
  (hq2: rew [P] q2 in v2 = F z2 w2)
  (HH00: rew [fun t => rew [P] t in u0 = v1] H00 in (hp0 ⊙ hc) = ha ⊙ hp1)
  (HH01: rew [fun t => rew [P] t in u1 = v2] H01 in (hp1 ⊙ hd) = hb ⊙ hp2)
  (HH10: rew [fun t => rew [P] t in v0 = F z1 w1] H10 in
    (hq0 ⊙ sigT_map_eq F he) = hc ⊙ hq1)
  (HH11: rew [fun t => rew [P] t in v1 = F z2 w2] H11 in
    (hq1 ⊙ sigT_map_eq F hg) = hd ⊙ hq2):
  let left := square_compose_map_coherence_dep f P Q F
    (square_stack H00 H10) (square_stack H01 H11) ha hb he hg
    (hp0 ⊙ hq0) (hp1 ⊙ hq1) (hp2 ⊙ hq2)
    (square_stack_dep P H00 H10 ha hc (sigT_map_eq F he) hp0 hp1 hq0 hq1 HH00 HH10)
    (square_stack_dep P H01 H11 hb hd (sigT_map_eq F hg) hp1 hp2 hq1 hq2 HH01 HH11) in
  let right := square_stack_dep P
    (square_compose H00 H01) (square_compose_map f H10 H11)
    (ha ⊙ hb) (hc ⊙ hd) (sigT_map_eq F (he ⊙ hg)) hp0 hp2 hq0 hq2
    (square_compose_dep P H00 H01 ha hb hc hd hp0 hp1 hp2 HH00 HH01)
    (square_compose_map_coherence_dep f P Q F H10 H11 hc hd he hg hq0 hq1 hq2 HH10 HH11) in
  rew [fun h => rew [fun t => rew [P] t in u0 = F z2 w2] h in
    ((hp0 ⊙ hq0) ⊙ sigT_map_eq F (he ⊙ hg)) = (ha ⊙ hb) ⊙ (hp2 ⊙ hq2)]
    square_interchange_map f H00 H01 H10 H11 in left = right.
Proof.
  destruct e, he, g, hg.
  revert a b c d H00 H01 H10 H11 ha hb hc hd HH00 HH01 HH10 HH11.
  revert p0 p1 p2 hp0 hp1 hp2.
  subst y0 y1 y2. cbn in hq0, hq1, hq2. subst v0 v1 v2.
  intros p0 p1 p2 hp0 hp1 hp2.
  subst x0 x1 x2. cbn in hp0, hp1, hp2. subst u0 u1 u2.
  intros a b c d H00 H01 H10 H11 ha hb hc hd HH00 HH01 HH10 HH11.
  cbn in H10, H11. subst c d.
  cbn in H00, H01. subst a b.
  cbn in *.
  revert HH00 HH01.
  generalize dependent hc.
  refine (homotopy_path_ind_r (fun h: F z0 w0 = F z0 w0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent hd.
  refine (homotopy_path_ind_r (fun h: F z0 w0 = F z0 w0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  intros HH00 HH01.
  generalize dependent ha.
  refine (homotopy_path_ind_r (fun h: F z0 w0 = F z0 w0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent hb.
  refine (homotopy_path_ind_r (fun h: F z0 w0 = F z0 w0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  now reflexivity.
Defined.

Lemma square_change_sides_compose_map {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p p': x0 = f y0} {q q': x1 = f y1} {r r': x2 = f y2}
  (Hp: p' = p) (Hq: q' = q) (Hr: r' = r)
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r):
  square_compose_map f (square_change_sides Hp H Hq) (square_change_sides Hq K Hr) =
  square_change_sides Hp (square_compose_map f H K) Hr.
Proof.
  destruct Hp, Hq, Hr.
  unfold square_change_sides.
  cbn [whisker_l whisker_r f_equal eq_sym eq_trans].
  now rewrite 3 eq_trans_refl_l.
Defined.

Lemma layer_square_map_source {Z V W T U X Y: Type}
  (L: Z -> V) (R: Z -> W) (f: V -> X) (g: W -> X) (d: T -> X)
  (k: forall z, f (L z) = g (R z))
  (F: X -> Y) (g0: T -> U) (j: U -> Y)
  (α: forall t, F (d t) = j (g0 t))
  {z0 z1: Z} (e: z0 = z1)
  {m: V} {n: W} (l: L z1 = m) (r: R z1 = n)
  {t0 t1: T} (b: t0 = t1) (c: f m = d t0) (c': g n = d t1)
  (H: hexagonal_coherence f d g l b r c (k z1) c'):
  let Nα := square_coherence_fill d g0 F j α b in
  square_map_along d g0 F j α b
    (layer_square_nat L R f g d k e l r b c c' H
      (square_coherence_fill L R f g k e)) Nα =
  square_change_sides (layer_cube_nat_side L f F e l c (α t0)) (square_stack
      (square_coherence_fill (fun z => f (L z)) (fun z => g (R z))
        F F (fun z => f_equal F (k z)) e)
      (layer_square_map d f g F g0 j α b l r c c' (k z1) H Nα))
    (layer_cube_nat_side R g F e r c' (α t1)).
Proof.
  destruct e, l, r, b.
  unfold layer_square_map, layer_square_nat, square_map_along, square_nat_along,
    layer_cube_nat_side, map_compose_tail.
  cbn.
  generalize H. unfold hexagonal_coherence. cbn [f_equal].
  generalize (α t0).
  generalize (k z0).
  generalize c', c.
  generalize (g (R z0)), (d t0), (j (g0 t0)).
  intros a z y s q t a0 H0.
  destruct q. subst a. cbn in H0. destruct H0.
  now destruct a0.
Defined.

Lemma layer_square_map_source_coherence_dep {Z V W T U X Y: Type}
  {PZ: Z -> Type} {PV: V -> Type} {PW: W -> Type} {PT: T -> Type}
  {PU: U -> Type} {PX: X -> Type} {PY: Y -> Type}
  (L: Z -> V) (R: Z -> W) (f: V -> X) (g: W -> X) (d: T -> X)
  (DL: forall z, PZ z -> PV (L z)) (DR: forall z, PZ z -> PW (R z))
  (DF: forall v, PV v -> PX (f v)) (DG: forall w, PW w -> PX (g w))
  (DT: forall t, PT t -> PX (d t))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [PX] k z in DF (L z) (DL z a) = DG (R z) (DR z a))
  (F: X -> Y) (g0: T -> U) (j: U -> Y)
  (FF: forall x, PX x -> PY (F x)) (GG: forall t, PT t -> PU (g0 t))
  (JJ: forall u, PU u -> PY (j u))
  (α: forall t, F (d t) = j (g0 t))
  (Hα: forall t a, rew [PY] α t in FF (d t) (DT t a) = JJ (g0 t) (GG t a))
  {z0 z1: Z} (e: z0 = z1) {m: V} {n: W}
  (l: L z1 = m) (r: R z1 = n)
  {t0 t1: T} (b: t0 = t1) (c: f m = d t0) (c': g n = d t1)
  (H: hexagonal_coherence f d g l b r c (k z1) c')
  {az0: PZ z0} {az1: PZ z1} {am: PV m} {an: PW n}
  {at0: PT t0} {at1: PT t1}
  (he: rew [PZ] e in az0 = az1) (hl: rew [PV] l in DL z1 az1 = am)
  (hr: rew [PW] r in DR z1 az1 = an) (hb: rew [PT] b in at0 = at1)
  (hc: rew [PX] c in DF m am = DT t0 at0)
  (hc': rew [PX] c' in DG n an = DT t1 at1)
  (HH: hexagonal_coherence_dep DF DT DG H hl hb hr hc (hk z1 az1) hc'):
  let npart := layer_square_nat L R f g d k e l r b c c' H
    (square_coherence_fill L R f g k e) in
  let dpart := layer_square_nat_coherence_dep L R f g d DL DR DF DG DT k hk
    e l r b c c' H he hl hr hb hc hc' HH in
  let Nα := square_coherence_fill d g0 F j α b in
  let dαinv := square_coherence_dep_reverse_fill d g0 F j
    DT GG FF JJ α Hα b hb in
  let left := sigT_map_eq DF (sigT_map_eq DL he ⊙ hl) ⊙ hc in
  let right := sigT_map_eq DG (sigT_map_eq DR he ⊙ hr) ⊙ hc' in
  let dleft := square_map_along_dep d g0 F j α PX PY FF b npart Nα
    (hk z0 az0) (sigT_map_eq DT hb) left right (Hα t0 at0) (Hα t1 at1)
    (sigT_map_eq JJ (sigT_map_eq GG hb)) dpart dαinv in
  let ne := square_coherence_fill (fun z => f (L z)) (fun z => g (R z))
    F F (fun z => f_equal F (k z)) e in
  let de := square_coherence_dep_fill (fun z => f (L z)) (fun z => g (R z)) F F
    (fun z a => DF (L z) (DL z a)) (fun z a => DG (R z) (DR z a)) FF FF
    (fun z => f_equal F (k z)) (fun z a => sigT_map_eq FF (hk z a)) e he in
  let nmapped := layer_square_map d f g F g0 j α b l r c c' (k z1) H Nα in
  let dmapped := layer_square_map_coherence_dep d f g F g0 j
    DT DF DG FF GG JJ α Hα b l r c c' (k z1) H hb hl hr hc hc' (hk z1 az1) HH in
  let left0 := sigT_map_eq FF (sigT_map_eq (fun z a => DF (L z) (DL z a)) he) in
  let right0 := sigT_map_eq FF (sigT_map_eq (fun z a => DG (R z) (DR z a)) he) in
  let left1 := sigT_map_eq FF (sigT_map_eq DF hl ⊙ hc) ⊙ Hα t0 at0 in
  let right1 := sigT_map_eq FF (sigT_map_eq DG hr ⊙ hc') ⊙ Hα t1 at1 in
  let leftfull := sigT_map_eq FF left ⊙ Hα t0 at0 in
  let rightfull := sigT_map_eq FF right ⊙ Hα t1 at1 in
  let dstack := square_stack_dep PY ne nmapped
    (sigT_map_eq FF (hk z0 az0)) (sigT_map_eq FF (hk z1 az1))
    (sigT_map_eq JJ (sigT_map_eq GG hb)) left0 right0 left1 right1 de dmapped in
  let dnormal := square_change_sides_dep PY
    (layer_cube_nat_side L f F e l c (α t0)) (square_stack ne nmapped)
    (layer_cube_nat_side R g F e r c' (α t1))
    (sigT_map_eq FF (hk z0 az0)) (sigT_map_eq JJ (sigT_map_eq GG hb))
    (left0 ⊙ left1) leftfull (right0 ⊙ right1) rightfull
    (layer_cube_nat_side_coherence_dep L f F DL DF FF e l c (α t0) he hl hc (Hα t0 at0)) dstack
    (layer_cube_nat_side_coherence_dep R g F DR DG FF e r c' (α t1) he hr hc' (Hα t1 at1)) in
  rew [fun h => rew [fun q => rew [PY] q in FF (f (L z0)) (DF (L z0) (DL z0 az0)) = JJ (g0 t1) (GG t1 at1)]
    h in (leftfull ⊙ sigT_map_eq JJ (sigT_map_eq GG hb)) =
      sigT_map_eq FF (hk z0 az0) ⊙ rightfull]
    layer_square_map_source L R f g d k F g0 j α e l r b c c' H in dleft = dnormal.
Proof.
  destruct e, he, l, hl, r, hr, b, hb.
  cbv in *.
  revert c c' H hc hc' HH.
  generalize (Hα t0 at0).
  generalize (α t0).
  generalize (JJ (g0 t0) (GG t0 at0)).
  generalize (j (g0 t0)).
  generalize (hk z0 az0).
  generalize (k z0).
  generalize (DG (R z0) (DR z0 az0)).
  generalize (g (R z0)).
  generalize (DT t0 at0).
  generalize (d t0).
  intros xd ad yg ag κ hκ zj aj aα hα c c' H hc hc' HH.
  destruct c, hc.
  revert κ hκ H HH. subst yg. intros κ hκ H HH.
  cbn in H. destruct H.
  revert hκ HH. destruct hc'. intros hκ HH.
  cbn in HH.
  change (eq_refl = f_equal (fun v => v) hκ) in HH.
  pose proof (HH • f_equal_id hκ) as K.
  revert HH. destruct K. intro HH.
  destruct aα, hα. cbn.
  pose (IX := fun q: (eq_refl: ag = ag) = eq_refl =>
    f_equal (fun p: ag = ag => p) q).
  pose (JX := fun q: (eq_refl: ag = ag) = eq_refl =>
    f_equal (fun p: ag = ag => f_equal (fun v => v) p) q).
  pose (bb := FF (f (L z0)) ag).
  pose (IY := fun q: (eq_refl: bb = bb) = eq_refl =>
    f_equal (fun p: bb = bb => p) q).
  pose (JY := fun q: (eq_refl: bb = bb) = eq_refl =>
    f_equal (fun p: bb = bb => f_equal (fun v => v) p) q).
  pose (M := fun q: (eq_refl: ag = ag) = eq_refl =>
    f_equal (fun p: ag = ag => f_equal (FF (f (L z0))) p) q).
  change (IY (IY (IY (IY (JY (IY (IY (M (IX (IX (IX (IX (JX HH)))))))))))) =
    IY (IY (IY (IY (JY (IY (IY (IY (IY (JY (IY (IY (M HH))))))))))))).
  unfold IX. rewrite 4 f_equal_id.
  unfold JX. rewrite f_equal_id_loop.
  unfold IY. rewrite 10 f_equal_id.
  unfold JY. now rewrite 2 f_equal_id_loop.
Defined.

Lemma square_nat_route {X Y: Type} (f: Y -> X)
  {x0 x1 x2 x3 y0 y1 y2 y3: X} {z0 z1 z2 z3: Y}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {c1: z0 = z1} {c2: z1 = z2} {c3: z2 = z3}
  {v0: x0 = y0} {v1: x1 = y1} {v2: x2 = y2} {v3: x3 = y3}
  {p0: y0 = f z0} {p1: y1 = f z1} {p2: y2 = f z2} {p3: y3 = f z3}
  {q0: x0 = f z0} {q1: x1 = f z1} {q2: x2 = f z2} {q3: x3 = f z3}
  (M0: q0 = v0 • p0) (M1: q1 = v1 • p1)
  (M2: q2 = v2 • p2) (M3: q3 = v3 • p3)
  (S1: v0 • b1 = a1 • v1) (S2: v1 • b2 = a2 • v2) (S3: v2 • b3 = a3 • v3)
  (H1: p0 • f_equal f c1 = b1 • p1)
  (H2: p1 • f_equal f c2 = b2 • p2)
  (H3: p2 • f_equal f c3 = b3 • p3):
  square_compose_map f (square_change_sides M0 (square_stack S1 H1) M1)
    (square_compose_map f (square_change_sides M1 (square_stack S2 H2) M2)
      (square_change_sides M2 (square_stack S3 H3) M3)) =
  square_change_sides M0
    (square_stack (square_compose S1 (square_compose S2 S3))
      (square_compose_map f H1 (square_compose_map f H2 H3))) M3.
Proof.
  rewrite 2 square_change_sides_compose_map.
  now rewrite 2 square_interchange_map.
Defined.

Lemma square_nat_route_coherence_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2 x3 y0 y1 y2 y3: X} {z0 z1 z2 z3: Y}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {c1: z0 = z1} {c2: z1 = z2} {c3: z2 = z3}
  {v0: x0 = y0} {v1: x1 = y1} {v2: x2 = y2} {v3: x3 = y3}
  {p0: y0 = f z0} {p1: y1 = f z1} {p2: y2 = f z2} {p3: y3 = f z3}
  {q0: x0 = f z0} {q1: x1 = f z1} {q2: x2 = f z2} {q3: x3 = f z3}
  {M0: q0 = v0 • p0} {M1: q1 = v1 • p1}
  {M2: q2 = v2 • p2} {M3: q3 = v3 • p3}
  {S1: v0 • b1 = a1 • v1} {S2: v1 • b2 = a2 • v2} {S3: v2 • b3 = a3 • v3}
  {H1: p0 • f_equal f c1 = b1 • p1}
  {H2: p1 • f_equal f c2 = b2 • p2}
  {H3: p2 • f_equal f c3 = b3 • p3}
  {ux0: P x0} {ux1: P x1} {ux2: P x2} {ux3: P x3}
  {uy0: P y0} {uy1: P y1} {uy2: P y2} {uy3: P y3}
  {uz0: Q z0} {uz1: Q z1} {uz2: Q z2} {uz3: Q z3}
  {ha1: rew [P] a1 in ux0 = ux1} {ha2: rew [P] a2 in ux1 = ux2}
  {ha3: rew [P] a3 in ux2 = ux3}
  {hb1: rew [P] b1 in uy0 = uy1} {hb2: rew [P] b2 in uy1 = uy2}
  {hb3: rew [P] b3 in uy2 = uy3}
  {hc1: rew [Q] c1 in uz0 = uz1} {hc2: rew [Q] c2 in uz1 = uz2}
  {hc3: rew [Q] c3 in uz2 = uz3}
  {hv0: rew [P] v0 in ux0 = uy0} {hv1: rew [P] v1 in ux1 = uy1}
  {hv2: rew [P] v2 in ux2 = uy2} {hv3: rew [P] v3 in ux3 = uy3}
  {hp0: rew [P] p0 in uy0 = F z0 uz0} {hp1: rew [P] p1 in uy1 = F z1 uz1}
  {hp2: rew [P] p2 in uy2 = F z2 uz2} {hp3: rew [P] p3 in uy3 = F z3 uz3}
  {hq0: rew [P] q0 in ux0 = F z0 uz0} {hq1: rew [P] q1 in ux1 = F z1 uz1}
  {hq2: rew [P] q2 in ux2 = F z2 uz2} {hq3: rew [P] q3 in ux3 = F z3 uz3}
  (DM0: rew [fun t => rew [P] t in ux0 = F z0 uz0] M0 in hq0 = hv0 ⊙ hp0)
  (DM1: rew [fun t => rew [P] t in ux1 = F z1 uz1] M1 in hq1 = hv1 ⊙ hp1)
  (DM2: rew [fun t => rew [P] t in ux2 = F z2 uz2] M2 in hq2 = hv2 ⊙ hp2)
  (DM3: rew [fun t => rew [P] t in ux3 = F z3 uz3] M3 in hq3 = hv3 ⊙ hp3)
  (DS1: rew [fun t => rew [P] t in ux0 = uy1] S1 in (hv0 ⊙ hb1) = ha1 ⊙ hv1)
  (DS2: rew [fun t => rew [P] t in ux1 = uy2] S2 in (hv1 ⊙ hb2) = ha2 ⊙ hv2)
  (DS3: rew [fun t => rew [P] t in ux2 = uy3] S3 in (hv2 ⊙ hb3) = ha3 ⊙ hv3)
  (DH1: rew [fun t => rew [P] t in uy0 = F z1 uz1] H1 in
    (hp0 ⊙ sigT_map_eq F hc1) = hb1 ⊙ hp1)
  (DH2: rew [fun t => rew [P] t in uy1 = F z2 uz2] H2 in
    (hp1 ⊙ sigT_map_eq F hc2) = hb2 ⊙ hp2)
  (DH3: rew [fun t => rew [P] t in uy2 = F z3 uz3] H3 in
    (hp2 ⊙ sigT_map_eq F hc3) = hb3 ⊙ hp3):
  let T1 := square_change_sides M0 (square_stack S1 H1) M1 in
  let T2 := square_change_sides M1 (square_stack S2 H2) M2 in
  let T3 := square_change_sides M2 (square_stack S3 H3) M3 in
  let DT1 := square_change_sides_dep P M0 (square_stack S1 H1) M1
    ha1 (sigT_map_eq F hc1) (hv0 ⊙ hp0) hq0 (hv1 ⊙ hp1) hq1 DM0
    (square_stack_dep P S1 H1 ha1 hb1 (sigT_map_eq F hc1) hv0 hv1 hp0 hp1 DS1 DH1) DM1 in
  let DT2 := square_change_sides_dep P M1 (square_stack S2 H2) M2
    ha2 (sigT_map_eq F hc2) (hv1 ⊙ hp1) hq1 (hv2 ⊙ hp2) hq2 DM1
    (square_stack_dep P S2 H2 ha2 hb2 (sigT_map_eq F hc2) hv1 hv2 hp1 hp2 DS2 DH2) DM2 in
  let DT3 := square_change_sides_dep P M2 (square_stack S3 H3) M3
    ha3 (sigT_map_eq F hc3) (hv2 ⊙ hp2) hq2 (hv3 ⊙ hp3) hq3 DM2
    (square_stack_dep P S3 H3 ha3 hb3 (sigT_map_eq F hc3) hv2 hv3 hp2 hp3 DS3 DH3) DM3 in
  let dleft := square_compose_map_coherence_dep f P Q F
    T1 (square_compose_map f T2 T3) ha1 (ha2 ⊙ ha3) hc1 (hc2 ⊙ hc3) hq0 hq1 hq3 DT1
    (square_compose_map_coherence_dep f P Q F T2 T3 ha2 ha3 hc2 hc3 hq1 hq2 hq3 DT2 DT3) in
  let SS := square_compose S1 (square_compose S2 S3) in
  let HH := square_compose_map f H1 (square_compose_map f H2 H3) in
  let DSS := square_compose_dep P S1 (square_compose S2 S3)
    ha1 (ha2 ⊙ ha3) hb1 (hb2 ⊙ hb3) hv0 hv1 hv3 DS1
    (square_compose_dep P S2 S3 ha2 ha3 hb2 hb3 hv1 hv2 hv3 DS2 DS3) in
  let DHH := square_compose_map_coherence_dep f P Q F
    H1 (square_compose_map f H2 H3) hb1 (hb2 ⊙ hb3) hc1 (hc2 ⊙ hc3) hp0 hp1 hp3 DH1
    (square_compose_map_coherence_dep f P Q F H2 H3 hb2 hb3 hc2 hc3 hp1 hp2 hp3 DH2 DH3) in
  let dright := square_change_sides_dep P M0 (square_stack SS HH) M3
    (ha1 ⊙ (ha2 ⊙ ha3)) (sigT_map_eq F (hc1 ⊙ (hc2 ⊙ hc3)))
    (hv0 ⊙ hp0) hq0 (hv3 ⊙ hp3) hq3 DM0
    (square_stack_dep P SS HH (ha1 ⊙ (ha2 ⊙ ha3)) (hb1 ⊙ (hb2 ⊙ hb3))
      (sigT_map_eq F (hc1 ⊙ (hc2 ⊙ hc3))) hv0 hv3 hp0 hp3 DSS DHH) DM3 in
  rew [fun h => rew [fun t => rew [P] t in ux0 = F z3 uz3] h in
    (hq0 ⊙ sigT_map_eq F (hc1 ⊙ (hc2 ⊙ hc3))) = (ha1 ⊙ (ha2 ⊙ ha3)) ⊙ hq3]
    square_nat_route f M0 M1 M2 M3 S1 S2 S3 H1 H2 H3 in dleft = dright.
Proof.
  subst q0 q1 q2 q3.
  cbn in DM0, DM1, DM2, DM3. subst hq0 hq1 hq2 hq3.
  destruct c1, hc1, c2, hc2, c3, hc3.
  revert a1 a2 a3 b1 b2 b3 S1 S2 S3 H1 H2 H3
    ha1 ha2 ha3 hb1 hb2 hb3 DS1 DS2 DS3 DH1 DH2 DH3.
  revert v0 v1 v2 v3 hv0 hv1 hv2 hv3.
  subst y0 y1 y2 y3. cbn in hp0, hp1, hp2, hp3. subst uy0 uy1 uy2 uy3.
  intros v0 v1 v2 v3 hv0 hv1 hv2 hv3.
  subst x0 x1 x2 x3. cbn in hv0, hv1, hv2, hv3. subst ux0 ux1 ux2 ux3.
  intros a1 a2 a3 b1 b2 b3 S1 S2 S3 H1 H2 H3
    ha1 ha2 ha3 hb1 hb2 hb3 DS1 DS2 DS3 DH1 DH2 DH3.
  cbn in H1, H2, H3. subst b1 b2 b3.
  cbn in S1, S2, S3. subst a1 a2 a3.
  cbn in *.
  revert DS1 DS2 DS3.
  generalize dependent hb1.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent hb2.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent hb3.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  intros DS1 DS2 DS3.
  generalize dependent ha1.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent ha2.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent ha3.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  now reflexivity.
Defined.

Lemma square_cube_rotate {X: Type} {x0 x1 x2 x3 y0 y1 y2 y3: X}
  {p: x0 = y0} {r: x1 = y1} {s: x2 = y2} {q: x3 = y3}
  {a0: x0 = x1} {a1: y0 = y1} {l0: x1 = x3} {l1: y1 = y3}
  {k0: x0 = x2} {k1: y0 = y2} {b0: x2 = x3} {b1: y2 = y3}
  {Na: p • a1 = a0 • r} {Nl: r • l1 = l0 • q}
  {Nk: p • k1 = k0 • s} {Nb: s • b1 = b0 • q}
  {Q0: a0 • l0 = k0 • b0} {Q1: a1 • l1 = k1 • b1}
  (C: square_cube (square_compose Na Nl) (square_compose Nk Nb) Q1 Q0):
  square_cube (square_compose (eq_sym Na) Q1)
    (square_compose Q0 (eq_sym Nb)) Nl Nk.
Proof.
  destruct p, a1, r, l1, q, s, b1.
  cbn in Na, Nl, Nk, Nb, Q1.
  subst a0 l0 k0 b0 k1.
  unfold square_cube, square_compose, whisker_l, whisker_r in *.
  cbn [eq_trans_assoc f_equal eq_trans eq_sym] in *.
  rewrite f_equal_id, eq_trans_refl_l in C.
  rewrite f_equal_id, 2 eq_trans_refl_l.
  now symmetry.
Defined.

Lemma square_cube_rotate_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 x2 x3 y0 y1 y2 y3: X}
  {p: x0 = y0} {r: x1 = y1} {s: x2 = y2} {q: x3 = y3}
  {a0: x0 = x1} {a1: y0 = y1} {l0: x1 = x3} {l1: y1 = y3}
  {k0: x0 = x2} {k1: y0 = y2} {b0: x2 = x3} {b1: y2 = y3}
  {Na: p • a1 = a0 • r} {Nl: r • l1 = l0 • q}
  {Nk: p • k1 = k0 • s} {Nb: s • b1 = b0 • q}
  {Q0: a0 • l0 = k0 • b0} {Q1: a1 • l1 = k1 • b1}
  (C: square_cube (square_compose Na Nl) (square_compose Nk Nb) Q1 Q0)
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  {v0: P y0} {v1: P y1} {v2: P y2} {v3: P y3}
  {hp: rew [P] p in u0 = v0} {hr: rew [P] r in u1 = v1}
  {hs: rew [P] s in u2 = v2} {hq: rew [P] q in u3 = v3}
  {ha0: rew [P] a0 in u0 = u1} {ha1: rew [P] a1 in v0 = v1}
  {hl0: rew [P] l0 in u1 = u3} {hl1: rew [P] l1 in v1 = v3}
  {hk0: rew [P] k0 in u0 = u2} {hk1: rew [P] k1 in v0 = v2}
  {hb0: rew [P] b0 in u2 = u3} {hb1: rew [P] b1 in v2 = v3}
  {HNa: rew [fun e => rew [P] e in u0 = v1] Na in (hp ⊙ ha1) = ha0 ⊙ hr}
  {HNl: rew [fun e => rew [P] e in u1 = v3] Nl in (hr ⊙ hl1) = hl0 ⊙ hq}
  {HNk: rew [fun e => rew [P] e in u0 = v2] Nk in (hp ⊙ hk1) = hk0 ⊙ hs}
  {HNb: rew [fun e => rew [P] e in u2 = v3] Nb in (hs ⊙ hb1) = hb0 ⊙ hq}
  {HQ0: rew [fun e => rew [P] e in u0 = u3] Q0 in (ha0 ⊙ hl0) = hk0 ⊙ hb0}
  {HQ1: rew [fun e => rew [P] e in v0 = v3] Q1 in (ha1 ⊙ hl1) = hk1 ⊙ hb1}
  (CC: square_cube_coherence_dep P (square_compose Na Nl) (square_compose Nk Nb)
    Q1 Q0 C (ha0 ⊙ hl0) (hk0 ⊙ hb0) (ha1 ⊙ hl1) (hk1 ⊙ hb1) hp hq
    (square_compose_dep P Na Nl _ _ _ _ _ _ _ HNa HNl)
    (square_compose_dep P Nk Nb _ _ _ _ _ _ _ HNk HNb) HQ1 HQ0):
  square_cube_coherence_dep P
    (square_compose (eq_sym Na) Q1) (square_compose Q0 (eq_sym Nb)) Nl Nk
    (square_cube_rotate C)
    (hp ⊙ hk1) (hk0 ⊙ hs) (hr ⊙ hl1) (hl0 ⊙ hq) ha0 hb1
    (square_compose_dep P (eq_sym Na) Q1 _ _ _ _ _ _ _ (sigT_sym_eq HNa) HQ1)
    (square_compose_dep P Q0 (eq_sym Nb) _ _ _ _ _ _ _ HQ0 (sigT_sym_eq HNb)) HNl HNk.
Proof.
  destruct p, a1, r, l1, q, s, b1.
  cbn in hp, ha1, hr, hl1, hq, hs, hb1.
  subst v0 v1 u1 v3 u3 v2 u2.
  cbn in Na, Nl, Nk, Nb, Q1.
  subst a0 l0 k0 b0 k1.
  unfold square_cube_coherence_dep, square_cube_rotate, square_cube,
    square_compose, whisker_l, whisker_r in *.
  cbn [eq_trans_assoc f_equal eq_trans eq_sym] in *.
  generalize dependent Q0.
  refine (homotopy_path_ind
    (fun h: @eq (x2 = x2) eq_refl eq_refl => eq_refl • f_equal (fun p => p) h)
    (fun h => eq_trans_refl_l (f_equal (fun p => p) h) • f_equal_id h) _ _).
  cbn. intros HQ0 CC.
  generalize dependent HQ1. generalize dependent ha1.
  refine (homotopy_path_ind (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. generalize dependent hk1.
  refine (homotopy_path_ind (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. generalize dependent hl0.
  refine (homotopy_path_ind_r (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. intros HQ0 HQ1 CC.
  generalize dependent HNb. generalize dependent hb0.
  refine (homotopy_path_ind_r (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. generalize dependent hb1.
  refine (homotopy_path_ind_r (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. intros HNb CC.
  pose proof (CC • f_equal_id _ •
    square_compose_dep_left_unit (P := P) (x := x2) (u := u0) HNb) as E.
  destruct E. now reflexivity.
Defined.

Lemma square_cube_collapse_map {X Y: Type} (f: Y -> X)
  {x0 x1: X} {y0 y1 y2 y3: Y}
  {a a': x0 = x1} {p: x0 = f y0} {q: x1 = f y3}
  {c: y0 = y1} {d: y1 = y3} {c': y0 = y2} {d': y2 = y3}
  {H: p • (f_equal f c • f_equal f d) = a • q}
  {K: p • (f_equal f c' • f_equal f d') = a' • q}
  {κ: c • d = c' • d'} {λ: a = a'}
  (C: square_cube H K (square_map f κ) λ): square_cube
    (whisker_l p (eq_trans_map_distr f c d) • H)
    (whisker_l p (eq_trans_map_distr f c' d') • K)
    (f_equal (fun e => f_equal f e) κ) λ.
Proof.
  destruct c, d, d'. cbn in κ. subst c'.
  unfold square_cube in C |- *.
  cbn in H, K, C |- *.
  rewrite (eq_trans_refl_l H), (eq_trans_refl_l K).
  now exact C.
Defined.

Lemma square_cube_collapse_map_coherence_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1: X} {y0 y1 y2 y3: Y}
  {a a': x0 = x1} {p: x0 = f y0} {q: x1 = f y3}
  {c: y0 = y1} {d: y1 = y3} {c': y0 = y2} {d': y2 = y3}
  {H: p • (f_equal f c • f_equal f d) = a • q}
  {K: p • (f_equal f c' • f_equal f d') = a' • q}
  {κ: c • d = c' • d'} {λ: a = a'}
  (C: square_cube H K (square_map f κ) λ)
  {u0: P x0} {u1: P x1} {v0: Q y0} {v1: Q y1} {v2: Q y2} {v3: Q y3}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y3 v3}
  {hc: rew [Q] c in v0 = v1} {hd: rew [Q] d in v1 = v3}
  {hc': rew [Q] c' in v0 = v2} {hd': rew [Q] d' in v2 = v3}
  {Hκ: rew [fun e => rew [Q] e in v0 = v3] κ in (hc ⊙ hd) = hc' ⊙ hd'}
  {Hλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  {HH: rew [fun e => rew [P] e in u0 = F y3 v3] H in
    (hp ⊙ (sigT_map_eq F hc ⊙ sigT_map_eq F hd)) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = F y3 v3] K in
    (hp ⊙ (sigT_map_eq F hc' ⊙ sigT_map_eq F hd')) = ha' ⊙ hq}
  (CC: square_cube_coherence_dep P H K (square_map f κ) λ C ha ha'
    (sigT_map_eq F hc ⊙ sigT_map_eq F hd)
    (sigT_map_eq F hc' ⊙ sigT_map_eq F hd') hp hq HH KK
    (square_map_dep f F κ hc' hd hc hd' Hκ) Hλ):
  square_cube_coherence_dep P
    (whisker_l p (eq_trans_map_distr f c d) • H)
    (whisker_l p (eq_trans_map_distr f c' d') • K)
    (f_equal (fun e => f_equal f e) κ) λ (square_cube_collapse_map f C)
    ha ha' (sigT_map_eq F (hc ⊙ hd)) (sigT_map_eq F (hc' ⊙ hd')) hp hq
    (square_collapse_map_dep f P Q F H HH) (square_collapse_map_dep f P Q F K KK) (sigT_map_eq
      (fun (e: y0 = y3) (h: rew [Q] e in v0 = v3) => sigT_map_eq F h) Hκ) Hλ.
Proof.
  destruct c, d, d'. cbn in κ. subst c'.
  destruct hc, hd. cbn in hd'. subst v2.
  generalize dependent hd'.
  refine (homotopy_path_ind_r (fun h: v0 = v0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. intros KK CC.
  destruct λ, Hλ.
  unfold square_cube_coherence_dep, square_cube, whisker_l, whisker_r in *.
  cbn [f_equal eq_trans] in C |- *.
  subst H. cbn in K. subst p.
  destruct a, ha.
  unfold square_collapse_map_dep. cbn in *.
  generalize dependent q.
  generalize (F y2 v0). generalize (f y2).
  intros z vz q hp hq KK HH CC.
  destruct q, hq. cbn in *.
  pose proof (eq_sym (f_equal_id HH) • CC • f_equal_id KK) as E.
  destruct E. now reflexivity.
Defined.

(** Paste a map prism and a naturality prism along their common side.
    Both supplied witnesses remain part of the resulting square cube. *)
Definition square_cube_glue_prisms {X Y: Type} (j: Y -> X)
  {f0 f1 g0 g1 fr0 fr1 gr0 gr1: X} {u0 u1 v0 v1: Y}
  {pF: f0 = fr0} {qF: f1 = fr1} {pG: g0 = gr0} {qG: g1 = gr1}
  {aF: f0 = f1} {aG: g0 = g1} {tF: fr0 = fr1} {tG: gr0 = gr1}
  {A0: f0 = g0} {A1: f1 = g1} {K0: fr0 = gr0} {K1: fr1 = gr1}
  {α0: fr0 = j u0} {α1: fr1 = j u1} {β0: gr0 = j v0} {β1: gr1 = j v1}
  {u: u0 = u1} {v: v0 = v1} {L0: u0 = v0} {L1: u1 = v1}
  (Hf: pF • tF = aF • qF) (Hg: pG • tG = aG • qG)
  (Np: pF • K0 = A0 • pG) (Nq: qF • K1 = A1 • qG)
  (Nm: tF • K1 = K0 • tG) (Na: aF • A1 = A0 • aG)
  (Nα: tF • α1 = α0 • f_equal j u)
  (Nβ: tG • β1 = β0 • f_equal j v)
  (Q0: α0 • f_equal j L0 = K0 • β0)
  (Q1: α1 • f_equal j L1 = K1 • β1)
  (NL: u • L1 = L0 • v)
  (NKH: square_cube (square_compose Hf Nq) (square_compose Np Hg) Nm Na)
  (NQ: square_cube (square_compose Nα (square_map j NL))
    (square_compose Nm Nβ) Q1 Q0): square_cube
    (square_compose_map j (square_stack Hf (eq_sym Nα)) (square_stack Nq Q1))
    (square_compose_map j (square_stack Np Q0) (square_stack Hg (eq_sym Nβ)))
    (f_equal (fun e => f_equal j e) NL) Na :=
  square_cube_change_faces
    (square_interchange_map j Hf Nq (eq_sym Nα) Q1)
    (square_cube_stack NKH (square_cube_collapse_map j (square_cube_rotate NQ)))
    (square_interchange_map j Np Hg Q0 (eq_sym Nβ)).

Lemma square_cube_glue_prisms_coherence_dep {X Y: Type} (j: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (J: forall y, Q y -> P (j y))
  {f0 f1 g0 g1 fr0 fr1 gr0 gr1: X} {u0 u1 v0 v1: Y} {pF: f0 = fr0} {qF: f1 = fr1} {pG: g0 = gr0} {qG: g1 = gr1}
  {aF: f0 = f1} {aG: g0 = g1} {tF: fr0 = fr1} {tG: gr0 = gr1} {A0: f0 = g0} {A1: f1 = g1} {K0: fr0 = gr0}
  {K1: fr1 = gr1}
  {α0: fr0 = j u0}
  {α1: fr1 = j u1}
  {β0: gr0 = j v0}
  {β1: gr1 = j v1} {u: u0 = u1} {v: v0 = v1} {L0: u0 = v0} {L1: u1 = v1}
  (Hf: pF • tF = aF • qF)
  (Hg: pG • tG = aG • qG)
  (Np: pF • K0 = A0 • pG)
  (Nq: qF • K1 = A1 • qG)
  (Nm: tF • K1 = K0 • tG)
  (Na: aF • A1 = A0 • aG)
  (Nα: tF • α1 = α0 • f_equal j u)
  (Nβ: tG • β1 = β0 • f_equal j v)
  (Q0: α0 • f_equal j L0 = K0 • β0)
  (Q1: α1 • f_equal j L1 = K1 • β1)
  (NL: u • L1 = L0 • v)
  (NKH: square_cube (square_compose Hf Nq) (square_compose Np Hg) Nm Na)
  (NQ: square_cube (square_compose Nα (square_map j NL))
    (square_compose Nm Nβ) Q1 Q0) {xf0: P f0} {xf1: P f1} {xg0: P g0} {xg1: P g1} {xfr0: P fr0} {xfr1: P fr1}
  {xgr0: P gr0} {xgr1: P gr1} {yu0: Q u0} {yu1: Q u1} {yv0: Q v0} {yv1: Q v1}
  {hpF: rew [P] pF in xf0 = xfr0}
  {hqF: rew [P] qF in xf1 = xfr1}
  {hpG: rew [P] pG in xg0 = xgr0}
  {hqG: rew [P] qG in xg1 = xgr1}
  {haF: rew [P] aF in xf0 = xf1}
  {haG: rew [P] aG in xg0 = xg1}
  {htF: rew [P] tF in xfr0 = xfr1}
  {htG: rew [P] tG in xgr0 = xgr1}
  {hA0: rew [P] A0 in xf0 = xg0}
  {hA1: rew [P] A1 in xf1 = xg1}
  {hK0: rew [P] K0 in xfr0 = xgr0}
  {hK1: rew [P] K1 in xfr1 = xgr1}
  {hα0: rew [P] α0 in xfr0 = (J u0 yu0)}
  {hα1: rew [P] α1 in xfr1 = (J u1 yu1)}
  {hβ0: rew [P] β0 in xgr0 = (J v0 yv0)}
  {hβ1: rew [P] β1 in xgr1 = (J v1 yv1)}
  {hu: rew [Q] u in yu0 = yu1}
  {hv: rew [Q] v in yv0 = yv1}
  {hL0: rew [Q] L0 in yu0 = yv0}
  {hL1: rew [Q] L1 in yu1 = yv1}
  {DHf: rew [fun e => rew [P] e in xf0 = xfr1] Hf in
    (hpF ⊙ htF) = haF ⊙ hqF}
  {DHg: rew [fun e => rew [P] e in xg0 = xgr1] Hg in
    (hpG ⊙ htG) = haG ⊙ hqG}
  {DNp: rew [fun e => rew [P] e in xf0 = xgr0] Np in
    (hpF ⊙ hK0) = hA0 ⊙ hpG}
  {DNq: rew [fun e => rew [P] e in xf1 = xgr1] Nq in
    (hqF ⊙ hK1) = hA1 ⊙ hqG}
  {DNm: rew [fun e => rew [P] e in xfr0 = xgr1] Nm in
    (htF ⊙ hK1) = hK0 ⊙ htG}
  {DNa: rew [fun e => rew [P] e in xf0 = xg1] Na in
    (haF ⊙ hA1) = hA0 ⊙ haG}
  {DNα: rew [fun e => rew [P] e in xfr0 = (J u1 yu1)] Nα in
    (htF ⊙ hα1) = hα0 ⊙ (sigT_map_eq J hu)}
  {DNβ: rew [fun e => rew [P] e in xgr0 = (J v1 yv1)] Nβ in
    (htG ⊙ hβ1) = hβ0 ⊙ (sigT_map_eq J hv)}
  {DQ0: rew [fun e => rew [P] e in xfr0 = (J v0 yv0)] Q0 in
    (hα0 ⊙ (sigT_map_eq J hL0)) = hK0 ⊙ hβ0}
  {DQ1: rew [fun e => rew [P] e in xfr1 = (J v1 yv1)] Q1 in
    (hα1 ⊙ (sigT_map_eq J hL1)) = hK1 ⊙ hβ1}
  {DNL: rew [fun e => rew [Q] e in yu0 = yv1] NL in
    (hu ⊙ hL1) = hL0 ⊙ hv}
  (D_NKH: square_cube_coherence_dep P (square_compose Hf Nq) (square_compose Np Hg)
    Nm Na NKH (haF ⊙ hA1) (hA0 ⊙ haG) (htF ⊙ hK1) (hK0 ⊙ htG) hpF hqG
    (square_compose_dep P Hf Nq _ _ _ _ _ _ _ DHf DNq)
    (square_compose_dep P Np Hg _ _ _ _ _ _ _ DNp DHg) DNm DNa)
  (D_NQ: square_cube_coherence_dep P
    (square_compose Nα (square_map j NL)) (square_compose Nm Nβ) Q1 Q0 NQ
    (hα0 ⊙ sigT_map_eq J hL0) (hK0 ⊙ hβ0)
    (hα1 ⊙ sigT_map_eq J hL1) (hK1 ⊙ hβ1) htF (sigT_map_eq J hv)
    (square_compose_dep P Nα (square_map j NL) _ _ _ _ _ _ _ DNα
      (square_map_dep j J NL hL0 hL1 hu hv DNL))
    (square_compose_dep P Nm Nβ _ _ _ _ _ _ _ DNm DNβ) DQ1 DQ0):
  square_cube_coherence_dep P
    (square_compose_map j (square_stack Hf (eq_sym Nα)) (square_stack Nq Q1))
    (square_compose_map j (square_stack Np Q0) (square_stack Hg (eq_sym Nβ)))
    (f_equal (fun e => f_equal j e) NL) Na
    (square_cube_glue_prisms j Hf Hg Np Nq Nm Na Nα Nβ Q0 Q1 NL NKH NQ)
    (haF ⊙ hA1) (hA0 ⊙ haG) (sigT_map_eq J (hu ⊙ hL1)) (sigT_map_eq J (hL0 ⊙ hv))
    (hpF ⊙ hα0) (hqG ⊙ hβ1)
    (square_compose_map_coherence_dep j P Q J _ _ _ _ _ _ _ _ _
      (square_stack_dep P Hf (eq_sym Nα) _ _ _ _ _ _ _ DHf (sigT_sym_eq DNα))
      (square_stack_dep P Nq Q1 _ _ _ _ _ _ _ DNq DQ1))
    (square_compose_map_coherence_dep j P Q J _ _ _ _ _ _ _ _ _
      (square_stack_dep P Np Q0 _ _ _ _ _ _ _ DNp DQ0)
      (square_stack_dep P Hg (eq_sym Nβ) _ _ _ _ _ _ _ DHg (sigT_sym_eq DNβ))) (sigT_map_eq
      (fun (e: u0 = v1) (h: rew [Q] e in yu0 = yv1) => sigT_map_eq J h) DNL) DNa.
Proof.
  unfold square_cube_glue_prisms.
  eapply square_cube_change_faces_coherence_dep.
  - now exact (square_interchange_map_coherence_dep j P Q J Hf Nq (eq_sym Nα) Q1
      _ _ _ _ _ _ _ _ _ _ _ _ DHf DNq (sigT_sym_eq DNα) DQ1).
  - eapply square_cube_stack_coherence_dep.
    + now exact D_NKH.
    + eapply square_cube_collapse_map_coherence_dep.
      now exact (square_cube_rotate_coherence_dep P NQ D_NQ).
  - now exact (square_interchange_map_coherence_dep j P Q J Np Hg Q0 (eq_sym Nβ)
      _ _ _ _ _ _ _ _ _ _ _ _ DNp DHg DQ0 (sigT_sym_eq DNβ)).
Defined.

Definition square_cube_inverse {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ: b = b'} {λ: a = a'} (C: square_cube H K κ λ):
  square_cube K H (eq_sym κ) (eq_sym λ) :=
  square_change_horizontal
    (eq_sym (eq_sym_map_distr (fun e => p • e) κ))
    (square_reverse C)
    (eq_sym (eq_sym_map_distr (fun e => e • q) λ)).

Lemma square_cube_inverse_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ: b = b'} {λ: a = a'} (C: square_cube H K κ λ)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (CC: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ):
  square_cube_coherence_dep P K H (eq_sym κ) (eq_sym λ) (square_cube_inverse C)
    ha' ha hb' hb hp hq KK HH (sigT_sym_eq Dκ) (sigT_sym_eq Dλ).
Proof.
  unfold square_cube_coherence_dep, square_cube_inverse.
  eapply (square_change_horizontal_dep (fun e => rew [P] e in u0 = v1)
    (eq_sym (eq_sym_map_distr (fun e => p • e) κ)) (square_reverse C)
    (eq_sym (eq_sym_map_distr (fun e => e • q) λ))).
  - now exact (sigT_map_eq_sym
      (fun (e: y0 = y1) (h: rew [P] e in v0 = v1) => hp ⊙ h) Dκ).
  - now exact (square_reverse_dep (fun e => rew [P] e in u0 = v1) C CC).
  - now exact (sigT_map_eq_sym
      (fun (e: x0 = x1) (h: rew [P] e in u0 = u1) => h ⊙ hq) Dλ).
Defined.

Lemma map_compose_path {A B C: Type} (f: B -> C) (g: A -> B)
  {a b: A} (e: a = b):
  f_equal (fun z => f (g z)) e = f_equal f (f_equal g e).
Proof. now destruct e. Defined.

Lemma square_map_left_unit {X Y: Type} (f: X -> Y) {x y: X} (p: x = y):
  @square_map X Y f x y x y p p eq_refl eq_refl (eq_trans_refl_l p) =
  eq_trans_refl_l (f_equal f p).
Proof. now destruct p. Defined.

Lemma square_coherence_map_edges {A B C D E: Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D) (F: D -> E)
  (K: forall a, f (u a) = g (v a)) {a b: A} (e: a = b):
  square_map F (square_coherence_fill u v f g K e) =
  square_change_sides
    (f_equal (fun p => f_equal F p) (eq_sym (map_compose_path f u e)))
    (square_coherence_fill (fun z => f (u z)) (fun z => g (v z)) F F
      (fun z => f_equal F (K z)) e)
    (f_equal (fun p => f_equal F p) (eq_sym (map_compose_path g v e))).
Proof.
  destruct e.
  cbn [square_coherence_fill map_compose_path f_equal eq_sym].
  unfold square_change_sides.
  cbn [whisker_l whisker_r f_equal eq_sym eq_trans].
  now exact (square_map_left_unit F (K a) •
    eq_sym (eq_trans_refl_l (eq_trans_refl_l (f_equal F (K a))))).
Defined.

Lemma square_coherence_precompose {A B C D E: Type}
  (w: A -> B) (u: B -> C) (v: B -> D) (f: C -> E) (g: D -> E)
  (K: forall b, f (u b) = g (v b)) {a b: A} (e: a = b):
  square_coherence_fill u v f g K (f_equal w e) =
  square_change_sides
    (f_equal (fun p => f_equal f p) (eq_sym (map_compose_path u w e)))
    (square_coherence_fill (fun z => u (w z)) (fun z => v (w z)) f g
      (fun z => K (w z)) e)
    (f_equal (fun p => f_equal g p) (eq_sym (map_compose_path v w e))).
Proof.
  destruct e.
  cbn [square_coherence_fill map_compose_path f_equal eq_sym].
  unfold square_change_sides.
  cbn [whisker_l whisker_r f_equal eq_sym eq_trans].
  now exact (eq_sym (eq_trans_refl_l (eq_trans_refl_l (K (w a))))).
Defined.

Lemma square_change_sides_compose {X: Type} {x0 x1 x2 y0 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p p': x0 = y0} {q q': x1 = y1} {r r': x2 = y2}
  (Hp: p' = p) (Hq: q' = q) (Hr: r' = r)
  (H: p • c = a • q) (K: q • d = b • r):
  square_compose (square_change_sides Hp H Hq) (square_change_sides Hq K Hr) =
  square_change_sides Hp (square_compose H K) Hr.
Proof.
  destruct Hp, Hq, Hr. unfold square_change_sides.
  cbn [whisker_l whisker_r f_equal eq_sym eq_trans].
  now rewrite 3 eq_trans_refl_l.
Defined.

Lemma square_map_along_twice {T X U Y V Z: Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (r1: U -> Y)
  (α: forall t, f (r t) = r1 (g t))
  (g1: U -> V) (F: Y -> Z) (j: V -> Z)
  (β: forall u, F (r1 u) = j (g1 u))
  {t0 t1: T} (e: t0 = t1) {x0 x1: X} {a: x0 = x1}
  {p: x0 = r t0} {q: x1 = r t1} (H: p • f_equal r e = a • q):
  let Nα := square_coherence_fill r g f r1 α e in
  let Nβ := square_coherence_fill r1 g1 F j β (f_equal g e) in
  square_map_along r1 g1 F j β (f_equal g e)
    (square_map_along r g f r1 α e H Nα) Nβ =
  square_change_sides (map_compose_tail F (f_equal f p) (α t0) (β (g t0)))
    (square_stack (square_map F (square_map f H))
      (eq_sym (square_compose (square_map F Nα) Nβ)))
    (map_compose_tail F (f_equal f q) (α t1) (β (g t1))).
Proof.
  destruct e.
  generalize H. generalize a. generalize p, q. generalize x0, x1.
  intros a0 a1 p0 p1. subst a0 a1.
  intros l H0. cbn in H0. destruct H0.
  unfold square_map_along, map_compose_tail.
  cbn.
  generalize (β (g t0)), (α t0).
  generalize (r1 (g t0)), (j (g1 (g t0))).
  intros z0 z1 b0 a0.
  now destruct a0, b0.
Defined.

Lemma hexagonal_prism_map_square_cube {A1 A2 A3 B U V C: Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (u: B -> U) (v: B -> V) (f: U -> C) (g: V -> C)
  (K: forall b, f (u b) = g (v b))
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  (p1: x0 = x1) (p2: x2 = x3) (p3: x4 = x5)
  (h1: f1 x1 = f2 x2) (h2: f1 x0 = f3 x4) (h3: f3 x5 = f2 x3)
  (H: hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3)
  (N: hexagonal_prism_coherence_map f1 f2 f3 u v f g K p1 p2 p3 h1 h2 h3 H):
  let Hrect := H in
  let Np := square_coherence_fill u v f g K (f_equal f1 p1 • h1) in
  let Nq := square_coherence_fill u v f g K (f_equal f3 p3 • h3) in
  let Nb := square_coherence_fill u v f g K (f_equal f2 p2) in
  let Na := square_coherence_fill u v f g K h2 in square_cube
    (square_compose (square_map f (square_map u Hrect)) Nq)
    (square_compose Np (square_map g (square_map v Hrect))) Nb Na.
Proof.
  unfold hexagonal_prism_coherence_map, hexagonal_prism_coherence in N.
  revert N. generalize H. unfold hexagonal_coherence.
  generalize (f_equal f1 p1), h1, (f_equal f2 p2), h2, (f_equal f3 p3), h3.
  generalize (f1 x0), (f1 x1), (f2 x2), (f2 x3), (f3 x4), (f3 x5).
  intros y0 y1 y2 y3 y4 y5 r1 r2 r3 s1 s2 s3 h.
  destruct r2, r3, s2, s3, s1.
  cbn in h. subst r1. cbn.
  generalize (K y0). generalize (g (v y0)).
  intros z k. destruct k. intro n.
  now exact n.
Defined.

Definition square_cube_change_caps {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ κ': b = b'} {λ λ': a = a'}
  (C: square_cube H K κ λ) (Eκ: κ = κ') (Eλ: λ = λ'):
  square_cube H K κ' λ'.
Proof. destruct Eκ, Eλ. now exact C. Defined.

Lemma square_cube_change_caps_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q}
  {κ κ': b = b'} {λ λ': a = a'}
  (C: square_cube H K κ λ) (Eκ: κ = κ') (Eλ: λ = λ')
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dκ': rew [fun e => rew [P] e in v0 = v1] κ' in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  {Dλ': rew [fun e => rew [P] e in u0 = u1] λ' in ha = ha'}
  (CC: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ)
  (EEκ: rew [fun k => rew [fun e => rew [P] e in v0 = v1] k in hb = hb'] Eκ in Dκ = Dκ')
  (EEλ: rew [fun l => rew [fun e => rew [P] e in u0 = u1] l in ha = ha'] Eλ in Dλ = Dλ'):
  square_cube_coherence_dep P H K κ' λ' (square_cube_change_caps C Eκ Eλ)
    ha ha' hb hb' hp hq HH KK Dκ' Dλ'.
Proof.
  destruct Eκ, Eλ. cbn in EEκ, EEλ. destruct EEκ, EEλ. now exact CC.
Defined.

Definition square_cube_inverse_map {X Y: Type} (f: Y -> X)
  {x0 x1: X} {y0 y1: Y}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  {H: p • f_equal f b = a • q} {K: p • f_equal f b' = a' • q}
  {κ: b = b'} {λ: a = a'}
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ):
  square_cube K H (f_equal (fun e => f_equal f e) (eq_sym κ)) (eq_sym λ) :=
  square_cube_change_caps
    (square_cube_inverse C)
    (eq_sym_map_distr (fun e => f_equal f e) κ) eq_refl.

Lemma square_cube_inverse_map_coherence_dep {X Y: Type}
  (f: Y -> X) (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1: X} {y0 y1: Y} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = f y0} {q: x1 = f y1}
  {H: p • f_equal f b = a • q} {K: p • f_equal f b' = a' • q}
  {κ: b = b'} {λ: a = a'} {C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ}
  {u0: P x0} {u1: P x1} {v0: Q y0} {v1: Q y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [Q] b in v0 = v1} {hb': rew [Q] b' in v0 = v1}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  {HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in (hp ⊙ sigT_map_eq F hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = F y1 v1] K in (hp ⊙ sigT_map_eq F hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [Q] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (CC: square_cube_coherence_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq F hb) (sigT_map_eq F hb') hp hq HH KK
    (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dκ) Dλ):
  square_cube_coherence_dep P K H (f_equal (fun e => f_equal f e) (eq_sym κ)) (eq_sym λ)
    (square_cube_inverse_map f C)
    ha' ha (sigT_map_eq F hb') (sigT_map_eq F hb) hp hq KK HH
    (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) (sigT_sym_eq Dκ))
      (sigT_sym_eq Dλ).
Proof.
  unfold square_cube_inverse_map.
  eapply square_cube_change_caps_coherence_dep.
  - now exact (square_cube_inverse_coherence_dep P C CC).
  - now exact (sigT_sym_eq_map
      (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dκ).
  - now reflexivity.
Defined.

Lemma square_change_sides_route {X: Type} {x0 x1 x2 x3 y0 y1 y2 y3: X}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {p0 q0: x0 = y0} {p1 q1: x1 = y1} {p2 q2: x2 = y2} {p3 q3: x3 = y3}
  (M0: q0 = p0) (M1: q1 = p1) (M2: q2 = p2) (M3: q3 = p3)
  (S1: p0 • b1 = a1 • p1) (S2: p1 • b2 = a2 • p2) (S3: p2 • b3 = a3 • p3):
  square_compose (square_change_sides M0 S1 M1)
    (square_compose (square_change_sides M1 S2 M2) (square_change_sides M2 S3 M3)) =
  square_change_sides M0 (square_compose S1 (square_compose S2 S3)) M3.
Proof. now rewrite 2 square_change_sides_compose. Defined.

Definition square_cube_trans_map {X Y: Type} (f: Y -> X)
  {x0 x1: X} {y0 y1: Y} {a a' a'': x0 = x1} {b b' b'': y0 = y1}
  {p: x0 = f y0} {q: x1 = f y1}
  {H: p • f_equal f b = a • q} {K: p • f_equal f b' = a' • q}
  {L: p • f_equal f b'' = a'' • q}
  {κ: b = b'} {λ: a = a'} {μ: b' = b''} {ν: a' = a''}
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ)
  (D: square_cube K L (f_equal (fun e => f_equal f e) μ) ν):
  square_cube H L (f_equal (fun e => f_equal f e) (κ • μ)) (λ • ν) :=
  square_cube_change_caps (square_cube_trans C D)
    (eq_sym (eq_trans_map_distr (fun e => f_equal f e) κ μ)) eq_refl.

Lemma square_cube_trans_map_coherence_dep {X Y: Type}
  (f: Y -> X) (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1: X} {y0 y1: Y} {a a' a'': x0 = x1} {b b' b'': y0 = y1}
  {p: x0 = f y0} {q: x1 = f y1}
  {H: p • f_equal f b = a • q} {K: p • f_equal f b' = a' • q} {L: p • f_equal f b'' = a'' • q}
  {κ: b = b'} {λ: a = a'} {μ: b' = b''} {ν: a' = a''}
  {C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ} {D: square_cube K L (f_equal (fun e =>
    f_equal f e) μ) ν}
  {u0: P x0} {u1: P x1} {v0: Q y0} {v1: Q y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {ha'': rew [P] a'' in u0 = u1}
  {hb: rew [Q] b in v0 = v1} {hb': rew [Q] b' in v0 = v1}
  {hb'': rew [Q] b'' in v0 = v1}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  {HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in (hp ⊙ sigT_map_eq F hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = F y1 v1] K in (hp ⊙ sigT_map_eq F hb') = ha' ⊙ hq}
  {LL: rew [fun e => rew [P] e in u0 = F y1 v1] L in (hp ⊙ sigT_map_eq F hb'') = ha'' ⊙ hq}
  {Dκ: rew [fun e => rew [Q] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  {Dμ: rew [fun e => rew [Q] e in v0 = v1] μ in hb' = hb''}
  {Dν: rew [fun e => rew [P] e in u0 = u1] ν in ha' = ha''}
  (CC: square_cube_coherence_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq F hb) (sigT_map_eq F hb') hp hq HH KK
    (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dκ) Dλ)
  (DD: square_cube_coherence_dep P K L (f_equal (fun e => f_equal f e) μ) ν D
    ha' ha'' (sigT_map_eq F hb') (sigT_map_eq F hb'') hp hq KK LL
    (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dμ) Dν):
  square_cube_coherence_dep P H L (f_equal (fun e => f_equal f e) (κ • μ)) (λ • ν)
    (square_cube_trans_map f C D)
    ha ha'' (sigT_map_eq F hb) (sigT_map_eq F hb'') hp hq HH LL
    (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) (Dκ ⊙ Dμ)) (Dλ ⊙ Dν).
Proof.
  unfold square_cube_trans_map.
  eapply square_cube_change_caps_coherence_dep.
  - now exact (square_cube_trans_coherence_dep P C D CC DD).
  - now exact (sigT_sym_eq (sigT_map_eq_comp
      (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dκ Dμ)).
  - now reflexivity.
Defined.

Definition square_cube_whisker_r {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a a': x0 = x1} {b b': y0 = y1} {d: x1 = x2} {c: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {H: p • f_equal f b = a • q} {K: p • f_equal f b' = a' • q}
  (S: q • f_equal f c = d • r) {κ: b = b'} {λ: a = a'}
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ):
  square_cube (square_compose_map f H S) (square_compose_map f K S)
    (f_equal (fun e => f_equal f e) (whisker_r κ c)) (whisker_r λ d) :=
  square_cube_compose_map f (μ := eq_refl) C (square_cube_refl S).

Lemma square_cube_whisker_r_coherence_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a a': x0 = x1} {b b': y0 = y1} {d: x1 = x2} {c: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {H: p • f_equal f b = a • q} {K: p • f_equal f b' = a' • q}
  {S: q • f_equal f c = d • r} {κ: b = b'} {λ: a = a'}
  {C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ}
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: Q y0} {v1: Q y1} {v2: Q y2}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [Q] b in v0 = v1} {hb': rew [Q] b' in v0 = v1}
  {hd: rew [P] d in u1 = u2} {hc: rew [Q] c in v1 = v2}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  {hr: rew [P] r in u2 = F y2 v2}
  {HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ sigT_map_eq F hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = F y1 v1] K in
    (hp ⊙ sigT_map_eq F hb') = ha' ⊙ hq}
  (SS: rew [fun e => rew [P] e in u1 = F y2 v2] S in
    (hq ⊙ sigT_map_eq F hc) = hd ⊙ hr)
  {Dκ: rew [fun e => rew [Q] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (CC: square_cube_coherence_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq F hb) (sigT_map_eq F hb') hp hq HH KK (sigT_map_eq
      (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => sigT_map_eq F h) Dκ) Dλ):
  let Wκ := sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in v0 = v1) => h ⊙ hc) Dκ in
  let Wλ := sigT_map_eq (fun (e: x0 = x1) (h: rew [P] e in u0 = u1) => h ⊙ hd) Dλ in
  square_cube_coherence_dep P (square_compose_map f H S) (square_compose_map f K S)
    (f_equal (fun e => f_equal f e) (whisker_r κ c)) (whisker_r λ d)
    (square_cube_whisker_r f S C)
    (ha ⊙ hd) (ha' ⊙ hd) (sigT_map_eq F (hb ⊙ hc)) (sigT_map_eq F (hb' ⊙ hc)) hp hr
    (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ HH SS)
    (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ KK SS) (sigT_map_eq
      (fun (e: y0 = y2) (h: rew [Q] e in v0 = v2) => sigT_map_eq F h) Wκ) Wλ.
Proof.
  intros Wκ Wλ. unfold square_cube_whisker_r.
  eapply (square_cube_change_caps_coherence_dep P _ eq_refl eq_refl).
  - now exact (square_cube_compose_map_coherence_dep f P Q F
      (μ := eq_refl) (Dμ := eq_refl) C (square_cube_refl S)
      CC (square_cube_refl_coherence_dep P S SS)).
  - now exact (f_equal
      (fun h => sigT_map_eq
        (fun (e: y0 = y2) (h: rew [Q] e in v0 = v2) => sigT_map_eq F h) h)
      (sigT_trans_eq_unit_r Wκ)).
  - now exact (sigT_trans_eq_unit_r Wλ).
Defined.

Definition square_cube_whisker_l {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {d: x0 = x1} {c: y0 = y1} {a a': x1 = x2} {b b': y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (S: p • f_equal f c = d • q)
  {H: q • f_equal f b = a • r} {K: q • f_equal f b' = a' • r}
  {κ: b = b'} {λ: a = a'}
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ):
  square_cube (square_compose_map f S H) (square_compose_map f S K)
    (f_equal (fun e => f_equal f e) (whisker_l c κ)) (whisker_l d λ) :=
  square_cube_change_caps
    (square_cube_compose_map f (κ := eq_refl) (square_cube_refl S) C)
    (f_equal (fun H => f_equal (fun e => f_equal f e) H)
      (eq_trans_refl_l (whisker_l c κ)))
    (eq_trans_refl_l (whisker_l d λ)).

Lemma square_cube_whisker_l_coherence_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {d: x0 = x1} {c: y0 = y1} {a a': x1 = x2} {b b': y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {S: p • f_equal f c = d • q}
  {H: q • f_equal f b = a • r} {K: q • f_equal f b' = a' • r}
  {κ: b = b'} {λ: a = a'}
  {C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ}
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: Q y0} {v1: Q y1} {v2: Q y2}
  {hd: rew [P] d in u0 = u1} {hc: rew [Q] c in v0 = v1}
  {ha: rew [P] a in u1 = u2} {ha': rew [P] a' in u1 = u2}
  {hb: rew [Q] b in v1 = v2} {hb': rew [Q] b' in v1 = v2}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  {hr: rew [P] r in u2 = F y2 v2}
  (SS: rew [fun e => rew [P] e in u0 = F y1 v1] S in
    (hp ⊙ sigT_map_eq F hc) = hd ⊙ hq)
  {HH: rew [fun e => rew [P] e in u1 = F y2 v2] H in
    (hq ⊙ sigT_map_eq F hb) = ha ⊙ hr}
  {KK: rew [fun e => rew [P] e in u1 = F y2 v2] K in
    (hq ⊙ sigT_map_eq F hb') = ha' ⊙ hr}
  {Dκ: rew [fun e => rew [Q] e in v1 = v2] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u1 = u2] λ in ha = ha'}
  (CC: square_cube_coherence_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq F hb) (sigT_map_eq F hb') hq hr HH KK (sigT_map_eq
      (fun (e: y1 = y2) (h: rew [Q] e in v1 = v2) => sigT_map_eq F h) Dκ) Dλ):
  let Wκ := sigT_map_eq (fun (e: y1 = y2) (h: rew [Q] e in v1 = v2) => hc ⊙ h) Dκ in
  let Wλ := sigT_map_eq (fun (e: x1 = x2) (h: rew [P] e in u1 = u2) => hd ⊙ h) Dλ in
  square_cube_coherence_dep P (square_compose_map f S H) (square_compose_map f S K)
    (f_equal (fun e => f_equal f e) (whisker_l c κ)) (whisker_l d λ)
    (square_cube_whisker_l f S C)
    (hd ⊙ ha) (hd ⊙ ha') (sigT_map_eq F (hc ⊙ hb)) (sigT_map_eq F (hc ⊙ hb')) hp hr
    (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ SS HH)
    (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ SS KK) (sigT_map_eq
      (fun (e: y0 = y2) (h: rew [Q] e in v0 = v2) => sigT_map_eq F h) Wκ) Wλ.
Proof.
  intros Wκ Wλ. unfold square_cube_whisker_l.
  eapply square_cube_change_caps_coherence_dep.
  - now exact (square_cube_compose_map_coherence_dep f P Q F
      (κ := eq_refl) (Dκ := eq_refl) (square_cube_refl S) C
      (square_cube_refl_coherence_dep P S SS) CC).
  - now exact (sigT_map_eq
      (fun (e: c • b = c • b')
        (h: rew [fun p => rew [Q] p in v0 = v2] e in (hc ⊙ hb) = hc ⊙ hb') =>
        sigT_map_eq (fun (p: y0 = y2) (h: rew [Q] p in v0 = v2) => sigT_map_eq F h) h)
      (sigT_trans_eq_unit_l Wκ)).
  - now exact (sigT_trans_eq_unit_l Wλ).
Defined.

Lemma square_compose_map_assoc {X Y: Type} (f: Y -> X)
  {x0 x1 x2 x3: X} {y0 y1 y2 y3: Y}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {p0: x0 = f y0} {p1: x1 = f y1} {p2: x2 = f y2} {p3: x3 = f y3}
  (H1: p0 • f_equal f b1 = a1 • p1)
  (H2: p1 • f_equal f b2 = a2 • p2)
  (H3: p2 • f_equal f b3 = a3 • p3): square_cube
    (square_compose_map f H1 (square_compose_map f H2 H3))
    (square_compose_map f (square_compose_map f H1 H2) H3)
    (f_equal (fun e => f_equal f e) (eq_trans_assoc b1 b2 b3))
    (eq_trans_assoc a1 a2 a3).
Proof.
  destruct b1, b2, b3.
  generalize H1, H2, H3. generalize a1, a2, a3.
  generalize p0, p1, p2, p3. generalize x0, x1, x2, x3.
  intros u0 u1 u2 u3 q0 q1 q2 q3. subst u0 u1 u2 u3.
  intros c1 c2 c3 K1 K2 K3. cbn in K1, K2, K3. destruct K1, K2, K3.
  now reflexivity.
Defined.

Lemma square_compose_map_assoc_coherence_dep {X Y: Type}
  (f: Y -> X) (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2 x3: X} {y0 y1 y2 y3: Y}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {p0: x0 = f y0} {p1: x1 = f y1} {p2: x2 = f y2} {p3: x3 = f y3}
  {H1: p0 • f_equal f b1 = a1 • p1}
  {H2: p1 • f_equal f b2 = a2 • p2}
  {H3: p2 • f_equal f b3 = a3 • p3}
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  {v0: Q y0} {v1: Q y1} {v2: Q y2} {v3: Q y3}
  {ha1: rew [P] a1 in u0 = u1} {ha2: rew [P] a2 in u1 = u2}
  {ha3: rew [P] a3 in u2 = u3}
  {hb1: rew [Q] b1 in v0 = v1} {hb2: rew [Q] b2 in v1 = v2}
  {hb3: rew [Q] b3 in v2 = v3}
  {hp0: rew [P] p0 in u0 = F y0 v0} {hp1: rew [P] p1 in u1 = F y1 v1}
  {hp2: rew [P] p2 in u2 = F y2 v2} {hp3: rew [P] p3 in u3 = F y3 v3}
  (HH1: rew [fun e => rew [P] e in u0 = F y1 v1] H1 in
    (hp0 ⊙ sigT_map_eq F hb1) = ha1 ⊙ hp1)
  (HH2: rew [fun e => rew [P] e in u1 = F y2 v2] H2 in
    (hp1 ⊙ sigT_map_eq F hb2) = ha2 ⊙ hp2)
  (HH3: rew [fun e => rew [P] e in u2 = F y3 v3] H3 in
    (hp2 ⊙ sigT_map_eq F hb3) = ha3 ⊙ hp3):
  square_cube_coherence_dep P
    (square_compose_map f H1 (square_compose_map f H2 H3))
    (square_compose_map f (square_compose_map f H1 H2) H3)
    (f_equal (fun e => f_equal f e) (eq_trans_assoc b1 b2 b3))
    (eq_trans_assoc a1 a2 a3) (square_compose_map_assoc f H1 H2 H3)
    (ha1 ⊙ (ha2 ⊙ ha3)) ((ha1 ⊙ ha2) ⊙ ha3)
    (sigT_map_eq F (hb1 ⊙ (hb2 ⊙ hb3))) (sigT_map_eq F ((hb1 ⊙ hb2) ⊙ hb3)) hp0 hp3
    (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ HH1
      (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ HH2 HH3))
    (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _
      (square_compose_map_coherence_dep f P Q F _ _ _ _ _ _ _ _ _ HH1 HH2) HH3) (sigT_map_eq
      (fun (e: y0 = y3) (h: rew [Q] e in v0 = v3) => sigT_map_eq F h)
      (sigT_trans_eq_assoc_l hb1 hb2 hb3))
    (sigT_trans_eq_assoc_l ha1 ha2 ha3).
Proof.
  destruct b1, b2, b3, hb1, hb2, hb3.
  unfold square_cube_coherence_dep, square_compose_map_assoc,
    square_compose_map_coherence_dep, square_compose_map.
  cbn in H1, H2, H3 |- *.
  subst p0 p1 p2.
  destruct a1, a2, a3, ha1, ha2, ha3.
  cbn in *.
  generalize dependent p3.
  generalize (F y0 v0). generalize (f y0).
  intros z vz p3 hp2 hp0 hp1 hp3 HH3 HH1 HH2.
  destruct p3, hp3. cbn in *.
  revert HH1. generalize dependent hp2.
  refine (homotopy_path_ind (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. intro HH2. generalize dependent hp1.
  refine (homotopy_path_ind (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  cbn. intro HH1. generalize dependent hp0.
  refine (homotopy_path_ind (fun h: u0 = u0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  now reflexivity.
Defined.

Lemma square_map_along_compose {T X U Y: Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (α: forall t, f (r t) = j (g t))
  {t0 t1 t2: T} (b1: t0 = t1) (b2: t1 = t2)
  {x0 x1 x2: X} {a1: x0 = x1} {a2: x1 = x2}
  {p0: x0 = r t0} {p1: x1 = r t1} {p2: x2 = r t2}
  (H1: p0 • f_equal r b1 = a1 • p1) (H2: p1 • f_equal r b2 = a2 • p2): square_cube
    (square_map_along r g f j α (b1 • b2) (square_compose_map r H1 H2)
      (square_coherence_fill r g f j α (b1 • b2)))
    (square_compose_map j
      (square_map_along r g f j α b1 H1 (square_coherence_fill r g f j α b1))
      (square_map_along r g f j α b2 H2 (square_coherence_fill r g f j α b2)))
    (f_equal (fun e => f_equal j e) (eq_trans_map_distr g b1 b2))
    (eq_trans_map_distr f a1 a2).
Proof.
  destruct b1, b2.
  generalize H1, H2. generalize a1, a2. generalize p0, p1, p2.
  generalize x0, x1, x2.
  intros u0 u1 u2 q0 q1 q2. subst u0 u1 u2.
  intros c1 c2 K1 K2. cbn in K1, K2. destruct K1, K2.
  unfold square_map_along, square_compose_map.
  cbn. generalize (α t0). generalize (j (g t0)).
  intros z k. now destruct k.
Defined.

Lemma square_map_along_compose_coherence_dep {T X U Y: Type}
  {PT: T -> Type} {PX: X -> Type} {PU: U -> Type} {PY: Y -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (J: forall u, PU u -> PY (j u))
  (α: forall t, f (r t) = j (g t))
  (Hα: forall t a, rew [PY] α t in F (r t) (R t a) = J (g t) (G t a))
  {t0 t1 t2: T} {b1: t0 = t1} {b2: t1 = t2}
  {x0 x1 x2: X} {a1: x0 = x1} {a2: x1 = x2}
  {p0: x0 = r t0} {p1: x1 = r t1} {p2: x2 = r t2}
  {H1: p0 • f_equal r b1 = a1 • p1} {H2: p1 • f_equal r b2 = a2 • p2}
  {u0: PX x0} {u1: PX x1} {u2: PX x2} {v0: PT t0} {v1: PT t1} {v2: PT t2}
  {ha1: rew [PX] a1 in u0 = u1} {ha2: rew [PX] a2 in u1 = u2}
  {hb1: rew [PT] b1 in v0 = v1} {hb2: rew [PT] b2 in v1 = v2}
  {hp0: rew [PX] p0 in u0 = R t0 v0} {hp1: rew [PX] p1 in u1 = R t1 v1}
  {hp2: rew [PX] p2 in u2 = R t2 v2}
  (HH1: rew [fun e => rew [PX] e in u0 = R t1 v1] H1 in
    (hp0 ⊙ sigT_map_eq R hb1) = ha1 ⊙ hp1)
  (HH2: rew [fun e => rew [PX] e in u1 = R t2 v2] H2 in
    (hp1 ⊙ sigT_map_eq R hb2) = ha2 ⊙ hp2):
  square_cube_coherence_dep PY
    (square_map_along r g f j α (b1 • b2) (square_compose_map r H1 H2)
      (square_coherence_fill r g f j α (b1 • b2)))
    (square_compose_map j
      (square_map_along r g f j α b1 H1 (square_coherence_fill r g f j α b1))
      (square_map_along r g f j α b2 H2 (square_coherence_fill r g f j α b2)))
    (f_equal (fun e => f_equal j e) (eq_trans_map_distr g b1 b2))
    (eq_trans_map_distr f a1 a2) (square_map_along_compose r g f j α b1 b2 H1 H2)
    (sigT_map_eq F (ha1 ⊙ ha2)) (sigT_map_eq F ha1 ⊙ sigT_map_eq F ha2)
    (sigT_map_eq J (sigT_map_eq G (hb1 ⊙ hb2)))
    (sigT_map_eq J (sigT_map_eq G hb1 ⊙ sigT_map_eq G hb2))
    (sigT_map_eq F hp0 ⊙ Hα t0 v0) (sigT_map_eq F hp2 ⊙ Hα t2 v2)
    (square_map_along_coherence_dep r g f j R G F J α Hα (b1 • b2) _ (hb1 ⊙ hb2)
      (square_compose_map_coherence_dep r PX PT R _ _ _ _ _ _ _ _ _ HH1 HH2))
    (square_compose_map_coherence_dep j PY PU J _ _ _ _ _ _ _ _ _
      (square_map_along_coherence_dep r g f j R G F J α Hα b1 H1 hb1 HH1)
      (square_map_along_coherence_dep r g f j R G F J α Hα b2 H2 hb2 HH2)) (sigT_map_eq
      (fun (e: g t0 = g t2) (h: rew [PU] e in G t0 v0 = G t2 v2) => sigT_map_eq J h)
      (sigT_map_eq_comp G hb1 hb2)) (sigT_map_eq_comp F ha1 ha2).
Proof.
  destruct b1, b2, hb1, hb2.
  revert a1 a2 H1 H2 ha1 ha2 HH1 HH2.
  subst x0 x1 x2. cbn in hp0, hp1, hp2. subst u0 u1 u2.
  intros a1 a2 H1 H2 ha1 ha2 HH1 HH2.
  cbn in H1, H2. subst a1 a2.
  cbn in *.
  generalize dependent ha1.
  refine (homotopy_path_ind_r (fun h: R t0 v0 = R t0 v0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent ha2.
  refine (homotopy_path_ind_r (fun h: R t0 v0 = R t0 v0 => f_equal (fun z => z) h)
    (fun h => f_equal_id h) _ _).
  unfold square_cube_coherence_dep, square_map_along,
    square_map_along_coherence_dep, square_compose_map_coherence_dep,
    square_compose_map, square_map_along_dep,
    square_coherence_dep_reverse_fill, square_coherence_dep_fill.
  cbn.
  generalize (Hα t0 v0). generalize (α t0).
  generalize (J (g t0) (G t0 v0)). generalize (j (g t0)).
  intros y v a h. now destruct a, h.
Defined.

(** Map a cube along a comparison between functions. The supplied
    naturality cube determines its two comparison squares. *)
Definition square_cube_map_along {T X U Y: Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (α: forall t, f (r t) = j (g t))
  {t0 t1: T} {x0 x1: X} {a a': x0 = x1} {b b': t0 = t1}
  {p: x0 = r t0} {q: x1 = r t1}
  {H: p • f_equal r b = a • q} {K: p • f_equal r b' = a' • q}
  {κ: b = b'} {λ: a = a'}
  (C: square_cube H K (f_equal (fun e => f_equal r e) κ) λ)
  {N0: square_coherence r g f j α b}
  {N1: square_coherence r g f j α b'}
  (N: square_cube (eq_sym N0) (eq_sym N1)
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) κ))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) κ))):
  square_cube (square_map_along r g f j α b H N0)
    (square_map_along r g f j α b' K N1)
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) κ))
    (f_equal (fun e => f_equal f e) λ) :=
  square_cube_stack (square_cube_map f C) N.

Lemma square_nat_route_left {X Y: Type} (f: Y -> X)
  {x0 x1 x2 x3 y0 y1 y2 y3: X} {z0 z1 z2 z3: Y}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {c1: z0 = z1} {c2: z1 = z2} {c3: z2 = z3}
  {v0: x0 = y0} {v1: x1 = y1} {v2: x2 = y2} {v3: x3 = y3}
  {p0: y0 = f z0} {p1: y1 = f z1} {p2: y2 = f z2} {p3: y3 = f z3}
  {q0: x0 = f z0} {q1: x1 = f z1} {q2: x2 = f z2} {q3: x3 = f z3}
  (M0: q0 = v0 • p0) (M1: q1 = v1 • p1)
  (M2: q2 = v2 • p2) (M3: q3 = v3 • p3)
  (S1: v0 • b1 = a1 • v1) (S2: v1 • b2 = a2 • v2) (S3: v2 • b3 = a3 • v3)
  (H1: p0 • f_equal f c1 = b1 • p1)
  (H2: p1 • f_equal f c2 = b2 • p2)
  (H3: p2 • f_equal f c3 = b3 • p3):
  square_compose_map f
    (square_compose_map f (square_change_sides M0 (square_stack S1 H1) M1)
      (square_change_sides M1 (square_stack S2 H2) M2))
    (square_change_sides M2 (square_stack S3 H3) M3) =
  square_change_sides M0
    (square_stack (square_compose (square_compose S1 S2) S3)
      (square_compose_map f (square_compose_map f H1 H2) H3)) M3.
Proof.
  rewrite 2 square_change_sides_compose_map.
  now rewrite 2 square_interchange_map.
Defined.

Lemma square_nat_route_left_coherence_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2 x3 y0 y1 y2 y3: X} {z0 z1 z2 z3: Y}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {c1: z0 = z1} {c2: z1 = z2} {c3: z2 = z3}
  {v0: x0 = y0} {v1: x1 = y1} {v2: x2 = y2} {v3: x3 = y3}
  {p0: y0 = f z0} {p1: y1 = f z1} {p2: y2 = f z2} {p3: y3 = f z3}
  {q0: x0 = f z0} {q1: x1 = f z1} {q2: x2 = f z2} {q3: x3 = f z3}
  {M0: q0 = v0 • p0} {M1: q1 = v1 • p1}
  {M2: q2 = v2 • p2} {M3: q3 = v3 • p3}
  {S1: v0 • b1 = a1 • v1} {S2: v1 • b2 = a2 • v2} {S3: v2 • b3 = a3 • v3}
  {H1: p0 • f_equal f c1 = b1 • p1}
  {H2: p1 • f_equal f c2 = b2 • p2}
  {H3: p2 • f_equal f c3 = b3 • p3}
  {ux0: P x0} {ux1: P x1} {ux2: P x2} {ux3: P x3}
  {uy0: P y0} {uy1: P y1} {uy2: P y2} {uy3: P y3}
  {uz0: Q z0} {uz1: Q z1} {uz2: Q z2} {uz3: Q z3}
  {ha1: rew [P] a1 in ux0 = ux1} {ha2: rew [P] a2 in ux1 = ux2}
  {ha3: rew [P] a3 in ux2 = ux3}
  {hb1: rew [P] b1 in uy0 = uy1} {hb2: rew [P] b2 in uy1 = uy2}
  {hb3: rew [P] b3 in uy2 = uy3}
  {hc1: rew [Q] c1 in uz0 = uz1} {hc2: rew [Q] c2 in uz1 = uz2}
  {hc3: rew [Q] c3 in uz2 = uz3}
  {hv0: rew [P] v0 in ux0 = uy0} {hv1: rew [P] v1 in ux1 = uy1}
  {hv2: rew [P] v2 in ux2 = uy2} {hv3: rew [P] v3 in ux3 = uy3}
  {hp0: rew [P] p0 in uy0 = F z0 uz0} {hp1: rew [P] p1 in uy1 = F z1 uz1}
  {hp2: rew [P] p2 in uy2 = F z2 uz2} {hp3: rew [P] p3 in uy3 = F z3 uz3}
  {hq0: rew [P] q0 in ux0 = F z0 uz0} {hq1: rew [P] q1 in ux1 = F z1 uz1}
  {hq2: rew [P] q2 in ux2 = F z2 uz2} {hq3: rew [P] q3 in ux3 = F z3 uz3}
  (DM0: rew [fun t => rew [P] t in ux0 = F z0 uz0] M0 in hq0 = hv0 ⊙ hp0)
  (DM1: rew [fun t => rew [P] t in ux1 = F z1 uz1] M1 in hq1 = hv1 ⊙ hp1)
  (DM2: rew [fun t => rew [P] t in ux2 = F z2 uz2] M2 in hq2 = hv2 ⊙ hp2)
  (DM3: rew [fun t => rew [P] t in ux3 = F z3 uz3] M3 in hq3 = hv3 ⊙ hp3)
  (DS1: rew [fun t => rew [P] t in ux0 = uy1] S1 in (hv0 ⊙ hb1) = ha1 ⊙ hv1)
  (DS2: rew [fun t => rew [P] t in ux1 = uy2] S2 in (hv1 ⊙ hb2) = ha2 ⊙ hv2)
  (DS3: rew [fun t => rew [P] t in ux2 = uy3] S3 in (hv2 ⊙ hb3) = ha3 ⊙ hv3)
  (DH1: rew [fun t => rew [P] t in uy0 = F z1 uz1] H1 in
    (hp0 ⊙ sigT_map_eq F hc1) = hb1 ⊙ hp1)
  (DH2: rew [fun t => rew [P] t in uy1 = F z2 uz2] H2 in
    (hp1 ⊙ sigT_map_eq F hc2) = hb2 ⊙ hp2)
  (DH3: rew [fun t => rew [P] t in uy2 = F z3 uz3] H3 in
    (hp2 ⊙ sigT_map_eq F hc3) = hb3 ⊙ hp3):
  let T1 := square_change_sides M0 (square_stack S1 H1) M1 in
  let T2 := square_change_sides M1 (square_stack S2 H2) M2 in
  let T3 := square_change_sides M2 (square_stack S3 H3) M3 in
  let DT1 := square_change_sides_dep P M0 (square_stack S1 H1) M1
    ha1 (sigT_map_eq F hc1) (hv0 ⊙ hp0) hq0 (hv1 ⊙ hp1) hq1 DM0
    (square_stack_dep P S1 H1 ha1 hb1 (sigT_map_eq F hc1) hv0 hv1 hp0 hp1 DS1 DH1) DM1 in
  let DT2 := square_change_sides_dep P M1 (square_stack S2 H2) M2
    ha2 (sigT_map_eq F hc2) (hv1 ⊙ hp1) hq1 (hv2 ⊙ hp2) hq2 DM1
    (square_stack_dep P S2 H2 ha2 hb2 (sigT_map_eq F hc2) hv1 hv2 hp1 hp2 DS2 DH2) DM2 in
  let DT3 := square_change_sides_dep P M2 (square_stack S3 H3) M3
    ha3 (sigT_map_eq F hc3) (hv2 ⊙ hp2) hq2 (hv3 ⊙ hp3) hq3 DM2
    (square_stack_dep P S3 H3 ha3 hb3 (sigT_map_eq F hc3) hv2 hv3 hp2 hp3 DS3 DH3) DM3 in
  let dleft := square_compose_map_coherence_dep f P Q F
    (square_compose_map f T1 T2) T3 (ha1 ⊙ ha2) ha3 (hc1 ⊙ hc2) hc3 hq0 hq2 hq3
    (square_compose_map_coherence_dep f P Q F T1 T2 ha1 ha2 hc1 hc2 hq0 hq1 hq2 DT1 DT2) DT3 in
  let SS := square_compose (square_compose S1 S2) S3 in
  let HH := square_compose_map f (square_compose_map f H1 H2) H3 in
  let DSS := square_compose_dep P (square_compose S1 S2) S3
    (ha1 ⊙ ha2) ha3 (hb1 ⊙ hb2) hb3 hv0 hv2 hv3
    (square_compose_dep P S1 S2 ha1 ha2 hb1 hb2 hv0 hv1 hv2 DS1 DS2) DS3 in
  let DHH := square_compose_map_coherence_dep f P Q F
    (square_compose_map f H1 H2) H3 (hb1 ⊙ hb2) hb3 (hc1 ⊙ hc2) hc3 hp0 hp2 hp3
    (square_compose_map_coherence_dep f P Q F H1 H2 hb1 hb2 hc1 hc2 hp0 hp1 hp2 DH1 DH2) DH3 in
  let dright := square_change_sides_dep P M0 (square_stack SS HH) M3
    ((ha1 ⊙ ha2) ⊙ ha3) (sigT_map_eq F ((hc1 ⊙ hc2) ⊙ hc3))
    (hv0 ⊙ hp0) hq0 (hv3 ⊙ hp3) hq3 DM0
    (square_stack_dep P SS HH ((ha1 ⊙ ha2) ⊙ ha3) ((hb1 ⊙ hb2) ⊙ hb3)
      (sigT_map_eq F ((hc1 ⊙ hc2) ⊙ hc3)) hv0 hv3 hp0 hp3 DSS DHH) DM3 in
  rew [fun h => rew [fun t => rew [P] t in ux0 = F z3 uz3] h in
    (hq0 ⊙ sigT_map_eq F ((hc1 ⊙ hc2) ⊙ hc3)) = ((ha1 ⊙ ha2) ⊙ ha3) ⊙ hq3]
    square_nat_route_left f M0 M1 M2 M3 S1 S2 S3 H1 H2 H3 in dleft = dright.
Proof.
  subst q0 q1 q2 q3.
  cbn in DM0, DM1, DM2, DM3. subst hq0 hq1 hq2 hq3.
  destruct c1, hc1, c2, hc2, c3, hc3.
  revert a1 a2 a3 b1 b2 b3 S1 S2 S3 H1 H2 H3
    ha1 ha2 ha3 hb1 hb2 hb3 DS1 DS2 DS3 DH1 DH2 DH3.
  revert v0 v1 v2 v3 hv0 hv1 hv2 hv3.
  subst y0 y1 y2 y3. cbn in hp0, hp1, hp2, hp3. subst uy0 uy1 uy2 uy3.
  intros v0 v1 v2 v3 hv0 hv1 hv2 hv3.
  subst x0 x1 x2 x3. cbn in hv0, hv1, hv2, hv3. subst ux0 ux1 ux2 ux3.
  intros a1 a2 a3 b1 b2 b3 S1 S2 S3 H1 H2 H3
    ha1 ha2 ha3 hb1 hb2 hb3 DS1 DS2 DS3 DH1 DH2 DH3.
  cbn in H1, H2, H3. subst b1 b2 b3.
  cbn in S1, S2, S3. subst a1 a2 a3.
  cbn in *.
  revert DS1 DS2 DS3.
  generalize dependent hb1.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent hb2.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent hb3.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  intros DS1 DS2 DS3.
  generalize dependent ha1.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent ha2.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  generalize dependent ha3.
  refine (homotopy_path_ind_r (fun h: F z0 uz0 = F z0 uz0 => f_equal (fun v => v) h)
    (fun h => f_equal_id h) _ _).
  now reflexivity.
Defined.

Lemma square_change_sides_route_left {X: Type} {x0 x1 x2 x3 y0 y1 y2 y3: X}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {p0 q0: x0 = y0} {p1 q1: x1 = y1} {p2 q2: x2 = y2} {p3 q3: x3 = y3}
  (M0: q0 = p0) (M1: q1 = p1) (M2: q2 = p2) (M3: q3 = p3)
  (S1: p0 • b1 = a1 • p1) (S2: p1 • b2 = a2 • p2) (S3: p2 • b3 = a3 • p3): square_compose
    (square_compose (square_change_sides M0 S1 M1) (square_change_sides M1 S2 M2))
    (square_change_sides M2 S3 M3) =
  square_change_sides M0 (square_compose (square_compose S1 S2) S3) M3.
Proof. now rewrite 2 square_change_sides_compose. Defined.

(** Cubes expressing compatibility of square operations with supplied
    edge squares. Shared boundary data is inferred from the inputs. *)
Definition square_compose_cube {X Y: Type} (r: Y -> X)
  {x0 x1 x2 x3 x4 x5: X} {y0 y1 y2 y3 y4 y5: Y}
  {v0: x0 = r y0} {v1: x1 = r y1} {v2: x2 = r y2}
  {v3: x3 = r y3} {v4: x4 = r y4} {v5: x5 = r y5}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y1 = y2} {l_p1: x1 = x2}
  {N_p1: v1 • f_equal r u_p1 = l_p1 • v2}
  {u_p2: y0 = y3} {l_p2: x0 = x3}
  {N_p2: v0 • f_equal r u_p2 = l_p2 • v3}
  {u_p3: y3 = y2} {l_p3: x3 = x2}
  {N_p3: v3 • f_equal r u_p3 = l_p3 • v2}
  {u_p4: y2 = y4} {l_p4: x2 = x4}
  {N_p4: v2 • f_equal r u_p4 = l_p4 • v4}
  {u_p5: y3 = y5} {l_p5: x3 = x5}
  {N_p5: v3 • f_equal r u_p5 = l_p5 • v5}
  {u_p6: y5 = y4} {l_p6: x5 = x4}
  {N_p6: v5 • f_equal r u_p6 = l_p6 • v4}
  {u_H0: u_p0 • u_p1 = u_p2 • u_p3} {l_H0: l_p0 • l_p1 = l_p2 • l_p3}
  (C_H0: square_cube
    (square_compose_map r N_p0 N_p1)
    (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0)
  {u_H1: u_p3 • u_p4 = u_p5 • u_p6} {l_H1: l_p3 • l_p4 = l_p5 • l_p6}
  (C_H1: square_cube
    (square_compose_map r N_p3 N_p4)
    (square_compose_map r N_p5 N_p6)
    (f_equal (fun e => f_equal r e) u_H1) l_H1): square_cube
    (square_compose_map r N_p0 (square_compose_map r N_p1 N_p4))
    (square_compose_map r (square_compose_map r N_p2 N_p5) N_p6)
    (f_equal (fun e => f_equal r e) (square_compose u_H0 u_H1))
    (square_compose l_H0 l_H1) :=
  square_cube_trans_map r (square_compose_map_assoc r N_p0 N_p1 N_p4)
    (square_cube_trans_map r (square_cube_whisker_r r N_p4 C_H0)
      (square_cube_trans_map r
        (square_cube_inverse_map r (square_compose_map_assoc r N_p2 N_p3 N_p4))
        (square_cube_trans_map r (square_cube_whisker_l r N_p2 C_H1)
          (square_compose_map_assoc r N_p2 N_p5 N_p6)))).

Definition square_stack_cube {X Y: Type} (r: Y -> X)
  {x0 x1 x2 x3 x4 x5: X} {y0 y1 y2 y3 y4 y5: Y}
  {v0: x0 = r y0} {v1: x1 = r y1} {v2: x2 = r y2}
  {v3: x3 = r y3} {v4: x4 = r y4} {v5: x5 = r y5}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y1 = y2} {l_p1: x1 = x2}
  {N_p1: v1 • f_equal r u_p1 = l_p1 • v2}
  {u_p2: y0 = y3} {l_p2: x0 = x3}
  {N_p2: v0 • f_equal r u_p2 = l_p2 • v3}
  {u_p3: y3 = y2} {l_p3: x3 = x2}
  {N_p3: v3 • f_equal r u_p3 = l_p3 • v2}
  {u_p4: y1 = y4} {l_p4: x1 = x4}
  {N_p4: v1 • f_equal r u_p4 = l_p4 • v4}
  {u_p5: y4 = y5} {l_p5: x4 = x5}
  {N_p5: v4 • f_equal r u_p5 = l_p5 • v5}
  {u_p6: y2 = y5} {l_p6: x2 = x5}
  {N_p6: v2 • f_equal r u_p6 = l_p6 • v5}
  {u_H0: u_p0 • u_p1 = u_p2 • u_p3} {l_H0: l_p0 • l_p1 = l_p2 • l_p3}
  (C_H0: square_cube
    (square_compose_map r N_p0 N_p1)
    (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0)
  {u_H1: u_p4 • u_p5 = u_p1 • u_p6} {l_H1: l_p4 • l_p5 = l_p1 • l_p6}
  (C_H1: square_cube
    (square_compose_map r N_p4 N_p5)
    (square_compose_map r N_p1 N_p6)
    (f_equal (fun e => f_equal r e) u_H1) l_H1): square_cube
    (square_compose_map r (square_compose_map r N_p0 N_p4) N_p5)
    (square_compose_map r N_p2 (square_compose_map r N_p3 N_p6))
    (f_equal (fun e => f_equal r e) (square_stack u_H0 u_H1))
    (square_stack l_H0 l_H1) :=
  square_cube_trans_map r
    (square_cube_inverse_map r (square_compose_map_assoc r N_p0 N_p4 N_p5))
    (square_cube_trans_map r (square_cube_whisker_l r N_p0 C_H1)
      (square_cube_trans_map r (square_compose_map_assoc r N_p0 N_p1 N_p6)
        (square_cube_trans_map r (square_cube_whisker_r r N_p6 C_H0)
          (square_cube_inverse_map r (square_compose_map_assoc r N_p2 N_p3 N_p6))))).

Definition square_change_sides_cube {X Y: Type} (r: Y -> X)
  {x0 x1 x2 x3: X} {y0 y1 y2 y3: Y}
  {v0: x0 = r y0} {v1: x1 = r y1}
  {v2: x2 = r y2} {v3: x3 = r y3}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y0 = y1} {l_p1: x0 = x1}
  {N_p1: v0 • f_equal r u_p1 = l_p1 • v1}
  {u_p2: y1 = y2} {l_p2: x1 = x2}
  {N_p2: v1 • f_equal r u_p2 = l_p2 • v2}
  {u_p3: y0 = y3} {l_p3: x0 = x3}
  {N_p3: v0 • f_equal r u_p3 = l_p3 • v3}
  {u_p4: y3 = y2} {l_p4: x3 = x2}
  {N_p4: v3 • f_equal r u_p4 = l_p4 • v2}
  {u_p5: y3 = y2} {l_p5: x3 = x2}
  {N_p5: v3 • f_equal r u_p5 = l_p5 • v2}
  {u_H0: u_p0 = u_p1} {l_H0: l_p0 = l_p1}
  (C_H0: square_cube N_p0 N_p1
    (f_equal (fun e => f_equal r e) u_H0) l_H0)
  {u_H1: u_p1 • u_p2 = u_p3 • u_p4} {l_H1: l_p1 • l_p2 = l_p3 • l_p4}
  (C_H1: square_cube
    (square_compose_map r N_p1 N_p2)
    (square_compose_map r N_p3 N_p4)
    (f_equal (fun e => f_equal r e) u_H1) l_H1)
  {u_H2: u_p5 = u_p4} {l_H2: l_p5 = l_p4}
  (C_H2: square_cube N_p5 N_p4
    (f_equal (fun e => f_equal r e) u_H2) l_H2):
  square_cube (square_compose_map r N_p0 N_p2) (square_compose_map r N_p3 N_p5)
    (f_equal (fun e => f_equal r e) (square_change_sides u_H0 u_H1 u_H2))
    (square_change_sides l_H0 l_H1 l_H2) :=
  square_cube_trans_map r (square_cube_whisker_r r N_p2 C_H0)
    (square_cube_trans_map r C_H1
      (square_cube_inverse_map r (square_cube_whisker_l r N_p3 C_H2))).

Definition square_map_cube {X Y U V: Type}
  (r: Y -> X) (g: Y -> U) (F: X -> V) (j: U -> V)
  (α: forall y, F (r y) = j (g y))
  {x0 x1 x2 x3: X} {y0 y1 y2 y3: Y}
  {v0: x0 = r y0} {v1: x1 = r y1}
  {v2: x2 = r y2} {v3: x3 = r y3}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y1 = y2} {l_p1: x1 = x2}
  {N_p1: v1 • f_equal r u_p1 = l_p1 • v2}
  {u_p2: y0 = y3} {l_p2: x0 = x3}
  {N_p2: v0 • f_equal r u_p2 = l_p2 • v3}
  {u_p3: y3 = y2} {l_p3: x3 = x2}
  {N_p3: v3 • f_equal r u_p3 = l_p3 • v2}
  {u_H0: u_p0 • u_p1 = u_p2 • u_p3} {l_H0: l_p0 • l_p1 = l_p2 • l_p3}
  (C_H0: square_cube
    (square_compose_map r N_p0 N_p1)
    (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0) (N: square_cube
    (eq_sym (square_coherence_fill r g F j α (u_p0 • u_p1)))
    (eq_sym (square_coherence_fill r g F j α (u_p2 • u_p3)))
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) u_H0))
    (f_equal (fun e => f_equal F e) (f_equal (fun e => f_equal r e) u_H0))): square_cube
    (square_compose_map j
      (square_map_along r g F j α u_p0 N_p0 (square_coherence_fill r g F j α u_p0))
      (square_map_along r g F j α u_p1 N_p1 (square_coherence_fill r g F j α u_p1)))
    (square_compose_map j
      (square_map_along r g F j α u_p2 N_p2 (square_coherence_fill r g F j α u_p2))
      (square_map_along r g F j α u_p3 N_p3 (square_coherence_fill r g F j α u_p3)))
    (f_equal (fun e => f_equal j e) (square_map g u_H0)) (square_map F l_H0) :=
  square_cube_trans_map j
    (square_cube_inverse_map j (square_map_along_compose r g F j α u_p0 u_p1 N_p0 N_p1))
    (square_cube_trans_map j (square_cube_map_along r g F j α C_H0 N)
      (square_map_along_compose r g F j α u_p2 u_p3 N_p2 N_p3)).

(** Paste the supplied map prism and comparison-family prism. The two
    routes perform double mapping and source extension in opposite
    orders, retaining both supplied prism witnesses. *)
Definition hexagonal_prism_pair_cube
  {A1 B A3 X U V Y1 Y2 W Z: Type}
  (f1: A1 -> X) (r: B -> X) (f3: A3 -> X)
  (j0: B -> U) (i0: B -> V) (j1: X -> Y1) (i1: X -> Y2)
  (Ej: U -> Y1) (Ei: V -> Y2) (F: Y1 -> Z) (G: Y2 -> Z)
  (I: U -> W) (J: V -> W) (d: W -> Z)
  (α: forall b, j1 (r b) = Ej (j0 b))
  (β: forall b, i1 (r b) = Ei (i0 b))
  (γ: forall u, F (Ej u) = d (I u))
  (δ: forall v, G (Ei v) = d (J v))
  (K: forall x, F (j1 x) = G (i1 x))
  (L: forall b, I (j0 b) = J (i0 b))
  (Q: forall b, hexagonal_coherence F d G
    (α b) (L b) (β b) (γ (j0 b)) (K (r b)) (δ (i0 b)))
  {x0 x1: A1} {b0 b1: B} {x4 x5: A3}
  (p1: x0 = x1) (p2: b0 = b1) (p3: x4 = x5)
  (h1: f1 x1 = r b0) (h2: f1 x0 = f3 x4) (h3: f3 x5 = r b1)
  (H: hexagonal_coherence f1 r f3 p1 p2 p3 h1 h2 h3)
  (Nmap: hexagonal_prism_coherence_map f1 r f3 j1 i1 F G K
    p1 p2 p3 h1 h2 h3 H)
  (Nnat: hexagonal_prism_coherence_nat F d G
    (fun b => j1 (r b)) (fun b => Ej (j0 b))
    (fun b => I (j0 b)) (fun b => J (i0 b))
    (fun b => i1 (r b)) (fun b => Ei (i0 b))
    α L β (fun b => γ (j0 b)) (fun b => K (r b))
    (fun b => δ (i0 b)) Q p2):
  let Nja := square_coherence_fill r j0 j1 Ej α p2 in
  let Nia := square_coherence_fill r i0 i1 Ei β p2 in
  let NL := square_coherence_fill j0 i0 I J L p2 in
  let Nγ := square_coherence_fill Ej I F d γ (f_equal j0 p2) in
  let Nδ := square_coherence_fill Ei J G d δ (f_equal i0 p2) in
  let Hrect := H in
  let p := f_equal f1 p1 • h1 in
  let q := f_equal f3 p3 • h3 in
  let Np := square_coherence_fill j1 i1 F G K p in
  let Nq := square_coherence_fill j1 i1 F G K q in
  let Na := square_coherence_fill j1 i1 F G K h2 in
  let mapped_j := square_map_along Ej I F d γ (f_equal j0 p2)
    (square_map_along r j0 j1 Ej α p2 Hrect Nja) Nγ in
  let mapped_i := square_map_along Ei J G d δ (f_equal i0 p2)
    (square_map_along r i0 i1 Ei β p2 Hrect Nia) Nδ in
  let source0 := layer_square_nat j1 i1 F G d K p
    (α b0) (β b0) (L b0) (γ (j0 b0)) (δ (i0 b0)) (Q b0) Np in
  let source1 := layer_square_nat j1 i1 F G d K q
    (α b1) (β b1) (L b1) (γ (j0 b1)) (δ (i0 b1)) (Q b1) Nq in
  square_cube (square_compose_map d mapped_j source1)
    (square_compose_map d source0 mapped_i)
    (f_equal (fun e => f_equal d e) NL) Na.
Proof.
  intros Nja Nia NL Nγ Nδ Hrect p q Np Nq Na mapped_j mapped_i source0 source1.
  pose (s1 := square_coherence_fill (fun b => j1 (r b)) (fun b => Ej (j0 b))
    F F (fun b => f_equal F (α b)) p2).
  pose (s2 := square_coherence_fill (fun b => Ej (j0 b)) (fun b => I (j0 b))
    F d (fun b => γ (j0 b)) p2).
  pose (s3 := square_coherence_fill (fun b => I (j0 b)) (fun b => J (i0 b))
    d d (fun b => f_equal d (L b)) p2).
  pose (t1 := square_coherence_fill (fun b => j1 (r b)) (fun b => i1 (r b))
    F G (fun b => K (r b)) p2).
  pose (t2 := square_coherence_fill (fun b => i1 (r b)) (fun b => Ei (i0 b))
    G G (fun b => f_equal G (β b)) p2).
  pose (t3 := square_coherence_fill (fun b => Ei (i0 b)) (fun b => J (i0 b))
    G d (fun b => δ (i0 b)) p2).

  pose (Nm := square_coherence_fill j1 i1 F G K (f_equal r p2)).
  pose (Nα := square_compose (square_map F Nja) Nγ).
  pose (Nβ := square_compose (square_map G Nia) Nδ).

  pose (m0 := f_equal (fun e => f_equal F e) (eq_sym (map_compose_path j1 r p2))).
  pose (m1 := f_equal (fun e => f_equal F e) (eq_sym (map_compose_path Ej j0 p2))).
  pose (m2 := f_equal (fun e => f_equal d e) (eq_sym (map_compose_path I j0 p2))).
  pose (m3 := f_equal (fun e => f_equal d e) (eq_sym (map_compose_path J i0 p2))).
  pose (m4 := f_equal (fun e => f_equal G e) (eq_sym (map_compose_path i1 r p2))).
  pose (m5 := f_equal (fun e => f_equal G e) (eq_sym (map_compose_path Ei i0 p2))).

  pose (Eleft := path_map2 (fun H K => square_compose H K)
      (path_map2 (fun H K => square_compose H K)
        (square_coherence_map_edges r j0 j1 Ej F α p2)
        (square_coherence_precompose j0 Ej I F d γ p2))
      (square_coherence_map_edges j0 i0 I J d L p2) •
    square_change_sides_route_left m0 m1 m2 m3 s1 s2 s3).
  pose (Eright := path_map2 (fun H K => square_compose H K)
      (square_coherence_precompose r j1 i1 F G K p2)
      (path_map2 (fun H K => square_compose H K)
        (square_coherence_map_edges r i0 i1 Ei G β p2)
        (square_coherence_precompose i0 Ei J G d δ p2)) •
    square_change_sides_route m0 m4 m5 m3 t1 t2 t3).

  pose (prism_nat := square_cube_change_faces Eleft
    (square_cube_change_sides m0 m3 Nnat) Eright).
  pose (prism_map := hexagonal_prism_map_square_cube f1 r f3 j1 i1 F G K
    p1 p2 p3 h1 h2 h3 H Nmap).

  pose (Hf := square_map F (square_map j1 Hrect)).
  pose (Hg := square_map G (square_map i1 Hrect)).
  pose (Q0 := Q b0).
  pose (Q1 := Q b1).

  pose (raw_square :=
    square_cube_glue_prisms d Hf Hg Np Nq Nm Na Nα Nβ Q0 Q1 NL prism_map prism_nat).

  pose (M0 := map_compose_tail F (f_equal j1 p) (α b0) (γ (j0 b0))).
  pose (M1 := map_compose_tail F (f_equal j1 q) (α b1) (γ (j0 b1))).
  pose (M2 := map_compose_tail G (f_equal i1 p) (β b0) (δ (i0 b0))).
  pose (M3 := map_compose_tail G (f_equal i1 q) (β b1) (δ (i0 b1))).

  pose (A := square_stack Hf (eq_sym Nα)).
  pose (B' := square_stack Hg (eq_sym Nβ)).
  pose (C0 := square_stack Np Q0).
  pose (C1 := square_stack Nq Q1).

  pose (eleft := path_map2 (fun H K => square_compose_map d H K)
      (square_map_along_twice r j0 j1 Ej α I F d γ p2 Hrect) eq_refl •
    square_change_sides_compose_map d M0 M1 M3 A C1).
  pose (eright := path_map2 (fun H K => square_compose_map d H K) eq_refl
      (square_map_along_twice r i0 i1 Ei β J G d δ p2 Hrect) •
    square_change_sides_compose_map d M0 M2 M3 C0 B').

  now exact (square_cube_change_faces eleft
    (square_cube_change_sides M0 M3 raw_square) eright).
Defined.

Lemma square_coherence_route_canonical {A A0 A1 A2 A3 B: Type}
  (x0: A -> A0) (x1: A -> A1) (x2: A -> A2) (x3: A -> A3)
  (f0: A0 -> B) (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (k1: forall a, f0 (x0 a) = f1 (x1 a))
  (k2: forall a, f1 (x1 a) = f2 (x2 a))
  (k3: forall a, f2 (x2 a) = f3 (x3 a)) {a b: A} (e: a = b):
  square_compose (square_coherence_fill x0 x1 f0 f1 k1 e)
    (square_compose (square_coherence_fill x1 x2 f1 f2 k2 e)
      (square_coherence_fill x2 x3 f2 f3 k3 e)) =
  square_coherence_fill x0 x3 f0 f3 (fun a => k1 a • (k2 a • k3 a)) e.
Proof.
  destruct e.
  cbn [square_coherence_fill f_equal].
  generalize (k1 a), (k2 a), (k3 a).
  generalize (f0 (x0 a)), (f1 (x1 a)), (f2 (x2 a)), (f3 (x3 a)).
  intros v0 v1 v2 v3 p q r. now destruct p, q, r.
Defined.

Lemma square_coherence_route_left_canonical {A A0 A1 A2 A3 B: Type}
  (x0: A -> A0) (x1: A -> A1) (x2: A -> A2) (x3: A -> A3)
  (f0: A0 -> B) (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (k1: forall a, f0 (x0 a) = f1 (x1 a))
  (k2: forall a, f1 (x1 a) = f2 (x2 a))
  (k3: forall a, f2 (x2 a) = f3 (x3 a)) {a b: A} (e: a = b): square_compose
    (square_compose (square_coherence_fill x0 x1 f0 f1 k1 e)
      (square_coherence_fill x1 x2 f1 f2 k2 e))
    (square_coherence_fill x2 x3 f2 f3 k3 e) =
  square_coherence_fill x0 x3 f0 f3 (fun a => (k1 a • k2 a) • k3 a) e.
Proof.
  destruct e.
  cbn [square_coherence_fill f_equal].
  generalize (k1 a), (k2 a), (k3 a).
  generalize (f0 (x0 a)), (f1 (x1 a)), (f2 (x2 a)), (f3 (x3 a)).
  intros v0 v1 v2 v3 p q r. now destruct p, q, r.
Defined.

Lemma hexagonal_prism_coherence_nat_fill_routes_computation {A A1 A2 A3 B: Type}
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
  hexagonal_prism_coherence_nat_fill f1 f2 f3 x0 x1 x2 x3 x4 x5
    p1 p2 p3 h1 h2 h3 H e =
  square_cube_change_faces
    (square_coherence_route_left_canonical x0 x1 x2 x3 f1 f1 f2 f2
      (fun a => f_equal f1 (p1 a)) h1 (fun a => f_equal f2 (p2 a)) e)
    (hexagonal_prism_nat_route_fill H e)
    (square_coherence_route_canonical x0 x4 x5 x3 f1 f3 f3 f2
      h2 (fun a => f_equal f3 (p3 a)) h3 e).
Proof.
  unfold hexagonal_prism_coherence_nat, hexagonal_prism_coherence.
  destruct e.
  unfold hexagonal_prism_coherence_nat_fill, hexagonal_prism_nat_route_fill,
    square_coherence_family_cube, square_coherence_route_canonical, square_coherence_route_left_canonical.
  unfold square_cube_change_faces, square_change_sides, square_cube,
    square_coherence_fill.
  cbn [f_equal].
  generalize (H a). unfold hexagonal_coherence.
  generalize (f_equal f1 (p1 a)), (h1 a), (f_equal f2 (p2 a)),
    (h2 a), (f_equal f3 (p3 a)), (h3 a).
  generalize (f1 (x0 a)), (f1 (x1 a)), (f2 (x2 a)),
    (f2 (x3 a)), (f3 (x4 a)), (f3 (x5 a)).
  intros y0 y1 y2 y3 y4 y5 r1 r2 r3 s1 s2 s3 h.
  destruct r2, r3, s2, s3, s1. cbn in h. subst r1.
  now reflexivity.
Defined.

Lemma square_coherence_route_coherence_dep
  {A A0 A1 A2 A3 B: Type} {PA: A -> Type}
  {P0: A0 -> Type} {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {PB: B -> Type}
  (x0: A -> A0) (x1: A -> A1) (x2: A -> A2) (x3: A -> A3)
  (f0: A0 -> B) (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (X0: forall a, PA a -> P0 (x0 a)) (X1: forall a, PA a -> P1 (x1 a))
  (X2: forall a, PA a -> P2 (x2 a)) (X3: forall a, PA a -> P3 (x3 a))
  (F0: forall x, P0 x -> PB (f0 x)) (F1: forall x, P1 x -> PB (f1 x))
  (F2: forall x, P2 x -> PB (f2 x)) (F3: forall x, P3 x -> PB (f3 x))
  (k1: forall a, f0 (x0 a) = f1 (x1 a))
  (k2: forall a, f1 (x1 a) = f2 (x2 a))
  (k3: forall a, f2 (x2 a) = f3 (x3 a))
  (HK1: forall a u, rew [PB] k1 a in F0 (x0 a) (X0 a u) = F1 (x1 a) (X1 a u))
  (HK2: forall a u, rew [PB] k2 a in F1 (x1 a) (X1 a u) = F2 (x2 a) (X2 a u))
  (HK3: forall a u, rew [PB] k3 a in F2 (x2 a) (X2 a u) = F3 (x3 a) (X3 a u))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  rew [fun p => rew [PB] p in F0 (x0 a) (X0 a aa) = F3 (x3 b) (X3 b ab)]
    square_compose (square_coherence_fill x0 x1 f0 f1 k1 e)
      (square_compose (square_coherence_fill x1 x2 f1 f2 k2 e)
        (square_coherence_fill x2 x3 f2 f3 k3 e)) in
    (sigT_map_eq F0 (sigT_map_eq X0 he) ⊙ (HK1 b ab ⊙ (HK2 b ab ⊙ HK3 b ab))) =
  (HK1 a aa ⊙ (HK2 a aa ⊙ HK3 a aa)) ⊙ sigT_map_eq F3 (sigT_map_eq X3 he).
Proof.
  eapply square_compose_dep.
  - now exact (square_coherence_dep_fill x0 x1 f0 f1 X0 X1 F0 F1 k1 HK1 e he).
  - eapply square_compose_dep.
    + now exact (square_coherence_dep_fill x1 x2 f1 f2 X1 X2 F1 F2 k2 HK2 e he).
    + now exact (square_coherence_dep_fill x2 x3 f2 f3 X2 X3 F2 F3 k3 HK3 e he).
Defined.

Lemma square_coherence_route_left_coherence_dep
  {A A0 A1 A2 A3 B: Type} {PA: A -> Type}
  {P0: A0 -> Type} {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {PB: B -> Type}
  (x0: A -> A0) (x1: A -> A1) (x2: A -> A2) (x3: A -> A3)
  (f0: A0 -> B) (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (X0: forall a, PA a -> P0 (x0 a)) (X1: forall a, PA a -> P1 (x1 a))
  (X2: forall a, PA a -> P2 (x2 a)) (X3: forall a, PA a -> P3 (x3 a))
  (F0: forall x, P0 x -> PB (f0 x)) (F1: forall x, P1 x -> PB (f1 x))
  (F2: forall x, P2 x -> PB (f2 x)) (F3: forall x, P3 x -> PB (f3 x))
  (k1: forall a, f0 (x0 a) = f1 (x1 a))
  (k2: forall a, f1 (x1 a) = f2 (x2 a))
  (k3: forall a, f2 (x2 a) = f3 (x3 a))
  (HK1: forall a u, rew [PB] k1 a in F0 (x0 a) (X0 a u) = F1 (x1 a) (X1 a u))
  (HK2: forall a u, rew [PB] k2 a in F1 (x1 a) (X1 a u) = F2 (x2 a) (X2 a u))
  (HK3: forall a u, rew [PB] k3 a in F2 (x2 a) (X2 a u) = F3 (x3 a) (X3 a u))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  rew [fun p => rew [PB] p in F0 (x0 a) (X0 a aa) = F3 (x3 b) (X3 b ab)]
    square_compose (square_compose (square_coherence_fill x0 x1 f0 f1 k1 e) (square_coherence_fill x1 x2
      f1 f2 k2 e)) (square_coherence_fill x2 x3 f2 f3 k3 e) in
    (sigT_map_eq F0 (sigT_map_eq X0 he) ⊙ ((HK1 b ab ⊙ HK2 b ab) ⊙ HK3 b ab)) =
  ((HK1 a aa ⊙ HK2 a aa) ⊙ HK3 a aa) ⊙ sigT_map_eq F3 (sigT_map_eq X3 he).
Proof.
  eapply square_compose_dep.
  - eapply square_compose_dep.
    + now exact (square_coherence_dep_fill x0 x1 f0 f1 X0 X1 F0 F1 k1 HK1 e he).
    + now exact (square_coherence_dep_fill x1 x2 f1 f2 X1 X2 F1 F2 k2 HK2 e he).
  - now exact (square_coherence_dep_fill x2 x3 f2 f3 X2 X3 F2 F3 k3 HK3 e he).
Defined.

Lemma square_coherence_route_coherence_dep_computation
  {A A0 A1 A2 A3 B: Type} {PA: A -> Type}
  {P0: A0 -> Type} {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {PB: B -> Type}
  (x0: A -> A0) (x1: A -> A1) (x2: A -> A2) (x3: A -> A3)
  (f0: A0 -> B) (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (X0: forall a, PA a -> P0 (x0 a)) (X1: forall a, PA a -> P1 (x1 a))
  (X2: forall a, PA a -> P2 (x2 a)) (X3: forall a, PA a -> P3 (x3 a))
  (F0: forall x, P0 x -> PB (f0 x)) (F1: forall x, P1 x -> PB (f1 x))
  (F2: forall x, P2 x -> PB (f2 x)) (F3: forall x, P3 x -> PB (f3 x))
  (k1: forall a, f0 (x0 a) = f1 (x1 a))
  (k2: forall a, f1 (x1 a) = f2 (x2 a))
  (k3: forall a, f2 (x2 a) = f3 (x3 a))
  (HK1: forall a u, rew [PB] k1 a in F0 (x0 a) (X0 a u) = F1 (x1 a) (X1 a u))
  (HK2: forall a u, rew [PB] k2 a in F1 (x1 a) (X1 a u) = F2 (x2 a) (X2 a u))
  (HK3: forall a u, rew [PB] k3 a in F2 (x2 a) (X2 a u) = F3 (x3 a) (X3 a u))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  rew [fun S => rew [fun p => rew [PB] p in F0 (x0 a) (X0 a aa) = F3 (x3 b) (X3 b ab)] S in
    (sigT_map_eq F0 (sigT_map_eq X0 he) ⊙ (HK1 b ab ⊙ (HK2 b ab ⊙ HK3 b ab))) =
    (HK1 a aa ⊙ (HK2 a aa ⊙ HK3 a aa)) ⊙ sigT_map_eq F3 (sigT_map_eq X3 he)]
    square_coherence_route_canonical x0 x1 x2 x3 f0 f1 f2 f3 k1 k2 k3 e in
    square_coherence_route_coherence_dep x0 x1 x2 x3 f0 f1 f2 f3
      X0 X1 X2 X3 F0 F1 F2 F3 k1 k2 k3 HK1 HK2 HK3 e he =
  square_coherence_dep_fill x0 x3 f0 f3 X0 X3 F0 F3
    (fun a => k1 a • (k2 a • k3 a))
    (fun a u => HK1 a u ⊙ (HK2 a u ⊙ HK3 a u)) e he.
Proof.
  destruct e, he.
  unfold square_coherence_route_coherence_dep, square_coherence_route_canonical,
    square_coherence_dep_fill, square_coherence_fill, square_compose_dep.
  cbn.
  generalize (HK3 a aa). generalize (HK2 a aa). generalize (HK1 a aa).
  generalize (k3 a), (k2 a), (k1 a).
  generalize (F3 (x3 a) (X3 a aa)), (F2 (x2 a) (X2 a aa)), (F1 (x1 a) (X1 a aa)).
  generalize (f3 (x3 a)), (f2 (x2 a)), (f1 (x1 a)).
  intros y1 y2 y3 v1 v2 v3 p q r h1 h2 h3.
  now destruct h3, h2, h1, r, q, p.
Defined.

Lemma square_coherence_route_left_coherence_dep_computation
  {A A0 A1 A2 A3 B: Type} {PA: A -> Type}
  {P0: A0 -> Type} {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {PB: B -> Type}
  (x0: A -> A0) (x1: A -> A1) (x2: A -> A2) (x3: A -> A3)
  (f0: A0 -> B) (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (X0: forall a, PA a -> P0 (x0 a)) (X1: forall a, PA a -> P1 (x1 a))
  (X2: forall a, PA a -> P2 (x2 a)) (X3: forall a, PA a -> P3 (x3 a))
  (F0: forall x, P0 x -> PB (f0 x)) (F1: forall x, P1 x -> PB (f1 x))
  (F2: forall x, P2 x -> PB (f2 x)) (F3: forall x, P3 x -> PB (f3 x))
  (k1: forall a, f0 (x0 a) = f1 (x1 a))
  (k2: forall a, f1 (x1 a) = f2 (x2 a))
  (k3: forall a, f2 (x2 a) = f3 (x3 a))
  (HK1: forall a u, rew [PB] k1 a in F0 (x0 a) (X0 a u) = F1 (x1 a) (X1 a u))
  (HK2: forall a u, rew [PB] k2 a in F1 (x1 a) (X1 a u) = F2 (x2 a) (X2 a u))
  (HK3: forall a u, rew [PB] k3 a in F2 (x2 a) (X2 a u) = F3 (x3 a) (X3 a u))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  rew [fun S => rew [fun p => rew [PB] p in F0 (x0 a) (X0 a aa) = F3 (x3 b) (X3 b ab)] S in
    (sigT_map_eq F0 (sigT_map_eq X0 he) ⊙ ((HK1 b ab ⊙ HK2 b ab) ⊙ HK3 b ab)) =
    ((HK1 a aa ⊙ HK2 a aa) ⊙ HK3 a aa) ⊙ sigT_map_eq F3 (sigT_map_eq X3 he)]
    square_coherence_route_left_canonical x0 x1 x2 x3 f0 f1 f2 f3 k1 k2 k3 e in
    square_coherence_route_left_coherence_dep x0 x1 x2 x3 f0 f1 f2 f3
      X0 X1 X2 X3 F0 F1 F2 F3 k1 k2 k3 HK1 HK2 HK3 e he =
  square_coherence_dep_fill x0 x3 f0 f3 X0 X3 F0 F3
    (fun a => (k1 a • k2 a) • k3 a)
    (fun a u => (HK1 a u ⊙ HK2 a u) ⊙ HK3 a u) e he.
Proof.
  destruct e, he.
  unfold square_coherence_route_left_coherence_dep, square_coherence_route_left_canonical,
    square_coherence_dep_fill, square_coherence_fill, square_compose_dep.
  cbn.
  generalize (HK3 a aa). generalize (HK2 a aa). generalize (HK1 a aa).
  generalize (k3 a), (k2 a), (k1 a).
  generalize (F3 (x3 a) (X3 a aa)), (F2 (x2 a) (X2 a aa)), (F1 (x1 a) (X1 a aa)).
  generalize (f3 (x3 a)), (f2 (x2 a)), (f1 (x1 a)).
  intros y1 y2 y3 v1 v2 v3 p q r h1 h2 h3.
  now destruct h3, h2, h1, r, q, p.
Defined.

Lemma hexagonal_prism_coherence_nat_fill_coherence_dep {A A1 A2 A3 B: Type}
  {PA: A -> Type} {P1: A1 -> Type} {P2: A2 -> Type}
  {P3: A3 -> Type} {PB: B -> Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (x0 x1: A -> A1) (x2 x3: A -> A2) (x4 x5: A -> A3)
  (p1: forall a, x0 a = x1 a) (p2: forall a, x2 a = x3 a)
  (p3: forall a, x4 a = x5 a)
  (h1: forall a, f1 (x1 a) = f2 (x2 a))
  (h2: forall a, f1 (x0 a) = f3 (x4 a))
  (h3: forall a, f3 (x5 a) = f2 (x3 a))
  (H: forall a, hexagonal_coherence f1 f2 f3
    (p1 a) (p2 a) (p3 a) (h1 a) (h2 a) (h3 a))
  (X0: forall a, PA a -> P1 (x0 a)) (X1: forall a, PA a -> P1 (x1 a))
  (X2: forall a, PA a -> P2 (x2 a)) (X3: forall a, PA a -> P2 (x3 a))
  (X4: forall a, PA a -> P3 (x4 a)) (X5: forall a, PA a -> P3 (x5 a))
  (F1: forall x, P1 x -> PB (f1 x)) (F2: forall x, P2 x -> PB (f2 x))
  (F3: forall x, P3 x -> PB (f3 x))
  (hp1: forall a u, rew [P1] p1 a in X0 a u = X1 a u)
  (hp2: forall a u, rew [P2] p2 a in X2 a u = X3 a u)
  (hp3: forall a u, rew [P3] p3 a in X4 a u = X5 a u)
  (hh1: forall a u, rew [PB] h1 a in F1 (x1 a) (X1 a u) = F2 (x2 a) (X2 a u))
  (hh2: forall a u, rew [PB] h2 a in F1 (x0 a) (X0 a u) = F3 (x4 a) (X4 a u))
  (hh3: forall a u, rew [PB] h3 a in F3 (x5 a) (X5 a u) = F2 (x3 a) (X3 a u))
  (HH: forall a u, hexagonal_coherence_dep F1 F2 F3 (H a)
    (hp1 a u) (hp2 a u) (hp3 a u) (hh1 a u) (hh2 a u) (hh3 a u))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  square_cube_coherence_dep PB (square_compose
      (square_compose (square_coherence_fill x0 x1 f1 f1 (fun a => f_equal f1 (p1 a)) e)
        (square_coherence_fill x1 x2 f1 f2 h1 e))
      (square_coherence_fill x2 x3 f2 f2 (fun a => f_equal f2 (p2 a)) e))
    (square_compose (square_coherence_fill x0 x4 f1 f3 h2 e)
      (square_compose (square_coherence_fill x4 x5 f3 f3 (fun a => f_equal f3 (p3 a)) e)
        (square_coherence_fill x5 x3 f3 f2 h3 e))) (H b) (H a)
    (hexagonal_prism_coherence_nat_fill f1 f2 f3 x0 x1 x2 x3 x4 x5
      p1 p2 p3 h1 h2 h3 H e)
    ((sigT_map_eq F1 (hp1 a aa) ⊙ hh1 a aa) ⊙ sigT_map_eq F2 (hp2 a aa))
    (hh2 a aa ⊙ (sigT_map_eq F3 (hp3 a aa) ⊙ hh3 a aa))
    ((sigT_map_eq F1 (hp1 b ab) ⊙ hh1 b ab) ⊙ sigT_map_eq F2 (hp2 b ab))
    (hh2 b ab ⊙ (sigT_map_eq F3 (hp3 b ab) ⊙ hh3 b ab))
    (sigT_map_eq F1 (sigT_map_eq X0 he)) (sigT_map_eq F2 (sigT_map_eq X3 he))
    (square_coherence_route_left_coherence_dep x0 x1 x2 x3 f1 f1 f2 f2
      X0 X1 X2 X3 F1 F1 F2 F2
      (fun a => f_equal f1 (p1 a)) h1 (fun a => f_equal f2 (p2 a))
      (fun a u => sigT_map_eq F1 (hp1 a u)) hh1
      (fun a u => sigT_map_eq F2 (hp2 a u)) e he)
    (square_coherence_route_coherence_dep x0 x4 x5 x3 f1 f3 f3 f2
      X0 X4 X5 X3 F1 F3 F3 F2
      h2 (fun a => f_equal f3 (p3 a)) h3
      hh2 (fun a u => sigT_map_eq F3 (hp3 a u)) hh3 e he)
    (HH b ab) (HH a aa).
Proof.
  rewrite hexagonal_prism_coherence_nat_fill_routes_computation.
  eapply square_cube_change_faces_coherence_dep.
  - now exact (square_coherence_route_left_coherence_dep_computation
      x0 x1 x2 x3 f1 f1 f2 f2 X0 X1 X2 X3 F1 F1 F2 F2
      (fun a => f_equal f1 (p1 a)) h1 (fun a => f_equal f2 (p2 a))
      (fun a u => sigT_map_eq F1 (hp1 a u)) hh1
      (fun a u => sigT_map_eq F2 (hp2 a u)) e he).
  - now exact (square_coherence_family_cube_coherence_dep x0 x3 f1 f2 X0 X3 F1 F2
      (fun a => (f_equal f1 (p1 a) • h1 a) • f_equal f2 (p2 a))
      (fun a => h2 a • (f_equal f3 (p3 a) • h3 a)) H
      (fun a u => (sigT_map_eq F1 (hp1 a u) ⊙ hh1 a u) ⊙ sigT_map_eq F2 (hp2 a u))
      (fun a u => hh2 a u ⊙ (sigT_map_eq F3 (hp3 a u) ⊙ hh3 a u)) HH e he).
  - now exact (square_coherence_route_coherence_dep_computation
      x0 x4 x5 x3 f1 f3 f3 f2 X0 X4 X5 X3 F1 F3 F3 F2
      h2 (fun a => f_equal f3 (p3 a)) h3
      hh2 (fun a u => sigT_map_eq F3 (hp3 a u)) hh3 e he).
Defined.

Lemma square_cube_nat_prism_coherence_dep {A A1 A2 A3 B: Type}
  {PA: A -> Type} {P1: A1 -> Type} {P2: A2 -> Type}
  {P3: A3 -> Type} {PB: B -> Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (x0 x1: A -> A1) (x2 x3: A -> A2) (x4 x5: A -> A3)
  (p1: forall a, x0 a = x1 a) (p2: forall a, x2 a = x3 a)
  (p3: forall a, x4 a = x5 a)
  (h1: forall a, f1 (x1 a) = f2 (x2 a))
  (h2: forall a, f1 (x0 a) = f3 (x4 a))
  (h3: forall a, f3 (x5 a) = f2 (x3 a))
  (H: forall a, hexagonal_coherence f1 f2 f3
    (p1 a) (p2 a) (p3 a) (h1 a) (h2 a) (h3 a))
  (X0: forall a, PA a -> P1 (x0 a)) (X1: forall a, PA a -> P1 (x1 a))
  (X2: forall a, PA a -> P2 (x2 a)) (X3: forall a, PA a -> P2 (x3 a))
  (X4: forall a, PA a -> P3 (x4 a)) (X5: forall a, PA a -> P3 (x5 a))
  (F1: forall x, P1 x -> PB (f1 x)) (F2: forall x, P2 x -> PB (f2 x))
  (F3: forall x, P3 x -> PB (f3 x))
  (hp1: forall a u, rew [P1] p1 a in X0 a u = X1 a u)
  (hp2: forall a u, rew [P2] p2 a in X2 a u = X3 a u)
  (hp3: forall a u, rew [P3] p3 a in X4 a u = X5 a u)
  (hh1: forall a u, rew [PB] h1 a in F1 (x1 a) (X1 a u) = F2 (x2 a) (X2 a u))
  (hh2: forall a u, rew [PB] h2 a in F1 (x0 a) (X0 a u) = F3 (x4 a) (X4 a u))
  (hh3: forall a u, rew [PB] h3 a in F3 (x5 a) (X5 a u) = F2 (x3 a) (X3 a u))
  (HH: forall a u, hexagonal_coherence_dep F1 F2 F3 (H a)
    (hp1 a u) (hp2 a u) (hp3 a u) (hh1 a u) (hh2 a u) (hh3 a u))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab)
  {y0 y1: B} {b0 b1: y0 = y1} {p: f1 (x0 b) = y0} {q: f2 (x3 b) = y1}
  {H0: p • b0 = ((f_equal f1 (p1 b) • h1 b) • f_equal f2 (p2 b)) • q}
  {H1: p • b1 = (h2 b • (f_equal f3 (p3 b) • h3 b)) • q}
  {κ: b0 = b1} (C: square_cube H0 H1 κ (H b))
  {v0: PB y0} {v1: PB y1}
  {hb0: rew [PB] b0 in v0 = v1} {hb1: rew [PB] b1 in v0 = v1}
  {hp: rew [PB] p in F1 (x0 b) (X0 b ab) = v0}
  {hq: rew [PB] q in F2 (x3 b) (X3 b ab) = v1}
  {HH0: rew [fun t => rew [PB] t in F1 (x0 b) (X0 b ab) = v1] H0 in
    (hp ⊙ hb0) = ((sigT_map_eq F1 (hp1 b ab) ⊙ hh1 b ab) ⊙ sigT_map_eq F2 (hp2 b ab)) ⊙ hq}
  {HH1: rew [fun t => rew [PB] t in F1 (x0 b) (X0 b ab) = v1] H1 in
    (hp ⊙ hb1) = (hh2 b ab ⊙ (sigT_map_eq F3 (hp3 b ab) ⊙ hh3 b ab)) ⊙ hq}
  {Dκ: rew [fun t => rew [PB] t in v0 = v1] κ in hb0 = hb1}
  (CC: square_cube_coherence_dep PB H0 H1 κ (H b) C
    ((sigT_map_eq F1 (hp1 b ab) ⊙ hh1 b ab) ⊙ sigT_map_eq F2 (hp2 b ab)) (hh2 b ab ⊙ (sigT_map_eq F3 (hp3
      b ab) ⊙ hh3 b ab)) hb0 hb1 hp hq HH0 HH1 Dκ (HH b ab))
  {p': f1 (x0 a) = y0} {q': f2 (x3 a) = y1}
  {E0: p' = f_equal f1 (f_equal x0 e) • p}
  {E1: q' = f_equal f2 (f_equal x3 e) • q}
  {hp': rew [PB] p' in F1 (x0 a) (X0 a aa) = v0}
  {hq': rew [PB] q' in F2 (x3 a) (X3 a aa) = v1}
  (EE0: rew [fun t => rew [PB] t in F1 (x0 a) (X0 a aa) = v0] E0 in hp' =
    sigT_map_eq F1 (sigT_map_eq X0 he) ⊙ hp)
  (EE1: rew [fun t => rew [PB] t in F2 (x3 a) (X3 a aa) = v1] E1 in hq' =
    sigT_map_eq F2 (sigT_map_eq X3 he) ⊙ hq):
  let NL := square_compose (square_compose (square_coherence_fill x0 x1 f1 f1 (fun a => f_equal f1 (p1
    a)) e) (square_coherence_fill x1 x2 f1 f2 h1 e)) (square_coherence_fill x2 x3 f2 f2 (fun a => f_equal
    f2 (p2 a)) e) in
  let NR := square_compose (square_coherence_fill x0 x4 f1 f3 h2 e)
    (square_compose (square_coherence_fill x4 x5 f3 f3 (fun a => f_equal f3 (p3 a)) e)
      (square_coherence_fill x5 x3 f3 f2 h3 e)) in
  let DNL := square_coherence_route_left_coherence_dep x0 x1 x2 x3 f1 f1 f2 f2
    X0 X1 X2 X3 F1 F1 F2 F2
    (fun a => f_equal f1 (p1 a)) h1 (fun a => f_equal f2 (p2 a))
    (fun a u => sigT_map_eq F1 (hp1 a u)) hh1
    (fun a u => sigT_map_eq F2 (hp2 a u)) e he in
  let DNR := square_coherence_route_coherence_dep x0 x4 x5 x3 f1 f3 f3 f2
    X0 X4 X5 X3 F1 F3 F3 F2 h2 (fun a => f_equal f3 (p3 a)) h3
    hh2 (fun a u => sigT_map_eq F3 (hp3 a u)) hh3 e he in
  let LL := square_change_sides_dep PB E0 _ E1 _ _ _ hp' _ hq' EE0
    (square_stack_dep PB _ _ _ _ _ _ _ _ _ DNL HH0) EE1 in
  let RR := square_change_sides_dep PB E0 _ E1 _ _ _ hp' _ hq' EE0
    (square_stack_dep PB _ _ _ _ _ _ _ _ _ DNR HH1) EE1 in
  square_cube_coherence_dep PB
    (square_change_sides E0 (square_stack NL H0) E1)
    (square_change_sides E0 (square_stack NR H1) E1) κ (H a)
    (square_cube_change_sides E0 E1
      (square_cube_stack
        (hexagonal_prism_coherence_nat_fill f1 f2 f3 x0 x1 x2 x3 x4 x5
          p1 p2 p3 h1 h2 h3 H e) C))
    ((sigT_map_eq F1 (hp1 a aa) ⊙ hh1 a aa) ⊙ sigT_map_eq F2 (hp2 a aa)) (hh2 a aa ⊙ (sigT_map_eq F3 (hp3
      a aa) ⊙ hh3 a aa)) hb0 hb1 hp' hq' LL RR Dκ (HH a aa).
Proof.
  intros NL NR DNL DNR LL RR.
  eapply (square_cube_change_sides_coherence_dep PB E0 E1 _ EE0 EE1).
  eapply square_cube_stack_coherence_dep.
  - now exact (hexagonal_prism_coherence_nat_fill_coherence_dep
        f1 f2 f3 x0 x1 x2 x3 x4 x5 p1 p2 p3 h1 h2 h3 H
        X0 X1 X2 X3 X4 X5 F1 F2 F3 hp1 hp2 hp3 hh1 hh2 hh3 HH e he).
  - now exact CC.
Defined.

Lemma square_cube_map_along_coherence_dep
  {T X U Y: Type} {PT: T -> Type} {PX: X -> Type} {PU: U -> Type} {PY: Y -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (J: forall u, PU u -> PY (j u))
  (α: forall t, f (r t) = j (g t))
  (Hα: forall t a, rew [PY] α t in F (r t) (R t a) = J (g t) (G t a))
  {t0 t1: T} {x0 x1: X} {a a': x0 = x1} {b b': t0 = t1}
  {p: x0 = r t0} {q: x1 = r t1}
  (H: p • f_equal r b = a • q) (K: p • f_equal r b' = a' • q)
  (κ: b = b') (λ: a = a')
  (C: square_cube H K (f_equal (fun e => f_equal r e) κ) λ)
  {u0: PX x0} {u1: PX x1} {v0: PT t0} {v1: PT t1}
  (ha: rew [PX] a in u0 = u1) (ha': rew [PX] a' in u0 = u1)
  (hb: rew [PT] b in v0 = v1) (hb': rew [PT] b' in v0 = v1)
  (hp: rew [PX] p in u0 = R t0 v0) (hq: rew [PX] q in u1 = R t1 v1)
  (HH: rew [fun e => rew [PX] e in u0 = R t1 v1] H in
    (hp ⊙ sigT_map_eq R hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [PX] e in u0 = R t1 v1] K in
    (hp ⊙ sigT_map_eq R hb') = ha' ⊙ hq)
  (Dκ: rew [fun e => rew [PT] e in v0 = v1] κ in hb = hb')
  (Dλ: rew [fun e => rew [PX] e in u0 = u1] λ in ha = ha')
  (CC: square_cube_coherence_dep PX H K (f_equal (fun e => f_equal r e) κ) λ C
    ha ha' (sigT_map_eq R hb) (sigT_map_eq R hb') hp hq HH KK (sigT_map_eq
      (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq R h) Dκ) Dλ)
  {N0: square_coherence r g f j α b} {N1: square_coherence r g f j α b'}
  (N: square_cube (eq_sym N0) (eq_sym N1)
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) κ))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) κ)))
  (DN0: rew [fun e => rew [PY] e in F (r t0) (R t0 v0) = J (g t1) (G t1 v1)]
    eq_sym N0 in (Hα t0 v0 ⊙ sigT_map_eq J (sigT_map_eq G hb)) =
    sigT_map_eq F (sigT_map_eq R hb) ⊙ Hα t1 v1)
  (DN1: rew [fun e => rew [PY] e in F (r t0) (R t0 v0) = J (g t1) (G t1 v1)]
    eq_sym N1 in (Hα t0 v0 ⊙ sigT_map_eq J (sigT_map_eq G hb')) =
    sigT_map_eq F (sigT_map_eq R hb') ⊙ Hα t1 v1)
  (NN: square_cube_coherence_dep PY (eq_sym N0) (eq_sym N1)
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) κ))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) κ)) N
    (sigT_map_eq F (sigT_map_eq R hb)) (sigT_map_eq F (sigT_map_eq R hb'))
    (sigT_map_eq J (sigT_map_eq G hb)) (sigT_map_eq J (sigT_map_eq G hb'))
    (Hα t0 v0) (Hα t1 v1) DN0 DN1 (sigT_map_eq
      (fun (e: g t0 = g t1) (h: rew [PU] e in G t0 v0 = G t1 v1) => sigT_map_eq J h) (sigT_map_eq
        (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq G h) Dκ)) (sigT_map_eq
      (fun (e: r t0 = r t1) (h: rew [PX] e in R t0 v0 = R t1 v1) => sigT_map_eq F h) (sigT_map_eq
        (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq R h) Dκ))):
  let L := square_map_along_dep r g f j α PX PY F b H
    N0 ha (sigT_map_eq R hb) hp hq
    (Hα t0 v0) (Hα t1 v1) (sigT_map_eq J (sigT_map_eq G hb)) HH DN0 in
  let M := square_map_along_dep r g f j α PX PY F b' K
    N1 ha' (sigT_map_eq R hb') hp hq
    (Hα t0 v0) (Hα t1 v1) (sigT_map_eq J (sigT_map_eq G hb')) KK DN1 in
  square_cube_coherence_dep PY
    (square_map_along r g f j α b H N0)
    (square_map_along r g f j α b' K N1)
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) κ))
    (f_equal (fun e => f_equal f e) λ)
    (square_cube_map_along r g f j α C N)
    (sigT_map_eq F ha) (sigT_map_eq F ha')
    (sigT_map_eq J (sigT_map_eq G hb)) (sigT_map_eq J (sigT_map_eq G hb'))
    (sigT_map_eq F hp ⊙ Hα t0 v0) (sigT_map_eq F hq ⊙ Hα t1 v1) L M (sigT_map_eq
      (fun (e: g t0 = g t1) (h: rew [PU] e in G t0 v0 = G t1 v1) => sigT_map_eq J h) (sigT_map_eq
        (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq G h) Dκ)) (sigT_map_eq
      (fun (e: x0 = x1) (h: rew [PX] e in u0 = u1) => sigT_map_eq F h) Dλ).
Proof.
  intros L M. unfold square_cube_map_along.
  now exact (square_cube_stack_coherence_dep PY (square_cube_map f C) N
    (square_cube_map_coherence_dep f F C CC) NN).
Defined.

Lemma square_cube_map_along_canonical_coherence_dep
  {T X U Y: Type} {PT: T -> Type} {PX: X -> Type} {PU: U -> Type} {PY: Y -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (J: forall u, PU u -> PY (j u))
  (α: forall t, f (r t) = j (g t))
  (Hα: forall t a, rew [PY] α t in F (r t) (R t a) = J (g t) (G t a))
  {t0 t1: T} {x0 x1: X} {a a': x0 = x1} {b b': t0 = t1}
  {p: x0 = r t0} {q: x1 = r t1}
  {H: p • f_equal r b = a • q} {K: p • f_equal r b' = a' • q}
  {κ: b = b'} {λ: a = a'}
  (C: square_cube H K (f_equal (fun e => f_equal r e) κ) λ)
  {u0: PX x0} {u1: PX x1} {v0: PT t0} {v1: PT t1}
  {ha: rew [PX] a in u0 = u1} {ha': rew [PX] a' in u0 = u1}
  {hb: rew [PT] b in v0 = v1} {hb': rew [PT] b' in v0 = v1}
  {hp: rew [PX] p in u0 = R t0 v0} {hq: rew [PX] q in u1 = R t1 v1}
  {HH: rew [fun e => rew [PX] e in u0 = R t1 v1] H in
    (hp ⊙ sigT_map_eq R hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [PX] e in u0 = R t1 v1] K in
    (hp ⊙ sigT_map_eq R hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [PT] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [PX] e in u0 = u1] λ in ha = ha'}
  (CC: square_cube_coherence_dep PX H K (f_equal (fun e => f_equal r e) κ) λ C
    ha ha' (sigT_map_eq R hb) (sigT_map_eq R hb') hp hq HH KK (sigT_map_eq
      (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq R h) Dκ) Dλ):
  let L := square_map_along_dep r g f j α PX PY F b H
    (square_coherence_fill r g f j α b) ha (sigT_map_eq R hb) hp hq
    (Hα t0 v0) (Hα t1 v1) (sigT_map_eq J (sigT_map_eq G hb)) HH
    (square_coherence_dep_reverse_fill r g f j R G F J α Hα b hb) in
  let M := square_map_along_dep r g f j α PX PY F b' K
    (square_coherence_fill r g f j α b') ha' (sigT_map_eq R hb') hp hq
    (Hα t0 v0) (Hα t1 v1) (sigT_map_eq J (sigT_map_eq G hb')) KK
    (square_coherence_dep_reverse_fill r g f j R G F J α Hα b' hb') in
  square_cube_coherence_dep PY
    (square_map_along r g f j α b H (square_coherence_fill r g f j α b))
    (square_map_along r g f j α b' K (square_coherence_fill r g f j α b'))
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) κ))
    (f_equal (fun e => f_equal f e) λ)
    (square_cube_map_along r g f j α C (square_coherence_cube r g f j α κ))
    (sigT_map_eq F ha) (sigT_map_eq F ha')
    (sigT_map_eq J (sigT_map_eq G hb)) (sigT_map_eq J (sigT_map_eq G hb'))
    (sigT_map_eq F hp ⊙ Hα t0 v0) (sigT_map_eq F hq ⊙ Hα t1 v1) L M (sigT_map_eq
      (fun (e: g t0 = g t1) (h: rew [PU] e in G t0 v0 = G t1 v1) => sigT_map_eq J h) (sigT_map_eq
        (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq G h) Dκ)) (sigT_map_eq
      (fun (e: x0 = x1) (h: rew [PX] e in u0 = u1) => sigT_map_eq F h) Dλ).
Proof.
  intros L M. unfold square_cube_map_along.
  eapply square_cube_stack_coherence_dep.
  - now exact (square_cube_map_coherence_dep f F C CC).
  - now exact (square_coherence_cube_dep_fill r g f j R G F J α Hα κ hb hb' Dκ).
Defined.

Lemma map_compose_path_map_dep {A B C D: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (f: B -> C) (g: A -> B) (j: C -> D)
  (F: forall b, PB b -> PC (f b)) (G: forall a, PA a -> PB (g a))
  (J: forall c, PC c -> PD (j c)) {a b: A} (e: a = b)
  {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  rew [fun p => rew [PD] p in J (f (g a)) (F (g a) (G a aa)) =
    J (f (g b)) (F (g b) (G b ab))]
    (f_equal (fun p => f_equal j p) (eq_sym (map_compose_path f g e))) in
    sigT_map_eq J (sigT_map_eq F (sigT_map_eq G he)) =
  sigT_map_eq J (sigT_map_eq (fun a u => F (g a) (G a u)) he).
Proof. now destruct e, he. Defined.

Lemma square_coherence_map_edges_coherence_dep {A B C D E: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type} {PE: E -> Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D) (j: D -> E)
  (U: forall a, PA a -> PB (u a)) (V: forall a, PA a -> PC (v a))
  (F: forall b, PB b -> PD (f b)) (G: forall c, PC c -> PD (g c))
  (J: forall d, PD d -> PE (j d))
  (K: forall a, f (u a) = g (v a))
  (HK: forall a z, rew [PD] K a in F (u a) (U a z) = G (v a) (V a z))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  let Hp := f_equal (fun p => f_equal j p) (eq_sym (map_compose_path f u e)) in
  let Hq := f_equal (fun p => f_equal j p) (eq_sym (map_compose_path g v e)) in
  let M := square_change_sides_dep PE Hp
    (square_coherence_fill (fun z => f (u z)) (fun z => g (v z)) j j
      (fun z => f_equal j (K z)) e) Hq _ _ _ _ _ _
    (map_compose_path_map_dep f u j F U J e he)
    (square_coherence_dep_fill (fun z => f (u z)) (fun z => g (v z)) j j
      (fun a z => F (u a) (U a z)) (fun a z => G (v a) (V a z)) J J
      (fun z => f_equal j (K z)) (fun a z => sigT_map_eq J (HK a z)) e he)
    (map_compose_path_map_dep g v j G V J e he) in
  rew [fun S => rew [fun p => rew [PE] p in J (f (u a)) (F (u a) (U a aa)) =
    J (g (v b)) (G (v b) (V b ab))] S in
    (sigT_map_eq J (sigT_map_eq F (sigT_map_eq U he)) ⊙ sigT_map_eq J (HK b ab)) =
    sigT_map_eq J (HK a aa) ⊙ sigT_map_eq J (sigT_map_eq G (sigT_map_eq V he))]
    square_coherence_map_edges u v f g j K e in
    (square_map_dep j J (square_coherence_fill u v f g K e)
      (HK a aa) (HK b ab) (sigT_map_eq F (sigT_map_eq U he))
      (sigT_map_eq G (sigT_map_eq V he))
      (square_coherence_dep_fill u v f g U V F G K HK e he)) = M.
Proof.
  intros Hp Hq M. subst M Hp Hq.
  destruct e, he.
  unfold square_coherence_map_edges, square_map_dep, square_coherence_dep_fill,
    square_coherence_fill, square_change_sides_dep, map_compose_path_map_dep.
  cbn.
  generalize (HK a aa).
  generalize (K a), (G (v a) (V a aa)).
  generalize (g (v a)).
  intros z k w hk. now destruct hk, k.
Defined.

Lemma square_coherence_precompose_coherence_dep {A B C D E: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type} {PE: E -> Type}
  (w: A -> B) (u: B -> C) (v: B -> D) (f: C -> E) (g: D -> E)
  (W: forall a, PA a -> PB (w a)) (U: forall b, PB b -> PC (u b))
  (V: forall b, PB b -> PD (v b))
  (F: forall c, PC c -> PE (f c)) (G: forall d, PD d -> PE (g d))
  (K: forall b, f (u b) = g (v b))
  (HK: forall b z, rew [PE] K b in F (u b) (U b z) = G (v b) (V b z))
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  let Hp := f_equal (fun p => f_equal f p) (eq_sym (map_compose_path u w e)) in
  let Hq := f_equal (fun p => f_equal g p) (eq_sym (map_compose_path v w e)) in
  let M := square_change_sides_dep PE Hp
    (square_coherence_fill (fun z => u (w z)) (fun z => v (w z)) f g
      (fun z => K (w z)) e) Hq _ _ _ _ _ _
    (map_compose_path_map_dep u w f U W F e he)
    (square_coherence_dep_fill (fun z => u (w z)) (fun z => v (w z)) f g
      (fun a z => U (w a) (W a z)) (fun a z => V (w a) (W a z)) F G
      (fun z => K (w z)) (fun a z => HK (w a) (W a z)) e he)
    (map_compose_path_map_dep v w g V W G e he) in
  rew [fun S => rew [fun p => rew [PE] p in F (u (w a)) (U (w a) (W a aa)) =
    G (v (w b)) (V (w b) (W b ab))] S in
    (sigT_map_eq F (sigT_map_eq U (sigT_map_eq W he)) ⊙ HK (w b) (W b ab)) =
    HK (w a) (W a aa) ⊙ sigT_map_eq G (sigT_map_eq V (sigT_map_eq W he))]
    square_coherence_precompose w u v f g K e in
    (square_coherence_dep_fill u v f g U V F G K HK
      (f_equal w e) (sigT_map_eq W he)) = M.
Proof.
  intros Hp Hq M. subst M Hp Hq.
  destruct e, he.
  unfold square_coherence_precompose, square_coherence_dep_fill,
    square_coherence_fill, square_change_sides_dep, map_compose_path_map_dep.
  cbn.
  generalize (HK (w a) (W a aa)).
  generalize (K (w a)), (G (v (w a)) (V (w a) (W a aa))).
  generalize (g (v (w a))).
  intros z k t hk. now destruct hk, k.
Defined.

Lemma square_map_along_twice_coherence_dep
  {T X U Y V Z: Type} {PT: T -> Type} {PX: X -> Type} {PU: U -> Type}
  {PY: Y -> Type} {PV: V -> Type} {PZ: Z -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (r1: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (R1: forall u, PU u -> PY (r1 u))
  (α: forall t, f (r t) = r1 (g t))
  (Hα: forall t a, rew [PY] α t in F (r t) (R t a) = R1 (g t) (G t a))
  (g1: U -> V) (j0: Y -> Z) (j: V -> Z)
  (G1: forall u, PU u -> PV (g1 u)) (J0: forall y, PY y -> PZ (j0 y))
  (J: forall v, PV v -> PZ (j v))
  (β: forall u, j0 (r1 u) = j (g1 u))
  (Hβ: forall u a, rew [PZ] β u in J0 (r1 u) (R1 u a) = J (g1 u) (G1 u a))
  {t0 t1: T} (e: t0 = t1) {x0 x1: X} {a: x0 = x1}
  {p: x0 = r t0} {q: x1 = r t1} (H: p • f_equal r e = a • q)
  {u0: PX x0} {u1: PX x1} {v0: PT t0} {v1: PT t1}
  (ha: rew [PX] a in u0 = u1) (he: rew [PT] e in v0 = v1)
  (hp: rew [PX] p in u0 = R t0 v0) (hq: rew [PX] q in u1 = R t1 v1)
  (HH: rew [fun p => rew [PX] p in u0 = R t1 v1] H in
    (hp ⊙ sigT_map_eq R he) = ha ⊙ hq):
  let Nα := square_coherence_fill r g f r1 α e in
  let Nβ := square_coherence_fill r1 g1 j0 j β (f_equal g e) in
  let Dα := square_coherence_dep_fill r g f r1 R G F R1 α Hα e he in
  let Dβ := square_coherence_dep_fill r1 g1 j0 j R1 G1 J0 J β Hβ
    (f_equal g e) (sigT_map_eq G he) in
  let N := square_compose (square_map j0 Nα) Nβ in
  let DN := square_compose_dep PZ _ _ _ _ _ _ _ _ _
    (square_map_dep j0 J0 Nα _ _ _ _ Dα) Dβ in
  let L0 := square_map_along_dep r g f r1 α PX PY F e H Nα
    ha (sigT_map_eq R he) hp hq (Hα t0 v0) (Hα t1 v1)
    (sigT_map_eq R1 (sigT_map_eq G he)) HH
    (square_coherence_dep_reverse_fill r g f r1 R G F R1 α Hα e he) in
  let L1 := square_map_along_dep r1 g1 j0 j β PY PZ J0 (f_equal g e)
    (square_map_along r g f r1 α e H Nα) Nβ
    (sigT_map_eq F ha) (sigT_map_eq R1 (sigT_map_eq G he))
    (sigT_map_eq F hp ⊙ Hα t0 v0) (sigT_map_eq F hq ⊙ Hα t1 v1)
    (Hβ (g t0) (G t0 v0)) (Hβ (g t1) (G t1 v1))
    (sigT_map_eq J (sigT_map_eq G1 (sigT_map_eq G he))) L0
    (square_coherence_dep_reverse_fill r1 g1 j0 j R1 G1 J0 J β Hβ
      (f_equal g e) (sigT_map_eq G he)) in
  let M0 := map_compose_tail j0 (f_equal f p) (α t0) (β (g t0)) in
  let M1 := map_compose_tail j0 (f_equal f q) (α t1) (β (g t1)) in
  let DM0 := map_compose_tail_dep j0 J0 (sigT_map_eq F hp)
    (Hα t0 v0) (Hβ (g t0) (G t0 v0)) in
  let DM1 := map_compose_tail_dep j0 J0 (sigT_map_eq F hq)
    (Hα t1 v1) (Hβ (g t1) (G t1 v1)) in
  let MH := square_map_dep j0 J0 (square_map f H) _ _ _ _
    (square_map_dep f F H ha (sigT_map_eq R he) hp hq HH) in
  let M := square_change_sides_dep PZ M0 _ M1 _ _ _ _ _ _ DM0
    (square_stack_dep PZ _ _ _ _ _ _ _ _ _ MH (sigT_sym_eq DN)) DM1 in
  rew [fun S => rew [fun p => rew [PZ] p in J0 (f x0) (F x0 u0) =
    J (g1 (g t1)) (G1 (g t1) (G t1 v1))] S in
    ((sigT_map_eq J0 (sigT_map_eq F hp ⊙ Hα t0 v0) ⊙ Hβ (g t0) (G t0 v0)) ⊙
      sigT_map_eq J (sigT_map_eq G1 (sigT_map_eq G he))) =
    sigT_map_eq J0 (sigT_map_eq F ha) ⊙
      (sigT_map_eq J0 (sigT_map_eq F hq ⊙ Hα t1 v1) ⊙ Hβ (g t1) (G t1 v1))]
    square_map_along_twice r g f r1 α g1 j0 j β e H in L1 = M.
Proof.
  intros Nα Nβ Dα Dβ N DN L0 L1 M0 M1 DM0 DM1 MH M.
  subst M MH DM0 DM1 M0 M1 L1 L0 DN N Dβ Dα Nβ Nα.
  destruct e, he.
  revert HH. revert ha. revert H. revert a.
  subst x0 x1.
  cbn [eq_rect] in hp, hq. subst u0 u1.
  intros a H ha HH.
  cbn [f_equal eq_trans] in H. subst a.
  change (eq_refl = f_equal (fun h => h) ha) in HH.
  generalize dependent HH. generalize dependent ha.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  cbn.
  unfold square_map_along_dep, square_coherence_dep_reverse_fill,
    square_coherence_dep_fill, square_coherence_fill, map_compose_tail_dep,
    square_map_along, square_stack_dep, square_map_dep, square_change_sides_dep.
  cbn.
  generalize (Hβ (g t0) (G t0 v0)).
  generalize (Hα t0 v0).
  generalize (β (g t0)). generalize (α t0).
  generalize (J (g1 (g t0)) (G1 (g t0) (G t0 v0))).
  generalize (R1 (g t0) (G t0 v0)).
  generalize (j (g1 (g t0))). generalize (r1 (g t0)).
  intros y z w t a0 b0 ha0 hb0.
  now destruct hb0, ha0, b0, a0.
Defined.

Lemma hexagonal_prism_map_square_cube_coherence_dep {A1 A2 A3 B U V C: Type}
  {PB: B -> Type} {PU: U -> Type} {PV: V -> Type} {PC: C -> Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  (u: B -> U) (v: B -> V) (f: U -> C) (g: V -> C)
  (K: forall b, f (u b) = g (v b))
  (U': forall b, PB b -> PU (u b)) (V': forall b, PB b -> PV (v b))
  (F: forall x, PU x -> PC (f x)) (G: forall x, PV x -> PC (g x))
  (HK: forall b a, rew [PC] K b in F (u b) (U' b a) = G (v b) (V' b a))
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  (p1: x0 = x1) (p2: x2 = x3) (p3: x4 = x5)
  (h1: f1 x1 = f2 x2) (h2: f1 x0 = f3 x4) (h3: f3 x5 = f2 x3)
  (H: hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3)
  {a0: PB (f1 x0)} {a1: PB (f1 x1)} {a2: PB (f2 x2)} {a3: PB (f2 x3)}
  {a4: PB (f3 x4)} {a5: PB (f3 x5)}
  (hr1: rew [PB] f_equal f1 p1 in a0 = a1)
  (hr2: rew [PB] f_equal f2 p2 in a2 = a3)
  (hr3: rew [PB] f_equal f3 p3 in a4 = a5)
  (hs1: rew [PB] h1 in a1 = a2) (hs2: rew [PB] h2 in a0 = a4)
  (hs3: rew [PB] h3 in a5 = a3)
  (HH: rew [fun e => rew [PB] e in a0 = a3] H in
    ((hr1 ⊙ hs1) ⊙ hr2) = hs2 ⊙ (hr3 ⊙ hs3)):
  let Hrect := H in
  let p := f_equal f1 p1 • h1 in
  let q := f_equal f3 p3 • h3 in
  let hp := hr1 ⊙ hs1 in
  let hq := hr3 ⊙ hs3 in
  let Np := square_coherence_fill u v f g K p in
  let Nq := square_coherence_fill u v f g K q in
  let Nb := square_coherence_fill u v f g K (f_equal f2 p2) in
  let Na := square_coherence_fill u v f g K h2 in
  let Hf := square_map_dep f F (square_map u Hrect) _ _ _ _
    (square_map_dep u U' Hrect hs2 hr2 hp hq HH) in
  let Hg := square_map_dep g G (square_map v Hrect) _ _ _ _
    (square_map_dep v V' Hrect hs2 hr2 hp hq HH) in
  let L := square_compose_dep PC _ _ _ _ _ _ _ _ _ Hf
    (square_coherence_dep_fill u v f g U' V' F G K HK q hq) in
  let M := square_compose_dep PC _ _ _ _ _ _ _ _ _
    (square_coherence_dep_fill u v f g U' V' F G K HK p hp) Hg in
  square_cube_coherence_dep PC
    (square_compose (square_map f (square_map u Hrect)) Nq)
    (square_compose Np (square_map g (square_map v Hrect))) Nb Na
    (hexagonal_prism_map_square_cube f1 f2 f3 u v f g K p1 p2 p3 h1 h2 h3 H
      (hexagonal_prism_coherence_map_fill f1 f2 f3 u v f g K p1 p2 p3 h1 h2 h3 H))
    (sigT_map_eq F (sigT_map_eq U' hs2) ⊙ HK (f3 x4) a4)
    (HK (f1 x0) a0 ⊙ sigT_map_eq G (sigT_map_eq V' hs2))
    (sigT_map_eq F (sigT_map_eq U' hr2) ⊙ HK (f2 x3) a3)
    (HK (f2 x2) a2 ⊙ sigT_map_eq G (sigT_map_eq V' hr2))
    (sigT_map_eq F (sigT_map_eq U' hp)) (sigT_map_eq G (sigT_map_eq V' hq)) L M
    (square_coherence_dep_fill u v f g U' V' F G K HK (f_equal f2 p2) hr2)
    (square_coherence_dep_fill u v f g U' V' F G K HK h2 hs2).
Proof.
  intros Hrect p q hp hq Np Nq Nb Na Hf Hg L M.
  subst M L Hg Hf Na Nb Nq Np hq hp q p Hrect.
  unfold square_cube_coherence_dep, hexagonal_prism_map_square_cube,
    hexagonal_prism_coherence_map_fill, hexagonal_prism_coherence_map,
    hexagonal_prism_coherence, hexagonal_coherence.
  unfold square_compose_dep, square_map_dep, square_coherence_dep_fill,
    square_coherence_fill.
  unfold hexagonal_coherence in H.
  generalize HH.
  generalize hs3.
  generalize hr3.
  generalize hs2.
  generalize hr2.
  generalize hs1.
  generalize hr1.
  generalize H.
  generalize (h3).
  generalize (f_equal f3 p3).
  generalize (h2).
  generalize (f_equal f2 p2).
  generalize (h1).
  generalize (f_equal f1 p1).
  generalize a5.
  generalize a4.
  generalize a3.
  generalize a2.
  generalize a1.
  generalize a0.
  generalize (f3 x5).
  generalize (f3 x4).
  generalize (f2 x3).
  generalize (f2 x2).
  generalize (f1 x1).
  generalize (f1 x0).
  intros y0 y1 y2 y3 y4 y5 v0 v1 v2 v3 v4 v5 r1 r2 r3 s1 s2 s3 h
    q1 q2 q3 w1 w2 w3 hh.
  destruct r2, r3, s2, s3, s1. cbn in h. subst r1.
  cbn [eq_rect eq_trans f_equal] in *.
  destruct q2, q3, w2, w3, w1.
  cbn [eq_rect eq_trans] in hh.
  change (f_equal (fun h => h) (f_equal (fun h => h) q1) = eq_refl) in hh.
  generalize dependent hh. generalize dependent q1.
  apply (homotopy_path_ind
    (fun h => f_equal (fun h => h) (f_equal (fun h => h) h))
    (fun h => f_equal_id (f_equal (fun h => h) h) • f_equal_id h)).
  cbn.
  generalize (HK y0 v0).
  generalize (K y0), (G (v y0) (V' y0 v0)).
  generalize (g (v y0)).
  intros z k w hk. now destruct hk, k.
Defined.

Lemma square_compose_change_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 x2 y0 y1 y2: X} {a: x0 = x1} {b: x1 = x2}
  {c: y0 = y1} {d: y1 = y2} {p: x0 = y0} {q: x1 = y1} {r: x2 = y2}
  {H H': p • c = a • q} {K K': q • d = b • r} (E: H = H') (F: K = K')
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: P y0} {v1: P y1} {v2: P y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [P] c in v0 = v1) (hd: rew [P] d in v1 = v2)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in u2 = v2)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (HH': rew [fun e => rew [P] e in u0 = v1] H' in (hp ⊙ hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = v2] K in (hq ⊙ hd) = hb ⊙ hr)
  (KK': rew [fun e => rew [P] e in u1 = v2] K' in (hq ⊙ hd) = hb ⊙ hr)
  (EE: rew [fun S => rew [fun e => rew [P] e in u0 = v1] S in
    (hp ⊙ hc) = ha ⊙ hq] E in HH = HH')
  (FF: rew [fun S => rew [fun e => rew [P] e in u1 = v2] S in
    (hq ⊙ hd) = hb ⊙ hr] F in KK = KK'):
  rew [fun S => rew [fun e => rew [P] e in u0 = v2] S in
    (hp ⊙ (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr]
    path_map2 (fun H K => square_compose H K) E F in
    square_compose_dep P H K ha hb hc hd hp hq hr HH KK =
  square_compose_dep P H' K' ha hb hc hd hp hq hr HH' KK'.
Proof. destruct E, F. cbn in EE, FF. destruct EE, FF. now reflexivity. Defined.

Lemma square_change_sides_route_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 x2 x3 y0 y1 y2 y3: X}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {p0 q0: x0 = y0} {p1 q1: x1 = y1} {p2 q2: x2 = y2} {p3 q3: x3 = y3}
  (M0: q0 = p0) (M1: q1 = p1) (M2: q2 = p2) (M3: q3 = p3)
  (S1: p0 • b1 = a1 • p1) (S2: p1 • b2 = a2 • p2) (S3: p2 • b3 = a3 • p3)
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  {v0: P y0} {v1: P y1} {v2: P y2} {v3: P y3}
  (ha1: rew [P] a1 in u0 = u1) (ha2: rew [P] a2 in u1 = u2)
  (ha3: rew [P] a3 in u2 = u3)
  (hb1: rew [P] b1 in v0 = v1) (hb2: rew [P] b2 in v1 = v2)
  (hb3: rew [P] b3 in v2 = v3)
  (hp0: rew [P] p0 in u0 = v0) (hp1: rew [P] p1 in u1 = v1)
  (hp2: rew [P] p2 in u2 = v2) (hp3: rew [P] p3 in u3 = v3)
  (hq0: rew [P] q0 in u0 = v0) (hq1: rew [P] q1 in u1 = v1)
  (hq2: rew [P] q2 in u2 = v2) (hq3: rew [P] q3 in u3 = v3)
  (DM0: rew [fun e => rew [P] e in u0 = v0] M0 in hq0 = hp0)
  (DM1: rew [fun e => rew [P] e in u1 = v1] M1 in hq1 = hp1)
  (DM2: rew [fun e => rew [P] e in u2 = v2] M2 in hq2 = hp2)
  (DM3: rew [fun e => rew [P] e in u3 = v3] M3 in hq3 = hp3)
  (HS1: rew [fun e => rew [P] e in u0 = v1] S1 in (hp0 ⊙ hb1) = ha1 ⊙ hp1)
  (HS2: rew [fun e => rew [P] e in u1 = v2] S2 in (hp1 ⊙ hb2) = ha2 ⊙ hp2)
  (HS3: rew [fun e => rew [P] e in u2 = v3] S3 in (hp2 ⊙ hb3) = ha3 ⊙ hp3):
  let H1 := square_change_sides_dep P M0 S1 M1 ha1 hb1 hp0 hq0 hp1 hq1 DM0 HS1 DM1 in
  let H2 := square_change_sides_dep P M1 S2 M2 ha2 hb2 hp1 hq1 hp2 hq2 DM1 HS2 DM2 in
  let H3 := square_change_sides_dep P M2 S3 M3 ha3 hb3 hp2 hq2 hp3 hq3 DM2 HS3 DM3 in
  rew [fun S => rew [fun e => rew [P] e in u0 = v3] S in
    (hq0 ⊙ (hb1 ⊙ (hb2 ⊙ hb3))) = (ha1 ⊙ (ha2 ⊙ ha3)) ⊙ hq3]
    square_change_sides_route M0 M1 M2 M3 S1 S2 S3 in
    square_compose_dep P _ _ _ _ _ _ _ _ _ H1
      (square_compose_dep P _ _ _ _ _ _ _ _ _ H2 H3) =
  square_change_sides_dep P M0 _ M3 _ _ hp0 hq0 hp3 hq3 DM0
    (square_compose_dep P S1 (square_compose S2 S3) _ _ _ _ hp0 hp1 hp3 HS1
      (square_compose_dep P S2 S3 ha2 ha3 hb2 hb3 hp1 hp2 hp3 HS2 HS3)) DM3.
Proof.
  intros H1 H2 H3. subst H1 H2 H3.
  destruct M0, DM0, M1, DM1, M2, DM2, M3, DM3.
  destruct q0, q1, q2, q3, hq0, hq1, hq2, hq3.
  cbn in S1, S2, S3. destruct S1, S2, S3, b1, b2, b3.
  cbn [eq_rect eq_trans] in *.
  destruct hb1, hb2, hb3.
  change (eq_refl = f_equal (fun h => h) ha1) in HS1.
  change (eq_refl = f_equal (fun h => h) ha2) in HS2.
  change (eq_refl = f_equal (fun h => h) ha3) in HS3.
  revert HS1. revert ha1.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  revert HS2. revert ha2.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  revert HS3. revert ha3.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  now reflexivity.
Defined.

Lemma square_change_sides_route_left_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 x2 x3 y0 y1 y2 y3: X}
  {a1: x0 = x1} {a2: x1 = x2} {a3: x2 = x3}
  {b1: y0 = y1} {b2: y1 = y2} {b3: y2 = y3}
  {p0 q0: x0 = y0} {p1 q1: x1 = y1} {p2 q2: x2 = y2} {p3 q3: x3 = y3}
  (M0: q0 = p0) (M1: q1 = p1) (M2: q2 = p2) (M3: q3 = p3)
  (S1: p0 • b1 = a1 • p1) (S2: p1 • b2 = a2 • p2) (S3: p2 • b3 = a3 • p3)
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  {v0: P y0} {v1: P y1} {v2: P y2} {v3: P y3}
  (ha1: rew [P] a1 in u0 = u1) (ha2: rew [P] a2 in u1 = u2)
  (ha3: rew [P] a3 in u2 = u3)
  (hb1: rew [P] b1 in v0 = v1) (hb2: rew [P] b2 in v1 = v2)
  (hb3: rew [P] b3 in v2 = v3)
  (hp0: rew [P] p0 in u0 = v0) (hp1: rew [P] p1 in u1 = v1)
  (hp2: rew [P] p2 in u2 = v2) (hp3: rew [P] p3 in u3 = v3)
  (hq0: rew [P] q0 in u0 = v0) (hq1: rew [P] q1 in u1 = v1)
  (hq2: rew [P] q2 in u2 = v2) (hq3: rew [P] q3 in u3 = v3)
  (DM0: rew [fun e => rew [P] e in u0 = v0] M0 in hq0 = hp0)
  (DM1: rew [fun e => rew [P] e in u1 = v1] M1 in hq1 = hp1)
  (DM2: rew [fun e => rew [P] e in u2 = v2] M2 in hq2 = hp2)
  (DM3: rew [fun e => rew [P] e in u3 = v3] M3 in hq3 = hp3)
  (HS1: rew [fun e => rew [P] e in u0 = v1] S1 in (hp0 ⊙ hb1) = ha1 ⊙ hp1)
  (HS2: rew [fun e => rew [P] e in u1 = v2] S2 in (hp1 ⊙ hb2) = ha2 ⊙ hp2)
  (HS3: rew [fun e => rew [P] e in u2 = v3] S3 in (hp2 ⊙ hb3) = ha3 ⊙ hp3):
  let H1 := square_change_sides_dep P M0 S1 M1 ha1 hb1 hp0 hq0 hp1 hq1 DM0 HS1 DM1 in
  let H2 := square_change_sides_dep P M1 S2 M2 ha2 hb2 hp1 hq1 hp2 hq2 DM1 HS2 DM2 in
  let H3 := square_change_sides_dep P M2 S3 M3 ha3 hb3 hp2 hq2 hp3 hq3 DM2 HS3 DM3 in
  rew [fun S => rew [fun e => rew [P] e in u0 = v3] S in
    (hq0 ⊙ ((hb1 ⊙ hb2) ⊙ hb3)) = ((ha1 ⊙ ha2) ⊙ ha3) ⊙ hq3]
    square_change_sides_route_left M0 M1 M2 M3 S1 S2 S3 in
    square_compose_dep P _ _ _ _ _ _ _ _ _
      (square_compose_dep P _ _ _ _ _ _ _ _ _ H1 H2) H3 =
  square_change_sides_dep P M0 _ M3 _ _ hp0 hq0 hp3 hq3 DM0
    (square_compose_dep P (square_compose S1 S2) S3 _ _ _ _ hp0 hp2 hp3
      (square_compose_dep P S1 S2 ha1 ha2 hb1 hb2 hp0 hp1 hp2 HS1 HS2) HS3) DM3.
Proof.
  intros H1 H2 H3. subst H1 H2 H3.
  destruct M0, DM0, M1, DM1, M2, DM2, M3, DM3.
  destruct q0, q1, q2, q3, hq0, hq1, hq2, hq3.
  cbn in S1, S2, S3. destruct S1, S2, S3, b1, b2, b3.
  cbn [eq_rect eq_trans] in *.
  destruct hb1, hb2, hb3.
  change (eq_refl = f_equal (fun h => h) ha1) in HS1.
  change (eq_refl = f_equal (fun h => h) ha2) in HS2.
  change (eq_refl = f_equal (fun h => h) ha3) in HS3.
  revert HS1. revert ha1.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  revert HS2. revert ha2.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  revert HS3. revert ha3.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  now reflexivity.
Defined.

Lemma square_compose_map_change_coherence_dep {X Y: Type}
  (f: Y -> X) (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2: X} {y0 y1 y2: Y} {a: x0 = x1} {b: x1 = x2}
  {c: y0 = y1} {d: y1 = y2} {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  {H H': p • f_equal f c = a • q} {K K': q • f_equal f d = b • r}
  (E: H = H') (G: K = K')
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: Q y0} {v1: Q y1} {v2: Q y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [Q] c in v0 = v1) (hd: rew [Q] d in v1 = v2)
  (hp: rew [P] p in u0 = F y0 v0) (hq: rew [P] q in u1 = F y1 v1)
  (hr: rew [P] r in u2 = F y2 v2)
  (HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq)
  (HH': rew [fun e => rew [P] e in u0 = F y1 v1] H' in (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = F y2 v2] K in (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr)
  (KK': rew [fun e => rew [P] e in u1 = F y2 v2] K' in (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr)
  (EE: rew [fun S => rew [fun e => rew [P] e in u0 = F y1 v1] S in
    (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq] E in HH = HH')
  (GG: rew [fun S => rew [fun e => rew [P] e in u1 = F y2 v2] S in
    (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr] G in KK = KK'):
  rew [fun S => rew [fun e => rew [P] e in u0 = F y2 v2] S in
    (hp ⊙ sigT_map_eq F (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr]
    path_map2 (fun H K => square_compose_map f H K) E G in
    square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK =
  square_compose_map_coherence_dep f P Q F H' K' ha hb hc hd hp hq hr HH' KK'.
Proof. destruct E, G. cbn in EE, GG. destruct EE, GG. now reflexivity. Defined.

Lemma square_change_sides_compose_map_coherence_dep {X Y: Type}
  (f: Y -> X) (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1 x2: X} {y0 y1 y2: Y} {a: x0 = x1} {b: x1 = x2}
  {c: y0 = y1} {d: y1 = y2}
  {p0 q0: x0 = f y0} {p1 q1: x1 = f y1} {p2 q2: x2 = f y2}
  (M0: q0 = p0) (M1: q1 = p1) (M2: q2 = p2)
  (H: p0 • f_equal f c = a • p1) (K: p1 • f_equal f d = b • p2)
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: Q y0} {v1: Q y1} {v2: Q y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [Q] c in v0 = v1) (hd: rew [Q] d in v1 = v2)
  (hp0: rew [P] p0 in u0 = F y0 v0) (hp1: rew [P] p1 in u1 = F y1 v1)
  (hp2: rew [P] p2 in u2 = F y2 v2)
  (hq0: rew [P] q0 in u0 = F y0 v0) (hq1: rew [P] q1 in u1 = F y1 v1)
  (hq2: rew [P] q2 in u2 = F y2 v2)
  (DM0: rew [fun e => rew [P] e in u0 = F y0 v0] M0 in hq0 = hp0)
  (DM1: rew [fun e => rew [P] e in u1 = F y1 v1] M1 in hq1 = hp1)
  (DM2: rew [fun e => rew [P] e in u2 = F y2 v2] M2 in hq2 = hp2)
  (HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in (hp0 ⊙ sigT_map_eq F hc) = ha ⊙ hp1)
  (KK: rew [fun e => rew [P] e in u1 = F y2 v2] K in (hp1 ⊙ sigT_map_eq F hd) = hb ⊙ hp2):
  rew [fun S => rew [fun e => rew [P] e in u0 = F y2 v2] S in
    (hq0 ⊙ sigT_map_eq F (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hq2]
    square_change_sides_compose_map f M0 M1 M2 H K in
    square_compose_map_coherence_dep f P Q F _ _ ha hb hc hd hq0 hq1 hq2
      (square_change_sides_dep P M0 H M1 ha (sigT_map_eq F hc) hp0 hq0 hp1 hq1 DM0 HH DM1)
      (square_change_sides_dep P M1 K M2 hb (sigT_map_eq F hd) hp1 hq1 hp2 hq2 DM1 KK DM2) =
  square_change_sides_dep P M0 (square_compose_map f H K) M2
    (ha ⊙ hb) (sigT_map_eq F (hc ⊙ hd)) hp0 hq0 hp2 hq2 DM0
    (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp0 hp1 hp2 HH KK) DM2.
Proof.
  destruct M0, DM0, M1, DM1, M2, DM2.
  destruct c, d, hc, hd.
  revert HH. revert KK. revert ha. revert hb. revert H. revert K. revert a. revert b.
  subst x0 x1 x2.
  cbn [eq_rect] in hq0, hq1, hq2. subst u0 u1 u2.
  intros b a K H hb ha KK HH.
  cbn [f_equal eq_trans] in H, K. subst a b.
  change (eq_refl = f_equal (fun h => h) ha) in HH.
  change (eq_refl = f_equal (fun h => h) hb) in KK.
  revert HH. revert ha.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  revert KK. revert hb.
  apply (homotopy_path_ind_r (fun h => f_equal (fun h => h) h) (fun h => f_equal_id h)).
  now reflexivity.
Defined.

Local Lemma hexagonal_prism_pair_nat_cube_coherence_dep
  {B X U V Y1 Y2 W Z: Type}
  {PB: B -> Type} {PX: X -> Type}
  {PU: U -> Type} {PV: V -> Type} {PY1: Y1 -> Type} {PY2: Y2 -> Type}
  {PW: W -> Type} {PZ: Z -> Type} (r: B -> X)
  (j0: B -> U) (i0: B -> V) (j1: X -> Y1) (i1: X -> Y2)
  (Ej: U -> Y1) (Ei: V -> Y2) (F: Y1 -> Z) (G: Y2 -> Z)
  (I: U -> W) (J: V -> W) (d: W -> Z)
  (α: forall b, j1 (r b) = Ej (j0 b))
  (β: forall b, i1 (r b) = Ei (i0 b))
  (γ: forall u, F (Ej u) = d (I u))
  (δ: forall v, G (Ei v) = d (J v))
  (K: forall x, F (j1 x) = G (i1 x))
  (L: forall b, I (j0 b) = J (i0 b))
  (Q: forall b, hexagonal_coherence F d G
    (α b) (L b) (β b) (γ (j0 b)) (K (r b)) (δ (i0 b)))
  (R0: forall b, PB b -> PX (r b))
  (LJ0: forall b, PB b -> PU (j0 b)) (LI0: forall b, PB b -> PV (i0 b))
  (LJ1: forall x, PX x -> PY1 (j1 x)) (LI1: forall x, PX x -> PY2 (i1 x))
  (LEj: forall u, PU u -> PY1 (Ej u)) (LEi: forall v, PV v -> PY2 (Ei v))
  (LF: forall y, PY1 y -> PZ (F y)) (LG: forall y, PY2 y -> PZ (G y))
  (LI: forall u, PU u -> PW (I u)) (LJ: forall v, PV v -> PW (J v))
  (LD: forall w, PW w -> PZ (d w))
  (Hα: forall b a, rew [PY1] α b in LJ1 (r b) (R0 b a) = LEj (j0 b) (LJ0 b a))
  (Hβ: forall b a, rew [PY2] β b in LI1 (r b) (R0 b a) = LEi (i0 b) (LI0 b a))
  (Hγ: forall u a, rew [PZ] γ u in LF (Ej u) (LEj u a) = LD (I u) (LI u a))
  (Hδ: forall v a, rew [PZ] δ v in LG (Ei v) (LEi v a) = LD (J v) (LJ v a))
  (HK: forall x a, rew [PZ] K x in LF (j1 x) (LJ1 x a) = LG (i1 x) (LI1 x a))
  (HL: forall b a, rew [PW] L b in LI (j0 b) (LJ0 b a) = LJ (i0 b) (LI0 b a))
  (QQ: forall b a, hexagonal_coherence_dep LF LD LG (Q b)
    (Hα b a) (HL b a) (Hβ b a)
    (Hγ (j0 b) (LJ0 b a)) (HK (r b) (R0 b a)) (Hδ (i0 b) (LI0 b a)))
  {b0 b1: B} (p2: b0 = b1) {a2: PB b0} {a3: PB b1}
  (hp2: rew [PB] p2 in a2 = a3):
  let Nnat := hexagonal_prism_coherence_nat_fill F d G
    (fun b => j1 (r b)) (fun b => Ej (j0 b))
    (fun b => I (j0 b)) (fun b => J (i0 b))
    (fun b => i1 (r b)) (fun b => Ei (i0 b))
    α L β (fun b => γ (j0 b)) (fun b => K (r b)) (fun b => δ (i0 b)) Q p2 in
  let Nja := square_coherence_fill r j0 j1 Ej α p2 in
  let Nia := square_coherence_fill r i0 i1 Ei β p2 in
  let NL := square_coherence_fill j0 i0 I J L p2 in
  let Nγ := square_coherence_fill Ej I F d γ (f_equal j0 p2) in
  let Nδ := square_coherence_fill Ei J G d δ (f_equal i0 p2) in
  let s1 := square_coherence_fill (fun b => j1 (r b)) (fun b => Ej (j0 b))
    F F (fun b => f_equal F (α b)) p2 in
  let s2 := square_coherence_fill (fun b => Ej (j0 b)) (fun b => I (j0 b))
    F d (fun b => γ (j0 b)) p2 in
  let s3 := square_coherence_fill (fun b => I (j0 b)) (fun b => J (i0 b))
    d d (fun b => f_equal d (L b)) p2 in
  let t1 := square_coherence_fill (fun b => j1 (r b)) (fun b => i1 (r b))
    F G (fun b => K (r b)) p2 in
  let t2 := square_coherence_fill (fun b => i1 (r b)) (fun b => Ei (i0 b))
    G G (fun b => f_equal G (β b)) p2 in
  let t3 := square_coherence_fill (fun b => Ei (i0 b)) (fun b => J (i0 b))
    G d (fun b => δ (i0 b)) p2 in
  let Nm := square_coherence_fill j1 i1 F G K (f_equal r p2) in
  let Nα := square_compose (square_map F Nja) Nγ in
  let Nβ := square_compose (square_map G Nia) Nδ in
  let m0 := f_equal (fun e => f_equal F e) (eq_sym (map_compose_path j1 r p2)) in
  let m1 := f_equal (fun e => f_equal F e) (eq_sym (map_compose_path Ej j0 p2)) in
  let m2 := f_equal (fun e => f_equal d e) (eq_sym (map_compose_path I j0 p2)) in
  let m3 := f_equal (fun e => f_equal d e) (eq_sym (map_compose_path J i0 p2)) in
  let m4 := f_equal (fun e => f_equal G e) (eq_sym (map_compose_path i1 r p2)) in
  let m5 := f_equal (fun e => f_equal G e) (eq_sym (map_compose_path Ei i0 p2)) in
  let Eleft := path_map2 (fun H K => square_compose H K)
      (path_map2 (fun H K => square_compose H K)
        (square_coherence_map_edges r j0 j1 Ej F α p2)
        (square_coherence_precompose j0 Ej I F d γ p2))
      (square_coherence_map_edges j0 i0 I J d L p2) •
    square_change_sides_route_left m0 m1 m2 m3 s1 s2 s3 in
  let Eright := path_map2 (fun H K => square_compose H K)
      (square_coherence_precompose r j1 i1 F G K p2)
      (path_map2 (fun H K => square_compose H K)
        (square_coherence_map_edges r i0 i1 Ei G β p2)
        (square_coherence_precompose i0 Ei J G d δ p2)) •
    square_change_sides_route m0 m4 m5 m3 t1 t2 t3 in
  let prism_nat := square_cube_change_faces Eleft
    (square_cube_change_sides m0 m3 Nnat) Eright in
  let DNja := square_coherence_dep_fill r j0 j1 Ej R0 LJ0 LJ1 LEj α Hα p2 hp2 in
  let DNia := square_coherence_dep_fill r i0 i1 Ei R0 LI0 LI1 LEi β Hβ p2 hp2 in
  let DNL := square_coherence_dep_fill j0 i0 I J LJ0 LI0 LI LJ L HL p2 hp2 in
  let DNγ := square_coherence_dep_fill Ej I F d LEj LI LF LD γ Hγ (f_equal j0 p2) (sigT_map_eq LJ0 hp2) in
  let DNδ := square_coherence_dep_fill Ei J G d LEi LJ LG LD δ Hδ (f_equal i0 p2) (sigT_map_eq LI0 hp2) in
  let DNm := square_coherence_dep_fill j1 i1 F G LJ1 LI1 LF LG K HK (f_equal r p2) (sigT_map_eq R0 hp2) in
  let DNα := square_compose_dep PZ _ _ _ _ _ _ _ _ _
    (square_map_dep F LF Nja _ _ _ _ DNja) DNγ in
  let DNβ := square_compose_dep PZ _ _ _ _ _ _ _ _ _
    (square_map_dep G LG Nia _ _ _ _ DNia) DNδ in
  let DL := square_compose_dep PZ _ _ _ _ _ _ _ _ _ DNα
    (square_map_dep d LD NL _ _ _ _ DNL) in
  let DR := square_compose_dep PZ _ _ _ _ _ _ _ _ _ DNm DNβ in
  square_cube_coherence_dep PZ _ _ _ _ prism_nat _ _ _ _ _ _ DL DR ((QQ b1 a3)) ((QQ b0 a2)).
Proof.
  intros Nnat Nja Nia NL Nγ Nδ s1 s2 s3 t1 t2 t3 Nm Nα Nβ m0 m1 m2 m3 m4 m5
    Eleft Eright prism_nat DNja DNia DNL DNγ DNδ DNm DNα DNβ DL DR.
  pose (Ds1 := square_coherence_dep_fill (fun b => j1 (r b)) (fun b => Ej (j0 b)) F F
    (fun b a => LJ1 (r b) (R0 b a)) (fun b a => LEj (j0 b) (LJ0 b a)) LF LF (fun b => f_equal F (α
      b)) (fun b a => sigT_map_eq LF (Hα b a)) p2 hp2).
  pose (Ds2 := square_coherence_dep_fill (fun b => Ej (j0 b)) (fun b => I (j0 b)) F d
    (fun b a => LEj (j0 b) (LJ0 b a)) (fun b a => LI (j0 b) (LJ0 b a)) LF LD (fun b => γ (j0 b))
      (fun b a => Hγ (j0 b) (LJ0 b a)) p2 hp2).
  pose (Ds3 := square_coherence_dep_fill (fun b => I (j0 b)) (fun b => J (i0 b)) d d
    (fun b a => LI (j0 b) (LJ0 b a)) (fun b a => LJ (i0 b) (LI0 b a)) LD LD (fun b => f_equal d (L
      b)) (fun b a => sigT_map_eq LD (HL b a)) p2 hp2).
  pose (Dt1 := square_coherence_dep_fill (fun b => j1 (r b)) (fun b => i1 (r b)) F G
    (fun b a => LJ1 (r b) (R0 b a)) (fun b a => LI1 (r b) (R0 b a)) LF LG (fun b => K (r b)) (fun b
      a => HK (r b) (R0 b a)) p2 hp2).
  pose (Dt2 := square_coherence_dep_fill (fun b => i1 (r b)) (fun b => Ei (i0 b)) G G
    (fun b a => LI1 (r b) (R0 b a)) (fun b a => LEi (i0 b) (LI0 b a)) LG LG (fun b => f_equal G (β
      b)) (fun b a => sigT_map_eq LG (Hβ b a)) p2 hp2).
  pose (Dt3 := square_coherence_dep_fill (fun b => Ei (i0 b)) (fun b => J (i0 b)) G d
    (fun b a => LEi (i0 b) (LI0 b a)) (fun b a => LJ (i0 b) (LI0 b a)) LG LD (fun b => δ (i0 b))
      (fun b a => Hδ (i0 b) (LI0 b a)) p2 hp2).
  pose (Dm0 := map_compose_path_map_dep j1 r F LJ1 R0 LF p2 hp2).
  pose (Dm1 := map_compose_path_map_dep Ej j0 F LEj LJ0 LF p2 hp2).
  pose (Dm2 := map_compose_path_map_dep I j0 d LI LJ0 LD p2 hp2).
  pose (Dm3 := map_compose_path_map_dep J i0 d LJ LI0 LD p2 hp2).
  pose (Dm4 := map_compose_path_map_dep i1 r G LI1 R0 LG p2 hp2).
  pose (Dm5 := map_compose_path_map_dep Ei i0 G LEi LI0 LG p2 hp2).
  pose (EEs1 := square_coherence_map_edges_coherence_dep r j0 j1 Ej F
    R0 LJ0 LJ1 LEj LF α Hα p2 hp2).
  pose (EEs2 := square_coherence_precompose_coherence_dep j0 Ej I F d
    LJ0 LEj LI LF LD γ Hγ p2 hp2).
  pose (EEs3 := square_coherence_map_edges_coherence_dep j0 i0 I J d
    LJ0 LI0 LI LJ LD L HL p2 hp2).
  pose (EEt1 := square_coherence_precompose_coherence_dep r j1 i1 F G
    R0 LJ1 LI1 LF LG K HK p2 hp2).
  pose (EEt2 := square_coherence_map_edges_coherence_dep r i0 i1 Ei G
    R0 LI0 LI1 LEi LG β Hβ p2 hp2).
  pose (EEt3 := square_coherence_precompose_coherence_dep i0 Ei J G d
    LI0 LEi LJ LG LD δ Hδ p2 hp2).
  pose (EEs12 := square_compose_change_coherence_dep PZ
    (square_coherence_map_edges r j0 j1 Ej F α p2)
    (square_coherence_precompose j0 Ej I F d γ p2) _ _ _ _ _ _ _ _ _ _ _ EEs1 EEs2).
  pose (EEt23 := square_compose_change_coherence_dep PZ
    (square_coherence_map_edges r i0 i1 Ei G β p2)
    (square_coherence_precompose i0 Ei J G d δ p2) _ _ _ _ _ _ _ _ _ _ _ EEt2 EEt3).
  pose (EEs123 := square_compose_change_coherence_dep PZ
    (path_map2 (fun H K => square_compose H K)
      (square_coherence_map_edges r j0 j1 Ej F α p2)
      (square_coherence_precompose j0 Ej I F d γ p2))
    (square_coherence_map_edges j0 i0 I J d L p2) _ _ _ _ _ _ _ _ _ _ _ EEs12 EEs3).
  pose (EEt123 := square_compose_change_coherence_dep PZ
    (square_coherence_precompose r j1 i1 F G K p2)
    (path_map2 (fun H K => square_compose H K)
      (square_coherence_map_edges r i0 i1 Ei G β p2)
      (square_coherence_precompose i0 Ei J G d δ p2)) _ _ _ _ _ _ _ _ _ _ _ EEt1 EEt23).
  pose (EEsroute := square_change_sides_route_left_coherence_dep PZ m0 m1 m2 m3 s1 s2 s3
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dm0 Dm1 Dm2 Dm3 Ds1 Ds2 Ds3).
  pose (EEtroute := square_change_sides_route_coherence_dep PZ m0 m4 m5 m3 t1 t2 t3
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dm0 Dm4 Dm5 Dm3 Dt1 Dt2 Dt3).
  pose (EEleft := EEs123 ⊙ EEsroute).
  pose (EEright := EEt123 ⊙ EEtroute).
  pose (DNnative := hexagonal_prism_coherence_nat_fill_coherence_dep F d G
    (fun b => j1 (r b)) (fun b => Ej (j0 b))
    (fun b => I (j0 b)) (fun b => J (i0 b))
    (fun b => i1 (r b)) (fun b => Ei (i0 b))
    α L β (fun b => γ (j0 b)) (fun b => K (r b)) (fun b => δ (i0 b)) Q
    (fun b a => LJ1 (r b) (R0 b a)) (fun b a => LEj (j0 b) (LJ0 b a))
    (fun b a => LI (j0 b) (LJ0 b a)) (fun b a => LJ (i0 b) (LI0 b a))
    (fun b a => LI1 (r b) (R0 b a)) (fun b a => LEi (i0 b) (LI0 b a))
    LF LD LG Hα HL Hβ
    (fun b a => Hγ (j0 b) (LJ0 b a)) (fun b a => HK (r b) (R0 b a))
    (fun b a => Hδ (i0 b) (LI0 b a)) QQ p2 hp2).
  pose (DNchanged := square_cube_change_sides_coherence_dep PZ m0 m3 Nnat Dm0 Dm3 DNnative).
  now exact (square_cube_change_faces_coherence_dep PZ EEleft DNchanged EEright).
Defined.

Lemma hexagonal_prism_pair_cube_coherence_dep
  {A1 B A3 X U V Y1 Y2 W Z: Type}
  {PA1: A1 -> Type} {PB: B -> Type} {PA3: A3 -> Type} {PX: X -> Type}
  {PU: U -> Type} {PV: V -> Type} {PY1: Y1 -> Type} {PY2: Y2 -> Type}
  {PW: W -> Type} {PZ: Z -> Type}
  (f1: A1 -> X) (r: B -> X) (f3: A3 -> X)
  (j0: B -> U) (i0: B -> V) (j1: X -> Y1) (i1: X -> Y2)
  (Ej: U -> Y1) (Ei: V -> Y2) (F: Y1 -> Z) (G: Y2 -> Z)
  (I: U -> W) (J: V -> W) (d: W -> Z)
  (α: forall b, j1 (r b) = Ej (j0 b))
  (β: forall b, i1 (r b) = Ei (i0 b))
  (γ: forall u, F (Ej u) = d (I u))
  (δ: forall v, G (Ei v) = d (J v))
  (K: forall x, F (j1 x) = G (i1 x))
  (L: forall b, I (j0 b) = J (i0 b))
  (Q: forall b, hexagonal_coherence F d G
    (α b) (L b) (β b) (γ (j0 b)) (K (r b)) (δ (i0 b)))
  (LF1: forall a, PA1 a -> PX (f1 a)) (R0: forall b, PB b -> PX (r b))
  (LF3: forall a, PA3 a -> PX (f3 a))
  (LJ0: forall b, PB b -> PU (j0 b)) (LI0: forall b, PB b -> PV (i0 b))
  (LJ1: forall x, PX x -> PY1 (j1 x)) (LI1: forall x, PX x -> PY2 (i1 x))
  (LEj: forall u, PU u -> PY1 (Ej u)) (LEi: forall v, PV v -> PY2 (Ei v))
  (LF: forall y, PY1 y -> PZ (F y)) (LG: forall y, PY2 y -> PZ (G y))
  (LI: forall u, PU u -> PW (I u)) (LJ: forall v, PV v -> PW (J v))
  (LD: forall w, PW w -> PZ (d w))
  (Hα: forall b a, rew [PY1] α b in LJ1 (r b) (R0 b a) = LEj (j0 b) (LJ0 b a))
  (Hβ: forall b a, rew [PY2] β b in LI1 (r b) (R0 b a) = LEi (i0 b) (LI0 b a))
  (Hγ: forall u a, rew [PZ] γ u in LF (Ej u) (LEj u a) = LD (I u) (LI u a))
  (Hδ: forall v a, rew [PZ] δ v in LG (Ei v) (LEi v a) = LD (J v) (LJ v a))
  (HK: forall x a, rew [PZ] K x in LF (j1 x) (LJ1 x a) = LG (i1 x) (LI1 x a))
  (HL: forall b a, rew [PW] L b in LI (j0 b) (LJ0 b a) = LJ (i0 b) (LI0 b a))
  (QQ: forall b a, hexagonal_coherence_dep LF LD LG (Q b)
    (Hα b a) (HL b a) (Hβ b a)
    (Hγ (j0 b) (LJ0 b a)) (HK (r b) (R0 b a)) (Hδ (i0 b) (LI0 b a)))
  {x0 x1: A1} {b0 b1: B} {x4 x5: A3}
  (p1: x0 = x1) (p2: b0 = b1) (p3: x4 = x5)
  (h1: f1 x1 = r b0) (h2: f1 x0 = f3 x4) (h3: f3 x5 = r b1)
  (H: hexagonal_coherence f1 r f3 p1 p2 p3 h1 h2 h3)
  {a0: PA1 x0} {a1: PA1 x1} {a2: PB b0} {a3: PB b1} {a4: PA3 x4} {a5: PA3 x5}
  (hp1: rew [PA1] p1 in a0 = a1) (hp2: rew [PB] p2 in a2 = a3)
  (hp3: rew [PA3] p3 in a4 = a5)
  (hh1: rew [PX] h1 in LF1 x1 a1 = R0 b0 a2)
  (hh2: rew [PX] h2 in LF1 x0 a0 = LF3 x4 a4)
  (hh3: rew [PX] h3 in LF3 x5 a5 = R0 b1 a3)
  (HH: hexagonal_coherence_dep LF1 R0 LF3 H hp1 hp2 hp3 hh1 hh2 hh3):
  let Nmap := hexagonal_prism_coherence_map_fill f1 r f3 j1 i1 F G K
    p1 p2 p3 h1 h2 h3 H in
  let Nnat := hexagonal_prism_coherence_nat_fill F d G
    (fun b => j1 (r b)) (fun b => Ej (j0 b))
    (fun b => I (j0 b)) (fun b => J (i0 b))
    (fun b => i1 (r b)) (fun b => Ei (i0 b))
    α L β (fun b => γ (j0 b)) (fun b => K (r b)) (fun b => δ (i0 b)) Q p2 in
  let hp := sigT_map_eq LF1 hp1 ⊙ hh1 in
  let hq := sigT_map_eq LF3 hp3 ⊙ hh3 in
  let Dmj0 := layer_square_map_coherence_dep r f1 f3 j1 j0 Ej
    R0 LF1 LF3 LJ1 LJ0 LEj α Hα p2 p1 p3 h1 h3 h2 H
    hp2 hp1 hp3 hh1 hh3 hh2 HH in
  let Dmi0 := layer_square_map_coherence_dep r f1 f3 i1 i0 Ei
    R0 LF1 LF3 LI1 LI0 LEi β Hβ p2 p1 p3 h1 h3 h2 H
    hp2 hp1 hp3 hh1 hh3 hh2 HH in
  let Dmj := square_map_along_dep Ej I F d γ PY1 PZ LF (f_equal j0 p2)
    (layer_square_map r f1 f3 j1 j0 Ej α p2 p1 p3 h1 h3 h2 H
      (square_coherence_fill r j0 j1 Ej α p2))
    (square_coherence_fill Ej I F d γ (f_equal j0 p2))
    (sigT_map_eq LJ1 hh2) (sigT_map_eq LEj (sigT_map_eq LJ0 hp2))
    (sigT_map_eq LJ1 hp ⊙ Hα b0 a2) (sigT_map_eq LJ1 hq ⊙ Hα b1 a3)
    (Hγ (j0 b0) (LJ0 b0 a2)) (Hγ (j0 b1) (LJ0 b1 a3))
    (sigT_map_eq LD (sigT_map_eq LI (sigT_map_eq LJ0 hp2))) Dmj0
    (square_coherence_dep_reverse_fill Ej I F d LEj LI LF LD γ Hγ
      (f_equal j0 p2) (sigT_map_eq LJ0 hp2)) in
  let Dmi := square_map_along_dep Ei J G d δ PY2 PZ LG (f_equal i0 p2)
    (layer_square_map r f1 f3 i1 i0 Ei β p2 p1 p3 h1 h3 h2 H
      (square_coherence_fill r i0 i1 Ei β p2))
    (square_coherence_fill Ei J G d δ (f_equal i0 p2))
    (sigT_map_eq LI1 hh2) (sigT_map_eq LEi (sigT_map_eq LI0 hp2))
    (sigT_map_eq LI1 hp ⊙ Hβ b0 a2) (sigT_map_eq LI1 hq ⊙ Hβ b1 a3)
    (Hδ (i0 b0) (LI0 b0 a2)) (Hδ (i0 b1) (LI0 b1 a3))
    (sigT_map_eq LD (sigT_map_eq LJ (sigT_map_eq LI0 hp2))) Dmi0
    (square_coherence_dep_reverse_fill Ei J G d LEi LJ LG LD δ Hδ
      (f_equal i0 p2) (sigT_map_eq LI0 hp2)) in
  let DS0 := layer_square_nat_coherence_dep j1 i1 F G d LJ1 LI1 LF LG LD K HK
    (f_equal f1 p1 • h1) (α b0) (β b0) (L b0) (γ (j0 b0)) (δ (i0 b0)) (Q b0)
    hp (Hα b0 a2) (Hβ b0 a2) (HL b0 a2)
    (Hγ (j0 b0) (LJ0 b0 a2)) (Hδ (i0 b0) (LI0 b0 a2)) (QQ b0 a2) in
  let DS1 := layer_square_nat_coherence_dep j1 i1 F G d LJ1 LI1 LF LG LD K HK
    (f_equal f3 p3 • h3) (α b1) (β b1) (L b1) (γ (j0 b1)) (δ (i0 b1)) (Q b1)
    hq (Hα b1 a3) (Hβ b1 a3) (HL b1 a3)
    (Hγ (j0 b1) (LJ0 b1 a3)) (Hδ (i0 b1) (LI0 b1 a3)) (QQ b1 a3) in
  let DL := square_compose_map_coherence_dep d PZ PW LD _ _ _ _ _ _ _ _ _ Dmj DS1 in
  let DR := square_compose_map_coherence_dep d PZ PW LD _ _ _ _ _ _ _ _ _ DS0 Dmi in
  square_cube_coherence_dep PZ _ _ _ _
    (hexagonal_prism_pair_cube f1 r f3 j0 i0 j1 i1 Ej Ei F G I J d
      α β γ δ K L Q p1 p2 p3 h1 h2 h3 H Nmap Nnat)
    _ _ _ _ _ _ DL DR (sigT_map_eq
      (fun (e: I (j0 b0) = J (i0 b1))
        (h: rew [PW] e in LI (j0 b0) (LJ0 b0 a2) = LJ (i0 b1) (LI0 b1 a3)) =>
        sigT_map_eq LD h)
      (square_coherence_dep_fill j0 i0 I J LJ0 LI0 LI LJ L HL p2 hp2))
    (square_coherence_dep_fill j1 i1 F G LJ1 LI1 LF LG K HK h2 hh2).
Proof.
  intros Nmap Nnat hp hq Dmj0 Dmi0 Dmj Dmi DS0 DS1 DL DR.
  pose (Nja := square_coherence_fill r j0 j1 Ej α p2).
  pose (Nia := square_coherence_fill r i0 i1 Ei β p2).
  pose (NL := square_coherence_fill j0 i0 I J L p2).
  pose (Nγ := square_coherence_fill Ej I F d γ (f_equal j0 p2)).
  pose (Nδ := square_coherence_fill Ei J G d δ (f_equal i0 p2)).
  pose (Hrect := H).
  pose (p := f_equal f1 p1 • h1).
  pose (q := f_equal f3 p3 • h3).
  pose (Np := square_coherence_fill j1 i1 F G K p).
  pose (Nq := square_coherence_fill j1 i1 F G K q).
  pose (Na := square_coherence_fill j1 i1 F G K h2).
  pose (mapped_j := square_map_along Ej I F d γ (f_equal j0 p2)
    (square_map_along r j0 j1 Ej α p2 Hrect Nja) Nγ).
  pose (mapped_i := square_map_along Ei J G d δ (f_equal i0 p2)
    (square_map_along r i0 i1 Ei β p2 Hrect Nia) Nδ).
  pose (source0 := layer_square_nat j1 i1 F G d K p
    (α b0) (β b0) (L b0) (γ (j0 b0)) (δ (i0 b0)) (Q b0) Np).
  pose (source1 := layer_square_nat j1 i1 F G d K q
    (α b1) (β b1) (L b1) (γ (j0 b1)) (δ (i0 b1)) (Q b1) Nq).
  pose (s1 := square_coherence_fill (fun b => j1 (r b)) (fun b => Ej (j0 b))
    F F (fun b => f_equal F (α b)) p2).
  pose (s2 := square_coherence_fill (fun b => Ej (j0 b)) (fun b => I (j0 b))
    F d (fun b => γ (j0 b)) p2).
  pose (s3 := square_coherence_fill (fun b => I (j0 b)) (fun b => J (i0 b))
    d d (fun b => f_equal d (L b)) p2).
  pose (t1 := square_coherence_fill (fun b => j1 (r b)) (fun b => i1 (r b))
    F G (fun b => K (r b)) p2).
  pose (t2 := square_coherence_fill (fun b => i1 (r b)) (fun b => Ei (i0 b))
    G G (fun b => f_equal G (β b)) p2).
  pose (t3 := square_coherence_fill (fun b => Ei (i0 b)) (fun b => J (i0 b))
    G d (fun b => δ (i0 b)) p2).

  pose (Nm := square_coherence_fill j1 i1 F G K (f_equal r p2)).
  pose (Nα := square_compose (square_map F Nja) Nγ).
  pose (Nβ := square_compose (square_map G Nia) Nδ).

  pose (m0 := f_equal (fun e => f_equal F e) (eq_sym (map_compose_path j1 r p2))).
  pose (m1 := f_equal (fun e => f_equal F e) (eq_sym (map_compose_path Ej j0 p2))).
  pose (m2 := f_equal (fun e => f_equal d e) (eq_sym (map_compose_path I j0 p2))).
  pose (m3 := f_equal (fun e => f_equal d e) (eq_sym (map_compose_path J i0 p2))).
  pose (m4 := f_equal (fun e => f_equal G e) (eq_sym (map_compose_path i1 r p2))).
  pose (m5 := f_equal (fun e => f_equal G e) (eq_sym (map_compose_path Ei i0 p2))).

  pose (Eleft := path_map2 (fun H K => square_compose H K)
      (path_map2 (fun H K => square_compose H K)
        (square_coherence_map_edges r j0 j1 Ej F α p2)
        (square_coherence_precompose j0 Ej I F d γ p2))
      (square_coherence_map_edges j0 i0 I J d L p2) •
    square_change_sides_route_left m0 m1 m2 m3 s1 s2 s3).
  pose (Eright := path_map2 (fun H K => square_compose H K)
      (square_coherence_precompose r j1 i1 F G K p2)
      (path_map2 (fun H K => square_compose H K)
        (square_coherence_map_edges r i0 i1 Ei G β p2)
        (square_coherence_precompose i0 Ei J G d δ p2)) •
    square_change_sides_route m0 m4 m5 m3 t1 t2 t3).

  pose (prism_nat := square_cube_change_faces Eleft
    (square_cube_change_sides m0 m3 Nnat) Eright).
  pose (prism_map := hexagonal_prism_map_square_cube f1 r f3 j1 i1 F G K
    p1 p2 p3 h1 h2 h3 H Nmap).

  pose (Hf := square_map F (square_map j1 Hrect)).
  pose (Hg := square_map G (square_map i1 Hrect)).
  pose (Q0 := Q b0).
  pose (Q1 := Q b1).

  pose (raw_square :=
    square_cube_glue_prisms d Hf Hg Np Nq Nm Na Nα Nβ Q0 Q1 NL prism_map prism_nat).

  pose (M0 := map_compose_tail F (f_equal j1 p) (α b0) (γ (j0 b0))).
  pose (M1 := map_compose_tail F (f_equal j1 q) (α b1) (γ (j0 b1))).
  pose (M2 := map_compose_tail G (f_equal i1 p) (β b0) (δ (i0 b0))).
  pose (M3 := map_compose_tail G (f_equal i1 q) (β b1) (δ (i0 b1))).

  pose (A := square_stack Hf (eq_sym Nα)).
  pose (B' := square_stack Hg (eq_sym Nβ)).
  pose (C0 := square_stack Np Q0).
  pose (C1 := square_stack Nq Q1).

  pose (eleft := path_map2 (fun H K => square_compose_map d H K)
      (square_map_along_twice r j0 j1 Ej α I F d γ p2 Hrect) eq_refl •
    square_change_sides_compose_map d M0 M1 M3 A C1).
  pose (eright := path_map2 (fun H K => square_compose_map d H K) eq_refl
      (square_map_along_twice r i0 i1 Ei β J G d δ p2 Hrect) •
    square_change_sides_compose_map d M0 M2 M3 C0 B').

  pose (Drect := HH).
  pose (DHf := square_map_dep F LF (square_map j1 Hrect) _ _ _ _
    (square_map_dep j1 LJ1 Hrect hh2 (sigT_map_eq R0 hp2) hp hq Drect)).
  pose (DHg := square_map_dep G LG (square_map i1 Hrect) _ _ _ _
    (square_map_dep i1 LI1 Hrect hh2 (sigT_map_eq R0 hp2) hp hq Drect)).
  pose (DNp := square_coherence_dep_fill j1 i1 F G LJ1 LI1 LF LG K HK p hp).
  pose (DNq := square_coherence_dep_fill j1 i1 F G LJ1 LI1 LF LG K HK q hq).
  pose (DNm := square_coherence_dep_fill j1 i1 F G LJ1 LI1 LF LG K HK
    (f_equal r p2) (sigT_map_eq R0 hp2)).
  pose (DNa := square_coherence_dep_fill j1 i1 F G LJ1 LI1 LF LG K HK h2 hh2).
  pose (DNja := square_coherence_dep_fill r j0 j1 Ej R0 LJ0 LJ1 LEj α Hα p2 hp2).
  pose (DNia := square_coherence_dep_fill r i0 i1 Ei R0 LI0 LI1 LEi β Hβ p2 hp2).
  pose (DNγ := square_coherence_dep_fill Ej I F d LEj LI LF LD γ Hγ
    (f_equal j0 p2) (sigT_map_eq LJ0 hp2)).
  pose (DNδ := square_coherence_dep_fill Ei J G d LEi LJ LG LD δ Hδ
    (f_equal i0 p2) (sigT_map_eq LI0 hp2)).
  pose (DNL := square_coherence_dep_fill j0 i0 I J LJ0 LI0 LI LJ L HL p2 hp2).
  pose (DNα := square_compose_dep PZ _ _ _ _ _ _ _ _ _
    (square_map_dep F LF Nja _ _ _ _ DNja) DNγ).
  pose (DNβ := square_compose_dep PZ _ _ _ _ _ _ _ _ _
    (square_map_dep G LG Nia _ _ _ _ DNia) DNδ).
  pose (DQ0 := (QQ b0 a2)).
  pose (DQ1 := (QQ b1 a3)).
  pose (DprismMap := hexagonal_prism_map_square_cube_coherence_dep f1 r f3 j1 i1 F G K
    LJ1 LI1 LF LG HK p1 p2 p3 h1 h2 h3 H
    (sigT_map_eq LF1 hp1) (sigT_map_eq R0 hp2) (sigT_map_eq LF3 hp3) hh1 hh2 hh3 Drect).
  pose (DprismNat := hexagonal_prism_pair_nat_cube_coherence_dep r j0 i0 j1 i1 Ej Ei F G I J d
    α β γ δ K L Q R0 LJ0 LI0 LJ1 LI1 LEj LEi LF LG LI LJ LD
    Hα Hβ Hγ Hδ HK HL QQ p2 hp2).
  pose (Draw := square_cube_glue_prisms_coherence_dep d PZ PW LD
    Hf Hg Np Nq Nm Na Nα Nβ Q0 Q1 NL prism_map prism_nat DprismMap DprismNat).
  pose (DM0 := map_compose_tail_dep F LF (sigT_map_eq LJ1 hp) (Hα b0 a2)
    (Hγ (j0 b0) (LJ0 b0 a2))).
  pose (DM1 := map_compose_tail_dep F LF (sigT_map_eq LJ1 hq) (Hα b1 a3)
    (Hγ (j0 b1) (LJ0 b1 a3))).
  pose (DM2 := map_compose_tail_dep G LG (sigT_map_eq LI1 hp) (Hβ b0 a2)
    (Hδ (i0 b0) (LI0 b0 a2))).
  pose (DM3 := map_compose_tail_dep G LG (sigT_map_eq LI1 hq) (Hβ b1 a3)
    (Hδ (i0 b1) (LI0 b1 a3))).
  pose (DA := square_stack_dep PZ _ _ _ _ _ _ _ _ _ DHf (sigT_sym_eq DNα)).
  pose (DB := square_stack_dep PZ _ _ _ _ _ _ _ _ _ DHg (sigT_sym_eq DNβ)).
  pose (DC0 := square_stack_dep PZ _ _ _ _ _ _ _ _ _ DNp DQ0).
  pose (DC1 := square_stack_dep PZ _ _ _ _ _ _ _ _ _ DNq DQ1).
  pose (DDtwiceJ := square_map_along_twice_coherence_dep r j0 j1 Ej R0 LJ0 LJ1 LEj α Hα
    I F d LI LF LD γ Hγ p2 Hrect hh2 hp2 hp hq Drect).
  pose (DDtwiceI := square_map_along_twice_coherence_dep r i0 i1 Ei R0 LI0 LI1 LEi β Hβ
    J G d LJ LG LD δ Hδ p2 Hrect hh2 hp2 hp hq Drect).
  pose (DDcompJ := square_compose_map_change_coherence_dep d PZ PW LD
    (square_map_along_twice r j0 j1 Ej α I F d γ p2 Hrect) eq_refl
    _ _ _ _ _ _ _ Dmj _ DS1 DS1 DDtwiceJ eq_refl).
  pose (DDcompI := square_compose_map_change_coherence_dep d PZ PW LD
    eq_refl (square_map_along_twice r i0 i1 Ei β J G d δ p2 Hrect)
    _ _ _ _ _ _ _ DS0 DS0 Dmi _ eq_refl DDtwiceI).
  pose (DDsideJ := square_change_sides_compose_map_coherence_dep d PZ PW LD
    M0 M1 M3 A C1 _ _ _ _ _ _ _ _ _ _ DM0 DM1 DM3 DA DC1).
  pose (DDsideI := square_change_sides_compose_map_coherence_dep d PZ PW LD
    M0 M2 M3 C0 B' _ _ _ _ _ _ _ _ _ _ DM0 DM2 DM3 DC0 DB).
  pose (EEleft := DDcompJ ⊙ DDsideJ).
  pose (EEright := DDcompI ⊙ DDsideI).
  change (square_cube_coherence_dep PZ _ _ _ _
    (square_cube_change_faces eleft (square_cube_change_sides M0 M3 raw_square) eright)
    _ _ _ _ _ _ DL DR (sigT_map_eq
      (fun (e: I (j0 b0) = J (i0 b1))
        (h: rew [PW] e in LI (j0 b0) (LJ0 b0 a2) = LJ (i0 b1) (LI0 b1 a3)) =>
        sigT_map_eq LD h) DNL) DNa).
  eapply square_cube_change_faces_coherence_dep.
  - now exact EEleft.
  - now exact (square_cube_change_sides_coherence_dep PZ M0 M3 raw_square DM0 DM3 Draw).
  - now exact EEright.
Defined.

(** Lift the cubes comparing square pastings through the corresponding
    dependent pastings, retaining their chosen boundary lifts. *)
Lemma square_compose_cube_coherence_dep {X Y: Type} (r: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (r y))
  {x0 x1 x2 x3 x4 x5: X} {y0 y1 y2 y3 y4 y5: Y} {v0: x0 = r y0} {v1: x1 = r y1} {v2: x2 = r y2} {v3: x3 = r y3}
  {v4: x4 = r y4} {v5: x5 = r y5}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y1 = y2} {l_p1: x1 = x2}
  {N_p1: v1 • f_equal r u_p1 = l_p1 • v2}
  {u_p2: y0 = y3} {l_p2: x0 = x3}
  {N_p2: v0 • f_equal r u_p2 = l_p2 • v3}
  {u_p3: y3 = y2} {l_p3: x3 = x2}
  {N_p3: v3 • f_equal r u_p3 = l_p3 • v2}
  {u_p4: y2 = y4} {l_p4: x2 = x4}
  {N_p4: v2 • f_equal r u_p4 = l_p4 • v4}
  {u_p5: y3 = y5} {l_p5: x3 = x5}
  {N_p5: v3 • f_equal r u_p5 = l_p5 • v5}
  {u_p6: y5 = y4} {l_p6: x5 = x4}
  {N_p6: v5 • f_equal r u_p6 = l_p6 • v4}
  {u_H0: u_p0 • u_p1 = u_p2 • u_p3} {l_H0: l_p0 • l_p1 = l_p2 • l_p3}
  {C_H0: square_cube (square_compose_map r N_p0 N_p1) (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0}
  {u_H1: u_p3 • u_p4 = u_p5 • u_p6} {l_H1: l_p3 • l_p4 = l_p5 • l_p6}
  {C_H1: square_cube (square_compose_map r N_p3 N_p4) (square_compose_map r N_p5 N_p6)
    (f_equal (fun e => f_equal r e) u_H1) l_H1}
  {ux0: P x0} {uy0: Q y0}
  {hv0: rew [P] v0 in ux0 = F y0 uy0}
  {ux1: P x1} {uy1: Q y1}
  {hv1: rew [P] v1 in ux1 = F y1 uy1}
  {ux2: P x2} {uy2: Q y2}
  {hv2: rew [P] v2 in ux2 = F y2 uy2}
  {ux3: P x3} {uy3: Q y3}
  {hv3: rew [P] v3 in ux3 = F y3 uy3}
  {ux4: P x4} {uy4: Q y4}
  {hv4: rew [P] v4 in ux4 = F y4 uy4}
  {ux5: P x5} {uy5: Q y5}
  {hv5: rew [P] v5 in ux5 = F y5 uy5}
  {hu0: rew [Q] u_p0 in uy0 = uy1} {hl0: rew [P] l_p0 in ux0 = ux1}
  {NN0: rew [fun e => rew [P] e in ux0 = F y1 uy1] N_p0 in
    (hv0 ⊙ sigT_map_eq F hu0) = hl0 ⊙ hv1}
  {hu1: rew [Q] u_p1 in uy1 = uy2} {hl1: rew [P] l_p1 in ux1 = ux2}
  {NN1: rew [fun e => rew [P] e in ux1 = F y2 uy2] N_p1 in
    (hv1 ⊙ sigT_map_eq F hu1) = hl1 ⊙ hv2}
  {hu2: rew [Q] u_p2 in uy0 = uy3} {hl2: rew [P] l_p2 in ux0 = ux3}
  {NN2: rew [fun e => rew [P] e in ux0 = F y3 uy3] N_p2 in
    (hv0 ⊙ sigT_map_eq F hu2) = hl2 ⊙ hv3}
  {hu3: rew [Q] u_p3 in uy3 = uy2} {hl3: rew [P] l_p3 in ux3 = ux2}
  {NN3: rew [fun e => rew [P] e in ux3 = F y2 uy2] N_p3 in
    (hv3 ⊙ sigT_map_eq F hu3) = hl3 ⊙ hv2}
  {hu4: rew [Q] u_p4 in uy2 = uy4} {hl4: rew [P] l_p4 in ux2 = ux4}
  {NN4: rew [fun e => rew [P] e in ux2 = F y4 uy4] N_p4 in
    (hv2 ⊙ sigT_map_eq F hu4) = hl4 ⊙ hv4}
  {hu5: rew [Q] u_p5 in uy3 = uy5} {hl5: rew [P] l_p5 in ux3 = ux5}
  {NN5: rew [fun e => rew [P] e in ux3 = F y5 uy5] N_p5 in
    (hv3 ⊙ sigT_map_eq F hu5) = hl5 ⊙ hv5}
  {hu6: rew [Q] u_p6 in uy5 = uy4} {hl6: rew [P] l_p6 in ux5 = ux4}
  {NN6: rew [fun e => rew [P] e in ux5 = F y4 uy4] N_p6 in
    (hv5 ⊙ sigT_map_eq F hu6) = hl6 ⊙ hv4}
  {DU0: rew [fun e => rew [Q] e in uy0 = uy2] u_H0 in (hu0 ⊙ hu1) = hu2 ⊙ hu3}
  {DL0: rew [fun e => rew [P] e in ux0 = ux2] l_H0 in (hl0 ⊙ hl1) = hl2 ⊙ hl3}
  {DU1: rew [fun e => rew [Q] e in uy3 = uy4] u_H1 in (hu3 ⊙ hu4) = hu5 ⊙ hu6}
  {DL1: rew [fun e => rew [P] e in ux3 = ux4] l_H1 in (hl3 ⊙ hl4) = hl5 ⊙ hl6}
  (CC0: square_cube_coherence_dep P
    (square_compose_map r N_p0 N_p1) (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0 C_H0
    (hl0 ⊙ hl1) (hl2 ⊙ hl3) (sigT_map_eq F (hu0 ⊙ hu1)) (sigT_map_eq F (hu2 ⊙ hu3)) hv0 hv2
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN0 NN1)
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN2 NN3)
    (sigT_map_eq (fun (e: y0 = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq F h) DU0) DL0)
  (CC1: square_cube_coherence_dep P
    (square_compose_map r N_p3 N_p4) (square_compose_map r N_p5 N_p6)
    (f_equal (fun e => f_equal r e) u_H1) l_H1 C_H1
    (hl3 ⊙ hl4) (hl5 ⊙ hl6) (sigT_map_eq F (hu3 ⊙ hu4)) (sigT_map_eq F (hu5 ⊙ hu6)) hv3 hv4
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN3 NN4)
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN5 NN6)
    (sigT_map_eq (fun (e: y3 = y4) (h: rew [Q] e in uy3 = uy4) => sigT_map_eq F h) DU1) DL1):
  square_cube_coherence_dep P
    (square_compose_map r N_p0 (square_compose_map r N_p1 N_p4))
    (square_compose_map r (square_compose_map r N_p2 N_p5) N_p6)
    (f_equal (fun e => f_equal r e) (square_compose u_H0 u_H1))
    (square_compose l_H0 l_H1) (square_compose_cube r C_H0 C_H1)
    (hl0 ⊙ (hl1 ⊙ hl4)) ((hl2 ⊙ hl5) ⊙ hl6)
    (sigT_map_eq F (hu0 ⊙ (hu1 ⊙ hu4))) (sigT_map_eq F ((hu2 ⊙ hu5) ⊙ hu6)) hv0 hv4
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN0
      (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN1 NN4))
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _
      (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN2 NN5) NN6)
    (sigT_map_eq (fun (e: y0 = y4) (h: rew [Q] e in uy0 = uy4) => sigT_map_eq F h)
      (square_compose_dep Q u_H0 u_H1 hu2 hu5 hu1 hu4 hu0 hu3 hu6 DU0 DU1))
    (square_compose_dep P l_H0 l_H1 hl2 hl5 hl1 hl4 hl0 hl3 hl6 DL0 DL1).
Proof.
  unfold square_compose_cube.
  now exact (square_cube_trans_map_coherence_dep r P Q F
    (square_compose_map_assoc_coherence_dep r P Q F NN0 NN1 NN4)
    (square_cube_trans_map_coherence_dep r P Q F
      (square_cube_whisker_r_coherence_dep r P Q F NN4 CC0)
      (square_cube_trans_map_coherence_dep r P Q F
        (square_cube_inverse_map_coherence_dep r P Q F
          (square_compose_map_assoc_coherence_dep r P Q F NN2 NN3 NN4))
        (square_cube_trans_map_coherence_dep r P Q F
          (square_cube_whisker_l_coherence_dep r P Q F NN2 CC1)
          (square_compose_map_assoc_coherence_dep r P Q F NN2 NN5 NN6))))).
Defined.

Lemma square_stack_cube_coherence_dep {X Y: Type} (r: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (r y))
  {x0 x1 x2 x3 x4 x5: X} {y0 y1 y2 y3 y4 y5: Y} {v0: x0 = r y0} {v1: x1 = r y1} {v2: x2 = r y2} {v3: x3 = r y3}
  {v4: x4 = r y4} {v5: x5 = r y5}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y1 = y2} {l_p1: x1 = x2}
  {N_p1: v1 • f_equal r u_p1 = l_p1 • v2}
  {u_p2: y0 = y3} {l_p2: x0 = x3}
  {N_p2: v0 • f_equal r u_p2 = l_p2 • v3}
  {u_p3: y3 = y2} {l_p3: x3 = x2}
  {N_p3: v3 • f_equal r u_p3 = l_p3 • v2}
  {u_p4: y1 = y4} {l_p4: x1 = x4}
  {N_p4: v1 • f_equal r u_p4 = l_p4 • v4}
  {u_p5: y4 = y5} {l_p5: x4 = x5}
  {N_p5: v4 • f_equal r u_p5 = l_p5 • v5}
  {u_p6: y2 = y5} {l_p6: x2 = x5}
  {N_p6: v2 • f_equal r u_p6 = l_p6 • v5}
  {u_H0: (u_p0 • u_p1) = (u_p2 • u_p3)} {l_H0: (l_p0 • l_p1) = (l_p2 • l_p3)}
  {C_H0: square_cube (square_compose_map r N_p0 N_p1) (square_compose_map r N_p2 N_p3) (f_equal
    (fun e => f_equal r e) u_H0) l_H0}
  {u_H1: (u_p4 • u_p5) = (u_p1 • u_p6)} {l_H1: (l_p4 • l_p5) = (l_p1 • l_p6)}
  {C_H1: square_cube (square_compose_map r N_p4 N_p5) (square_compose_map r N_p1 N_p6) (f_equal
    (fun e => f_equal r e) u_H1) l_H1}
  {ux0: P x0} {uy0: Q y0}
  {hv0: rew [P] v0 in ux0 = F y0 uy0}
  {ux1: P x1} {uy1: Q y1}
  {hv1: rew [P] v1 in ux1 = F y1 uy1}
  {ux2: P x2} {uy2: Q y2}
  {hv2: rew [P] v2 in ux2 = F y2 uy2}
  {ux3: P x3} {uy3: Q y3}
  {hv3: rew [P] v3 in ux3 = F y3 uy3}
  {ux4: P x4} {uy4: Q y4}
  {hv4: rew [P] v4 in ux4 = F y4 uy4}
  {ux5: P x5} {uy5: Q y5}
  {hv5: rew [P] v5 in ux5 = F y5 uy5}
  {hu0: rew [Q] u_p0 in uy0 = uy1} {hl0: rew [P] l_p0 in ux0 = ux1}
  {NN0: rew [fun e => rew [P] e in ux0 = F y1 uy1] N_p0 in (hv0 ⊙ sigT_map_eq F hu0) = hl0 ⊙ hv1}
  {hu1: rew [Q] u_p1 in uy1 = uy2} {hl1: rew [P] l_p1 in ux1 = ux2}
  {NN1: rew [fun e => rew [P] e in ux1 = F y2 uy2] N_p1 in (hv1 ⊙ sigT_map_eq F hu1) = hl1 ⊙ hv2}
  {hu2: rew [Q] u_p2 in uy0 = uy3} {hl2: rew [P] l_p2 in ux0 = ux3}
  {NN2: rew [fun e => rew [P] e in ux0 = F y3 uy3] N_p2 in (hv0 ⊙ sigT_map_eq F hu2) = hl2 ⊙ hv3}
  {hu3: rew [Q] u_p3 in uy3 = uy2} {hl3: rew [P] l_p3 in ux3 = ux2}
  {NN3: rew [fun e => rew [P] e in ux3 = F y2 uy2] N_p3 in (hv3 ⊙ sigT_map_eq F hu3) = hl3 ⊙ hv2}
  {hu4: rew [Q] u_p4 in uy1 = uy4} {hl4: rew [P] l_p4 in ux1 = ux4}
  {NN4: rew [fun e => rew [P] e in ux1 = F y4 uy4] N_p4 in (hv1 ⊙ sigT_map_eq F hu4) = hl4 ⊙ hv4}
  {hu5: rew [Q] u_p5 in uy4 = uy5} {hl5: rew [P] l_p5 in ux4 = ux5}
  {NN5: rew [fun e => rew [P] e in ux4 = F y5 uy5] N_p5 in (hv4 ⊙ sigT_map_eq F hu5) = hl5 ⊙ hv5}
  {hu6: rew [Q] u_p6 in uy2 = uy5} {hl6: rew [P] l_p6 in ux2 = ux5}
  {NN6: rew [fun e => rew [P] e in ux2 = F y5 uy5] N_p6 in (hv2 ⊙ sigT_map_eq F hu6) = hl6 ⊙ hv5}
  {DU0: rew [fun e => rew [Q] e in uy0 = uy2] u_H0 in (hu0 ⊙ hu1) = (hu2 ⊙ hu3)}
  {DL0: rew [fun e => rew [P] e in ux0 = ux2] l_H0 in (hl0 ⊙ hl1) = (hl2 ⊙ hl3)}
  {DU1: rew [fun e => rew [Q] e in uy1 = uy5] u_H1 in (hu4 ⊙ hu5) = (hu1 ⊙ hu6)}
  {DL1: rew [fun e => rew [P] e in ux1 = ux5] l_H1 in (hl4 ⊙ hl5) = (hl1 ⊙ hl6)}
  (CC0: square_cube_coherence_dep P (square_compose_map r N_p0 N_p1) (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0 C_H0
    (hl0 ⊙ hl1) (hl2 ⊙ hl3) (sigT_map_eq F (hu0 ⊙ hu1)) (sigT_map_eq F (hu2 ⊙ hu3)) hv0 hv2
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN0 NN1)
      (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN2 NN3) (sigT_map_eq (fun (e: y0
      = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq F h) DU0) DL0)
  (CC1: square_cube_coherence_dep P (square_compose_map r N_p4 N_p5) (square_compose_map r N_p1 N_p6)
    (f_equal (fun e => f_equal r e) u_H1) l_H1 C_H1
    (hl4 ⊙ hl5) (hl1 ⊙ hl6) (sigT_map_eq F (hu4 ⊙ hu5)) (sigT_map_eq F (hu1 ⊙ hu6)) hv1 hv5
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN4 NN5)
      (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN1 NN6) (sigT_map_eq (fun (e: y1
      = y5) (h: rew [Q] e in uy1 = uy5) => sigT_map_eq F h) DU1) DL1):
  square_cube_coherence_dep P (square_compose_map r (square_compose_map r N_p0 N_p4) N_p5)
    (square_compose_map r N_p2 (square_compose_map r N_p3 N_p6))
    (f_equal (fun e => f_equal r e) (square_stack u_H0 u_H1)) (square_stack l_H0 l_H1)
    (square_stack_cube r C_H0 C_H1)
    ((hl0 ⊙ hl4) ⊙ hl5) (hl2 ⊙ (hl3 ⊙ hl6)) (sigT_map_eq F ((hu0 ⊙ hu4) ⊙ hu5)) (sigT_map_eq F (hu2
      ⊙ (hu3 ⊙ hu6))) hv0 hv5
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ (square_compose_map_coherence_dep r
      P Q F _ _ _ _ _ _ _ _ _ NN0 NN4) NN5) (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _
      _ _ NN2 (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN3 NN6))
    (sigT_map_eq (fun (e: y0 = y5) (h: rew [Q] e in uy0 = uy5) => sigT_map_eq F h)
      (square_stack_dep Q u_H0 u_H1 hu2 hu1 hu5 hu0 hu3 hu4 hu6 DU0 DU1)) (square_stack_dep P l_H0
      l_H1 hl2 hl1 hl5 hl0 hl3 hl4 hl6 DL0 DL1).
Proof.
  unfold square_stack_cube.
  now exact (square_cube_trans_map_coherence_dep r P Q F
    (square_cube_inverse_map_coherence_dep r P Q F
      (square_compose_map_assoc_coherence_dep r P Q F NN0 NN4 NN5))
    (square_cube_trans_map_coherence_dep r P Q F
      (square_cube_whisker_l_coherence_dep r P Q F NN0 CC1)
      (square_cube_trans_map_coherence_dep r P Q F
        (square_compose_map_assoc_coherence_dep r P Q F NN0 NN1 NN6)
        (square_cube_trans_map_coherence_dep r P Q F
          (square_cube_whisker_r_coherence_dep r P Q F NN6 CC0)
          (square_cube_inverse_map_coherence_dep r P Q F
            (square_compose_map_assoc_coherence_dep r P Q F NN2 NN3 NN6)))))).
Defined.

Lemma square_change_sides_cube_coherence_dep {X Y: Type} (r: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (r y))
  {x0 x1 x2 x3: X} {y0 y1 y2 y3: Y} {v0: x0 = r y0} {v1: x1 = r y1} {v2: x2 = r y2} {v3: x3 = r y3}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y0 = y1} {l_p1: x0 = x1}
  {N_p1: v0 • f_equal r u_p1 = l_p1 • v1}
  {u_p2: y1 = y2} {l_p2: x1 = x2}
  {N_p2: v1 • f_equal r u_p2 = l_p2 • v2}
  {u_p3: y0 = y3} {l_p3: x0 = x3}
  {N_p3: v0 • f_equal r u_p3 = l_p3 • v3}
  {u_p4: y3 = y2} {l_p4: x3 = x2}
  {N_p4: v3 • f_equal r u_p4 = l_p4 • v2}
  {u_p5: y3 = y2} {l_p5: x3 = x2}
  {N_p5: v3 • f_equal r u_p5 = l_p5 • v2}
  {u_H0: u_p0 = u_p1} {l_H0: l_p0 = l_p1}
  {C_H0: square_cube N_p0 N_p1 (f_equal (fun e => f_equal r e) u_H0) l_H0}
  {u_H1: (u_p1 • u_p2) = (u_p3 • u_p4)} {l_H1: (l_p1 • l_p2) = (l_p3 • l_p4)}
  {C_H1: square_cube (square_compose_map r N_p1 N_p2) (square_compose_map r N_p3 N_p4) (f_equal
    (fun e => f_equal r e) u_H1) l_H1}
  {u_H2: u_p5 = u_p4} {l_H2: l_p5 = l_p4}
  {C_H2: square_cube N_p5 N_p4 (f_equal (fun e => f_equal r e) u_H2) l_H2}
  {ux0: P x0} {uy0: Q y0}
  {hv0: rew [P] v0 in ux0 = F y0 uy0}
  {ux1: P x1} {uy1: Q y1}
  {hv1: rew [P] v1 in ux1 = F y1 uy1}
  {ux2: P x2} {uy2: Q y2}
  {hv2: rew [P] v2 in ux2 = F y2 uy2}
  {ux3: P x3} {uy3: Q y3}
  {hv3: rew [P] v3 in ux3 = F y3 uy3}
  {hu0: rew [Q] u_p0 in uy0 = uy1} {hl0: rew [P] l_p0 in ux0 = ux1}
  {NN0: rew [fun e => rew [P] e in ux0 = F y1 uy1] N_p0 in (hv0 ⊙ sigT_map_eq F hu0) = hl0 ⊙ hv1}
  {hu1: rew [Q] u_p1 in uy0 = uy1} {hl1: rew [P] l_p1 in ux0 = ux1}
  {NN1: rew [fun e => rew [P] e in ux0 = F y1 uy1] N_p1 in (hv0 ⊙ sigT_map_eq F hu1) = hl1 ⊙ hv1}
  {hu2: rew [Q] u_p2 in uy1 = uy2} {hl2: rew [P] l_p2 in ux1 = ux2}
  {NN2: rew [fun e => rew [P] e in ux1 = F y2 uy2] N_p2 in (hv1 ⊙ sigT_map_eq F hu2) = hl2 ⊙ hv2}
  {hu3: rew [Q] u_p3 in uy0 = uy3} {hl3: rew [P] l_p3 in ux0 = ux3}
  {NN3: rew [fun e => rew [P] e in ux0 = F y3 uy3] N_p3 in (hv0 ⊙ sigT_map_eq F hu3) = hl3 ⊙ hv3}
  {hu4: rew [Q] u_p4 in uy3 = uy2} {hl4: rew [P] l_p4 in ux3 = ux2}
  {NN4: rew [fun e => rew [P] e in ux3 = F y2 uy2] N_p4 in (hv3 ⊙ sigT_map_eq F hu4) = hl4 ⊙ hv2}
  {hu5: rew [Q] u_p5 in uy3 = uy2} {hl5: rew [P] l_p5 in ux3 = ux2}
  {NN5: rew [fun e => rew [P] e in ux3 = F y2 uy2] N_p5 in (hv3 ⊙ sigT_map_eq F hu5) = hl5 ⊙ hv2}
  {DU0: rew [fun e => rew [Q] e in uy0 = uy1] u_H0 in hu0 = hu1}
  {DL0: rew [fun e => rew [P] e in ux0 = ux1] l_H0 in hl0 = hl1}
  {DU1: rew [fun e => rew [Q] e in uy0 = uy2] u_H1 in (hu1 ⊙ hu2) = (hu3 ⊙ hu4)}
  {DL1: rew [fun e => rew [P] e in ux0 = ux2] l_H1 in (hl1 ⊙ hl2) = (hl3 ⊙ hl4)}
  {DU2: rew [fun e => rew [Q] e in uy3 = uy2] u_H2 in hu5 = hu4}
  {DL2: rew [fun e => rew [P] e in ux3 = ux2] l_H2 in hl5 = hl4}
  (CC0: square_cube_coherence_dep P N_p0 N_p1
    (f_equal (fun e => f_equal r e) u_H0) l_H0 C_H0
    hl0 hl1 (sigT_map_eq F hu0) (sigT_map_eq F hu1) hv0 hv1
    NN0 NN1 (sigT_map_eq (fun (e: y0 = y1) (h: rew [Q] e in uy0 = uy1) => sigT_map_eq F h) DU0) DL0)
  (CC1: square_cube_coherence_dep P (square_compose_map r N_p1 N_p2) (square_compose_map r N_p3 N_p4)
    (f_equal (fun e => f_equal r e) u_H1) l_H1 C_H1
    (hl1 ⊙ hl2) (hl3 ⊙ hl4) (sigT_map_eq F (hu1 ⊙ hu2)) (sigT_map_eq F (hu3 ⊙ hu4)) hv0 hv2
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN1 NN2)
      (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN3 NN4) (sigT_map_eq (fun (e: y0
      = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq F h) DU1) DL1)
  (CC2: square_cube_coherence_dep P N_p5 N_p4
    (f_equal (fun e => f_equal r e) u_H2) l_H2 C_H2
    hl5 hl4 (sigT_map_eq F hu5) (sigT_map_eq F hu4) hv3 hv2
    NN5 NN4 (sigT_map_eq (fun (e: y3 = y2) (h: rew [Q] e in uy3 = uy2) => sigT_map_eq F h) DU2) DL2):
  square_cube_coherence_dep P (square_compose_map r N_p0 N_p2) (square_compose_map r N_p3 N_p5)
    (f_equal (fun e => f_equal r e) (square_change_sides u_H0 u_H1 u_H2)) (square_change_sides l_H0 l_H1 l_H2)
    (square_change_sides_cube r C_H0 C_H1 C_H2)
    (hl0 ⊙ hl2) (hl3 ⊙ hl5) (sigT_map_eq F (hu0 ⊙ hu2)) (sigT_map_eq F (hu3 ⊙ hu5)) hv0 hv2
    (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN0 NN2)
      (square_compose_map_coherence_dep r P Q F _ _ _ _ _ _ _ _ _ NN3 NN5)
    (sigT_map_eq (fun (e: y0 = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq F h)
      (square_change_sides_dep Q u_H0 u_H1 u_H2 hu3 hu2 hu1 hu0 hu4 hu5 DU0 DU1 DU2))
      (square_change_sides_dep P l_H0 l_H1 l_H2 hl3 hl2 hl1 hl0 hl4 hl5 DL0 DL1 DL2).
Proof.
  unfold square_change_sides_cube.
  now exact (square_cube_trans_map_coherence_dep r P Q F
    (square_cube_whisker_r_coherence_dep r P Q F NN2 CC0)
    (square_cube_trans_map_coherence_dep r P Q F CC1
      (square_cube_inverse_map_coherence_dep r P Q F
        (square_cube_whisker_l_coherence_dep r P Q F NN3 CC2)))).
Defined.

Lemma square_map_cube_coherence_dep {X Y U V: Type}
  (r: Y -> X) (g: Y -> U) (f: X -> V) (j: U -> V)
  (P: X -> Type) (Q: Y -> Type) (PU: U -> Type) (PV: V -> Type)
  (R: forall y, Q y -> P (r y)) (G: forall y, Q y -> PU (g y))
  (F: forall x, P x -> PV (f x)) (J: forall u, PU u -> PV (j u))
  (α: forall y, f (r y) = j (g y))
  (Dα: forall y a, rew [PV] α y in F (r y) (R y a) = J (g y) (G y a))
  {x0 x1 x2 x3: X} {y0 y1 y2 y3: Y} {v0: x0 = r y0} {v1: x1 = r y1} {v2: x2 = r y2} {v3: x3 = r y3}
  {u_p0: y0 = y1} {l_p0: x0 = x1}
  {N_p0: v0 • f_equal r u_p0 = l_p0 • v1}
  {u_p1: y1 = y2} {l_p1: x1 = x2}
  {N_p1: v1 • f_equal r u_p1 = l_p1 • v2}
  {u_p2: y0 = y3} {l_p2: x0 = x3}
  {N_p2: v0 • f_equal r u_p2 = l_p2 • v3}
  {u_p3: y3 = y2} {l_p3: x3 = x2}
  {N_p3: v3 • f_equal r u_p3 = l_p3 • v2}
  {u_H0: u_p0 • u_p1 = u_p2 • u_p3} {l_H0: l_p0 • l_p1 = l_p2 • l_p3}
  {C_H0: square_cube (square_compose_map r N_p0 N_p1) (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0} {N: square_cube
    (eq_sym (square_coherence_fill r g f j α (u_p0 • u_p1)))
    (eq_sym (square_coherence_fill r g f j α (u_p2 • u_p3)))
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) u_H0))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) u_H0))}
  {ux0: P x0} {uy0: Q y0}
  {hv0: rew [P] v0 in ux0 = R y0 uy0}
  {ux1: P x1} {uy1: Q y1}
  {hv1: rew [P] v1 in ux1 = R y1 uy1}
  {ux2: P x2} {uy2: Q y2}
  {hv2: rew [P] v2 in ux2 = R y2 uy2}
  {ux3: P x3} {uy3: Q y3}
  {hv3: rew [P] v3 in ux3 = R y3 uy3}
  {hu0: rew [Q] u_p0 in uy0 = uy1} {hl0: rew [P] l_p0 in ux0 = ux1}
  {NN0: rew [fun e => rew [P] e in ux0 = R y1 uy1] N_p0 in
    (hv0 ⊙ sigT_map_eq R hu0) = hl0 ⊙ hv1}
  {hu1: rew [Q] u_p1 in uy1 = uy2} {hl1: rew [P] l_p1 in ux1 = ux2}
  {NN1: rew [fun e => rew [P] e in ux1 = R y2 uy2] N_p1 in
    (hv1 ⊙ sigT_map_eq R hu1) = hl1 ⊙ hv2}
  {hu2: rew [Q] u_p2 in uy0 = uy3} {hl2: rew [P] l_p2 in ux0 = ux3}
  {NN2: rew [fun e => rew [P] e in ux0 = R y3 uy3] N_p2 in
    (hv0 ⊙ sigT_map_eq R hu2) = hl2 ⊙ hv3}
  {hu3: rew [Q] u_p3 in uy3 = uy2} {hl3: rew [P] l_p3 in ux3 = ux2}
  {NN3: rew [fun e => rew [P] e in ux3 = R y2 uy2] N_p3 in
    (hv3 ⊙ sigT_map_eq R hu3) = hl3 ⊙ hv2}
  {DU0: rew [fun e => rew [Q] e in uy0 = uy2] u_H0 in (hu0 ⊙ hu1) = hu2 ⊙ hu3}
  {DL0: rew [fun e => rew [P] e in ux0 = ux2] l_H0 in (hl0 ⊙ hl1) = hl2 ⊙ hl3}
  (CC0: square_cube_coherence_dep P
    (square_compose_map r N_p0 N_p1) (square_compose_map r N_p2 N_p3)
    (f_equal (fun e => f_equal r e) u_H0) l_H0 C_H0
    (hl0 ⊙ hl1) (hl2 ⊙ hl3) (sigT_map_eq R (hu0 ⊙ hu1)) (sigT_map_eq R (hu2 ⊙ hu3)) hv0 hv2
    (square_compose_map_coherence_dep r P Q R _ _ _ _ _ _ _ _ _ NN0 NN1)
    (square_compose_map_coherence_dep r P Q R _ _ _ _ _ _ _ _ _ NN2 NN3)
    (sigT_map_eq (fun (e: y0 = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq R h) DU0) DL0)
  (NN: square_cube_coherence_dep PV
    (eq_sym (square_coherence_fill r g f j α (u_p0 • u_p1)))
    (eq_sym (square_coherence_fill r g f j α (u_p2 • u_p3)))
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) u_H0))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) u_H0)) N
    (sigT_map_eq F (sigT_map_eq R (hu0 ⊙ hu1)))
    (sigT_map_eq F (sigT_map_eq R (hu2 ⊙ hu3)))
    (sigT_map_eq J (sigT_map_eq G (hu0 ⊙ hu1)))
    (sigT_map_eq J (sigT_map_eq G (hu2 ⊙ hu3))) (Dα y0 uy0) (Dα y2 uy2)
    (square_coherence_dep_reverse_fill r g f j R G F J α Dα (u_p0 • u_p1) (hu0 ⊙ hu1))
    (square_coherence_dep_reverse_fill r g f j R G F J α Dα (u_p2 • u_p3) (hu2 ⊙ hu3)) (sigT_map_eq
      (fun (e: g y0 = g y2) (h: rew [PU] e in G y0 uy0 = G y2 uy2) => sigT_map_eq J h)
      (sigT_map_eq (fun (e: y0 = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq G h) DU0)) (sigT_map_eq
      (fun (e: r y0 = r y2) (h: rew [P] e in R y0 uy0 = R y2 uy2) => sigT_map_eq F h)
      (sigT_map_eq (fun (e: y0 = y2) (h: rew [Q] e in uy0 = uy2) => sigT_map_eq R h) DU0))):
  square_cube_coherence_dep PV
    (square_compose_map j
      (square_map_along r g f j α u_p0 N_p0 (square_coherence_fill r g f j α u_p0))
      (square_map_along r g f j α u_p1 N_p1 (square_coherence_fill r g f j α u_p1)))
    (square_compose_map j
      (square_map_along r g f j α u_p2 N_p2 (square_coherence_fill r g f j α u_p2))
      (square_map_along r g f j α u_p3 N_p3 (square_coherence_fill r g f j α u_p3)))
    (f_equal (fun e => f_equal j e) (square_map g u_H0)) (square_map f l_H0)
    (square_map_cube r g f j α C_H0 N)
    (sigT_map_eq F hl0 ⊙ sigT_map_eq F hl1) (sigT_map_eq F hl2 ⊙ sigT_map_eq F hl3)
    (sigT_map_eq J (sigT_map_eq G hu0 ⊙ sigT_map_eq G hu1))
    (sigT_map_eq J (sigT_map_eq G hu2 ⊙ sigT_map_eq G hu3))
    (sigT_map_eq F hv0 ⊙ Dα y0 uy0) (sigT_map_eq F hv2 ⊙ Dα y2 uy2)
    (square_compose_map_coherence_dep j PV PU J _ _ _ _ _ _ _ _ _
      (square_map_along_coherence_dep r g f j R G F J α Dα u_p0 N_p0 hu0 NN0)
      (square_map_along_coherence_dep r g f j R G F J α Dα u_p1 N_p1 hu1 NN1))
    (square_compose_map_coherence_dep j PV PU J _ _ _ _ _ _ _ _ _
      (square_map_along_coherence_dep r g f j R G F J α Dα u_p2 N_p2 hu2 NN2)
      (square_map_along_coherence_dep r g f j R G F J α Dα u_p3 N_p3 hu3 NN3)) (sigT_map_eq
      (fun (e: g y0 = g y2) (h: rew [PU] e in G y0 uy0 = G y2 uy2) => sigT_map_eq J h)
      (square_map_dep g G u_H0 hu2 hu1 hu0 hu3 DU0))
    (square_map_dep f F l_H0 hl2 hl1 hl0 hl3 DL0).
Proof.
  unfold square_map_cube.
  now exact (square_cube_trans_map_coherence_dep j PV PU J
    (square_cube_inverse_map_coherence_dep j PV PU J
      (square_map_along_compose_coherence_dep r g f j R G F J α Dα NN0 NN1))
    (square_cube_trans_map_coherence_dep j PV PU J
      (square_cube_map_along_coherence_dep r g f j R G F J α Dα
        _ _ u_H0 l_H0 C_H0 _ _ _ _ _ _
        (square_compose_map_coherence_dep r P Q R _ _ _ _ _ _ _ _ _ NN0 NN1)
        (square_compose_map_coherence_dep r P Q R _ _ _ _ _ _ _ _ _ NN2 NN3)
        DU0 DL0 CC0 N _ _ NN)
      (square_map_along_compose_coherence_dep r g f j R G F J α Dα NN2 NN3))).
Defined.

(** Change the four comparisons of a cube and recover its dependent
    coherence along the same changes. *)

Definition square_cube_transport {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H H': p • b = a • q} {K K': p • b' = a' • q}
  {κ κ': b = b'} {λ λ': a = a'}
  (NH: H = H') (NK: K = K') (Nκ: κ = κ') (Nλ: λ = λ')
  (C: square_cube H' K' κ' λ'): square_cube H K κ λ.
Proof. now destruct NH, NK, Nκ, Nλ. Defined.

Lemma square_cube_coherence_dep_transport {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H H': p • b = a • q} {K K': p • b' = a' • q} {κ κ': b = b'} {λ λ': a = a'}
  (NH: H = H') (NK: K = K') (Nκ: κ = κ') (Nλ: λ = λ')
  (C: square_cube H' K' κ' λ')
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [P] b in v0 = v1) (hb': rew [P] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (DH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (DK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq)
  (Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb')
  (Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha')
  (DD: square_cube_coherence_dep P H K κ λ
    (square_cube_transport NH NK Nκ Nλ C)
    ha ha' hb hb' hp hq DH DK Dκ Dλ):
  square_cube_coherence_dep P H' K' κ' λ' C ha ha' hb hb' hp hq
    (rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp ⊙ hb) = ha ⊙ hq] NH in DH)
    (rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp ⊙ hb') = ha' ⊙ hq] NK in DK)
    (rew [fun h => rew [fun e => rew [P] e in v0 = v1] h in hb = hb'] Nκ in Dκ)
    (rew [fun h => rew [fun e => rew [P] e in u0 = u1] h in ha = ha'] Nλ in Dλ).
Proof. now destruct NH, NK, Nκ, Nλ. Defined.

Lemma square_compose_map_coherence_dep_transport {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
  (F: forall y, Q y -> P (f y))
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r)
  {u0: P x0} {u1: P x1} {u2: P x2}
  {v0: Q y0} {v1: Q y1} {v2: Q y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [Q] c in v0 = v1)
  (hd: rew [Q] d in v1 = v2)
  (hp: rew [P] p in u0 = F y0 v0) (hq: rew [P] q in u1 = F y1 v1)
  (hr: rew [P] r in u2 = F y2 v2)
  (HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = F y2 v2] K in
    (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr)
  {H': p • f_equal f c = a • q} {K': q • f_equal f d = b • r}
  (NH: H = H') (NK: K = K'):
  rew [fun h => rew [fun e => rew [P] e in u0 = F y2 v2] h in
    (hp ⊙ sigT_map_eq F (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr]
    path_map2 (fun h k => square_compose_map f h k) NH NK in
    (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK) =
  square_compose_map_coherence_dep f P Q F H' K' ha hb hc hd hp hq hr
    (rew [fun h => rew [fun e => rew [P] e in u0 = F y1 v1] h in
      (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq] NH in HH)
    (rew [fun h => rew [fun e => rew [P] e in u1 = F y2 v2] h in
      (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr] NK in KK).
Proof. now destruct NH, NK. Defined.

Set Keyed Unification.

Lemma square_cube_coherence_dep_change_lifts {X: Type} {P: X -> Type}
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  {H: p • b = a • q} {K: p • b' = a' • q} {κ: b = b'} {λ: a = a'}
  {C: square_cube H K κ λ}
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {ha': rew [P] a' in u0 = u1}
  {hb: rew [P] b in v0 = v1} {hb': rew [P] b' in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  {HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq}
  {KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq}
  {Dκ: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'}
  {Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'}
  (D: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ)
  {na: rew [P] a in u0 = u1} {na': rew [P] a' in u0 = u1}
  {nb: rew [P] b in v0 = v1} {nb': rew [P] b' in v0 = v1}
  {np: rew [P] p in u0 = v0} {nq: rew [P] q in u1 = v1}
  (Ea: na = ha) (Ea': na' = ha') (Eb: nb = hb) (Eb': nb' = hb')
  (Ep: np = hp) (Eq: nq = hq):
  let L := path_map2 (fun h k => h ⊙ k) Ep Eb in
  let L' := path_map2 (fun h k => h ⊙ k) Ep Eb' in
  let R := path_map2 (fun h k => h ⊙ k) Ea Eq in
  let R' := path_map2 (fun h k => h ⊙ k) Ea' Eq in
  square_cube_coherence_dep P H K κ λ C na na' nb nb' np nq
    (f_equal (fun h => rew [fun e => rew [P] e in u0 = v1] H in h) L • (HH • eq_sym R))
    (f_equal (fun h => rew [fun e => rew [P] e in u0 = v1] K in h) L' • (KK • eq_sym R'))
    (f_equal (fun h => rew [fun e => rew [P] e in v0 = v1] κ in h) Eb • (Dκ • eq_sym Eb'))
    (f_equal (fun h => rew [fun e => rew [P] e in u0 = u1] λ in h) Ea • (Dλ • eq_sym Ea')).
Proof.
  destruct Ea, Ea', Eb, Eb', Ep, Eq.
  cbn [path_map2 f_equal eq_sym].
  rewrite 4 eq_trans_refl_l, 4 eq_trans_refl_r.
  now exact D.
Defined.
