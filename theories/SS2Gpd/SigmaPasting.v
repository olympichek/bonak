(** Sigma assembly respects square and cube pasting, including the
    normalizations of mapped paths and canonical naturality faces. *)

From Bonak.Lib Require Import Notation SigT RewLemmas Coh2Shapes.
From Bonak.SSGpd Require Import Pasting Coh3Shapes Lemmas.
From Bonak.SS2Gpd Require Import Pasting.

Set Keyed Unification.

Definition sigT_square {X: Type} {P: X -> Type} {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq):
  (= p; hp) • (= b; hb) = (= a; ha) • (= q; hq) :=
  eq_trans_eq_existT_curried p hp b hb •
    (eq_existT_curried_eq H HH • eq_sym (eq_trans_eq_existT_curried a ha q hq)).

Lemma sigT_square_cube {X: Type} (P: X -> Type)
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
  (DD: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ):
  square_cube (sigT_square H HH) (sigT_square K KK)
    (eq_existT_curried_eq κ Dκ) (eq_existT_curried_eq λ Dλ).
Proof.
  destruct λ, κ. cbn in Dλ, Dκ. destruct Dλ, Dκ.
  destruct p, b, q. cbn in hp, hb, hq.
  destruct hp, hb. destruct hq.
  cbn in H. destruct H.
  cbn in HH.
  revert DD. revert KK.
  pattern ha, HH.
  apply (homotopy_path_ind_r (fun h: u1 = u1 =>
    sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros KK DD.
  cbn [square_cube whisker_l whisker_r f_equal] in C.
  revert DD. revert KK. pattern K, C.
  apply (homotopy_path_ind_r (fun k => eq_refl • k)
    (fun k => eq_trans_refl_l k)).
  cbn. intros KK DD.
  unfold square_cube_coherence_dep in DD. cbn in DD.
  pose (F := fun e: x1 = x1 => rew [P] e in u1 = u1).
  pattern KK, DD.
  apply (homotopy_path_ind_r
    (fun k: @eq_refl _ u1 = @eq_refl _ u1 =>
      @sigT_trans_eq (x1 = x1) F
        (@eq_refl X x1) (@eq_refl X x1) (@eq_refl X x1)
        (@eq_refl _ u1) (@eq_refl _ u1) (@eq_refl _ u1)
        eq_refl eq_refl eq_refl k)
    (fun k => @sigT_trans_eq_refl (x1 = x1) F (@eq_refl X x1)
      (@eq_refl _ u1) (@eq_refl _ u1) (@eq_refl _ u1) eq_refl k
 • eq_trans_refl_l k)).
  now reflexivity.
Defined.

Lemma sigT_square_stack {X: Type} (P: X -> Type) {x0 x1 y0 y1 z0 z1: X}
  {a: x0 = x1} {c: y0 = y1} {d: z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  (H: p • c = a • q) (K: r • d = c • s)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1} {w0: P z0} {w1: P z1}
  (ha: rew [P] a in u0 = u1) (hc: rew [P] c in v0 = v1)
  (hd: rew [P] d in w0 = w1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in v0 = w0) (hs: rew [P] s in v1 = w1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in v0 = w1] K in (hr ⊙ hd) = hc ⊙ hs):
  square_stack (sigT_square H HH) (sigT_square K KK) =
  sigT_path_paste (sigT_path_paste eq_refl eq_refl) eq_refl •
    (eq_existT_curried_eq (square_stack H K)
      (square_stack_dep P H K ha hc hd hp hq hr hs HH KK) •
     eq_sym (sigT_path_paste eq_refl (sigT_path_paste eq_refl eq_refl))).
Proof.
  destruct p, r, d, s, q.
  cbn in hp, hr, hd, hs, hq.
  destruct hp, hr, hd, hs, hq.
  cbn in K. destruct K.
  cbn in KK.
  revert HH. pattern hc, KK.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros HH.
  cbn in H. destruct H.
  cbn in HH.
  pattern ha, HH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  now reflexivity.
Defined.

Lemma sigT_path_paste_refl {X: Type} {P: X -> Type}
  {x y z: X} {u: P x} {v: P y} {w: P z}
  (p: x = y) (q: y = z)
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w):
  sigT_path_paste (a := (= p; hp)) (b := (= q; hq)) eq_refl eq_refl =
  eq_trans_eq_existT_curried p hp q hq.
Proof.
  now exact (eq_trans_refl_l (eq_trans_eq_existT_curried p hp q hq)).
Defined.

Lemma sigT_square_stack_normalize {X: Type} (P: X -> Type) {x0 x1 y0 y1 z0 z1: X}
  {a: x0 = x1} {c: y0 = y1} {d: z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  (H: p • c = a • q) (K: r • d = c • s)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1} {w0: P z0} {w1: P z1}
  (ha: rew [P] a in u0 = u1) (hc: rew [P] c in v0 = v1)
  (hd: rew [P] d in w0 = w1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in v0 = w0) (hs: rew [P] s in v1 = w1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in v0 = w1] K in (hr ⊙ hd) = hc ⊙ hs)
  {ta: (x0; u0) = (x1; u1)} {tc: (y0; v0) = (y1; v1)}
  {td: (z0; w0) = (z1; w1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  {tr: (y0; v0) = (z0; w0)} {ts: (y1; v1) = (z1; w1)}
  (Na: ta = (= a; ha)) (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  (Nr: tr = (= r; hr)) (Ns: ts = (= s; hs)):
  square_stack
    (sigT_path_paste Np Nc •
      (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)))
    (sigT_path_paste Nr Nd •
      (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nc Ns))) =
  sigT_path_paste (sigT_path_paste Np Nr) Nd •
    (eq_existT_curried_eq (square_stack H K)
      (square_stack_dep P H K ha hc hd hp hq hr hs HH KK) •
     eq_sym (sigT_path_paste Na (sigT_path_paste Nq Ns))).
Proof.
  subst ta tc td tp tq tr ts.
  pose proof (sigT_square_stack P H K ha hc hd hp hq hr hs HH KK) as S.
  rewrite 6 sigT_path_paste_refl.
  rewrite 2 sigT_path_paste_refl in S.
  now exact S.
Defined.

Lemma sigT_eq_inverse {X: Type} {P: X -> Type}
  {x y: X} {u: P x} {v: P y}
  {p q: x = y}
  {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  (H: p = q)
  (HH: rew [fun e => rew [P] e in u = v] H in hp = hq):
  eq_sym (eq_existT_curried_eq H HH) =
  eq_existT_curried_eq (eq_sym H) (sigT_sym_eq HH).
Proof.
  destruct H. cbn in HH. now destruct HH.
Defined.

Lemma sigT_square_map {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq):
  square_map (fun z: {x: X &T P x} => (f z.1; F z.1 z.2)) (sigT_square H HH) =
  sigT_path_paste (f_equal_eq_existT_curried f F p hp)
    (f_equal_eq_existT_curried f F b hb) •
    (eq_existT_curried_eq (square_map f H)
      (square_map_dep f F H ha hb hp hq HH) •
    eq_sym (sigT_path_paste (f_equal_eq_existT_curried f F a ha)
      (f_equal_eq_existT_curried f F q hq))).
Proof.
  destruct p, b, q. cbn in hp, hb, hq.
  destruct hp, hb, hq.
  cbn in H. destruct H. cbn in HH.
  pattern ha, HH.
  apply (homotopy_path_ind_r (fun h: u1 = u1 =>
    sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  now reflexivity.
Defined.

Lemma sigT_square_map_normalize {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  {ta: (x0; u0) = (x1; u1)} {tb: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)):
  square_map (fun z: {x: X &T P x} => (f z.1; F z.1 z.2))
    (sigT_path_paste Np Nb •
      (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq))) =
  sigT_path_paste (sigT_path_map f F Np) (sigT_path_map f F Nb) •
    (eq_existT_curried_eq (square_map f H)
      (square_map_dep f F H ha hb hp hq HH) •
    eq_sym (sigT_path_paste (sigT_path_map f F Na) (sigT_path_map f F Nq))).
Proof.
  subst ta tb tp tq.
  unfold sigT_path_map. cbn [f_equal].
  rewrite 4 eq_trans_refl_l, 2 sigT_path_paste_refl.
  now apply sigT_square_map.
Defined.

Lemma sigT_square_map_cap_normalize {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  {tb: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)):
  square_map (fun z: {x: X &T P x} => (f z.1; F z.1 z.2))
    (sigT_path_paste Np Nb •
      (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste (eq_refl: (= a; ha) = (= a; ha)) Nq))) =
  sigT_path_paste (sigT_path_map f F Np) (sigT_path_map f F Nb) •
    (eq_existT_curried_eq (square_map f H)
      (square_map_dep f F H ha hb hp hq HH) •
    eq_sym (sigT_path_paste (f_equal_eq_existT_curried f F a ha) (sigT_path_map f F Nq))).
Proof.
  refine (sigT_square_map_normalize f F H ha hb hp hq HH eq_refl Nb Np Nq • _).
  now exact (f_equal
    (fun E => sigT_path_paste (sigT_path_map f F Np) (sigT_path_map f F Nb) •
      (eq_existT_curried_eq (square_map f H)
        (square_map_dep f F H ha hb hp hq HH) •
       eq_sym (sigT_path_paste E (sigT_path_map f F Nq))))
    (sigT_path_map_refl f F a ha)).
Defined.

Lemma sigT_eq_inverse_normalize {X: Type} {P: X -> Type}
  {x y: X} {a: P x} {b: P y} {p q: x = y}
  {hp: rew [P] p in a = b} {hq: rew [P] q in a = b}
  (H: p = q) (HH: rew [fun e => rew [P] e in a = b] H in hp = hq)
  {tp tq: (x; a) = (y; b)} (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)):
  eq_sym (Np • (eq_existT_curried_eq H HH • eq_sym Nq)) =
  Nq • (eq_existT_curried_eq (eq_sym H) (sigT_sym_eq HH) • eq_sym Np).
Proof.
  subst tp tq. cbn [eq_sym].
  rewrite 2 eq_trans_refl_l, 2 eq_trans_refl_r.
  now apply sigT_eq_inverse.
Defined.

Lemma sigT_hex_rect {X: Type} (P: X -> Type)
  {x0 x1 x2 x3 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: x2 = x3}
  {d: x0 = y1} {e: y1 = y2} {f: y2 = x3}
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  {v1: P y1} {v2: P y2}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in u1 = u2}
  {hc: rew [P] c in u2 = u3} {hd: rew [P] d in u0 = v1}
  {he: rew [P] e in v1 = v2} {hf: rew [P] f in v2 = u3}
  {ta: (x0; u0) = (x1; u1)} {tb: (x1; u1) = (x2; u2)}
  {tc: (x2; u2) = (x3; u3)} {td: (x0; u0) = (y1; v1)}
  {te: (y1; v1) = (y2; v2)} {tf: (y2; v2) = (x3; u3)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb)) (Nc: tc = (= c; hc))
  (Nd: td = (= d; hd)) (Ne: te = (= e; he)) (Nf: tf = (= f; hf))
  (H: (a • b) • c = d • (e • f))
  (HH: rew [fun e => rew [P] e in u0 = u3] H in
    ((ha ⊙ hb) ⊙ hc) = hd ⊙ (he ⊙ hf)):
  sigT_path_paste (sigT_path_paste Na Nb) Nc •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Nd (sigT_path_paste Ne Nf))) =
  sigT_path_paste (sigT_path_paste Na Nb) Nc •
    (eq_existT_curried_eq H
      HH •
     eq_sym (sigT_path_paste Nd (sigT_path_paste Ne Nf))).
Proof.
  now reflexivity.
Defined.

Lemma sigT_square_coherence {A B C D: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x))
  (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x))
  (K: forall x, f (u x) = g (v x))
  (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a))
  {x y: A} (p: x = y) {a: PA x} {b: PA y} (hp: rew [PA] p in a = b):
  square_coherence_fill
    (fun z: {x: A &T PA x} => (u z.1; U z.1 z.2))
    (fun z: {x: A &T PA x} => (v z.1; V z.1 z.2))
    (fun z: {x: B &T PB x} => (f z.1; F z.1 z.2))
    (fun z: {x: C &T PC x} => (g z.1; G z.1 z.2))
    (fun z => (= K z.1; HK z.1 z.2)) (= p; hp) =
  sigT_path_paste (sigT_path_map f F (f_equal_eq_existT_curried u U p hp)) eq_refl •
    (eq_existT_curried_eq (square_coherence_fill u v f g K p)
      (square_coherence_dep_fill u v f g U V F G K HK p hp) •
    eq_sym (sigT_path_paste eq_refl
      (sigT_path_map g G (f_equal_eq_existT_curried v V p hp)))).
Proof.
  destruct p, hp.
  unfold sigT_path_map, square_coherence_fill, square_coherence.
  cbn.
  unfold square_coherence_dep_fill.
  generalize (HK x a).
  generalize (K x), (G (v x) (V x a)).
  generalize (g (v x)).
  intros z k w hk.
  now destruct hk, k.
Defined.

Lemma sigT_map_compose_tail_normalized {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x y z: X} {p: x = y} {q: y = z} {w: Y} {r: f z = w}
  {u: P x} {v: P y} {s: P z} {t: Q w}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = s)
  (hr: rew [Q] r in F z s = t)
  {tp: (x; u) = (y; v)} {tq: (y; v) = (z; s)}
  {tr: (f z; F z s) = (w; t)}
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)) (Nr: tr = (= r; hr)):
  let tf := fun z: {a: X &T P a} => (f z.1; F z.1 z.2) in
  map_compose_tail tf tp tq tr =
  sigT_path_paste (sigT_path_map f F (sigT_path_paste Np Nq)) Nr •
    (eq_existT_curried_eq (map_compose_tail f p q r)
      (map_compose_tail_dep f F hp hq hr) •
     eq_sym (sigT_path_paste (sigT_path_map f F Np)
       (sigT_path_paste (sigT_path_map f F Nq) Nr))).
Proof.
  subst tp tq tr. now destruct hp, p, hq, q, hr, r.
Defined.

Lemma sigT_square_change_sides {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (H: p • b = a • q) (Hq: q' = q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hp': rew [P] p' in u0 = v0)
  (hq: rew [P] q in u1 = v1) (hq': rew [P] q' in u1 = v1)
  (HHp: rew [fun e => rew [P] e in u0 = v0] Hp in hp' = hp)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (HHq: rew [fun e => rew [P] e in u1 = v1] Hq in hq' = hq) :
  square_change_sides (eq_existT_curried_eq Hp HHp) (sigT_square H HH)
    (eq_existT_curried_eq Hq HHq) =
  sigT_square (square_change_sides Hp H Hq)
    (square_change_sides_dep P Hp H Hq ha hb hp hp' hq hq' HHp HH HHq).
Proof.
  destruct Hp, Hq. cbn in HHp, HHq. destruct HHp, HHq.
  destruct p', b, q'. cbn in hp', hb, hq'.
  destruct hp', hb, hq'.
  cbn in H. destruct H. cbn in HH.
  pattern ha, HH.
  apply (homotopy_path_ind_r (fun h: u1 = u1 =>
    sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  now reflexivity.
Defined.

Lemma sigT_square_change_sides_normalized {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (H: p • b = a • q) (Hq: q' = q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hp': rew [P] p' in u0 = v0)
  (hq: rew [P] q in u1 = v1) (hq': rew [P] q' in u1 = v1)
  (HHp: rew [fun e => rew [P] e in u0 = v0] Hp in hp' = hp)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (HHq: rew [fun e => rew [P] e in u1 = v1] Hq in hq' = hq)
  {ta: (x0; u0) = (x1; u1)} {tb: (y0; v0) = (y1; v1)}
  {tp tp': (x0; u0) = (y0; v0)} {tq tq': (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Np': tp' = (= p'; hp'))
  (Nq: tq = (= q; hq)) (Nq': tq' = (= q'; hq')):
  square_change_sides
    (Np' • (eq_existT_curried_eq Hp HHp • eq_sym Np))
    (sigT_path_paste Np Nb •
      (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)))
    (Nq' • (eq_existT_curried_eq Hq HHq • eq_sym Nq)) =
  sigT_path_paste Np' Nb •
    (eq_existT_curried_eq (square_change_sides Hp H Hq)
      (square_change_sides_dep P Hp H Hq ha hb hp hp' hq hq' HHp HH HHq) •
     eq_sym (sigT_path_paste Na Nq')).
Proof.
  subst ta tb tp tp' tq tq'.
  cbn [eq_sym]. rewrite 2 eq_trans_refl_l, 2 eq_trans_refl_r.
  unfold sigT_path_paste. cbn [whisker_l whisker_r f_equal].
  rewrite 4 eq_trans_refl_l.
  now apply sigT_square_change_sides.
Defined.

Lemma sigT_square_compose_map {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
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
    (hq ⊙ sigT_map_eq F hd) = hb ⊙ hr):
  let tf := fun z: {y: Y &T Q y} => (f z.1; F z.1 z.2) in
  let Htotal := sigT_path_paste eq_refl (f_equal_eq_existT_curried f F c hc) •
    (eq_existT_curried_eq H HH • eq_sym (eq_trans_eq_existT_curried a ha q hq)) in
  let Ktotal := sigT_path_paste eq_refl (f_equal_eq_existT_curried f F d hd) •
    (eq_existT_curried_eq K KK • eq_sym (eq_trans_eq_existT_curried b hb r hr)) in
  square_compose_map tf Htotal Ktotal =
  sigT_path_paste eq_refl
    (f_equal (fun e => f_equal tf e) (eq_trans_eq_existT_curried c hc d hd) •
      f_equal_eq_existT_curried f F (c • d) (hc ⊙ hd)) •
    (eq_existT_curried_eq (square_compose_map f H K)
      (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK) •
     eq_sym (sigT_path_paste (sigT_path_paste eq_refl eq_refl) eq_refl)).
Proof.
  destruct c, d.
  revert HH. revert hp. revert ha. revert u0. revert H. revert a.
  pattern x0, p.
  apply (homotopy_path_ind (fun x: X => x) (fun x => eq_refl)).
  cbn. intros a H u0 ha hp HH.
  revert KK. revert hr. revert hb. revert u2. revert K. revert b.
  pattern x2, r.
  apply (homotopy_path_ind (fun x: X => x) (fun x => eq_refl)).
  cbn. intros b K u2 hb hr KK.
  revert HH. revert KK. revert hq. revert ha. revert hb. revert u1.
  revert H. revert K. revert a. revert b.
  pattern x1, q.
  apply (homotopy_path_ind (fun x: X => x) (fun x => eq_refl)).
  cbn. intros b a K H u1 hb ha hq KK HH.
  cbn in hc, hd, hp, hr, hq.
  destruct hc, hd.
  revert HH. revert ha. pattern u0, hp.
  apply (homotopy_path_ind (fun u: P (f y0) => u) (fun u => eq_refl)).
  cbn. intros ha HH.
  revert KK. revert hb. pattern u2, hr.
  apply (homotopy_path_ind (fun u: P (f y0) => u) (fun u => eq_refl)).
  cbn. intros hb KK.
  revert HH. revert KK. revert ha. revert hb. pattern u1, hq.
  apply (homotopy_path_ind (fun u: P (f y0) => u) (fun u => eq_refl)).
  cbn. intros hb ha KK HH.
  cbn in K. destruct K.
  cbn in KK.
  revert HH. pattern hb, KK.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros HH.
  cbn in H. destruct H.
  cbn in HH.
  pattern ha, HH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  now reflexivity.
Defined.

Lemma sigT_square_compose_map_normalize {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
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
  {ta: (x0; u0) = (x1; u1)} {tb: (x1; u1) = (x2; u2)}
  {tc: (y0; v0) = (y1; v1)} {td: (y1; v1) = (y2; v2)}
  {tp: (x0; u0) = (f y0; F y0 v0)}
  {tq: (x1; u1) = (f y1; F y1 v1)}
  {tr: (x2; u2) = (f y2; F y2 v2)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)) (Nr: tr = (= r; hr)):
  let tf := fun z: {y: Y &T Q y} => (f z.1; F z.1 z.2) in
  let Htotal := sigT_path_paste Np
    (f_equal (fun e => f_equal tf e) Nc • f_equal_eq_existT_curried f F c hc) •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)) in
  let Ktotal := sigT_path_paste Nq
    (f_equal (fun e => f_equal tf e) Nd • f_equal_eq_existT_curried f F d hd) •
    (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nb Nr)) in
  square_compose_map tf Htotal Ktotal =
  sigT_path_paste Np
    (f_equal (fun e => f_equal tf e) (sigT_path_paste Nc Nd) •
      f_equal_eq_existT_curried f F (c • d) (hc ⊙ hd)) •
    (eq_existT_curried_eq (square_compose_map f H K)
      (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK) •
     eq_sym (sigT_path_paste (sigT_path_paste Na Nb) Nr)).
Proof.
  subst ta tb tc td tp tq tr.
  cbn [f_equal]. rewrite 2 (eq_trans_refl_l _).
  pose proof (sigT_square_compose_map f P Q F H K ha hb hc hd hp hq hr HH KK) as S.
  rewrite 4 sigT_path_paste_refl.
  rewrite sigT_path_paste_refl in S.
  now exact S.
Defined.

Lemma sigT_square_cube_normalize {X: Type} (P: X -> Type)
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
  (DD: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ)
  {ta ta': (x0; u0) = (x1; u1)} {tb tb': (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Na': ta' = (= a'; ha'))
  (Nb: tb = (= b; hb)) (Nb': tb' = (= b'; hb'))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)):
  square_cube
    (sigT_path_paste Np Nb •
      (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)))
    (sigT_path_paste Np Nb' •
      (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Na' Nq)))
    (Nb • (eq_existT_curried_eq κ Dκ • eq_sym Nb'))
    (Na • (eq_existT_curried_eq λ Dλ • eq_sym Na')).
Proof.
  subst ta ta' tb tb' tp tq.
  cbn [eq_sym]. rewrite 2 (eq_trans_refl_l _).
  rewrite 4 sigT_path_paste_refl.
  now exact (sigT_square_cube P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ DD).
Defined.

Lemma sigT_eq_map_normalized {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  {x y: A} {u: P x} {v: P y}
  {p q: x = y} {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  {tp tq: (x; u) = (y; v)}
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  (H: p = q)
  (HH: rew [fun e => rew [P] e in u = v] H in hp = hq):
  f_equal
    (fun e => f_equal (fun z: {a: A &T P a} => (f z.1; F z.1 z.2)) e)
    (Np • (eq_existT_curried_eq H HH • eq_sym Nq)) =
  sigT_path_map f F Np •
    (eq_existT_curried_eq (f_equal (fun e => f_equal f e) H)
      (sigT_map_eq (f := fun e => f_equal f e)
        (Q := fun e => rew [Q] e in F x u = F y v)
        (fun (e: x = y) (h: rew [P] e in u = v) => sigT_map_eq F h) HH) •
     eq_sym (sigT_path_map f F Nq)).
Proof.
  subst tp tq. destruct H. cbn in HH. destruct HH.
  now destruct hp, p.
Defined.

Section DirectMapTail.

Context {X Y: Type} {P: X -> Type} {Q: Y -> Type} (f: X -> Y) (F: forall x, P x -> Q (f x)).

Context {x y z: X} {w: Y} {p: x = y} {q: y = z} {r: f z = w} {a: P x} {b: P y} {c: P z} {d: Q w}.

Context (hp: rew [P] p in a = b) (hq: rew [P] q in b = c) (hr: rew [Q] r in F z c = d).

Context {tp: (x; a) = (y; b)} (Np: tp = (= p; hp)).

Let Ncomp := sigT_path_paste Np (eq_refl: (= q; hq) = (= q; hq)).

Let NL := sigT_path_paste (sigT_path_map f F Ncomp) (eq_refl: (= r; hr) = (= r; hr)).

Let NR := sigT_path_paste (sigT_path_map f F Np)
  (sigT_path_paste (f_equal_eq_existT_curried f F q hq) (eq_refl: (= r; hr) = (= r; hr))).

Let tf := fun z: {x: X &T P x} => (f z.1; F z.1 z.2).

Lemma sigT_map_tail_direct_normalize:
  map_compose_tail tf tp (= q; hq) (= r; hr) =
  NL • (eq_existT_curried_eq (map_compose_tail f p q r) (map_compose_tail_dep f F hp hq hr) • eq_sym NR).
Proof.
  pose proof (sigT_map_compose_tail_normalized f F hp hq hr Np
    (eq_refl: (= q; hq) = (= q; hq)) (eq_refl: (= r; hr) = (= r; hr))) as N.
  rewrite sigT_path_map_refl in N. now exact N.
Defined.

Context (R: {x: X &T P x} -> Type) (S: {x: Y &T Q x} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2)).

Context {da: R (x; a)} {db: R (y; b)} {dc: R (z; c)} {dd: S (w; d)}.

Context (dp: rew [R] tp in da = db) (dq: rew [R](= q; hq) in db = dc) (dr: rew [S](= r; hr) in V (z; c) dc = dd).

Let pf := fun x (uv: {u: P x &T R (x; u)}) => (F x uv.1; V (x; uv.1) uv.2): {u: Q (f x)&T S (f x; u)}.

Let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in da = db] Np in dp).

Let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := dq).

Let er := eq_existT_curried_dep (Q := S) (H := r) (Hu := hr) (Hv := dr).

Context (pp: rew [fun x => {u: P x &T R (x; u)}] p in (a; da) = (b; db)) (EP: pp = ep).

Let SourceE := sigT_pair_path_paste R Np (eq_refl: (= q; hq) = (= q; hq)) dp dq EP (eq_refl: eq = eq).

Let MapCompE := sigT_pair_path_map f F R S V Ncomp (dp ⊙ dq) SourceE.

Let MapPE := sigT_pair_path_map f F R S V Np dp EP.

Let MapQE := sigT_dep_path_map_direct f F R S V dq.

Let EL := sigT_pair_path_paste S (sigT_path_map f F Ncomp) (eq_refl: (= r; hr) = (= r; hr))
  (sigT_map_eq V (dp ⊙ dq)) dr MapCompE (eq_refl: er = er).

Let ER := sigT_pair_path_paste S (sigT_path_map f F Np)
  (sigT_path_paste (f_equal_eq_existT_curried f F q hq) (eq_refl: (= r; hr) = (= r; hr)))
  (sigT_map_eq V dp) (sigT_map_eq V dq ⊙ dr) MapPE
  (sigT_pair_path_paste S (f_equal_eq_existT_curried f F q hq) (eq_refl: (= r; hr) = (= r; hr))
    (sigT_map_eq V dq) dr MapQE (eq_refl: er = er)).

Let E := fun e: (f x; F x a) = (w; d) => rew [S] e in V (x; a) da = dd.

Definition sigT_map_tail_direct_higher_transport :=
  rew [fun h => rew [E] h in (sigT_map_eq V (dp ⊙ dq) ⊙ dr) = sigT_map_eq V dp ⊙ (sigT_map_eq V dq ⊙ dr)]
    sigT_map_tail_direct_normalize in map_compose_tail_dep tf V dp dq dr.

Lemma sigT_map_tail_direct_pair_factory:
  map_compose_tail_dep f pf pp eq er =
  f_equal (fun h => rew [fun e => rew [fun x => {u: Q x &T S (x; u)}] e in (F x a; V (x; a) da) = (d; dd)]
    (map_compose_tail f p q r) in h) EL •
    (sigT_eq_dep_normalize S (map_compose_tail f p q r) (map_compose_tail_dep f F hp hq hr) NL NR
      (sigT_map_eq V (dp ⊙ dq) ⊙ dr) (sigT_map_eq V dp ⊙ (sigT_map_eq V dq ⊙ dr))
      sigT_map_tail_direct_higher_transport • eq_sym ER).
Proof.
  unfold EL, ER, MapPE, MapQE, MapCompE, SourceE, ep, eq, er, pf, E, NL, NR, Ncomp, tf,
    sigT_map_tail_direct_higher_transport, sigT_map_tail_direct_normalize.
  clear EL ER MapPE MapQE MapCompE SourceE.
  subst pp tp. destruct hp, p, hq, q, hr, r. cbn in dp, dq, dr. destruct dp, dq, dr.
  now reflexivity.
Defined.

End DirectMapTail.

Lemma sigT_layer_square_nat
  {Z V V' W X: Type} {S: Z -> Type} {QL: V -> Type} {QR: V' -> Type}
  {PW: W -> Type} {P: X -> Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (RL: forall z, S z -> QL (L z)) (RR: forall z, S z -> QR (R z))
  (F: forall v, QL v -> P (f v)) (G: forall v, QR v -> P (g v))
  (D: forall w, PW w -> P (d w))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [P] k z in F (L z) (RL z a) = G (R z) (RR z a))
  {z1 z2: Z} (p: z1 = z2) {m: V} {n: V'}
  (l: L z2 = m) (r: R z2 = n) {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: hexagonal_coherence f d g l e r c (k z2) c')
  {a1: S z1} {a2: S z2} {am: QL m} {an: QR n} {aw1: PW w1} {aw2: PW w2}
  (hp: rew [S] p in a1 = a2)
  (hl: rew [QL] l in RL z2 a2 = am) (hr: rew [QR] r in RR z2 a2 = an)
  (he: rew [PW] e in aw1 = aw2)
  (hc: rew [P] c in F m am = D w1 aw1)
  (hc': rew [P] c' in G n an = D w2 aw2)
  (HH: hexagonal_coherence_dep F D G H hl he hr hc (hk z2 a2) hc') :
  let tL := fun z: {x: Z &T S x} => (L z.1; RL z.1 z.2) in
  let tR := fun z: {x: Z &T S x} => (R z.1; RR z.1 z.2) in
  let tf := fun z: {x: V &T QL x} => (f z.1; F z.1 z.2) in
  let tg := fun z: {x: V' &T QR x} => (g z.1; G z.1 z.2) in
  let td := fun z: {x: W &T PW x} => (d z.1; D z.1 z.2) in
  let tk := fun z: {x: Z &T S x} => (= k z.1; hk z.1 z.2) in
  let lnorm := sigT_path_paste
    (sigT_path_paste
      (f_equal (fun e => f_equal tf e)
        (sigT_path_paste (f_equal_eq_existT_curried L RL p hp) eq_refl) •
       f_equal_eq_existT_curried f F (f_equal L p • l) (sigT_map_eq RL hp ⊙ hl))
      eq_refl)
    (sigT_path_map d D (p := e) (hp := he) eq_refl) in
  let rnorm := sigT_path_paste eq_refl
    (sigT_path_paste
      (f_equal (fun e => f_equal tg e)
        (sigT_path_paste (f_equal_eq_existT_curried R RR p hp) eq_refl) •
       f_equal_eq_existT_curried g G (f_equal R p • r) (sigT_map_eq RR hp ⊙ hr))
      eq_refl) in
  layer_square_nat tL tR tf tg td tk (= p; hp) (= l; hl) (= r; hr)
    (= e; he) (= c; hc) (= c'; hc')
    (eq_existT_curried_hex f F g G d D H HH)
    (square_coherence_fill tL tR tf tg tk (= p; hp)) =
  lnorm •
    (eq_existT_curried_eq
      (layer_square_nat L R f g d k p l r e c c' H
        (square_coherence_fill L R f g k p))
      (layer_square_nat_coherence_dep L R f g d RL RR F G D k hk
        p l r e c c' H hp hl hr he hc hc' HH) • eq_sym rnorm).
Proof.
  cbn zeta.
  unfold layer_square_nat at 1. unfold square_nat_along at 1.
  pose (EL := sigT_map_tail_direct_normalize f F (sigT_map_eq RL hp) hl hc
    (f_equal_eq_existT_curried L RL p hp)).
  pose (ER := sigT_map_tail_direct_normalize g G (sigT_map_eq RR hp) hr hc'
    (f_equal_eq_existT_curried R RR p hp)).
  pose (EN := sigT_square_coherence L R f g RL RR F G k hk p hp).
  pose (EH := sigT_hex_rect P (f_equal_eq_existT_curried f F l hl)
    (eq_refl: (= c; hc) = (= c; hc)) (f_equal_eq_existT_curried d D e he)
    (eq_refl: (= k z2; hk z2 a2) = (= k z2; hk z2 a2))
    (f_equal_eq_existT_curried g G r hr) (eq_refl: (= c'; hc') = (= c'; hc')) H HH).
  pose (ES := sigT_square_stack_normalize P
    (square_coherence_fill L R f g k p)
    H
    (hk z1 a1) (hk z2 a2) (sigT_map_eq D he)
    (sigT_map_eq F (sigT_map_eq RL hp)) (sigT_map_eq G (sigT_map_eq RR hp))
    (sigT_map_eq F hl ⊙ hc) (sigT_map_eq G hr ⊙ hc')
    (square_coherence_dep_fill L R f g RL RR F G k hk p hp)
    HH
    (eq_refl: (= k z1; hk z1 a1) = (= k z1; hk z1 a1))
    (eq_refl: (= k z2; hk z2 a2) = (= k z2; hk z2 a2))
    (f_equal_eq_existT_curried d D e he)
    (sigT_path_map f F (f_equal_eq_existT_curried L RL p hp))
    (sigT_path_map g G (f_equal_eq_existT_curried R RR p hp))
    (sigT_path_paste (f_equal_eq_existT_curried f F l hl) (eq_refl: (= c; hc) = (= c; hc)))
    (sigT_path_paste (f_equal_eq_existT_curried g G r hr) (eq_refl: (= c'; hc') = (= c'; hc')))).
  refine (path_map3 (fun l m r => square_change_sides l m r) EL
    (path_map2 (fun n h => square_stack n h) EN EH • ES) ER • _).
  refine (sigT_square_change_sides_normalized P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ • _).
  match goal with
  | |- (sigT_path_paste ?NL (f_equal_eq_existT_curried d D e he) • ?Tail) = _ =>
      now exact (f_equal (fun nl => nl • Tail) (f_equal (fun nb => sigT_path_paste NL nb)
        (eq_sym (sigT_path_map_refl d D e he))))
  end.
Defined.

Section ExplicitLayerMap.

Context
  {T M N X Y U: Type} {PT: T -> Type} {PM: M -> Type} {PN: N -> Type}
  {P: X -> Type} {Q: Y -> Type} {PU: U -> Type}
  (r: T -> X) (s: M -> X) (t: N -> X) (f: X -> Y) (g: T -> U) (j: U -> Y)
  (R: forall d, PT d -> P (r d))
  (S: forall m, PM m -> P (s m)) (T': forall n, PN n -> P (t n))
  (F: forall x, P x -> Q (f x))
  (G: forall d, PT d -> PU (g d)) (J: forall u, PU u -> Q (j u))
  (α: forall d, f (r d) = j (g d))
  (Hα: forall d a, rew [Q] α d in F (r d) (R d a) = J (g d) (G d a))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: hexagonal_coherence s r t p e q v k w)
  {ad: PT d} {ad': PT d'} {am: PM m} {am': PM m'} {an: PN n} {an': PN n'}
  (he: rew [PT] e in ad = ad') (hp: rew [PM] p in am = am')
  (hq: rew [PN] q in an = an')
  (hv: rew [P] v in S m' am' = R d ad)
  (hw: rew [P] w in T' n' an' = R d' ad')
  (hk: rew [P] k in S m am = T' n an)
  (HH: hexagonal_coherence_dep S R T' H hp he hq hv hk hw).

Let tr := fun z: {x: T &T PT x} => (r z.1; R z.1 z.2).

Let ts := fun z: {x: M &T PM x} => (s z.1; S z.1 z.2).

Let tt := fun z: {x: N &T PN x} => (t z.1; T' z.1 z.2).

Let tf := fun z: {x: X &T P x} => (f z.1; F z.1 z.2).

Let tg := fun z: {x: T &T PT x} => (g z.1; G z.1 z.2).

Let tj := fun z: {x: U &T PU x} => (j z.1; J z.1 z.2).

Let tα := fun z: {x: T &T PT x} => (= α z.1; Hα z.1 z.2).

Let Ns := f_equal_eq_existT_curried s S p hp.

Let Nt := f_equal_eq_existT_curried t T' q hq.

Let Nr := f_equal_eq_existT_curried r R e he.

Let NP := sigT_path_paste Ns (eq_refl: (= v; hv) = (= v; hv)).

Let NQ := sigT_path_paste Nt (eq_refl: (= w; hw) = (= w; hw)).

Let HR := H.

Let HR1 := HH.

Let Enhex := sigT_hex_rect P Ns (eq_refl: (= v; hv) = (= v; hv)) Nr
  (eq_refl: (= k; hk) = (= k; hk)) Nt (eq_refl: (= w; hw) = (= w; hw)) H HH.

Let Enmap := f_equal (fun c => square_map tf c) Enhex •
  sigT_square_map_cap_normalize f F HR hk (sigT_map_eq R he)
    (sigT_map_eq S hp ⊙ hv) (sigT_map_eq T' hq ⊙ hw) HR1
    Nr NP NQ.

Let HN := square_coherence_fill r g f j α e.

Let HN1 := square_coherence_dep_fill r g f j R G F J α Hα e he.

Let NNL := sigT_path_paste (sigT_path_map f F Nr) (eq_refl: (= α d'; Hα d' ad') = (= α d'; Hα d' ad')).

Let NNR := sigT_path_paste (eq_refl: (= α d; Hα d ad) = (= α d; Hα d ad))
  (sigT_path_map j J (f_equal_eq_existT_curried g G e he)).

Let Ennat := f_equal (fun c => eq_sym c) (sigT_square_coherence r g f j R G F J α Hα e he) •
  sigT_eq_inverse_normalize HN HN1 NNL NNR.

Let HM := square_map f HR.

Let HM1 := square_map_dep f F HR hk (sigT_map_eq R he)
  (sigT_map_eq S hp ⊙ hv) (sigT_map_eq T' hq ⊙ hw) HR1.

Let Encstack := sigT_square_stack_normalize Q HM (eq_sym HN)
  (sigT_map_eq F hk) (sigT_map_eq F (sigT_map_eq R he))
  (sigT_map_eq J (sigT_map_eq G he))
  (sigT_map_eq F (sigT_map_eq S hp ⊙ hv)) (sigT_map_eq F (sigT_map_eq T' hq ⊙ hw))
  (Hα d ad) (Hα d' ad') HM1 (sigT_sym_eq HN1)
  (f_equal_eq_existT_curried f F k hk)
  (sigT_path_map f F Nr) (sigT_path_map j J (f_equal_eq_existT_curried g G e he))
  (sigT_path_map f F NP) (sigT_path_map f F NQ)
  (eq_refl: (= α d; Hα d ad) = (= α d; Hα d ad))
  (eq_refl: (= α d'; Hα d' ad') = (= α d'; Hα d' ad')).

Let NLEFT := sigT_path_paste
  (sigT_path_paste (sigT_path_map f F NP) (eq_refl: (= α d; Hα d ad) = (= α d; Hα d ad)))
  (sigT_path_map j J (f_equal_eq_existT_curried g G e he)).

Let NRIGHTSIDE := sigT_path_paste (sigT_path_map f F NQ)
  (eq_refl: (= α d'; Hα d' ad') = (= α d'; Hα d' ad')).

Definition sigT_layer_square_map:
  layer_square_map tr ts tt tf tg tj tα
    (= e; he) (= p; hp) (= q; hq) (= v; hv) (= w; hw) (= k; hk)
    (eq_existT_curried_hex s S t T' r R H HH)
    (square_coherence_fill tr tg tf tj tα (= e; he)) =
  NLEFT •
    (eq_existT_curried_eq (layer_square_map r s t f g j α e p q v w k H HN)
      (layer_square_map_coherence_dep r s t f g j R S T' F G J α Hα
        e p q v w k H he hp hq hv hw hk HH) •
     eq_sym (sigT_path_paste (f_equal_eq_existT_curried f F k hk) NRIGHTSIDE)) :=
  path_map2 (fun h k => square_stack h k) Enmap Ennat • Encstack.

End ExplicitLayerMap.

(** Pairing is compatible with the normalizations of each pasting operation. *)

Lemma sigT_square_dep_normalize {X: Type} {P: X -> Type}
  (R: {x: X &T P x} -> Type)
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  {ta: (x0; u0) = (x1; u1)} {tb: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  {r0: R (x0; u0)} {r1: R (x1; u1)}
  {s0: R (y0; v0)} {s1: R (y1; v1)}
  (da: rew [R] ta in r0 = r1) (db: rew [R] tb in s0 = s1)
  (dp: rew [R] tp in r0 = s0) (dq: rew [R] tq in r1 = s1)
  (DHH: rew [fun e => rew [R] e in r0 = s1] (sigT_path_paste Np Nb •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq))) in
    (dp ⊙ db) = da ⊙ dq):
  rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u0; r0) = (v1; s1)] H in
    (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r0 = s0] Np in dp) ⊙
     eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in s0 = s1] Nb in db)) =
    eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da) ⊙
    eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in r1 = s1] Nq in dq).
Proof.
  now exact (f_equal (fun h =>
    rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (v1; s1)] H in h)
    (sigT_dep_path_paste_normalize R Np Nb dp db) •
    (sigT_eq_dep_normalize R H HH (sigT_path_paste Np Nb) (sigT_path_paste Na Nq)
      (dp ⊙ db) (da ⊙ dq) DHH •
     eq_sym (sigT_dep_path_paste_normalize R Na Nq da dq))).
Defined.

Section PairHexRect.

Context {X: Type} (P: X -> Type)
  {x0 x1 x2 x3 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: x2 = x3}
  {d: x0 = y1} {e: y1 = y2} {f: y2 = x3}
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  {v1: P y1} {v2: P y2}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in u1 = u2}
  {hc: rew [P] c in u2 = u3} {hd: rew [P] d in u0 = v1}
  {he: rew [P] e in v1 = v2} {hf: rew [P] f in v2 = u3}
  {ta: (x0; u0) = (x1; u1)} {tb: (x1; u1) = (x2; u2)}
  {tc: (x2; u2) = (x3; u3)} {td: (x0; u0) = (y1; v1)}
  {te: (y1; v1) = (y2; v2)} {tf: (y2; v2) = (x3; u3)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb)) (Nc: tc = (= c; hc))
  (Nd: td = (= d; hd)) (Ne: te = (= e; he)) (Nf: tf = (= f; hf))
  (H: (a • b) • c = d • (e • f))
  (HH: rew [fun e => rew [P] e in u0 = u3] H in
    ((ha ⊙ hb) ⊙ hc) = hd ⊙ (he ⊙ hf)).

Context (R: {x: X &T P x} -> Type).

Context {r0: R (x0; u0)} {r1: R (x1; u1)} {r2: R (x2; u2)} {r3: R (x3; u3)}
  {s1: R (y1; v1)} {s2: R (y2; v2)}.

Context (da: rew [R] ta in r0 = r1) (db: rew [R] tb in r1 = r2) (dc: rew [R] tc in r2 = r3)
  (dd: rew [R] td in r0 = s1) (de: rew [R] te in s1 = s2) (df: rew [R] tf in s2 = r3).

Let NL := sigT_path_paste (sigT_path_paste Na Nb) Nc.

Let NR := sigT_path_paste Nd (sigT_path_paste Ne Nf).

Let Ht := NL • (eq_existT_curried_eq H HH • eq_sym NR).

Let Route := fun e: (x0; u0) = (x3; u3) => rew [R] e in r0 = r3.

Context (DHH: rew [Route] Ht in ((da ⊙ db) ⊙ dc) = dd ⊙ (de ⊙ df)).

Let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da).

Let eb := eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in r1 = r2] Nb in db).

Let ec := eq_existT_curried_dep (Q := R) (H := c) (Hu := hc) (Hv := rew [fun e => rew [R] e in r2 = r3] Nc in dc).

Let ed := eq_existT_curried_dep (Q := R) (H := d) (Hu := hd) (Hv := rew [fun e => rew [R] e in r0 = s1] Nd in dd).

Let ee := eq_existT_curried_dep (Q := R) (H := e) (Hu := he) (Hv := rew [fun e => rew [R] e in s1 = s2] Ne in de).

Let ef := eq_existT_curried_dep (Q := R) (H := f) (Hu := hf) (Hv := rew [fun e => rew [R] e in s2 = r3] Nf in df).

Definition sigT_hex_pair_left_route:
  (ea ⊙ eb) ⊙ ec =
  eq_existT_curried_dep (Q := R) (H := (a • b) • c) (Hu := (ha ⊙ hb) ⊙ hc)
    (Hv := rew [Route] NL in ((da ⊙ db) ⊙ dc)).
Proof.
  unfold ea, eb, ec, NL, Route.
  refine (f_equal (fun h => h ⊙ _) (sigT_dep_path_paste_normalize R Na Nb da db) • _).
  now exact (sigT_dep_path_paste_normalize R (sigT_path_paste Na Nb) Nc (da ⊙ db) dc).
Defined.

Definition sigT_hex_pair_right_route:
  ed ⊙ (ee ⊙ ef) =
  eq_existT_curried_dep (Q := R) (H := d • (e • f)) (Hu := hd ⊙ (he ⊙ hf))
    (Hv := rew [Route] NR in (dd ⊙ (de ⊙ df))).
Proof.
  unfold ed, ee, ef, NR, Route.
  refine (f_equal (fun h => _ ⊙ h) (sigT_dep_path_paste_normalize R Ne Nf de df) • _).
  now exact (sigT_dep_path_paste_normalize R Nd (sigT_path_paste Ne Nf) dd (de ⊙ df)).
Defined.

Let EH := fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (u3; r3).

Definition sigT_hex_pair_factory:
  rew [EH] H in ((ea ⊙ eb) ⊙ ec) = ed ⊙ (ee ⊙ ef) :=
  f_equal (fun h => rew [EH] H in h) sigT_hex_pair_left_route •
    (sigT_eq_dep_normalize R H HH NL NR ((da ⊙ db) ⊙ dc) (dd ⊙ (de ⊙ df)) DHH •
     eq_sym sigT_hex_pair_right_route).

Let HR := H.

Let HR1 := HH.

Definition sigT_hex_rect_normalized_higher := DHH.

Let Drect := sigT_square_dep_normalize R HR HR1 Nd Nc (sigT_path_paste Na Nb) (sigT_path_paste Ne Nf)
  dd dc (da ⊙ db) (de ⊙ df) sigT_hex_rect_normalized_higher.

Let EL := path_map2 (fun h k => h ⊙ k) (sigT_dep_path_paste_normalize R Na Nb da db) (eq_refl: ec = ec).

Let ER := path_map2 (fun h k => h ⊙ k) (eq_refl: ed = ed) (sigT_dep_path_paste_normalize R Ne Nf de df).

Lemma sigT_hex_rect_pair_dep:
  sigT_hex_pair_factory =
  f_equal (fun h => rew [EH] HR in h) EL • (Drect • eq_sym ER).
Proof.
  cbv beta iota zeta delta[ea eb ec ed ee ef EH EL ER Drect HR HR1
    sigT_hex_rect_normalized_higher sigT_hex_pair_factory sigT_hex_pair_left_route
    sigT_hex_pair_right_route Route Ht NL NR] in *.
  clear ea eb ec ed ee ef EH EL ER Drect HR HR1 Route Ht NL NR.
  subst ta tb tc td te tf.
  destruct a, b, c, e, f. cbn in ha, hb, hc, he, hf. destruct ha, hb, hc, he, hf.
  cbn in da, db, dc, de, df. destruct da, db, dc, de, df.
  cbn in H. destruct H. cbn in HH.
  revert DHH. revert dd. pattern hd, HH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros dd DHH.
  pattern dd, DHH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  now reflexivity.
Defined.

Context {ea0: rew [fun x => {u: P x &T R (x; u)}] a in (u0; r0) = (u1; r1)}
  {eb0: rew [fun x => {u: P x &T R (x; u)}] b in (u1; r1) = (u2; r2)}
  {ec0: rew [fun x => {u: P x &T R (x; u)}] c in (u2; r2) = (u3; r3)}
  {ed0: rew [fun x => {u: P x &T R (x; u)}] d in (u0; r0) = (v1; s1)}
  {ee0: rew [fun x => {u: P x &T R (x; u)}] e in (v1; s1) = (v2; s2)}
  {ef0: rew [fun x => {u: P x &T R (x; u)}] f in (v2; s2) = (u3; r3)}.

Context (EPa: ea0 = ea) (EPb: eb0 = eb) (EPc: ec0 = ec)
  (EPd: ed0 = ed) (EPe: ee0 = ee) (EPf: ef0 = ef).

Let AtomL := path_map2 (fun h k => h ⊙ k) (path_map2 (fun h k => h ⊙ k) EPa EPb) EPc.

Let AtomR := path_map2 (fun h k => h ⊙ k) EPd (path_map2 (fun h k => h ⊙ k) EPe EPf).

Definition sigT_hex_pair_factory_normalize:
  rew [EH] H in ((ea0 ⊙ eb0) ⊙ ec0) = ed0 ⊙ (ee0 ⊙ ef0) :=
  f_equal (fun h => rew [EH] H in h) AtomL • (sigT_hex_pair_factory • eq_sym AtomR).

Let EL0 := path_map2 (fun h k => h ⊙ k)
  (path_map2 (fun h k => h ⊙ k) EPa EPb • sigT_dep_path_paste_normalize R Na Nb da db) EPc.

Let ER0 := path_map2 (fun h k => h ⊙ k) EPd
  (path_map2 (fun h k => h ⊙ k) EPe EPf • sigT_dep_path_paste_normalize R Ne Nf de df).

Lemma sigT_hex_rect_pair_dep_normalize:
  sigT_hex_pair_factory_normalize =
  f_equal (fun h => rew [EH] HR in h) EL0 • (Drect • eq_sym ER0).
Proof.
  unfold sigT_hex_pair_factory_normalize, AtomL, AtomR, EL0, ER0.
  subst ea0 eb0 ec0 ed0 ee0 ef0.
  cbn [path_map2 f_equal eq_sym].
  rewrite 3 (eq_trans_refl_l _).
  now exact sigT_hex_rect_pair_dep.
Defined.

End PairHexRect.

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

Let NR := sigT_path_paste (p := H1') (h := Hu1') eq_refl (sigT_path_paste (q := H3') (k := Hu3') N2 eq_refl).

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

Let EL := sigT_hex_pair_left_normalize f1 g1 h1 f3 g3 h3
  H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3.

Let ER := sigT_hex_pair_right_normalize f1 g1 h1 f3 g3 h3 f2 g2 h2
  H1' Hu1' Hv1' H2' Hu2' Hv2' H3' Hu3' Hv3'.

Lemma sigT_hex_pair_factory_match:
  eq_existT_curried_hex_dep f1 g1 h1 f3 g3 h3 f2 g2 h2
    H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3 H1' Hu1' Hv1'
    H2' Hu2' Hv2' H3' Hu3' Hv3' HH HHu HHv =
  sigT_hex_pair_factory_normalize P' N1 eq_refl N3 eq_refl N2 eq_refl HH HHu S
    (sigT_map_eq (f := T1) (Q := S) V1 Hv1) Hv2
    (sigT_map_eq (f := T3) (Q := S) V3 Hv3) Hv1'
    (sigT_map_eq (f := T2) (Q := S) V2 Hv2') Hv3' HHv
    (sigT_dep_path_map_direct f1 g1 (fun z => R1 z.1 z.2) S V1 Hv1) eq_refl
    (sigT_dep_path_map_direct f3 g3 (fun z => R3 z.1 z.2) S V3 Hv3) eq_refl
    (sigT_dep_path_map_direct f2 g2 (fun z => R2 z.1 z.2) S V2 Hv2') eq_refl.
Proof.
  unfold eq_existT_curried_hex_dep, sigT_hex_pair_factory_normalize,
    sigT_hex_pair_factory, sigT_hex_pair_left_route, sigT_hex_pair_right_route.
  unfold sigT_hex_pair_left_normalize, sigT_hex_pair_right_normalize.
  cbn beta iota zeta.
  symmetry.
  now apply (rew_conjugate_compose
    (fun e: f1 x0 = f3 x3 => rew [fun x => {u: P' x &T R' x u}] e in
      (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)) HH).
Defined.

End PairedHexRoutes.

Lemma sigT_units_left {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {u: P x} {v: P y} (h: rew [P] p in u = v):
  rew [fun e => rew [P] e in u = v](eq_trans_refl_l p) in
    sigT_trans_eq (P := P) (p := eq_refl) eq_refl (p' := p) h =
    sigT_trans_eq (P := P) (p := p) h (p' := eq_refl) eq_refl.
Proof. now destruct h, p. Defined.

Section UnitPair.

Context {X: Type} {P: X -> Type} (R: {x: X &T P x} -> Type).

Context {x y: X} (p: x = y) {u: P x} {v: P y} (h: rew [P] p in u = v).

Let NL := sigT_path_paste (p := eq_refl) (q := p) (h := eq_refl) (k := h) (a := @eq_refl _ (x; u)) (b := (= p; h)) eq_refl eq_refl.

Let NR := sigT_path_paste (p := p) (q := eq_refl) (h := h) (k := eq_refl) (a := (= p; h)) (b := @eq_refl _ (y; v)) eq_refl eq_refl.

Definition sigT_units_normalize:
  eq_trans_refl_l (= p; h) = NL •
    (eq_existT_curried_eq (eq_trans_refl_l p) (sigT_units_left h) • eq_sym NR).
Proof. now destruct h, p. Defined.

Context {r: R (x; u)} {s: R (y; v)} (d: rew [R](= p; h) in r = s).

Let E := fun e: (x; u) = (y; v) => rew [R] e in r = s.

Definition sigT_units_higher_transport :=
  rew [fun H => rew [E] H in
    (sigT_trans_eq (P := R) (p := eq_refl) eq_refl (p' := (= p; h)) d) =
    sigT_trans_eq (P := R) (p := (= p; h)) d (p' := eq_refl) eq_refl]
    sigT_units_normalize in sigT_units_left d.

Lemma sigT_units_pair_dep_factory:
  sigT_units_left (eq_existT_curried_dep (Q := R) (H := p) (Hu := h) (Hv := d)) =
  sigT_square_dep_normalize R
    (a := p) (b := p) (p := eq_refl) (q := eq_refl)
    (ha := h) (hb := h) (hp := eq_refl) (hq := eq_refl)
    (ta := (= p; h)) (tb := (= p; h)) (tp := @eq_refl _ (x; u)) (tq := @eq_refl _ (y; v))
    (eq_trans_refl_l p) (sigT_units_left h) eq_refl eq_refl eq_refl eq_refl
    d d (@eq_refl _ r) (@eq_refl _ s) sigT_units_higher_transport.
Proof.
  unfold sigT_units_higher_transport, sigT_units_normalize.
  now destruct d, h, p.
Defined.

End UnitPair.

Section ReverseUnitPair.

Context {X: Type} {P: X -> Type} (R: {x: X &T P x} -> Type).

Context {x y: X} (p: x = y) {u: P x} {v: P y} (h: rew [P] p in u = v).

Let NL := sigT_path_paste (p := eq_refl) (q := p) (h := eq_refl) (k := h)
  (a := @eq_refl _ (x; u)) (b := (= p; h)) eq_refl eq_refl.

Let NR := sigT_path_paste (p := p) (q := eq_refl) (h := h) (k := eq_refl)
  (a := (= p; h)) (b := @eq_refl _ (y; v)) eq_refl eq_refl.

Let RN := f_equal (fun e => eq_sym e) (sigT_units_normalize p h) •
  sigT_eq_inverse_normalize (eq_trans_refl_l p) (sigT_units_left h) NL NR.

Context {r: R (x; u)} {s: R (y; v)} (d: rew [R](= p; h) in r = s).

Let E := fun e: (x; u) = (y; v) => rew [R] e in r = s.

Definition sigT_units_reverse_higher_transport :=
  rew [fun H => rew [E] H in
    sigT_trans_eq (P := R) (p := (= p; h)) d (p' := eq_refl) eq_refl =
    sigT_trans_eq (P := R) (p := eq_refl) eq_refl (p' := (= p; h)) d] RN in
    sigT_sym_eq (sigT_units_left d).

Lemma sigT_units_pair_dep_reverse_factory:
  sigT_sym_eq (sigT_units_left (eq_existT_curried_dep (Q := R) (H := p) (Hu := h) (Hv := d))) =
  sigT_square_dep_normalize R
    (a := eq_refl) (b := eq_refl) (p := p) (q := p)
    (ha := eq_refl) (hb := eq_refl) (hp := h) (hq := h)
    (ta := @eq_refl _ (x; u)) (tb := @eq_refl _ (y; v)) (tp := (= p; h)) (tq := (= p; h))
    (eq_sym (eq_trans_refl_l p)) (sigT_sym_eq (sigT_units_left h))
    eq_refl eq_refl eq_refl eq_refl (@eq_refl _ r) (@eq_refl _ s) d d
    sigT_units_reverse_higher_transport.
Proof.
  unfold sigT_units_reverse_higher_transport, RN, sigT_units_normalize.
  now destruct d, h, p.
Defined.

End ReverseUnitPair.

Lemma sigT_dep_path_map_twice {A B D: Type}
  {PA: A -> Type} {PB: B -> Type} {PD: D -> Type}
  (u: A -> B) (f: B -> D) (U: forall x, PA x -> PB (u x)) (F: forall x, PB x -> PD (f x))
  (RA: {x: A &T PA x} -> Type) (RB: {x: B &T PB x} -> Type) (RD: {x: D &T PD x} -> Type)
  (UU: forall z, RA z -> RB (u z.1; U z.1 z.2))
  (FF: forall z, RB z -> RD (f z.1; F z.1 z.2))
  {x y: A} {a: PA x} {b: PA y} {p: x = y} {hp: rew [PA] p in a = b}
  {r: RA (x; a)} {s: RA (y; b)} (dp: rew [RA](= p; hp) in r = s):
  sigT_map_eq (fun x (av: {a: PB x &T RB (x; a)}) => (F x av.1; FF (x; av.1) av.2))
    (sigT_map_eq (fun x (av: {a: PA x &T RA (x; a)}) => (U x av.1; UU (x; av.1) av.2))
      (eq_existT_curried_dep (Q := RA) (H := p) (Hu := hp) (Hv := dp))) =
  eq_existT_curried_dep (Q := RD) (H := f_equal f (f_equal u p))
    (Hu := sigT_map_eq F (sigT_map_eq U hp))
    (Hv := rew [fun e => rew [RD] e in FF (u x; U x a) (UU (x; a) r) = FF (u y; U y b) (UU (y; b) s)]
      (sigT_path_map f F (f_equal_eq_existT_curried u U p hp)) in
      sigT_map_eq FF (sigT_map_eq UU dp)).
Proof.
  now exact (f_equal
    (fun h => sigT_map_eq
      (fun x (av: {a: PB x &T RB (x; a)}) => (F x av.1; FF (x; av.1) av.2)) h)
    (sigT_dep_path_map_direct u U RA RB UU dp) •
    sigT_dep_path_map_normalize f F RB RD FF
      (f_equal_eq_existT_curried u U p hp) (sigT_map_eq UU dp)).
Defined.

Section PairNaturality.

Context {A B C D: Type} {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}.

Context (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D).

Context (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x)).

Context (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x)).

Context (RA: {x: A &T PA x} -> Type) (RB: {x: B &T PB x} -> Type).

Context (RC: {x: C &T PC x} -> Type) (RD: {x: D &T PD x} -> Type).

Context (UU: forall z, RA z -> RB (u z.1; U z.1 z.2)).

Context (VV: forall z, RA z -> RC (v z.1; V z.1 z.2)).

Context (FF: forall z, RB z -> RD (f z.1; F z.1 z.2)).

Context (GG: forall z, RC z -> RD (g z.1; G z.1 z.2)).

Context (K: forall x, f (u x) = g (v x)).

Context (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a)).

Context (DK: forall z r, rew [RD](= K z.1; HK z.1 z.2) in
  FF (u z.1; U z.1 z.2) (UU z r) = GG (v z.1; V z.1 z.2) (VV z r)).

Context {x y: A} (p: x = y) {a: PA x} {b: PA y} (hp: rew [PA] p in a = b).

Context {r: RA (x; a)} {s: RA (y; b)} (dp: rew [RA](= p; hp) in r = s).

Let tu := fun z: {x: A &T PA x} => (u z.1; U z.1 z.2).

Let tv := fun z: {x: A &T PA x} => (v z.1; V z.1 z.2).

Let tf := fun z: {x: B &T PB x} => (f z.1; F z.1 z.2).

Let tg := fun z: {x: C &T PC x} => (g z.1; G z.1 z.2).

Let tK := fun z => (= K z.1; HK z.1 z.2).

Let E := fun e: (f (u x); F (u x) (U x a)) = (g (v y); G (v y) (V y b)) =>
  rew [RD] e in FF (u x; U x a) (UU (x; a) r) = GG (v y; V y b) (VV (y; b) s).

Let Nleft := sigT_path_paste (b := (= K y; HK y b))
  (sigT_path_map f F (f_equal_eq_existT_curried u U p hp)) eq_refl.

Let Nright := sigT_path_paste (a := (= K x; HK x a)) eq_refl
  (sigT_path_map g G (f_equal_eq_existT_curried v V p hp)).

Let UP: forall x, {a: PA x &T RA (x; a)} -> {b: PB (u x) &T RB (u x; b)} := fun x (av: {a: PA x &T RA (x;
  a)}) => (U x av.1; UU (x; av.1) av.2).

Let VP: forall x, {a: PA x &T RA (x; a)} -> {b: PC (v x) &T RC (v x; b)} := fun x (av: {a: PA x &T RA (x;
  a)}) => (V x av.1; VV (x; av.1) av.2).

Let FP: forall x, {a: PB x &T RB (x; a)} -> {b: PD (f x) &T RD (f x; b)} := fun x (av: {a: PB x &T RB (x;
  a)}) => (F x av.1; FF (x; av.1) av.2).

Let GP: forall x, {a: PC x &T RC (x; a)} -> {b: PD (g x) &T RD (g x; b)} := fun x (av: {a: PC x &T RC (x;
  a)}) => (G x av.1; GG (x; av.1) av.2).

Let KP := fun x (av: {a: PA x &T RA (x; a)}) =>
  eq_existT_curried_dep (Q := RD) (H := K x) (Hu := HK x av.1) (Hv := DK (x; av.1) av.2).

Let ep := eq_existT_curried_dep (Q := RA) (H := p) (Hu := hp) (Hv := dp).

Definition sigT_square_coherence_higher_transport :=
  rew [fun h => rew [E] h in
    (sigT_map_eq FF (sigT_map_eq UU dp) ⊙ DK (y; b) s) =
    DK (x; a) r ⊙ sigT_map_eq GG (sigT_map_eq VV dp)]
    (sigT_square_coherence u v f g U V F G K HK p hp) in
    square_coherence_dep_fill tu tv tf tg UU VV FF GG tK DK (= p; hp) dp.

Let Dfactory := sigT_square_dep_normalize RD
  (square_coherence_fill u v f g K p)
  (square_coherence_dep_fill u v f g U V F G K HK p hp)
  (eq_refl: (= K x; HK x a) = (= K x; HK x a))
  (eq_refl: (= K y; HK y b) = (= K y; HK y b))
  (sigT_path_map f F (f_equal_eq_existT_curried u U p hp))
  (sigT_path_map g G (f_equal_eq_existT_curried v V p hp))
  (DK (x; a) r) (DK (y; b) s)
  (sigT_map_eq FF (sigT_map_eq UU dp)) (sigT_map_eq GG (sigT_map_eq VV dp))
  sigT_square_coherence_higher_transport.

Let AtomL := path_map2 (fun h k => h ⊙ k)
  (sigT_dep_path_map_twice u f U F RA RB RD UU FF dp)
  (eq_refl: KP y (b; s) = KP y (b; s)).

Let AtomR := path_map2 (fun h k => h ⊙ k)
  (eq_refl: KP x (a; r) = KP x (a; r))
  (sigT_dep_path_map_twice v g V G RA RC RD VV GG dp).

Lemma sigT_square_coherence_pair_dep_factory:
  square_coherence_dep_fill u v f g UP VP FP GP K KP p ep =
  f_equal (fun h => rew [fun e => rew [fun x => {a: PD x &T RD (x; a)}] e in
    (F (u x) (U x a); FF (u x; U x a) (UU (x; a) r)) =
    (G (v y) (V y b); GG (v y; V y b) (VV (y; b) s))]
    (square_coherence_fill u v f g K p) in h) AtomL • (Dfactory • eq_sym AtomR).
Proof.
  unfold AtomL, AtomR, Dfactory, sigT_square_coherence_higher_transport.
  clear AtomL AtomR Dfactory.
  destruct p, hp, dp.
  assert (N: sigT_square_coherence u v f g U V F G K HK eq_refl (@eq_refl _ a) =
    sigT_units_normalize (K x) (HK x a)).
  { unfold sigT_square_coherence, sigT_units_normalize,
      square_coherence_fill, square_coherence, sigT_path_map.
    cbn. unfold square_coherence_dep_fill, sigT_units_left.
    generalize (HK x a).
    generalize (K x), (G (v x) (V x a)).
    generalize (g (v x)).
    intros z k w hk. now destruct hk, k. }
  rewrite N.
  cbn [sigT_dep_path_map_twice path_map2 f_equal eq_sym].
  rewrite (eq_trans_refl_l _).
  now exact (sigT_units_pair_dep_factory RD (K x) (HK x a) (DK (x; a) r)).
Defined.

End PairNaturality.

Section PairNaturalityReverse.

Context {A B C D: Type} {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}.

Context (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D).

Context (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x)).

Context (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x)).

Context (RA: {x: A &T PA x} -> Type) (RB: {x: B &T PB x} -> Type).

Context (RC: {x: C &T PC x} -> Type) (RD: {x: D &T PD x} -> Type).

Context (UU: forall z, RA z -> RB (u z.1; U z.1 z.2)).

Context (VV: forall z, RA z -> RC (v z.1; V z.1 z.2)).

Context (FF: forall z, RB z -> RD (f z.1; F z.1 z.2)).

Context (GG: forall z, RC z -> RD (g z.1; G z.1 z.2)).

Context (K: forall x, f (u x) = g (v x)).

Context (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a)).

Context (DK: forall z r, rew [RD](= K z.1; HK z.1 z.2) in
  FF (u z.1; U z.1 z.2) (UU z r) = GG (v z.1; V z.1 z.2) (VV z r)).

Context {x y: A} (p: x = y) {a: PA x} {b: PA y} (hp: rew [PA] p in a = b).

Context {r: RA (x; a)} {s: RA (y; b)} (dp: rew [RA](= p; hp) in r = s).

Let tu := fun z: {x: A &T PA x} => (u z.1; U z.1 z.2).

Let tv := fun z: {x: A &T PA x} => (v z.1; V z.1 z.2).

Let tf := fun z: {x: B &T PB x} => (f z.1; F z.1 z.2).

Let tg := fun z: {x: C &T PC x} => (g z.1; G z.1 z.2).

Let tK := fun z => (= K z.1; HK z.1 z.2).

Let E := fun e: (f (u x); F (u x) (U x a)) = (g (v y); G (v y) (V y b)) =>
  rew [RD] e in FF (u x; U x a) (UU (x; a) r) = GG (v y; V y b) (VV (y; b) s).

Let Nleft := sigT_path_paste (b := (= K y; HK y b))
  (sigT_path_map f F (f_equal_eq_existT_curried u U p hp)) eq_refl.

Let Nright := sigT_path_paste (a := (= K x; HK x a)) eq_refl
  (sigT_path_map g G (f_equal_eq_existT_curried v V p hp)).

Let UP: forall x, {a: PA x &T RA (x; a)} -> {b: PB (u x) &T RB (u x; b)} := fun x (av: {a: PA x &T RA (x;
  a)}) => (U x av.1; UU (x; av.1) av.2).

Let VP: forall x, {a: PA x &T RA (x; a)} -> {b: PC (v x) &T RC (v x; b)} := fun x (av: {a: PA x &T RA (x;
  a)}) => (V x av.1; VV (x; av.1) av.2).

Let FP: forall x, {a: PB x &T RB (x; a)} -> {b: PD (f x) &T RD (f x; b)} := fun x (av: {a: PB x &T RB (x;
  a)}) => (F x av.1; FF (x; av.1) av.2).

Let GP: forall x, {a: PC x &T RC (x; a)} -> {b: PD (g x) &T RD (g x; b)} := fun x (av: {a: PC x &T RC (x;
  a)}) => (G x av.1; GG (x; av.1) av.2).

Let KP := fun x (av: {a: PA x &T RA (x; a)}) =>
  eq_existT_curried_dep (Q := RD) (H := K x) (Hu := HK x av.1) (Hv := DK (x; av.1) av.2).

Let ep := eq_existT_curried_dep (Q := RA) (H := p) (Hu := hp) (Hv := dp).

Let ReverseNorm := f_equal (fun e => eq_sym e) (sigT_square_coherence u v f g U V F G K HK p hp) •
  sigT_eq_inverse_normalize (square_coherence_fill u v f g K p)
    (square_coherence_dep_fill u v f g U V F G K HK p hp) Nleft Nright.

Definition sigT_square_coherence_reverse_higher_transport :=
  rew [fun h => rew [E] h in
    (DK (x; a) r ⊙ sigT_map_eq GG (sigT_map_eq VV dp)) =
    sigT_map_eq FF (sigT_map_eq UU dp) ⊙ DK (y; b) s] ReverseNorm in
    square_coherence_dep_reverse_fill tu tv tf tg UU VV FF GG tK DK (= p; hp) dp.

Let Dfactory := sigT_square_dep_normalize RD
  (eq_sym (square_coherence_fill u v f g K p))
  (sigT_sym_eq (square_coherence_dep_fill u v f g U V F G K HK p hp))
  (sigT_path_map f F (f_equal_eq_existT_curried u U p hp))
  (sigT_path_map g G (f_equal_eq_existT_curried v V p hp))
  (eq_refl: (= K x; HK x a) = (= K x; HK x a))
  (eq_refl: (= K y; HK y b) = (= K y; HK y b))
  (sigT_map_eq FF (sigT_map_eq UU dp)) (sigT_map_eq GG (sigT_map_eq VV dp))
  (DK (x; a) r) (DK (y; b) s) sigT_square_coherence_reverse_higher_transport.

Let AtomL := path_map2 (fun h k => h ⊙ k)
  (sigT_dep_path_map_twice u f U F RA RB RD UU FF dp)
  (eq_refl: KP y (b; s) = KP y (b; s)).

Let AtomR := path_map2 (fun h k => h ⊙ k)
  (eq_refl: KP x (a; r) = KP x (a; r))
  (sigT_dep_path_map_twice v g V G RA RC RD VV GG dp).

Lemma sigT_square_coherence_reverse_pair_dep_factory:
  square_coherence_dep_reverse_fill u v f g UP VP FP GP K KP p ep =
  f_equal (fun h => rew [fun e => rew [fun x => {a: PD x &T RD (x; a)}] e in
    (F (u x) (U x a); FF (u x; U x a) (UU (x; a) r)) =
    (G (v y) (V y b); GG (v y; V y b) (VV (y; b) s))]
    (eq_sym (square_coherence_fill u v f g K p)) in h) AtomR • (Dfactory • eq_sym AtomL).
Proof.
  unfold AtomL, AtomR, Dfactory, sigT_square_coherence_reverse_higher_transport, ReverseNorm.
  clear AtomL AtomR Dfactory ReverseNorm.
  destruct p, hp, dp.
  assert (N: sigT_square_coherence u v f g U V F G K HK eq_refl (@eq_refl _ a) =
    sigT_units_normalize (K x) (HK x a)).
  { unfold sigT_square_coherence, sigT_units_normalize,
      square_coherence_fill, square_coherence, sigT_path_map.
    cbn. unfold square_coherence_dep_fill, sigT_units_left.
    generalize (HK x a).
    generalize (K x), (G (v x) (V x a)).
    generalize (g (v x)).
    intros z k w hk. now destruct hk, k. }
  rewrite N.
  cbn [sigT_dep_path_map_twice path_map2 f_equal eq_sym].
  rewrite (eq_trans_refl_l _).
  now exact (sigT_units_pair_dep_reverse_factory RD (K x) (HK x a) (DK (x; a) r)).
Defined.

End PairNaturalityReverse.

Section PairStack.

Context {X: Type} (P: X -> Type) {x0 x1 y0 y1 z0 z1: X}
  {a: x0 = x1} {c: y0 = y1} {d: z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  (H: p • c = a • q) (K: r • d = c • s)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1} {w0: P z0} {w1: P z1}
  (ha: rew [P] a in u0 = u1) (hc: rew [P] c in v0 = v1)
  (hd: rew [P] d in w0 = w1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in v0 = w0) (hs: rew [P] s in v1 = w1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in v0 = w1] K in (hr ⊙ hd) = hc ⊙ hs)
  {ta: (x0; u0) = (x1; u1)} {tc: (y0; v0) = (y1; v1)}
  {td: (z0; w0) = (z1; w1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  {tr: (y0; v0) = (z0; w0)} {ts: (y1; v1) = (z1; w1)}
  (Na: ta = (= a; ha)) (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  (Nr: tr = (= r; hr)) (Ns: ts = (= s; hs)).

Context (R: {x: X &T P x} -> Type).

Context {r0: R (x0; u0)} {r1: R (x1; u1)} {s0: R (y0; v0)} {s1: R (y1; v1)} {t0: R (z0; w0)} {t1: R (z1; w1)}.

Context (da: rew [R] ta in r0 = r1) (dc: rew [R] tc in s0 = s1) (dd: rew [R] td in t0 = t1)
  (dp: rew [R] tp in r0 = s0) (dq: rew [R] tq in r1 = s1)
  (dr: rew [R] tr in s0 = t0) (ds: rew [R] ts in s1 = t1).

Let Ht := sigT_path_paste Np Nc • (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)).

Let Kt := sigT_path_paste Nr Nd • (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nc Ns)).

Context (DHH: rew [fun e => rew [R] e in r0 = s1] Ht in (dp ⊙ dc) = da ⊙ dq)
  (DKK: rew [fun e => rew [R] e in s0 = t1] Kt in (dr ⊙ dd) = dc ⊙ ds).

Let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da).

Let ec := eq_existT_curried_dep (Q := R) (H := c) (Hu := hc) (Hv := rew [fun e => rew [R] e in s0 = s1] Nc in dc).

Let ed := eq_existT_curried_dep (Q := R) (H := d) (Hu := hd) (Hv := rew [fun e => rew [R] e in t0 = t1] Nd in dd).

Let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r0 = s0] Np in dp).

Let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in r1 = s1] Nq in dq).

Let er := eq_existT_curried_dep (Q := R) (H := r) (Hu := hr) (Hv := rew [fun e => rew [R] e in s0 = t0] Nr in dr).

Let es := eq_existT_curried_dep (Q := R) (H := s) (Hu := hs) (Hv := rew [fun e => rew [R] e in s1 = t1] Ns in ds).

Let DHp := sigT_square_dep_normalize R H HH Na Nc Np Nq da dc dp dq DHH.

Let DKp := sigT_square_dep_normalize R K KK Nc Nd Nr Ns dc dd dr ds DKK.

Let HS := square_stack H K.

Let HS1 := square_stack_dep P H K ha hc hd hp hq hr hs HH KK.

Let Route := fun e: (x0; u0) = (z1; w1) => rew [R] e in r0 = t1.

Definition sigT_square_stack_normalized_higher :=
  rew [fun h => rew [Route] h in ((dp ⊙ dr) ⊙ dd) = da ⊙ (dq ⊙ ds)]
    (sigT_square_stack_normalize P H K ha hc hd hp hq hr hs HH KK Na Nc Nd Np Nq Nr Ns) in
    square_stack_dep R Ht Kt da dc dd dp dq dr ds DHH DKK.

Let Dstack := sigT_square_dep_normalize R HS HS1 Na Nd (sigT_path_paste Np Nr) (sigT_path_paste Nq Ns)
  da dd (dp ⊙ dr) (dq ⊙ ds) sigT_square_stack_normalized_higher.

Let El := path_map2 (fun h k => h ⊙ k) (sigT_dep_path_paste_normalize R Np Nr dp dr) (eq_refl: ed = ed).

Let Er := path_map2 (fun h k => h ⊙ k) (eq_refl: ea = ea) (sigT_dep_path_paste_normalize R Nq Ns dq ds).

Lemma sigT_square_stack_pair_dep:
  square_stack_dep (fun x => {u: P x &T R (x; u)}) H K ea ec ed ep eq er es DHp DKp =
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (w1; t1)] HS in h) El •
    (Dstack • eq_sym Er).
Proof.
  cbv beta iota zeta delta[ea ec ed ep eq er es DHp DKp HS HS1 El Er Dstack
    sigT_square_stack_normalized_higher Route Ht Kt] in *.
  clear ea ec ed ep eq er es DHp DKp HS HS1 El Er Dstack Route Ht Kt.
  subst ta tc td tp tq tr ts.
  destruct p, r, d, s, q. cbn in hp, hr, hd, hs, hq. destruct hp, hr, hd, hs, hq.
  cbn in dp, dr, dd, ds, dq. destruct dp, dr, dd, ds, dq.
  cbn in K. destruct K. cbn in KK.
  revert DHH. revert HH. revert DKK. revert dc. pattern hc, KK.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros dc DKK HH DHH.
  revert DHH. pattern dc, DKK.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  cbn. intros DHH.
  cbn in H. destruct H. cbn in HH.
  revert DHH. revert da. pattern ha, HH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros da DHH.
  pattern da, DHH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  now reflexivity.
Defined.

Context (aa: rew [fun x => {u: P x &T R (x; u)}] a in (u0; r0) = (u1; r1))
  (cc: rew [fun x => {u: P x &T R (x; u)}] c in (v0; s0) = (v1; s1))
  (ddp: rew [fun x => {u: P x &T R (x; u)}] d in (w0; t0) = (w1; t1))
  (pp: rew [fun x => {u: P x &T R (x; u)}] p in (u0; r0) = (v0; s0))
  (qq: rew [fun x => {u: P x &T R (x; u)}] q in (u1; r1) = (v1; s1))
  (rr: rew [fun x => {u: P x &T R (x; u)}] r in (v0; s0) = (w0; t0))
  (ss: rew [fun x => {u: P x &T R (x; u)}] s in (v1; s1) = (w1; t1)).

Context (Ea: aa = ea) (Ec: cc = ec) (Ed: ddp = ed) (Ep: pp = ep) (Eq: qq = eq) (Erp: rr = er) (Es: ss = es).

Let RawH := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (v1; s1)] H in h)
  (path_map2 (fun h k => h ⊙ k) Ep Ec) • (DHp • eq_sym (path_map2 (fun h k => h ⊙ k) Ea Eq)).

Let RawK := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (v0; s0) = (w1; t1)] K in h)
  (path_map2 (fun h k => h ⊙ k) Erp Ed) • (DKp • eq_sym (path_map2 (fun h k => h ⊙ k) Ec Es)).

Let RawEl := path_map2 (fun h k => h ⊙ k)
  (path_map2 (fun h k => h ⊙ k) Ep Erp • sigT_dep_path_paste_normalize R Np Nr dp dr) Ed.

Let RawEr := path_map2 (fun h k => h ⊙ k) Ea
  (path_map2 (fun h k => h ⊙ k) Eq Es • sigT_dep_path_paste_normalize R Nq Ns dq ds).

Lemma sigT_square_stack_pair_dep_paint_normalized:
  square_stack_dep (fun x => {u: P x &T R (x; u)}) H K aa cc ddp pp qq rr ss RawH RawK =
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (w1; t1)] HS in h) RawEl •
    (Dstack • eq_sym RawEr).
Proof.
  unfold RawH, RawK, RawEl, RawEr.
  subst aa cc ddp pp qq rr ss.
  cbn[path_map2 f_equal eq_sym].
  rewrite 4 eq_trans_refl_l, 2 eq_trans_refl_r.
  now apply sigT_square_stack_pair_dep.
Defined.

End PairStack.

Section PairSquareMapCapData.

Context {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  {tb: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)).

Context (R: {x: X &T P x} -> Type) (S: {y: Y &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2)).

Context {r0: R (x0; u0)} {r1: R (x1; u1)} {s0: R (y0; v0)} {s1: R (y1; v1)}
  (da: rew [R](= a; ha) in r0 = r1) (db: rew [R] tb in s0 = s1)
  (dp: rew [R] tp in r0 = s0) (dq: rew [R] tq in r1 = s1).

Let Ht := sigT_path_paste Np Nb •
  (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste (eq_refl: (= a; ha) = (= a; ha)) Nq)).

Context (DHH: rew [fun e => rew [R] e in r0 = s1] Ht in (dp ⊙ db) = da ⊙ dq).

Let tf := fun z: {x: X &T P x} => (f z.1; F z.1 z.2).

Let pf := fun x (uv: {a: P x &T R (x; a)}) => (F x uv.1; V (x; uv.1) uv.2): {a: Q (f x)&T S (f x; a)}.

Let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 =
  r1](eq_refl: (= a; ha) = (= a; ha)) in da).

Let eb := eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in s0 = s1] Nb in db).

Let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r0 = s0] Np in dp).

Let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in r1 = s1] Nq in dq).

Let DHp := sigT_square_dep_normalize R H HH (eq_refl: (= a; ha) = (= a; ha)) Nb Np Nq da db dp dq DHH.

Let HM := square_map f H.

Let HM1 := square_map_dep f F H ha hb hp hq HH.

Let Rmapped := fun e: tf (x0; u0) = tf (y1; v1) => rew [S] e in V (x0; u0) r0 = V (y1; v1) s1.

Definition sigT_square_map_cap_normalized_higher :=
  rew [fun c => rew [Rmapped] c in
    (sigT_map_eq V dp ⊙ sigT_map_eq V db) = sigT_map_eq V da ⊙ sigT_map_eq V dq]
    (sigT_square_map_cap_normalize f F H ha hb hp hq HH Nb Np Nq) in
    (square_map_dep tf V Ht da db dp dq DHH).

Let Dmapped := sigT_square_dep_normalize S HM HM1
  (f_equal_eq_existT_curried f F a ha) (sigT_path_map f F Nb)
  (sigT_path_map f F Np) (sigT_path_map f F Nq)
  (sigT_map_eq V da) (sigT_map_eq V db) (sigT_map_eq V dp) (sigT_map_eq V dq)
  sigT_square_map_cap_normalized_higher.

Let El := path_map2 (fun h k => h ⊙ k)
  (sigT_dep_path_map_normalize f F R S V Np dp)
  (sigT_dep_path_map_normalize f F R S V Nb db).

Let Er := path_map2 (fun h k => h ⊙ k)
  (sigT_dep_path_map_direct f F R S V da)
  (sigT_dep_path_map_normalize f F R S V Nq dq).

Lemma sigT_square_map_pair_dep_cap:
  square_map_dep f pf H ea eb ep eq DHp =
  f_equal (fun h => rew [fun e => rew [fun y => {a: Q y &T S (y; a)}] e in
    (F x0 u0; V (x0; u0) r0) = (F y1 v1; V (y1; v1) s1)] HM in h) El •
    (Dmapped • eq_sym Er).
Proof.
  cbv beta iota zeta delta [ea eb ep eq DHp HM HM1 El Er Dmapped
    sigT_square_map_cap_normalized_higher Rmapped Ht pf tf] in *.
  clear ea eb ep eq DHp HM HM1 El Er Dmapped Rmapped Ht pf tf.
  subst tb tp tq.
  destruct p, b, q. cbn in hp, hb, hq.
  destruct hp, hb, hq.
  cbn in H. destruct H. cbn in HH.
  revert da DHH.
  pattern ha, HH.
  apply (homotopy_path_ind_r
    (fun h: u1 = u1 => sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros da DHH.
  cbn in dp, db, dq. destruct dp, db, dq.
  cbn in DHH.
  pattern da, DHH.
  apply (homotopy_path_ind_r
    (fun h: r1 = r1 => sigT_trans_eq (P := R) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  now reflexivity.
Defined.

Context
  (bb: rew [fun x => {u: P x &T R (x; u)}] b in (v0; s0) = (v1; s1))
  (pp: rew [fun x => {u: P x &T R (x; u)}] p in (u0; r0) = (v0; s0))
  (qq: rew [fun x => {u: P x &T R (x; u)}] q in (u1; r1) = (v1; s1)).

Context (Eb: bb = eb) (Ep: pp = ep) (Eq: qq = eq).

Let RawH := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (v1; s1)] H in h)
  (path_map2 (fun h k => h ⊙ k) Ep Eb) • (DHp • eq_sym (path_map2 (fun h k => h ⊙ k) (eq_refl: ea = ea) Eq)).

Let RawEl := path_map2 (fun h k => h ⊙ k)
  (f_equal (fun h => sigT_map_eq pf h) Ep • sigT_dep_path_map_normalize f F R S V Np dp)
  (f_equal (fun h => sigT_map_eq pf h) Eb • sigT_dep_path_map_normalize f F R S V Nb db).

Let RawEr := path_map2 (fun h k => h ⊙ k)
  (sigT_dep_path_map_direct f F R S V da)
  (f_equal (fun h => sigT_map_eq pf h) Eq • sigT_dep_path_map_normalize f F R S V Nq dq).

Lemma sigT_square_map_pair_dep_cap_paint_normalized:
  square_map_dep f pf H ea bb pp qq RawH =
  f_equal (fun h => rew [fun e => rew [fun y => {u: Q y &T S (y; u)}] e in
    (F x0 u0; V (x0; u0) r0) = (F y1 v1; V (y1; v1) s1)] HM in h) RawEl •
    (Dmapped • eq_sym RawEr).
Proof.
  unfold RawH, RawEl, RawEr.
  subst bb pp qq.
  cbn[path_map2 f_equal eq_sym].
  rewrite 4 eq_trans_refl_l, eq_trans_refl_r.
  now apply sigT_square_map_pair_dep_cap.
Defined.

End PairSquareMapCapData.

Lemma sigT_square_map_dep_normalize {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type)
  (R: {x: X &T P x} -> Type) (S: {y: Y &T Q y} -> Type)
  (F: forall y, Q y -> P (f y))
  (V: forall z, S z -> R (f z.1; F z.1 z.2))
  {x0 x1: X} {y0 y1: Y}
  {a: x0 = x1} {c: y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f c = a • q)
  {u0: P x0} {u1: P x1} {v0: Q y0} {v1: Q y1}
  {ha: rew [P] a in u0 = u1} {hc: rew [Q] c in v0 = v1}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  (HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq)
  {ta: (x0; u0) = (x1; u1)} {tc: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (f y0; F y0 v0)} {tq: (x1; u1) = (f y1; F y1 v1)}
  (Na: ta = (= a; ha)) (Nc: tc = (= c; hc)) (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  {r0: R (x0; u0)} {r1: R (x1; u1)} {s0: S (y0; v0)} {s1: S (y1; v1)}
  (da: rew [R] ta in r0 = r1) (dc: rew [S] tc in s0 = s1)
  (dp: rew [R] tp in r0 = V (y0; v0) s0)
  (dq: rew [R] tq in r1 = V (y1; v1) s1)
  (DHH: rew [fun e => rew [R] e in r0 = V (y1; v1) s1]
    (sigT_path_paste Np (sigT_path_map f F Nc) •
     (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq))) in
    (dp ⊙ sigT_map_eq V dc) = da ⊙ dq):
  rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u0; r0) = (F y1 v1; V (y1; v1) s1)] H in
    (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in _ = _] Np in dp) ⊙
      sigT_map_eq (fun y (uv: {u: Q y &T S (y; u)}) =>
        (F y uv.1; V (y; uv.1) uv.2))
      (eq_existT_curried_dep (Q := S) (H := c) (Hu := hc) (Hv := rew [fun e => rew [S] e in _ = _] Nc in dc))) =
    eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in _ = _] Na in da) ⊙
    eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in _ = _] Nq in dq).
Proof.
  now exact (let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp)
    (Hv := rew [fun e => rew [R] e in r0 = V (y0; v0) s0] Np in dp) in
  let EL := f_equal (fun h => ep ⊙ h)
      (sigT_dep_path_map_normalize f F S R V Nc dc) •
    sigT_dep_path_paste_normalize R Np (sigT_path_map f F Nc) dp (sigT_map_eq V dc) in
  let ER := sigT_dep_path_paste_normalize R Na Nq da dq in
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u0; r0) = (F y1 v1; V (y1; v1) s1)] H in h) EL •
    (sigT_eq_dep_normalize R H HH
      (sigT_path_paste Np (sigT_path_map f F Nc)) (sigT_path_paste Na Nq)
      (dp ⊙ sigT_map_eq V dc) (da ⊙ dq) DHH • eq_sym ER)).
Defined.

Lemma sigT_square_map_dep_paint_computation {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type)
  (R: {x: X &T P x} -> Type) (S: {y: Y &T Q y} -> Type)
  (F: forall y, Q y -> P (f y))
  (V: forall z, S z -> R (f z.1; F z.1 z.2))
  {x0 x1: X} {y0 y1: Y}
  {a: x0 = x1} {c: y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f c = a • q)
  {u0: P x0} {u1: P x1} {v0: Q y0} {v1: Q y1}
  {ha: rew [P] a in u0 = u1} {hc: rew [Q] c in v0 = v1}
  {hp: rew [P] p in u0 = F y0 v0} {hq: rew [P] q in u1 = F y1 v1}
  (HH: rew [fun e => rew [P] e in u0 = F y1 v1] H in
    (hp ⊙ sigT_map_eq F hc) = ha ⊙ hq)
  {ta: (x0; u0) = (x1; u1)} {tc: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (f y0; F y0 v0)} {tq: (x1; u1) = (f y1; F y1 v1)}
  (Na: ta = (= a; ha)) (Nc: tc = (= c; hc)) (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  {r0: R (x0; u0)} {r1: R (x1; u1)} {s0: S (y0; v0)} {s1: S (y1; v1)}
  (da: rew [R] ta in r0 = r1) (dc: rew [S] tc in s0 = s1)
  (dp: rew [R] tp in r0 = V (y0; v0) s0)
  (dq: rew [R] tq in r1 = V (y1; v1) s1)
  (DHH: rew [fun e => rew [R] e in r0 = V (y1; v1) s1]
    (sigT_path_paste Np (sigT_path_map f F Nc) •
     (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq))) in
    (dp ⊙ sigT_map_eq V dc) = da ⊙ dq):
  let PPX := fun x => {u: P x &T R (x; u)} in
  let PPY := fun y => {u: Q y &T S (y; u)} in
  let PF := fun y (uv: PPY y) => (F y uv.1; V (y; uv.1) uv.2): PPX (f y) in
  let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha)
    (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da) in
  let ec := eq_existT_curried_dep (Q := S) (H := c) (Hu := hc)
    (Hv := rew [fun e => rew [S] e in s0 = s1] Nc in dc) in
  let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp)
    (Hv := rew [fun e => rew [R] e in r0 = V (y0; v0) s0] Np in dp) in
  let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq)
    (Hv := rew [fun e => rew [R] e in r1 = V (y1; v1) s1] Nq in dq) in
  forall (aa: rew [PPX] a in (u0; r0) = (u1; r1))
    (cc: rew [PPY] c in (v0; s0) = (v1; s1))
    (pp: rew [PPX] p in (u0; r0) = PF y0 (v0; s0))
    (qq: rew [PPX] q in (u1; r1) = PF y1 (v1; s1))
    (Ea: aa = ea) (Ec: cc = ec) (Ep: pp = ep) (Eq: qq = eq),
  let Move := fun h => rew [fun e => rew [PPX] e in
    (u0; r0) = PF y1 (v1; s1)] H in h in
  let RawH := f_equal Move
    (path_map2 (fun (h: rew [PPX] p in (u0; r0) = PF y0 (v0; s0))
      (k: rew [PPY] c in (v0; s0) = (v1; s1)) =>
        h ⊙ sigT_map_eq PF k) Ep Ec) •
    (sigT_square_map_dep_normalize f P Q R S F V H HH Na Nc Np Nq da dc dp dq DHH •
      eq_sym (path_map2 (fun h k => h ⊙ k) Ea Eq)) in
  let EL := sigT_pair_path_paste R Np (sigT_path_map f F Nc)
    dp (sigT_map_eq V dc) Ep (sigT_pair_path_map f F S R V Nc dc Ec) in
  let ER := sigT_pair_path_paste R Na Nq da dq Ea Eq in
  RawH = f_equal Move EL •
    (sigT_eq_dep_normalize R H HH
      (sigT_path_paste Np (sigT_path_map f F Nc)) (sigT_path_paste Na Nq)
      (dp ⊙ sigT_map_eq V dc) (da ⊙ dq) DHH • eq_sym ER).
Proof.
  cbn zeta. intros aa cc pp qq Ea Ec Ep Eq.
  subst aa cc pp qq.
  cbn [path_map2 f_equal eq_sym sigT_pair_path_paste sigT_pair_path_map].
  unfold sigT_pair_path_paste, sigT_pair_path_map.
  cbn [path_map2 f_equal eq_sym].
  rewrite 3 eq_trans_refl_l, eq_trans_refl_r.
  unfold path_map2.
  cbn [f_equal].
  rewrite eq_trans_refl_l.
  now reflexivity.
Defined.

(** Transport dependent pastings when their chosen faces change. *)

Lemma square_stack_dep_transport {X: Type} (P: X -> Type)
  {x0 x1 y0 y1 z0 z1: X} {a: x0 = x1} {c: y0 = y1} {d: z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  {H H': p • c = a • q} {K K': r • d = c • s} (NH: H = H') (NK: K = K')
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1} {w0: P z0} {w1: P z1}
  (ha: rew [P] a in u0 = u1) (hc: rew [P] c in v0 = v1) (hd: rew [P] d in w0 = w1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in v0 = w0) (hs: rew [P] s in v1 = w1)
  (DH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (DK: rew [fun e => rew [P] e in v0 = w1] K in (hr ⊙ hd) = hc ⊙ hs):
  rew [fun h => rew [fun e => rew [P] e in u0 = w1] h in ((hp ⊙ hr) ⊙ hd) = ha ⊙ (hq ⊙ hs)]
    path_map2 (fun h k => square_stack h k) NH NK in
    square_stack_dep P H K ha hc hd hp hq hr hs DH DK =
  square_stack_dep P H' K' ha hc hd hp hq hr hs
    (rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp ⊙ hc) = ha ⊙ hq] NH in DH)
    (rew [fun k => rew [fun e => rew [P] e in v0 = w1] k in (hr ⊙ hd) = hc ⊙ hs] NK in DK).
Proof. now destruct NH, NK. Defined.

Lemma square_map_dep_transport {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  {H K: p • b = a • q} (N: H = K)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (DH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq):
  rew [fun h => rew [fun e => rew [Q] e in F x0 u0 = F y1 v1] h in
    (sigT_map_eq F hp ⊙ sigT_map_eq F hb) = sigT_map_eq F ha ⊙ sigT_map_eq F hq]
    f_equal (fun h => square_map f h) N in (square_map_dep f F H ha hb hp hq DH) =
  square_map_dep f F K ha hb hp hq
    (rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp ⊙ hb) = ha ⊙ hq] N in DH).
Proof. now destruct N. Defined.

Lemma square_change_sides_dep_transport {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (H: p • b = a • q) (Hq: q' = q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hp': rew [P] p' in u0 = v0)
  (hq: rew [P] q in u1 = v1) (hq': rew [P] q' in u1 = v1)
  (HHp: rew [fun e => rew [P] e in u0 = v0] Hp in hp' = hp)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (HHq: rew [fun e => rew [P] e in u1 = v1] Hq in hq' = hq)
  (HPnew: p' = p) (Hnew: p • b = a • q) (HQnew: q' = q)
  (EP: Hp = HPnew) (EH: H = Hnew) (EQ: Hq = HQnew):
  rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp' ⊙ hb) = ha ⊙ hq']
    (path_map3 (fun l m r => square_change_sides l m r) EP EH EQ) in
    square_change_sides_dep P Hp H Hq ha hb hp hp' hq hq' HHp HH HHq =
  square_change_sides_dep P HPnew Hnew HQnew ha hb hp hp' hq hq'
    (rew [fun h => rew [fun e => rew [P] e in u0 = v0] h in hp' = hp] EP in HHp)
    (rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp ⊙ hb) = ha ⊙ hq] EH in HH)
    (rew [fun h => rew [fun e => rew [P] e in u1 = v1] h in hq' = hq] EQ in HHq).
Proof. now destruct EP, EH, EQ. Defined.

Section PairMapData.

Context
  {T M N X Y U: Type} {PT: T -> Type} {PM: M -> Type} {PN: N -> Type}
  {P: X -> Type} {Q: Y -> Type} {PU: U -> Type}
  (r: T -> X) (s: M -> X) (t: N -> X) (f: X -> Y) (g: T -> U) (j: U -> Y)
  (R: forall d, PT d -> P (r d))
  (S: forall m, PM m -> P (s m)) (T': forall n, PN n -> P (t n))
  (F: forall x, P x -> Q (f x))
  (G: forall d, PT d -> PU (g d)) (J: forall u, PU u -> Q (j u))
  (α: forall d, f (r d) = j (g d))
  (Hα: forall d a, rew [Q] α d in F (r d) (R d a) = J (g d) (G d a))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: hexagonal_coherence s r t p e q v k w)
  {ad: PT d} {ad': PT d'} {am: PM m} {am': PM m'} {an: PN n} {an': PN n'}
  (he: rew [PT] e in ad = ad') (hp: rew [PM] p in am = am')
  (hq: rew [PN] q in an = an')
  (hv: rew [P] v in S m' am' = R d ad)
  (hw: rew [P] w in T' n' an' = R d' ad')
  (hk: rew [P] k in S m am = T' n an)
  (HH: hexagonal_coherence_dep S R T' H hp he hq hv hk hw).

Let tr := fun z: {x: T &T PT x} => (r z.1; R z.1 z.2).

Let ts := fun z: {x: M &T PM x} => (s z.1; S z.1 z.2).

Let tt := fun z: {x: N &T PN x} => (t z.1; T' z.1 z.2).

Let tf := fun z: {x: X &T P x} => (f z.1; F z.1 z.2).

Let tg := fun z: {x: T &T PT x} => (g z.1; G z.1 z.2).

Let tj := fun z: {x: U &T PU x} => (j z.1; J z.1 z.2).

Let tα := fun z: {x: T &T PT x} => (= α z.1; Hα z.1 z.2).

Context (ST: {x: T &T PT x} -> Type) (SM: {x: M &T PM x} -> Type)
  (SN: {x: N &T PN x} -> Type) (SX: {x: X &T P x} -> Type)
  (SY: {x: Y &T Q x} -> Type) (SU: {x: U &T PU x} -> Type).

Context (dR: forall z, ST z -> SX (tr z)) (dS: forall z, SM z -> SX (ts z))
  (dT: forall z, SN z -> SX (tt z)) (dF: forall z, SX z -> SY (tf z))
  (dG: forall z, ST z -> SU (tg z)) (dJ: forall z, SU z -> SY (tj z)).

Context (dHα: forall z a, rew [SY] tα z in dF (tr z) (dR z a) = dJ (tg z) (dG z a)).

Context {dad: ST (d; ad)} {dad': ST (d'; ad')}
  {dam: SM (m; am)} {dam': SM (m'; am')} {dan: SN (n; an)} {dan': SN (n'; an')}.

Context (dhe: rew [ST](= e; he) in dad = dad')
  (dhp: rew [SM](= p; hp) in dam = dam') (dhq: rew [SN](= q; hq) in dan = dan')
  (dhv: rew [SX](= v; hv) in dS (m'; am') dam' = dR (d; ad) dad)
  (dhw: rew [SX](= w; hw) in dT (n'; an') dan' = dR (d'; ad') dad')
  (dhk: rew [SX](= k; hk) in dS (m; am) dam = dT (n; an) dan).

Let tH := eq_existT_curried_hex s S t T' r R H HH.

Context (dHH: hexagonal_coherence_dep dS dR dT tH dhp dhe dhq dhv dhk dhw).

Let pR := fun z (uv: {a: PT z &T ST (z; a)}) => (R z uv.1; dR (z; uv.1) uv.2): {a: P (r z)&T SX (r z; a)}.

Let pS := fun z (uv: {a: PM z &T SM (z; a)}) => (S z uv.1; dS (z; uv.1) uv.2): {a: P (s z)&T SX (s z; a)}.

Let pT := fun z (uv: {a: PN z &T SN (z; a)}) => (T' z uv.1; dT (z; uv.1) uv.2): {a: P (t z)&T SX (t z; a)}.

Let pf := fun z (uv: {a: P z &T SX (z; a)}) => (F z uv.1; dF (z; uv.1) uv.2): {a: Q (f z)&T SY (f z; a)}.

Let pg := fun z (uv: {a: PT z &T ST (z; a)}) => (G z uv.1; dG (z; uv.1) uv.2): {a: PU (g z)&T SU (g z; a)}.

Let pj := fun z (uv: {a: PU z &T SU (z; a)}) => (J z uv.1; dJ (z; uv.1) uv.2): {a: Q (j z)&T SY (j z; a)}.

Let phα := fun z (uv: {a: PT z &T ST (z; a)}) => eq_existT_curried_dep (Q := SY)
  (H := α z) (Hu := Hα z uv.1) (Hv := dHα (z; uv.1) uv.2).

Let ee := eq_existT_curried_dep (Q := ST) (H := e) (Hu := he) (Hv := dhe).

Let ep := eq_existT_curried_dep (Q := SM) (H := p) (Hu := hp) (Hv := dhp).

Let eq := eq_existT_curried_dep (Q := SN) (H := q) (Hu := hq) (Hv := dhq).

Let ev := eq_existT_curried_dep (Q := SX) (H := v) (Hu := hv) (Hv := dhv).

Let ew := eq_existT_curried_dep (Q := SX) (H := w) (Hu := hw) (Hv := dhw).

Let ek := eq_existT_curried_dep (Q := SX) (H := k) (Hu := hk) (Hv := dhk).

Let Nl := sigT_path_paste
  (sigT_path_paste (sigT_path_map f F
    (sigT_path_paste (f_equal_eq_existT_curried s S p hp) (eq_refl: (= v; hv) = (= v; hv))))
    (eq_refl: (= α d; Hα d ad) = (= α d; Hα d ad)))
  (sigT_path_map j J (f_equal_eq_existT_curried g G e he)).

Let Nr := sigT_path_paste (f_equal_eq_existT_curried f F k hk)
  (sigT_path_paste (sigT_path_map f F
    (sigT_path_paste (f_equal_eq_existT_curried t T' q hq) (eq_refl: (= w; hw) = (= w; hw))))
    (eq_refl: (= α d'; Hα d' ad') = (= α d'; Hα d' ad'))).

Let dl := (sigT_map_eq dF (sigT_map_eq dS dhp ⊙ dhv) ⊙ dHα (d; ad) dad) ⊙
  sigT_map_eq dJ (sigT_map_eq dG dhe).

Let dr := sigT_map_eq dF dhk ⊙
  (sigT_map_eq dF (sigT_map_eq dT dhq ⊙ dhw) ⊙ dHα (d'; ad') dad').

Let Route := fun e: (f (s m); F (s m) (S m am)) = (j (g d'); J (g d') (G d' ad')) =>
  rew [SY] e in dF (ts (m; am)) (dS (m; am) dam) = dJ (tg (d'; ad')) (dG (d'; ad') dad').

Lemma paired_map_left:
  (sigT_map_eq pf (sigT_map_eq pS ep ⊙ ev) ⊙ phα d (ad; dad)) ⊙
    sigT_map_eq pj (sigT_map_eq pg ee) =
  eq_existT_curried_dep (Q := SY)
    (H := (f_equal f (f_equal s p • v) • α d) • f_equal j (f_equal g e))
    (Hu := (sigT_map_eq F (sigT_map_eq S hp ⊙ hv) ⊙ Hα d ad) ⊙
      sigT_map_eq J (sigT_map_eq G he)) (Hv := rew [Route] Nl in dl).
Proof.
  pose (ES := sigT_dep_path_map_direct s S SM SX dS dhp).
  eassert (ESV: sigT_map_eq pS ep ⊙ ev = _).
  { refine (path_map2 (fun h k => h ⊙ k) ES eq_refl • _).
    now exact (sigT_dep_path_paste_normalize SX
      (f_equal_eq_existT_curried s S p hp) eq_refl (sigT_map_eq dS dhp) dhv). }
  eassert (EFSV: sigT_map_eq (f := f) (P := fun x => {u: P x &T SX (x; u)}) (Q := fun y => {u: Q y &T SY (y;
    u)}) pf (sigT_map_eq pS ep ⊙ ev) = _).
  { refine (f_equal (fun h => sigT_map_eq (f := f) (P := fun x => {u: P x &T SX (x; u)}) (Q := fun y => {u:
    Q y &T SY (y; u)}) pf h) ESV • _).
    now exact (sigT_dep_path_map_normalize f F SX SY dF
      (sigT_path_paste (f_equal_eq_existT_curried s S p hp) eq_refl)
      (sigT_map_eq dS dhp ⊙ dhv)). }
  eassert (EPrefix: sigT_map_eq (f := f) (P := fun x => {u: P x &T SX (x; u)}) (Q := fun y => {u: Q y &T SY
    (y; u)}) pf (sigT_map_eq pS ep ⊙ ev) ⊙ phα d (ad; dad) = _).
  { refine (path_map2 (fun h k => h ⊙ k) EFSV eq_refl • _).
    now exact (sigT_dep_path_paste_normalize SY
      (sigT_path_map f F (sigT_path_paste (f_equal_eq_existT_curried s S p hp) eq_refl))
      eq_refl (sigT_map_eq dF (sigT_map_eq dS dhp ⊙ dhv)) (dHα (d; ad) dad)). }
  refine (path_map2 (fun h k => h ⊙ k) EPrefix
    (sigT_dep_path_map_twice g j G J ST SU SY dG dJ dhe) • _).
  now exact (sigT_dep_path_paste_normalize SY
    (sigT_path_paste (sigT_path_map f F
      (sigT_path_paste (f_equal_eq_existT_curried s S p hp) eq_refl)) eq_refl)
    (sigT_path_map j J (f_equal_eq_existT_curried g G e he))
    (sigT_map_eq dF (sigT_map_eq dS dhp ⊙ dhv) ⊙ dHα (d; ad) dad)
    (sigT_map_eq dJ (sigT_map_eq dG dhe))).
Defined.

Lemma paired_map_right:
  sigT_map_eq pf ek ⊙ (sigT_map_eq pf (sigT_map_eq pT eq ⊙ ew) ⊙ phα d' (ad'; dad')) =
  eq_existT_curried_dep (Q := SY)
    (H := f_equal f k • (f_equal f (f_equal t q • w) • α d'))
    (Hu := sigT_map_eq F hk ⊙ (sigT_map_eq F (sigT_map_eq T' hq ⊙ hw) ⊙ Hα d' ad'))
    (Hv := rew [Route] Nr in dr).
Proof.
  pose (ET := sigT_dep_path_map_direct t T' SN SX dT dhq).
  eassert (ETW: sigT_map_eq pT eq ⊙ ew = _).
  { refine (path_map2 (fun h k => h ⊙ k) ET eq_refl • _).
    now exact (sigT_dep_path_paste_normalize SX
      (f_equal_eq_existT_curried t T' q hq) eq_refl (sigT_map_eq dT dhq) dhw). }
  eassert (EFTW: sigT_map_eq (f := f) (P := fun x => {u: P x &T SX (x; u)}) (Q := fun y => {u: Q y &T SY (y;
    u)}) pf (sigT_map_eq pT eq ⊙ ew) = _).
  { refine (f_equal (fun h => sigT_map_eq (f := f) (P := fun x => {u: P x &T SX (x; u)}) (Q := fun y => {u:
    Q y &T SY (y; u)}) pf h) ETW • _).
    now exact (sigT_dep_path_map_normalize f F SX SY dF
      (sigT_path_paste (f_equal_eq_existT_curried t T' q hq) eq_refl)
      (sigT_map_eq dT dhq ⊙ dhw)). }
  eassert (EPrefix: sigT_map_eq (f := f) (P := fun x => {u: P x &T SX (x; u)}) (Q := fun y => {u: Q y &T SY
    (y; u)}) pf (sigT_map_eq pT eq ⊙ ew) ⊙ phα d'(ad'; dad') = _).
  { refine (path_map2 (fun h k => h ⊙ k) EFTW eq_refl • _).
    now exact (sigT_dep_path_paste_normalize SY
      (sigT_path_map f F (sigT_path_paste (f_equal_eq_existT_curried t T' q hq) eq_refl))
      eq_refl (sigT_map_eq dF (sigT_map_eq dT dhq ⊙ dhw)) (dHα (d'; ad') dad')). }
  refine (path_map2 (fun h k => h ⊙ k)
    (sigT_dep_path_map_direct f F SX SY dF dhk) EPrefix • _).
  now exact (sigT_dep_path_paste_normalize SY
    (f_equal_eq_existT_curried f F k hk)
    (sigT_path_paste (sigT_path_map f F
      (sigT_path_paste (f_equal_eq_existT_curried t T' q hq) eq_refl)) eq_refl)
    (sigT_map_eq dF dhk)
    (sigT_map_eq dF (sigT_map_eq dT dhq ⊙ dhw) ⊙ dHα (d'; ad') dad')).
Defined.

Let HM := layer_square_map r s t f g j α e p q v w k H
  (square_coherence_fill r g f j α e).

Let HM1 := layer_square_map_coherence_dep r s t f g j R S T' F G J α Hα
  e p q v w k H he hp hq hv hw hk HH.

Definition paired_map_higher:
  rew [Route] (eq_existT_curried_eq HM HM1) in (rew [Route] Nl in dl) =
  rew [Route] Nr in dr.
Proof.
  pose proof (layer_square_map_coherence_dep tr ts tt tf tg tj dR dS dT dF dG dJ tα dHα
    (= e; he) (= p; hp) (= q; hq) (= v; hv) (= w; hw) (= k; hk) tH dhe dhp dhq dhv dhw dhk dHH) as DM.
  pose (Norm := sigT_layer_square_map r s t f g j R S T' F G J α Hα
    e p q v w k H he hp hq hv hw hk HH).
  pose proof (rew [fun h => rew [Route] h in dl = dr] Norm in DM) as NN.
  apply (rew_conjugate Route) in NN.
  now exact NN.
Defined.

Let pHH := eq_existT_curried_hex_dep (R1 := fun x u => SM (x; u))
  (R2 := fun x u => SN (x; u)) (R3 := fun x u => ST (x; u)) (R' := fun x u => SX (x; u))
  s S (fun x u => dS (x; u)) r R (fun x u => dR (x; u)) t T' (fun x u => dT (x; u))
  p hp dhp v hv dhv e he dhe k hk dhk q hq dhq w hw dhw H HH dHH.
Local Ltac with_layer_higher_paint k :=
  lazymatch goal with
  | |- _ = _ • (eq_existT_curried_dep_eq _ _ ?HIGH • _) =>
    lazymatch HIGH with
    | rew_conjugate _ _ _ _ _ _ ?RAW => k RAW
    end
  end.

Local Ltac with_layer_mapped_paint k :=
  with_layer_higher_paint ltac: (fun RAW =>
    lazymatch RAW with
    | @eq_rect _ _ _ ?STAGE _ _ =>
      lazymatch STAGE with
      | square_stack_dep _ _ _ _ _ _ _ _ _ _ ?DMAP ?DREV => k DMAP
      end
    end).

Lemma sigT_layer_square_map_pair_dep:
  layer_square_map_coherence_dep r s t f g j pR pS pT pf pg pj α phα
    e p q v w k H ee ep eq ev ew ek pHH =
  f_equal (fun h => rew [fun e => rew [fun y => {u: Q y &T SY (y; u)}] e in
    (F (s m) (S m am); dF (ts (m; am)) (dS (m; am) dam)) =
    (J (g d') (G d' ad'); dJ (tg (d'; ad')) (dG (d'; ad') dad'))] HM in h) paired_map_left •
    (eq_existT_curried_dep_eq (Q := SY) HM HM1 paired_map_higher • eq_sym paired_map_right).
Proof.
  unfold layer_square_map_coherence_dep at 1.
  unfold square_map_along_coherence_dep at 1.
  unfold square_map_along_dep at 1.
  pose proof (sigT_hex_pair_factory_match
    (R1 := fun x u => SM (x; u)) (R2 := fun x u => SN (x; u))
    (R3 := fun x u => ST (x; u)) (R' := fun x u => SX (x; u)) s S (fun x u => dS (x; u))
    r R (fun x u => dR (x; u)) t T'(fun x u => dT (x; u))
    p hp dhp v hv dhv e he dhe k hk dhk q hq dhq w hw dhw H HH dHH) as HF.
  unfold pHH.
  rewrite HF.
  rewrite sigT_hex_rect_pair_dep_normalize.
  rewrite sigT_square_map_pair_dep_cap_paint_normalized.
  rewrite sigT_square_coherence_reverse_pair_dep_factory.
  lazymatch goal with
  | |- square_stack_dep _ ?H0 ?K0 ?aa ?cc ?dd ?pp ?qq ?rr ?ss ?DH0 ?DK0 = _ =>
    lazymatch DH0 with
    | ?L0 • (?F0 • eq_sym ?R0) =>
      lazymatch F0 with
      | sigT_square_dep_normalize ?RR ?HH ?HH1 ?NA ?NC ?NP ?NQ ?DA ?DC ?DP ?DQ ?DH =>
        lazymatch DK0 with
        | ?L1 • (?F1 • eq_sym ?R1) =>
          lazymatch F1 with
          | sigT_square_dep_normalize ?RR1 ?KK ?KK1 ?NC1 ?ND ?NR ?NS ?DC1 ?DD ?DR ?DS ?DK =>
            lazymatch L0 with | f_equal _ (path_map2 _ ?EP ?EC) =>
              lazymatch R0 with | path_map2 _ ?EA ?EQ =>
                lazymatch L1 with | f_equal _ (path_map2 _ ?ER ?ED) =>
                  lazymatch R1 with | path_map2 _ ?EC1 ?ES =>
                    let ST := constr: (sigT_square_stack_pair_dep_paint_normalized Q HH KK
                      (sigT_map_eq F hk) (sigT_map_eq F (sigT_map_eq R he))
                      (sigT_map_eq J (sigT_map_eq G he))
                      (sigT_map_eq F (sigT_map_eq S hp ⊙ hv)) (sigT_map_eq F (sigT_map_eq T' hq ⊙ hw))
                      (Hα d ad) (Hα d' ad') HH1 KK1 NA NC ND NP NQ NR NS RR
                      DA DC DD DP DQ DR DS DH DK aa cc dd pp qq rr ss EA EC ED EP EQ ER ES) in
                    rewrite ST
                  end
                end
              end
            end
          end
        end
      end
    end
  end.
  unfold sigT_square_dep_normalize.
  rewrite (rew_conjugate_compose
    (fun e: f (s m) = j (g d') => rew [fun y => {u: Q y &T SY (y; u)}] e in
      (F (s m) (S m am); dF (ts (m; am)) (dS (m; am) dam)) =
      (J (g d') (G d' ad'); dJ (tg (d'; ad')) (dG (d'; ad') dad'))) HM).
  unfold paired_map_higher.
  unfold sigT_layer_square_map.
  cbn beta iota zeta.
  with_layer_higher_paint ltac: (fun RAW =>
    lazymatch RAW with
    | @eq_rect _ _ ?PP ?UU _ (@eq_trans _ _ _ _ ?E1 ?E2) =>
      rewrite <- (rew_compose PP E1 E2 UU)
    end).
  unfold layer_square_map_coherence_dep, square_map_along_coherence_dep, square_map_along_dep.
  rewrite (square_stack_dep_transport SY).
  with_layer_mapped_paint ltac: (fun DMAP =>
    lazymatch DMAP with
    | @eq_rect _ _ ?FP ?FD _ (@eq_trans _ _ _ _ ?E1 ?E2) =>
      rewrite <- (rew_compose FP E1 E2 FD)
    end).
  with_layer_mapped_paint ltac: (fun DMAP =>
    lazymatch DMAP with
    | @eq_rect _ _ _ ?INNER _ _ =>
      lazymatch INNER with
      | @eq_rect _ _ _ ?FD _ (@f_equal _ _ _ _ _ ?NN) =>
        lazymatch FD with
        | square_map_dep ?TF ?DF ?HX ?DA ?DB ?DP ?DQ ?DH =>
          rewrite (square_map_dep_transport (P := SX) (Q := SY) TF DF NN DA DB DP DQ DH)
        end
      end
    end).
  now reflexivity.
Defined.

Let NA := f_equal_eq_existT_curried f F k hk.

Let NC := f_equal_eq_existT_curried g G e he.

Let NSP := sigT_path_paste (f_equal_eq_existT_curried s S p hp) (eq_refl: (= v; hv) = (= v; hv)).

Let NTQ := sigT_path_paste (f_equal_eq_existT_curried t T' q hq) (eq_refl: (= w; hw) = (= w; hw)).

Let NP := sigT_path_paste (sigT_path_map f F NSP) (eq_refl: (= α d; Hα d ad) = (= α d; Hα d ad)).

Let NQ := sigT_path_paste (sigT_path_map f F NTQ) (eq_refl: (= α d'; Hα d' ad') = (= α d'; Hα d' ad')).

Let DP := sigT_map_eq dF (sigT_map_eq dS dhp ⊙ dhv) ⊙ dHα (d; ad) dad.

Let DQ := sigT_map_eq dF (sigT_map_eq dT dhq ⊙ dhw) ⊙ dHα (d'; ad') dad'.

Let ParentNorm := sigT_layer_square_map r s t f g j R S T' F G J α Hα
  e p q v w k H he hp hq hv hw hk HH.

Definition sigT_layer_square_map_higher_transport :=
  rew [fun h => rew [Route] h in dl = dr] ParentNorm in
  layer_square_map_coherence_dep tr ts tt tf tg tj dR dS dT dF dG dJ tα dHα
    (= e; he) (= p; hp) (= q; hq) (= v; hv) (= w; hw) (= k; hk) tH
    dhe dhp dhq dhv dhw dhk dHH.

Let ES := sigT_dep_path_map_direct s S SM SX dS dhp.

Let ESV := sigT_pair_path_paste SX (f_equal_eq_existT_curried s S p hp) eq_refl
  (sigT_map_eq dS dhp) dhv ES (eq_refl: ev = ev).

Let EFSV := sigT_pair_path_map f F SX SY dF NSP (sigT_map_eq dS dhp ⊙ dhv) ESV.

Let ET := sigT_dep_path_map_direct t T' SN SX dT dhq.

Let ETW := sigT_pair_path_paste SX (f_equal_eq_existT_curried t T' q hq) eq_refl
  (sigT_map_eq dT dhq) dhw ET (eq_refl: ew = ew).

Let EFTW := sigT_pair_path_map f F SX SY dF NTQ (sigT_map_eq dT dhq ⊙ dhw) ETW.

Definition paired_map_prefix_left :=
  sigT_pair_path_paste SY (sigT_path_map f F NSP) eq_refl
    (sigT_map_eq dF (sigT_map_eq dS dhp ⊙ dhv)) (dHα (d; ad) dad)
    EFSV (eq_refl: phα d (ad; dad) = phα d (ad; dad)).

Definition paired_map_prefix_right :=
  sigT_pair_path_paste SY (sigT_path_map f F NTQ) eq_refl
    (sigT_map_eq dF (sigT_map_eq dT dhq ⊙ dhw)) (dHα (d'; ad') dad')
    EFTW (eq_refl: phα d'(ad'; dad') = phα d'(ad'; dad')).

Let Ea := sigT_dep_path_map_direct f F SX SY dF dhk.

Let Ec := sigT_dep_path_map_direct g G ST SU dG dhe.

Let Factory := sigT_square_map_dep_normalize j Q PU SY SU J dJ HM HM1
  NA NC NP NQ (sigT_map_eq dF dhk) (sigT_map_eq dG dhe) DP DQ
  sigT_layer_square_map_higher_transport.

Definition layer_map_square_factory :=
  f_equal (fun h => rew [fun e => rew [fun y => {u: Q y &T SY (y; u)}] e in
    (F (s m) (S m am); dF (ts (m; am)) (dS (m; am) dam)) =
    (J (g d') (G d' ad'); dJ (tg (d'; ad')) (dG (d'; ad') dad'))] HM in h)
    (path_map2 (fun
      (h: rew [fun y => {u: Q y &T SY (y; u)}](f_equal f (f_equal s p • v) • α d) in
        (F (s m) (S m am); dF (ts (m; am)) (dS (m; am) dam)) = pj (g d) (G d ad; dG (d; ad) dad))
      (k: rew [fun u => {a: PU u &T SU (u; a)}] f_equal g e in
        (G d ad; dG (d; ad) dad) = (G d' ad'; dG (d'; ad') dad')) =>
      h ⊙ sigT_map_eq (f := j) (P := fun u => {a: PU u &T SU (u; a)})
      (Q := fun y => {a: Q y &T SY (y; a)}) pj k) paired_map_prefix_left Ec) •
    (Factory • eq_sym (path_map2 (fun h k => h ⊙ k) Ea paired_map_prefix_right)).

Lemma sigT_layer_square_map_pair_factory:
  layer_square_map_coherence_dep r s t f g j pR pS pT pf pg pj α phα
    e p q v w k H ee ep eq ev ew ek pHH = layer_map_square_factory.
Proof.
  unfold layer_map_square_factory, Factory.
  rewrite (sigT_square_map_dep_paint_computation j Q PU SY SU J dJ HM HM1
    NA NC NP NQ (sigT_map_eq dF dhk) (sigT_map_eq dG dhe) DP DQ
    sigT_layer_square_map_higher_transport
    (sigT_map_eq pf ek) (sigT_map_eq pg ee)
    (sigT_map_eq pf (sigT_map_eq pS ep ⊙ ev) ⊙ phα d (ad; dad))
    (sigT_map_eq pf (sigT_map_eq pT eq ⊙ ew) ⊙ phα d'(ad'; dad'))
    Ea Ec paired_map_prefix_left paired_map_prefix_right).
  now exact sigT_layer_square_map_pair_dep.
Defined.

End PairMapData.

Lemma sigT_square_cube_dep_normalize {X: Type} (P: X -> Type) (R: {x: X &T P x} -> Type)
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
  (DD: square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ)
  {ta ta': (x0; u0) = (x1; u1)} {tb tb': (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Na': ta' = (= a'; ha'))
  (Nb: tb = (= b; hb)) (Nb': tb' = (= b'; hb'))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  {r0: R (x0; u0)} {r1: R (x1; u1)} {s0: R (y0; v0)} {s1: R (y1; v1)}
  (da: rew [R] ta in r0 = r1) (da': rew [R] ta' in r0 = r1)
  (db: rew [R] tb in s0 = s1) (db': rew [R] tb' in s0 = s1)
  (dp: rew [R] tp in r0 = s0) (dq: rew [R] tq in r1 = s1)
  (DHH: rew [fun e => rew [R] e in r0 = s1] (sigT_path_paste Np Nb • (eq_existT_curried_eq H HH • eq_sym
    (sigT_path_paste Na Nq))) in (dp ⊙ db) = da ⊙ dq)
  (DKK: rew [fun e => rew [R] e in r0 = s1] (sigT_path_paste Np Nb' • (eq_existT_curried_eq K KK • eq_sym
    (sigT_path_paste Na' Nq))) in (dp ⊙ db') = da' ⊙ dq)
  (DDκ: rew [fun e => rew [R] e in s0 = s1] (Nb • (eq_existT_curried_eq κ Dκ • eq_sym Nb')) in db = db')
  (DDλ: rew [fun e => rew [R] e in r0 = r1] (Na • (eq_existT_curried_eq λ Dλ • eq_sym Na')) in da = da')
  (DDD: square_cube_coherence_dep R ((sigT_path_paste Np Nb • (eq_existT_curried_eq H HH • eq_sym
    (sigT_path_paste Na Nq)))) ((sigT_path_paste Np Nb' • (eq_existT_curried_eq K KK • eq_sym
    (sigT_path_paste Na' Nq))))
    ((Nb • (eq_existT_curried_eq κ Dκ • eq_sym Nb'))) ((Na • (eq_existT_curried_eq λ Dλ • eq_sym Na')))
    (sigT_square_cube_normalize P H K κ λ C ha ha' hb hb' hp hq HH KK Dκ Dλ DD Na Na' Nb Nb' Np Nq)
    da da' db db' dp dq DHH DKK DDκ DDλ):
  square_cube_coherence_dep (fun x => {u: P x &T R (x; u)}) H K κ λ C
    (eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 = r1] Na in
      da)) (eq_existT_curried_dep (Q := R) (H := a') (Hu := ha') (Hv := rew [fun e => rew [R] e in r0 = r1]
      Na' in da')) (eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in s0
       = s1] Nb in db)) (eq_existT_curried_dep (Q := R) (H := b') (Hu := hb') (Hv := rew [fun e => rew [R] e
      in s0 = s1] Nb' in db')) (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew
      [R] e in r0 = s0] Np in dp)) (eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e =>
      rew [R] e in r1 = s1] Nq in dq))
    (sigT_square_dep_normalize R H HH Na Nb Np Nq da db dp dq DHH)
    (sigT_square_dep_normalize R K KK Na' Nb' Np Nq da' db' dp dq DKK)
    (sigT_eq_dep_normalize R κ Dκ Nb Nb' db db' DDκ)
    (sigT_eq_dep_normalize R λ Dλ Na Na' da da' DDλ).
Proof.
  subst ta ta' tb tb' tp tq.
  destruct λ, κ. cbn in Dλ, Dκ. destruct Dλ, Dκ.
  cbn in DDλ, DDκ. destruct DDλ, DDκ.
  destruct p, b, q. cbn in hp, hb, hq.
  destruct hp, hb, hq. cbn in dp, db, dq.
  destruct dp, db, dq.
  cbn in H. destruct H.
  cbn in HH.
  revert DDD. revert DKK. revert DHH. revert da. revert DD. revert KK.
  pattern ha, HH.
  apply (homotopy_path_ind_r (fun h: u1 = u1 =>
    sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros KK DD da DHH DKK DDD.
  revert DDD. revert DKK. pattern da, DHH.
  apply (homotopy_path_ind_r (fun h: r1 = r1 =>
    sigT_trans_eq (P := R) (p := eq_refl) h (p' := eq_refl) eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  cbn. intros DKK DDD.
  cbn [square_cube whisker_l whisker_r f_equal] in C.
  revert DDD. revert DKK. revert DD. revert KK. pattern K, C.
  apply (homotopy_path_ind_r (fun k => eq_refl • k)
    (fun k => eq_trans_refl_l k)).
  cbn. intros KK DD DKK DDD.
  unfold square_cube_coherence_dep in DD. cbn in DD.
  pose (F := fun e: x1 = x1 => rew [P] e in u1 = u1).
  revert DDD. revert DKK. pattern KK, DD.
  apply (homotopy_path_ind_r
    (fun k: @eq_refl _ u1 = @eq_refl _ u1 =>
      @sigT_trans_eq (x1 = x1) F
        (@eq_refl X x1) (@eq_refl X x1) (@eq_refl X x1)
        (@eq_refl _ u1) (@eq_refl _ u1) (@eq_refl _ u1)
        eq_refl eq_refl eq_refl k)
    (fun k => @sigT_trans_eq_refl (x1 = x1) F (@eq_refl X x1)
      (@eq_refl _ u1) (@eq_refl _ u1) (@eq_refl _ u1) eq_refl k
 • eq_trans_refl_l k)).
  cbn. intros DKK DDD.
  unfold square_cube_coherence_dep in DDD. cbn in DDD.
  pose (G := fun e: (x1; u1) = (x1; u1) => rew [R] e in r1 = r1).
  pattern DKK, DDD.
  apply (homotopy_path_ind_r
    (fun k: @eq_refl _ r1 = @eq_refl _ r1 =>
      @sigT_trans_eq ((x1; u1) = (x1; u1)) G
        (@eq_refl _ (x1; u1)) (@eq_refl _ (x1; u1)) (@eq_refl _ (x1; u1))
        (@eq_refl _ r1) (@eq_refl _ r1) (@eq_refl _ r1)
        eq_refl eq_refl eq_refl k)
    (fun k => @sigT_trans_eq_refl ((x1; u1) = (x1; u1)) G (@eq_refl _ (x1; u1))
      (@eq_refl _ r1) (@eq_refl _ r1) (@eq_refl _ r1) eq_refl k
 • eq_trans_refl_l k)).
  now reflexivity.
Defined.

Lemma sigT_square_compose_map_dep_normalize {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
  (F: forall y, Q y -> P (f y))
  (R: {x: X &T P x} -> Type) (S: {y: Y &T Q y} -> Type)
  (V: forall z, S z -> R (f z.1; F z.1 z.2))
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
  {ta: (x0; u0) = (x1; u1)} {tb: (x1; u1) = (x2; u2)}
  {tc: (y0; v0) = (y1; v1)} {td: (y1; v1) = (y2; v2)}
  {tp: (x0; u0) = (f y0; F y0 v0)}
  {tq: (x1; u1) = (f y1; F y1 v1)}
  {tr: (x2; u2) = (f y2; F y2 v2)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)) (Nr: tr = (= r; hr))
  {r0: R (x0; u0)} {r1: R (x1; u1)} {r2: R (x2; u2)}
  {s0: S (y0; v0)} {s1: S (y1; v1)} {s2: S (y2; v2)}
  (da: rew [R] ta in r0 = r1) (db: rew [R] tb in r1 = r2)
  (dc: rew [S] tc in s0 = s1) (dd: rew [S] td in s1 = s2)
  (dp: rew [R] tp in r0 = V (y0; v0) s0)
  (dq: rew [R] tq in r1 = V (y1; v1) s1)
  (dr: rew [R] tr in r2 = V (y2; v2) s2):
  let tf := fun z: {y: Y &T Q y} => (f z.1; F z.1 z.2) in
  let Htotal := sigT_path_paste Np
    (f_equal (fun e => f_equal tf e) Nc • f_equal_eq_existT_curried f F c hc) •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)) in
  let Ktotal := sigT_path_paste Nq
    (f_equal (fun e => f_equal tf e) Nd • f_equal_eq_existT_curried f F d hd) •
    (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nb Nr)) in
  forall
  (DHH: rew [fun e => rew [R] e in r0 = V (y1; v1) s1] Htotal in
    (dp ⊙ sigT_map_eq V dc) = da ⊙ dq)
  (DKK: rew [fun e => rew [R] e in r1 = V (y2; v2) s2] Ktotal in
    (dq ⊙ sigT_map_eq V dd) = db ⊙ dr),
  rew [fun e => rew [R] e in r0 = V (y2; v2) s2]
    eq_existT_curried_eq (square_compose_map f H K)
      (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK) in
    (rew [fun e => rew [R] e in r0 = V (y2; v2) s2]
      (sigT_path_paste Np (sigT_path_map f F (sigT_path_paste Nc Nd))) in
      (dp ⊙ sigT_map_eq V (dc ⊙ dd))) =
    rew [fun e => rew [R] e in r0 = V (y2; v2) s2]
      (sigT_path_paste (sigT_path_paste Na Nb) Nr) in ((da ⊙ db) ⊙ dr).
Proof.
  cbn zeta. intros DHH DKK.
  pose (tf := fun z: {y: Y &T Q y} => (f z.1; F z.1 z.2)).
  pose (Ht := sigT_path_paste Np (sigT_path_map f F Nc) •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq))).
  pose (Kt := sigT_path_paste Nq (sigT_path_map f F Nd) •
    (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nb Nr))).
  pose proof (square_compose_map_coherence_dep tf R S V Ht Kt
    da db dc dd dp dq dr DHH DKK) as DC.
  pose (N := sigT_square_compose_map_normalize f P Q F H K
    ha hb hc hd hp hq hr HH KK Na Nb Nc Nd Np Nq Nr).
  pose proof (rew [fun h => rew [fun e => rew [R] e in r0 = V (y2; v2) s2] h in
    (dp ⊙ sigT_map_eq V (dc ⊙ dd)) = (da ⊙ db) ⊙ dr] N in DC) as DN.
  apply (rew_conjugate (fun e: (x0; u0) = (f y2; F y2 v2) =>
    rew [R] e in r0 = V (y2; v2) s2)) in DN.
  now exact DN.
Defined.

Lemma sigT_square_compose_map_pair_dep_normalize {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
  (F: forall y, Q y -> P (f y))
  (R: {x: X &T P x} -> Type) (S: {y: Y &T Q y} -> Type)
  (V: forall z, S z -> R (f z.1; F z.1 z.2))
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
  {ta: (x0; u0) = (x1; u1)} {tb: (x1; u1) = (x2; u2)}
  {tc: (y0; v0) = (y1; v1)} {td: (y1; v1) = (y2; v2)}
  {tp: (x0; u0) = (f y0; F y0 v0)}
  {tq: (x1; u1) = (f y1; F y1 v1)}
  {tr: (x2; u2) = (f y2; F y2 v2)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)) (Nr: tr = (= r; hr))
  {r0: R (x0; u0)} {r1: R (x1; u1)} {r2: R (x2; u2)}
  {s0: S (y0; v0)} {s1: S (y1; v1)} {s2: S (y2; v2)}
  (da: rew [R] ta in r0 = r1) (db: rew [R] tb in r1 = r2)
  (dc: rew [S] tc in s0 = s1) (dd: rew [S] td in s1 = s2)
  (dp: rew [R] tp in r0 = V (y0; v0) s0)
  (dq: rew [R] tq in r1 = V (y1; v1) s1)
  (dr: rew [R] tr in r2 = V (y2; v2) s2):
  let tf := fun z: {y: Y &T Q y} => (f z.1; F z.1 z.2) in
  let Htotal := sigT_path_paste Np
    (f_equal (fun e => f_equal tf e) Nc • f_equal_eq_existT_curried f F c hc) •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)) in
  let Ktotal := sigT_path_paste Nq
    (f_equal (fun e => f_equal tf e) Nd • f_equal_eq_existT_curried f F d hd) •
    (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nb Nr)) in
  forall
  (DHH: rew [fun e => rew [R] e in r0 = V (y1; v1) s1] Htotal in
    (dp ⊙ sigT_map_eq V dc) = da ⊙ dq)
  (DKK: rew [fun e => rew [R] e in r1 = V (y2; v2) s2] Ktotal in
    (dq ⊙ sigT_map_eq V dd) = db ⊙ dr),
  let PF := (fun y (uv: {u: Q y &T S (y; u)}) => (F y uv.1; V (y; uv.1) uv.2)) in
  let EL := f_equal (fun h: rew [fun y => {u: Q y &T S (y; u)}](c • d) in (v0; s0) = (v2; s2) =>
    (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in _ = _] Np in dp)) ⊙
    sigT_map_eq PF h)
    (sigT_dep_path_paste_normalize S Nc Nd dc dd) •
    (f_equal (fun h: rew [fun x => {u: P x &T R (x; u)}] f_equal f (c • d) in (F y0 v0; V (y0; v0) s0) = (F
      y2 v2; V (y2; v2) s2) => (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew
      [R] e in _ = _] Np in dp)) ⊙ h)
      (sigT_dep_path_map_normalize f F S R V (sigT_path_paste Nc Nd) (dc ⊙ dd)) •
     sigT_dep_path_paste_normalize R Np (sigT_path_map f F (sigT_path_paste Nc Nd))
       dp (sigT_map_eq V (dc ⊙ dd))) in
  let ER := f_equal (fun h: rew [fun x => {u: P x &T R (x; u)}](a • b) in (u0; r0) = (u2; r2) => h ⊙
    (eq_existT_curried_dep (Q := R) (H := r) (Hu := hr) (Hv := rew [fun e => rew [R] e in _ = _] Nr in dr)))
    (sigT_dep_path_paste_normalize R Na Nb da db) •
    sigT_dep_path_paste_normalize R (sigT_path_paste Na Nb) Nr (da ⊙ db) dr in
  square_compose_map_coherence_dep f
    (fun x => {u: P x &T R (x; u)}) (fun y => {u: Q y &T S (y; u)}) PF H K
    (eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in _ = _] Na in da))
      (eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in _ = _] Nb in db))
      (eq_existT_curried_dep (Q := S) (H := c) (Hu := hc) (Hv := rew [fun e => rew [S] e in _ = _] Nc in dc))
      (eq_existT_curried_dep (Q := S) (H := d) (Hu := hd) (Hv := rew [fun e => rew [S] e in _ = _] Nd in dd))
      (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in _ = _] Np in dp))
      (eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in _ = _] Nq in dq))
      (eq_existT_curried_dep (Q := R) (H := r) (Hu := hr) (Hv := rew [fun e => rew [R] e in _ = _] Nr in dr))
    (sigT_square_map_dep_normalize f P Q R S F V H HH Na Nc Np Nq da dc dp dq DHH)
      (sigT_square_map_dep_normalize f P Q R S F V K KK Nb Nd Nq Nr db dd dq dr DKK) =
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u0; r0) = (F y2 v2; V (y2; v2) s2)] square_compose_map f H K in h) EL •
    (eq_existT_curried_dep_eq (Q := R) (square_compose_map f H K)
      (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK)
      (sigT_square_compose_map_dep_normalize f P Q F R S V H K
        ha hb hc hd hp hq hr HH KK Na Nb Nc Nd Np Nq Nr
        da db dc dd dp dq dr DHH DKK) • eq_sym ER).
Proof.
  cbn zeta. intros DHH DKK.
  subst ta tb tc td tp tq tr.
  destruct c, d.
  generalize dependent x0. intros x0 a p. revert a.
  pattern x0, p. apply (homotopy_path_ind (fun x: X => x) (fun x => eq_refl)).
  cbn. intros a H u0 ha hp HH r0 da dp DHH.
  generalize dependent x2. intros x2 b r. revert b.
  pattern x2, r. apply (homotopy_path_ind (fun x: X => x) (fun x => eq_refl)).
  cbn. intros b K u2 hb hr KK r2 db dr DKK.
  generalize dependent x1. intros x1 q.
  pattern x1, q. apply (homotopy_path_ind (fun x: X => x) (fun x => eq_refl)).
  cbn. intros u1 hq r1 dq a H ha HH da DHH b K hb KK db DKK.
  cbn in hc, hd, hp, hr, hq.
  destruct hc, hd. cbn in dc, dd. destruct dc, dd.
  generalize dependent u0. intros u0 hp.
  pattern u0, hp. apply (homotopy_path_ind (fun u: P (f y0) => u) (fun u => eq_refl)).
  cbn. intros r0 dp ha HH da DHH.
  generalize dependent u2. intros u2 hr.
  pattern u2, hr. apply (homotopy_path_ind (fun u: P (f y0) => u) (fun u => eq_refl)).
  cbn. intros r2 dr hb KK db DKK.
  generalize dependent u1. intros u1 hq.
  pattern u1, hq. apply (homotopy_path_ind (fun u: P (f y0) => u) (fun u => eq_refl)).
  cbn. intros r1 dq ha HH da DHH hb KK db DKK.
  generalize dependent r0. intros r0 dp.
  pattern r0, dp. apply (homotopy_path_ind (fun r: R (f y0; F y0 v0) => r) (fun r => eq_refl)).
  cbn. intros da DHH.
  generalize dependent r2. intros r2 dr.
  pattern r2, dr. apply (homotopy_path_ind (fun r: R (f y0; F y0 v0) => r) (fun r => eq_refl)).
  cbn. intros db DKK.
  generalize dependent r1. intros r1 dq.
  pattern r1, dq. apply (homotopy_path_ind (fun r: R (f y0; F y0 v0) => r) (fun r => eq_refl)).
  cbn. intros da DHH db DKK.
  cbn in K. destruct K.
  cbn in KK.
  revert DKK. revert db. pattern hb, KK.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros db DKK.
  pattern db, DKK.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  cbn.
  cbn in H. destruct H.
  cbn in HH.
  revert DHH. revert da. pattern ha, HH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros da DHH.
  pattern da, DHH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  now reflexivity.
Defined.

Lemma sigT_eq_map_pair_dep_normalize {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {u: P x} {v: P y} {p q: x = y}
  {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  {tp tq: (x; u) = (y; v)} (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  (H: p = q) (HH: rew [fun e => rew [P] e in u = v] H in hp = hq)
  {r: R (x; u)} {s: R (y; v)} (dp: rew [R] tp in r = s) (dq: rew [R] tq in r = s)
  (DD: rew [fun e => rew [R] e in r = s]
    (Np • (eq_existT_curried_eq H HH • eq_sym Nq)) in dp = dq):
  let PF := (fun x (uv: {u: P x &T R (x; u)}) => (F x uv.1; V (x; uv.1) uv.2)) in
  let EH := f_equal (fun e => f_equal f e) H in
  let EHH := sigT_map_eq (f := fun e => f_equal f e)
    (Q := fun e => rew [Q] e in F x u = F y v)
    (fun (e: x = y) (h: rew [P] e in u = v) => sigT_map_eq F h) HH in
  let ND := sigT_eq_map_normalized f F Np Nq H HH in
  let DDmapped := sigT_map_eq
    (f := fun e => f_equal (fun z: {a: A &T P a} => (f z.1; F z.1 z.2)) e)
    (Q := fun e => rew [S] e in V (x; u) r = V (y; v) s)
    (fun (e: (x; u) = (y; v)) (d: rew [R] e in r = s) => sigT_map_eq V d) DD in
  let DDnorm := rew [fun h => rew [fun e => rew [S] e in V (x; u) r = V (y; v) s] h in
    sigT_map_eq V dp = sigT_map_eq V dq] ND in DDmapped in
  sigT_map_eq (f := fun e => f_equal f e)
    (Q := fun e => rew [fun y => {u: Q y &T S (y; u)}] e in
      (F x u; V (x; u) r) = (F y v; V (y; v) s))
    (fun (e: x = y) (h: rew [fun x => {u: P x &T R (x; u)}] e in (u; r) = (v; s)) =>
      sigT_map_eq PF h)
    (sigT_eq_dep_normalize R H HH Np Nq dp dq DD) =
  f_equal (fun h => rew [fun e => rew [fun y => {u: Q y &T S (y; u)}] e in
      (F x u; V (x; u) r) = (F y v; V (y; v) s)] EH in h)
    (sigT_dep_path_map_normalize f F R S V Np dp) •
    (sigT_eq_dep_normalize S EH EHH
      (sigT_path_map f F Np) (sigT_path_map f F Nq)
      (sigT_map_eq V dp) (sigT_map_eq V dq) DDnorm •
     eq_sym (sigT_dep_path_map_normalize f F R S V Nq dq)).
Proof.
  cbn zeta.
  subst tp tq. destruct H. cbn in HH. destruct HH.
  cbn in DD. destruct DD.
  destruct hp, p. cbn in dp. destruct dp.
  now reflexivity.
Defined.

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

Let NR := sigT_path_paste (p := H1') (h := Hu1') eq_refl (sigT_path_paste (q := H3') (k := Hu3') N2 eq_refl).

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

Let EL := sigT_hex_pair_left_normalize f1 g1 h1 f3 g3 h3
  H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3.

Let ER := sigT_hex_pair_right_normalize f1 g1 h1 f3 g3 h3 f2 g2 h2
  H1' Hu1' Hv1' H2' Hu2' Hv2' H3' Hu3' Hv3'.

Context {C: Type} {Q': C -> Type} (S': {x: C &T Q' x} -> Type)
  (f: B -> C) (F: forall x, P' x -> Q'(f x))
  (W: forall z, S z -> S'(f z.1; F z.1 z.2)).

Let DL := (sigT_map_eq (f := T1) (Q := S) V1 Hv1 ⊙ Hv2) ⊙ sigT_map_eq (f := T3) (Q := S) V3 Hv3.

Let DR := Hv1' ⊙ (sigT_map_eq (f := T2) (Q := S) V2 Hv2' ⊙ Hv3').

Let PF := (fun x (uv: {u: P' x &T R' x u}) =>
  @existT _ (fun u: Q'(f x) => S'(f x; u)) (F x uv.1) (W (x; uv.1) uv.2)).

Let EH := f_equal (fun e => f_equal f e) HH.

Let EHH := sigT_map_eq (f := fun e => f_equal f e)
  (Q := fun e => rew [Q'] e in F (f1 x0) (g1 x0 u0) = F (f3 x3) (g3 x3 u3))
  (fun (e: f1 x0 = f3 x3) (h: rew [P'] e in g1 x0 u0 = g3 x3 u3) => sigT_map_eq F h) HHu.

Let ND := sigT_eq_map_normalized f F NL NR HH HHu.

Let DDM := sigT_map_eq
  (f := fun e => f_equal (fun z: {x: B &T P' x} => (f z.1; F z.1 z.2)) e)
  (Q := fun e => rew [S'] e in W (f1 x0; g1 x0 u0) (h1 x0 u0 v0) = W (f3 x3; g3 x3 u3) (h3 x3 u3 v3))
  (fun (e: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3))
    (d: rew [S] e in (h1 x0 u0 v0: S (f1 x0; g1 x0 u0)) = h3 x3 u3 v3) => sigT_map_eq W d) HHv.

Let DDNorm := rew [fun h => rew [fun e => rew [S'] e in
  W (f1 x0; g1 x0 u0) (h1 x0 u0 v0) = W (f3 x3; g3 x3 u3) (h3 x3 u3 v3)] h in
  sigT_map_eq W DL = sigT_map_eq W DR] ND in DDM.

Let MPL := sigT_dep_path_map_normalize f F S S' W NL DL.

Let MPR := sigT_dep_path_map_normalize f F S S' W NR DR.

Let ELCap := f_equal (fun h: rew [fun x => {u: P' x &T R' x u}]
  (f_equal f1 H1 • H2) • f_equal f3 H3 in
  (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3) => sigT_map_eq PF h) EL • MPL.

Let ERCap := f_equal (fun h: rew [fun x => {u: P' x &T R' x u}]
  H1' • (f_equal f2 H2' • H3') in
  (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3) => sigT_map_eq PF h) ER • MPR.

Lemma sigT_hex_map_pair_left_normalize:
  sigT_map_eq (f := f) (P := fun x => {u: P' x &T R' x u}) (Q := fun x => {u: Q' x &T S'(x; u)}) PF PL =
  eq_existT_curried_dep (Q := S')
    (H := f_equal f ((f_equal f1 H1 • H2) • f_equal f3 H3))
    (Hu := sigT_map_eq F ((sigT_map_eq g1 Hu1 ⊙ Hu2) ⊙ sigT_map_eq g3 Hu3))
    (Hv := rew [fun e => rew [S'] e in
      W (f1 x0; g1 x0 u0) (h1 x0 u0 v0) = W (f3 x3; g3 x3 u3) (h3 x3 u3 v3)]
      (sigT_path_map f F NL) in sigT_map_eq W DL).
Proof. now exact ELCap. Defined.

Lemma sigT_hex_map_pair_right_normalize:
  sigT_map_eq (f := f) (P := fun x => {u: P' x &T R' x u}) (Q := fun x => {u: Q' x &T S'(x; u)}) PF PR =
  eq_existT_curried_dep (Q := S')
    (H := f_equal f (H1' • (f_equal f2 H2' • H3')))
    (Hu := sigT_map_eq F (Hu1' ⊙ (sigT_map_eq g2 Hu2' ⊙ Hu3')))
    (Hv := rew [fun e => rew [S'] e in
      W (f1 x0; g1 x0 u0) (h1 x0 u0 v0) = W (f3 x3; g3 x3 u3) (h3 x3 u3 v3)]
      (sigT_path_map f F NR) in sigT_map_eq W DR).
Proof. now exact ERCap. Defined.

Lemma sigT_hex_map_pair_dep_normalize:
  sigT_map_eq (f := fun e => f_equal f e)
    (Q := fun e => rew [fun x => {u: Q' x &T S'(x; u)}] e in
      (F (f1 x0) (g1 x0 u0); W (f1 x0; g1 x0 u0) (h1 x0 u0 v0)) =
      (F (f3 x3) (g3 x3 u3); W (f3 x3; g3 x3 u3) (h3 x3 u3 v3)))
    (fun (e: f1 x0 = f3 x3)
      (h: rew [fun x => {u: P' x &T R' x u}] e in
        (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)) => sigT_map_eq PF h)
    (eq_existT_curried_hex_dep f1 g1 h1 f3 g3 h3 f2 g2 h2
      H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3 H1' Hu1' Hv1'
      H2' Hu2' Hv2' H3' Hu3' Hv3' HH HHu HHv) =
  f_equal (fun h => rew [fun e => rew [fun x => {u: Q' x &T S'(x; u)}] e in
      (F (f1 x0) (g1 x0 u0); W (f1 x0; g1 x0 u0) (h1 x0 u0 v0)) =
      (F (f3 x3) (g3 x3 u3); W (f3 x3; g3 x3 u3) (h3 x3 u3 v3))] EH in h) ELCap •
    (sigT_eq_dep_normalize S' EH EHH
      (sigT_path_map f F NL) (sigT_path_map f F NR)
      (sigT_map_eq W DL) (sigT_map_eq W DR) DDNorm • eq_sym ERCap).
Proof.
  unfold eq_existT_curried_hex_dep.
  fold S T1 T2 T3 V1 V2 V3 NL NR EL ER DL DR PF.
  rewrite (sigT_map_eq_conjugate
    (P := fun e: f1 x0 = f3 x3 => rew [fun x => {u: P' x &T R' x u}] e in
      (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3))
    (Q := fun e: f (f1 x0) = f (f3 x3) => rew [fun x => {u: Q' x &T S'(x; u)}] e in
      (F (f1 x0) (g1 x0 u0); W (f1 x0; g1 x0 u0) (h1 x0 u0 v0)) =
      (F (f3 x3) (g3 x3 u3); W (f3 x3; g3 x3 u3) (h3 x3 u3 v3)))
    (f := fun e => f_equal f e)
    (fun (e: f1 x0 = f3 x3) (h: rew [fun x => {u: P' x &T R' x u}] e in
      (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)) => sigT_map_eq PF h)
    HH EL ER (sigT_eq_dep_normalize S HH HHu NL NR DL DR HHv)).
  rewrite (sigT_eq_map_pair_dep_normalize f F S S' W NL NR HH HHu DL DR HHv).
  unfold ELCap, ERCap.
  now apply (rew_conjugate_compose
    (fun e: f (f1 x0) = f (f3 x3) => rew [fun x => {u: Q' x &T S'(x; u)}] e in
      (F (f1 x0) (g1 x0 u0); W (f1 x0; g1 x0 u0) (h1 x0 u0 v0)) =
      (F (f3 x3) (g3 x3 u3); W (f3 x3; g3 x3 u3) (h3 x3 u3 v3))) EH).
Defined.

End PairedHexRoutes.

Section PairChangeSidesNormalized.

Context {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (H: p • b = a • q) (Hq: q' = q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hp': rew [P] p' in u0 = v0)
  (hq: rew [P] q in u1 = v1) (hq': rew [P] q' in u1 = v1)
  (HHp: rew [fun e => rew [P] e in u0 = v0] Hp in hp' = hp)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (HHq: rew [fun e => rew [P] e in u1 = v1] Hq in hq' = hq)
  {ta: (x0; u0) = (x1; u1)} {tb: (y0; v0) = (y1; v1)}
  {tp tp': (x0; u0) = (y0; v0)} {tq tq': (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Np': tp' = (= p'; hp'))
  (Nq: tq = (= q; hq)) (Nq': tq' = (= q'; hq')).

Context (R: {x: X &T P x} -> Type).

Context {r0: R (x0; u0)} {r1: R (x1; u1)} {s0: R (y0; v0)} {s1: R (y1; v1)}.

Context (da: rew [R] ta in r0 = r1) (db: rew [R] tb in s0 = s1)
  (dp: rew [R] tp in r0 = s0) (dp': rew [R] tp' in r0 = s0)
  (dq: rew [R] tq in r1 = s1) (dq': rew [R] tq' in r1 = s1).

Let Hpt := Np' • (eq_existT_curried_eq Hp HHp • eq_sym Np).

Let Hqt := Nq' • (eq_existT_curried_eq Hq HHq • eq_sym Nq).

Let Ht := sigT_path_paste Np Nb • (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)).

Context (DP: rew [fun e => rew [R] e in r0 = s0] Hpt in dp' = dp)
  (DH: rew [fun e => rew [R] e in r0 = s1] Ht in (dp ⊙ db) = da ⊙ dq)
  (DQ: rew [fun e => rew [R] e in r1 = s1] Hqt in dq' = dq).

Let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da).

Let eb := eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in s0 = s1] Nb in db).

Let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r0 = s0] Np in dp).

Let ep' := eq_existT_curried_dep (Q := R) (H := p') (Hu := hp') (Hv := rew [fun e => rew [R] e in r0 = s0] Np' in dp').

Let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in r1 = s1] Nq in dq).

Let eq' := eq_existT_curried_dep (Q := R) (H := q') (Hu := hq') (Hv := rew [fun e => rew [R] e in r1 = s1] Nq' in dq').

Let DPp := sigT_eq_dep_normalize R Hp HHp Np' Np dp' dp DP.

Let DQp := sigT_eq_dep_normalize R Hq HHq Nq' Nq dq' dq DQ.

Let DHp := sigT_square_dep_normalize R H HH Na Nb Np Nq da db dp dq DH.

Let HC := square_change_sides Hp H Hq.

Let HC1 := square_change_sides_dep P Hp H Hq ha hb hp hp' hq hq' HHp HH HHq.

Let Route := fun e: (x0; u0) = (y1; v1) => rew [R] e in r0 = s1.

Definition sigT_square_change_sides_normalized_higher :=
  rew [fun h => rew [Route] h in (dp' ⊙ db) = da ⊙ dq']
    (sigT_square_change_sides_normalized P Hp H Hq ha hb hp hp' hq hq' HHp HH HHq
      Na Nb Np Np' Nq Nq') in
    square_change_sides_dep R Hpt Ht Hqt da db dp dp' dq dq' DP DH DQ.

Let Dresult := sigT_square_dep_normalize R HC HC1 Na Nb Np' Nq' da db dp' dq'
  sigT_square_change_sides_normalized_higher.

Lemma sigT_square_change_sides_pair_dep_normalized:
  square_change_sides_dep (fun x => {u: P x &T R (x; u)}) Hp H Hq ea eb ep ep' eq eq' DPp DHp DQp =
  Dresult.
Proof.
  cbv beta iota zeta delta[ea eb ep ep' eq eq' DPp DQp DHp HC HC1 Dresult
    sigT_square_change_sides_normalized_higher Route Hpt Hqt Ht] in *.
  clear ea eb ep ep' eq eq' DPp DQp DHp HC HC1 Dresult Route Hpt Hqt Ht.
  subst ta tb tp tp' tq tq'.
  destruct Hp, Hq. cbn in HHp, HHq. destruct HHp, HHq.
  cbn in DP, DQ. destruct DP, DQ.
  destruct p', b, q'. cbn in hp', hb, hq'. destruct hp', hb, hq'.
  cbn in dp', db, dq'. destruct dp', db, dq'.
  cbn in H. destruct H. cbn in HH.
  revert DH. revert da. pattern ha, HH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := P) (p := eq_refl) h)).
  cbn. intros da DH.
  pattern da, DH.
  apply (homotopy_path_ind_r (fun h => h ⊙ eq_refl)
    (fun h => sigT_trans_eq_unit_r (P := R) (p := eq_refl) h)).
  now reflexivity.
Defined.

Context (aa: rew [fun x => {u: P x &T R (x; u)}] a in (u0; r0) = (u1; r1))
  (bb: rew [fun x => {u: P x &T R (x; u)}] b in (v0; s0) = (v1; s1))
  (pp: rew [fun x => {u: P x &T R (x; u)}] p in (u0; r0) = (v0; s0))
  (pp': rew [fun x => {u: P x &T R (x; u)}] p' in (u0; r0) = (v0; s0))
  (qq: rew [fun x => {u: P x &T R (x; u)}] q in (u1; r1) = (v1; s1))
  (qq': rew [fun x => {u: P x &T R (x; u)}] q' in (u1; r1) = (v1; s1)).

Context (Ea: aa = ea) (Eb: bb = eb) (Ep: pp = ep) (Ep': pp' = ep') (Eq: qq = eq) (Eq': qq' = eq').

Let RawP := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (v0; s0)] Hp in h)
  Ep' • (DPp • eq_sym Ep).

Let RawQ := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u1; r1) = (v1; s1)] Hq in h)
  Eq' • (DQp • eq_sym Eq).

Let RawH := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (v1; s1)] H in h)
  (path_map2 (fun h k => h ⊙ k) Ep Eb) • (DHp • eq_sym (path_map2 (fun h k => h ⊙ k) Ea Eq)).

Lemma sigT_square_change_sides_pair_dep_paint_normalized:
  square_change_sides_dep (fun x => {u: P x &T R (x; u)}) Hp H Hq aa bb pp pp' qq qq' RawP RawH RawQ =
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u0; r0) = (v1; s1)] HC in h)
    (path_map2 (fun h k => h ⊙ k) Ep' Eb) •
    (Dresult • eq_sym (path_map2 (fun h k => h ⊙ k) Ea Eq')).
Proof.
  unfold RawP, RawH, RawQ.
  subst aa bb pp pp' qq qq'.
  cbn[path_map2 f_equal eq_sym].
  rewrite 4 eq_trans_refl_l, 4 eq_trans_refl_r.
  now apply sigT_square_change_sides_pair_dep_normalized.
Defined.

End PairChangeSidesNormalized.

Lemma sigT_eq_dep_normalize_change_left {X: Type} {P: X -> Type}
  (R: {x: X &T P x} -> Type) {x y: X} {u: P x} {v: P y}
  {p p': x = y} {h: rew [P] p in u = v} {h': rew [P] p' in u = v}
  (H: p = p') (HH: rew [fun e => rew [P] e in u = v] H in h = h')
  {t t': (x; u) = (y; v)} (N N1: t = (= p; h)) (N': t' = (= p'; h'))
  (E: N = N1) {r: R (x; u)} {s: R (y; v)}
  (d: rew [R] t in r = s) (d': rew [R] t' in r = s)
  (D: rew [fun e => rew [R] e in r = s]
    (N • (eq_existT_curried_eq H HH • eq_sym N')) in d = d') :
  let C := fun n => n • (eq_existT_curried_eq H HH • eq_sym N') in
  let Cdep := fun c => rew [fun e => rew [R] e in r = s] c in d = d' in
  let D1 := rew [Cdep] f_equal C E in D in
  let edge := fun n => eq_existT_curried_dep (Q := R) (H := p) (Hu := h)
    (Hv := rew [fun e => rew [R] e in r = s] n in d) in
  sigT_eq_dep_normalize R H HH N N' d d' D =
  f_equal (fun a => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e
    in (u; r) = (v; s)] H in a) (f_equal edge E) •
    sigT_eq_dep_normalize R H HH N1 N' d d' D1.
Proof.
  destruct E. cbn zeta. cbn [f_equal].
  now rewrite eq_trans_refl_l.
Defined.

Section PairedNat.

Context
  {Z V V' W X: Type} {S: Z -> Type} {QL: V -> Type} {QR: V' -> Type}
  {PW: W -> Type} {P: X -> Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (RL: forall z, S z -> QL (L z)) (RR: forall z, S z -> QR (R z))
  (F: forall v, QL v -> P (f v)) (G: forall v, QR v -> P (g v))
  (D: forall w, PW w -> P (d w))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [P] k z in F (L z) (RL z a) = G (R z) (RR z a))
  {z1 z2: Z} (p: z1 = z2) {m: V} {n: V'}
  (l: L z2 = m) (r: R z2 = n) {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: hexagonal_coherence f d g l e r c (k z2) c')
  {a1: S z1} {a2: S z2} {am: QL m} {an: QR n} {aw1: PW w1} {aw2: PW w2}
  (hp: rew [S] p in a1 = a2)
  (hl: rew [QL] l in RL z2 a2 = am) (hr: rew [QR] r in RR z2 a2 = an)
  (he: rew [PW] e in aw1 = aw2)
  (hc: rew [P] c in F m am = D w1 aw1)
  (hc': rew [P] c' in G n an = D w2 aw2)
  (HH: hexagonal_coherence_dep F D G H hl he hr hc (hk z2 a2) hc').

Let tL := fun z: {x: Z &T S x} => (L z.1; RL z.1 z.2).

Let tR := fun z: {x: Z &T S x} => (R z.1; RR z.1 z.2).

Let tf := fun z: {x: V &T QL x} => (f z.1; F z.1 z.2).

Let tg := fun z: {x: V' &T QR x} => (g z.1; G z.1 z.2).

Let td := fun z: {x: W &T PW x} => (d z.1; D z.1 z.2).

Let tk := fun z: {x: Z &T S x} => (= k z.1; hk z.1 z.2).

Context (SZ: {z: Z &T S z} -> Type) (SV: {z: V &T QL z} -> Type)
  (SV': {z: V' &T QR z} -> Type) (SW: {z: W &T PW z} -> Type)
  (SX: {z: X &T P z} -> Type).

Context (dL: forall z, SZ z -> SV (tL z)) (dR: forall z, SZ z -> SV'(tR z))
  (df: forall z, SV z -> SX (tf z)) (dg: forall z, SV' z -> SX (tg z))
  (dd: forall z, SW z -> SX (td z)).

Context (dHK: forall z a, rew [SX] tk z in df (tL z) (dL z a) = dg (tR z) (dR z a)).

Context {da1: SZ (z1; a1)} {da2: SZ (z2; a2)} {dam: SV (m; am)} {dan: SV'(n; an)}
  {daw1: SW (w1; aw1)} {daw2: SW (w2; aw2)}.

Context (dhp: rew [SZ](= p; hp) in da1 = da2)
  (dhl: rew [SV](= l; hl) in dL (z2; a2) da2 = dam)
  (dhr: rew [SV'](= r; hr) in dR (z2; a2) da2 = dan)
  (dhe: rew [SW](= e; he) in daw1 = daw2)
  (dhc: rew [SX](= c; hc) in df (m; am) dam = dd (w1; aw1) daw1)
  (dhc': rew [SX](= c'; hc') in dg (n; an) dan = dd (w2; aw2) daw2).

Let tH := eq_existT_curried_hex f F g G d D H HH.

Context (dHH: hexagonal_coherence_dep df dd dg tH dhl dhe dhr dhc
  (dHK (z2; a2) da2) dhc').

Let pL := fun z (uv: {a: S z &T SZ (z; a)}) => (RL z uv.1; dL (z; uv.1) uv.2): {a: QL (L z)&T SV (L z; a)}.

Let pR := fun z (uv: {a: S z &T SZ (z; a)}) => (RR z uv.1; dR (z; uv.1) uv.2): {a: QR (R z)&T SV'(R z; a)}.

Let pf := fun z (uv: {a: QL z &T SV (z; a)}) => (F z uv.1; df (z; uv.1) uv.2): {a: P (f z)&T SX (f z; a)}.

Let pg := fun z (uv: {a: QR z &T SV'(z; a)}) => (G z uv.1; dg (z; uv.1) uv.2): {a: P (g z)&T SX (g z; a)}.

Let pd := fun z (uv: {a: PW z &T SW (z; a)}) => (D z uv.1; dd (z; uv.1) uv.2): {a: P (d z)&T SX (d z; a)}.

Let phk := fun z (uv: {a: S z &T SZ (z; a)}) =>
  eq_existT_curried_dep (Q := SX) (H := k z) (Hu := hk z uv.1) (Hv := dHK (z; uv.1) uv.2).

Let ep := eq_existT_curried_dep (Q := SZ) (H := p) (Hu := hp) (Hv := dhp).

Let el := eq_existT_curried_dep (Q := SV) (H := l) (Hu := hl) (Hv := dhl).

Let er := eq_existT_curried_dep (Q := SV') (H := r) (Hu := hr) (Hv := dhr).

Let ee := eq_existT_curried_dep (Q := SW) (H := e) (Hu := he) (Hv := dhe).

Let ec := eq_existT_curried_dep (Q := SX) (H := c) (Hu := hc) (Hv := dhc).

Let ec' := eq_existT_curried_dep (Q := SX) (H := c') (Hu := hc') (Hv := dhc').

Let Nl := sigT_path_paste
  (sigT_path_paste (sigT_path_map f F
    (sigT_path_paste (f_equal_eq_existT_curried L RL p hp)
      (eq_refl: (= l; hl) = (= l; hl)))) (eq_refl: (= c; hc) = (= c; hc)))
  (sigT_path_map d D (p := e) (hp := he) eq_refl).

Let Nr := sigT_path_paste (eq_refl: (= k z1; hk z1 a1) = (= k z1; hk z1 a1))
  (sigT_path_paste (sigT_path_map g G
    (sigT_path_paste (f_equal_eq_existT_curried R RR p hp)
      (eq_refl: (= r; hr) = (= r; hr)))) (eq_refl: (= c'; hc') = (= c'; hc'))).

Let dl := (sigT_map_eq df (sigT_map_eq dL dhp ⊙ dhl) ⊙ dhc) ⊙ sigT_map_eq dd dhe.

Let dr := dHK (z1; a1) da1 ⊙ (sigT_map_eq dg (sigT_map_eq dR dhp ⊙ dhr) ⊙ dhc').

Lemma paired_nat_left:
  (sigT_map_eq pf (sigT_map_eq pL ep ⊙ el) ⊙ ec) ⊙ sigT_map_eq pd ee =
  eq_existT_curried_dep (Q := SX)
    (H := (f_equal f (f_equal L p • l) • c) • f_equal d e)
    (Hu := (sigT_map_eq F (sigT_map_eq RL hp ⊙ hl) ⊙ hc) ⊙ sigT_map_eq D he)
    (Hv := rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] Nl in dl).
Proof.
  pose (ELmap := sigT_dep_path_map_direct L RL (fun z => SZ (z.1; z.2)) (fun z => SV (z.1; z.2))
    (fun z => dL (z.1; z.2)) (p := p) (hp := hp) dhp).
  pose (ELsrc := sigT_pair_path_paste (fun z => SV (z.1; z.2)) (f_equal_eq_existT_curried L RL p hp)
    (eq_refl: (= l; hl) = (= l; hl)) (sigT_map_eq (p := (= p; hp)) (fun z => dL (z.1; z.2)) dhp) dhl ELmap eq_refl).
  pose (ELouter := sigT_pair_path_map f F (fun z => SV (z.1; z.2)) (fun z => SX (z.1; z.2))
    (fun z => df (z.1; z.2)) (a := f_equal tL (= p; hp) • (= l; hl)) (sigT_path_paste (f_equal_eq_existT_curried L RL p hp)
      (eq_refl: (= l; hl) = (= l; hl)))
    (sigT_map_eq (p := (= p; hp)) (fun z => dL (z.1; z.2)) dhp ⊙ dhl) ELsrc).
  pose (ELvert := sigT_pair_path_paste (fun z => SX (z.1; z.2))
    (sigT_path_map f F (sigT_path_paste (f_equal_eq_existT_curried L RL p hp)
      (eq_refl: (= l; hl) = (= l; hl)))) (eq_refl: (= c; hc) = (= c; hc))
    (sigT_map_eq (p := f_equal tL (= p; hp) • (= l; hl)) (fun z => df (z.1; z.2)) (sigT_map_eq (p := (= p; hp))
      (fun z => dL (z.1; z.2)) dhp ⊙ dhl))
    dhc ELouter eq_refl).
  pose (ELbottom := sigT_dep_path_map_direct d D (fun z => SW (z.1; z.2)) (fun z => SX (z.1; z.2))
    (fun z => dd (z.1; z.2)) (p := e) (hp := he) dhe).
  pose (NV := sigT_path_paste (sigT_path_map f F (sigT_path_paste (f_equal_eq_existT_curried L RL p hp)
    (eq_refl: (= l; hl) = (= l; hl)))) (eq_refl: (= c; hc) = (= c; hc))).
  pose (ELdirect := sigT_pair_path_paste (fun z => SX (z.1; z.2)) NV
    (f_equal_eq_existT_curried d D e he)
    (sigT_map_eq (p := f_equal tL (= p; hp) • (= l; hl)) (fun z => df (z.1; z.2)) (sigT_map_eq (p := (= p; hp))
      (fun z => dL (z.1; z.2)) dhp ⊙ dhl) ⊙ dhc)
    (sigT_map_eq (p := (= e; he)) (fun z => dd (z.1; z.2)) dhe) ELvert ELbottom).
  pose (EN := f_equal (fun n => sigT_path_paste NV n) (eq_sym (sigT_path_map_refl d D e he))).
  refine (ELdirect • _).
  now exact (f_equal (fun n => eq_existT_curried_dep (Q := fun z => SX (z.1; z.2))
    (H := (f_equal f (f_equal L p • l) • c) • f_equal d e)
    (Hu := (sigT_map_eq F (sigT_map_eq RL hp ⊙ hl) ⊙ hc) ⊙ sigT_map_eq D he)
    (Hv := rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] n in dl)) EN).
Defined.

Lemma paired_nat_right:
  phk z1 (a1; da1) ⊙ (sigT_map_eq pg (sigT_map_eq pR ep ⊙ er) ⊙ ec') =
  eq_existT_curried_dep (Q := SX)
    (H := k z1 • (f_equal g (f_equal R p • r) • c'))
    (Hu := hk z1 a1 ⊙ (sigT_map_eq G (sigT_map_eq RR hp ⊙ hr) ⊙ hc'))
    (Hv := rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] Nr in dr).
Proof.
  pose (ERmap := sigT_dep_path_map_direct R RR (fun z => SZ (z.1; z.2)) (fun z => SV'(z.1; z.2))
    (fun z => dR (z.1; z.2)) (p := p) (hp := hp) dhp).
  pose (ERsrc := sigT_pair_path_paste (fun z => SV'(z.1; z.2)) (f_equal_eq_existT_curried R RR p hp)
    (eq_refl: (= r; hr) = (= r; hr)) (sigT_map_eq (p := (= p; hp)) (fun z => dR (z.1; z.2)) dhp) dhr ERmap eq_refl).
  pose (ERouter := sigT_pair_path_map g G (fun z => SV'(z.1; z.2)) (fun z => SX (z.1; z.2))
    (fun z => dg (z.1; z.2)) (a := f_equal tR (= p; hp) • (= r; hr)) (sigT_path_paste (f_equal_eq_existT_curried R RR p hp)
      (eq_refl: (= r; hr) = (= r; hr)))
    (sigT_map_eq (p := (= p; hp)) (fun z => dR (z.1; z.2)) dhp ⊙ dhr) ERsrc).
  pose (ERvert := sigT_pair_path_paste (fun z => SX (z.1; z.2))
    (sigT_path_map g G (sigT_path_paste (f_equal_eq_existT_curried R RR p hp)
      (eq_refl: (= r; hr) = (= r; hr)))) (eq_refl: (= c'; hc') = (= c'; hc'))
    (sigT_map_eq (p := f_equal tR (= p; hp) • (= r; hr)) (fun z => dg (z.1; z.2)) (sigT_map_eq (p := (= p; hp))
      (fun z => dR (z.1; z.2)) dhp ⊙ dhr))
    dhc' ERouter eq_refl).
  now exact (sigT_pair_path_paste (fun z => SX (z.1; z.2))
    (eq_refl: (= k z1; hk z1 a1) = (= k z1; hk z1 a1))
    (sigT_path_paste (sigT_path_map g G (sigT_path_paste (f_equal_eq_existT_curried R RR p hp)
      (eq_refl: (= r; hr) = (= r; hr)))) (eq_refl: (= c'; hc') = (= c'; hc')))
    (dHK (z1; a1) da1) (sigT_map_eq (p := f_equal tR (= p; hp) • (= r; hr)) (fun z => dg (z.1; z.2))
      (sigT_map_eq (p := (= p; hp)) (fun z => dR (z.1; z.2)) dhp ⊙ dhr) ⊙ dhc') eq_refl ERvert).
Defined.

Let HN := layer_square_nat L R f g d k p l r e c c' H
  (square_coherence_fill L R f g k p).

Let HN1 := layer_square_nat_coherence_dep L R f g d RL RR F G D k hk
  p l r e c c' H hp hl hr he hc hc' HH.

Let HNt := layer_square_nat tL tR tf tg td tk (= p; hp) (= l; hl) (= r; hr)
  (= e; he) (= c; hc) (= c'; hc') tH (square_coherence_fill tL tR tf tg tk (= p; hp)).

Definition paired_nat_higher:
  rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2]
    (eq_existT_curried_eq HN HN1) in
    (rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] Nl in dl) =
    rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] Nr in dr.
Proof.
  pose proof (layer_square_nat_coherence_dep tL tR tf tg td dL dR df dg dd tk dHK
    (= p; hp) (= l; hl) (= r; hr) (= e; he) (= c; hc) (= c'; hc') tH
    dhp dhl dhr dhe dhc dhc' dHH) as DN.
  pose (N := sigT_layer_square_nat L R f g d RL RR F G D k hk
    p l r e c c' H hp hl hr he hc hc' HH).
  pose proof (rew [fun h => rew [fun e => rew [SX] e in
    df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] h in dl = dr] N in DN) as NN.
  apply (rew_conjugate (fun e: (f (L z1); F (L z1) (RL z1 a1)) = (d w2; D w2 aw2) =>
    rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2)) in NN.
  now exact NN.
Defined.

Let pHH := eq_existT_curried_hex_dep (R1 := fun x u => SV (x; u))
  (R2 := fun x u => SV'(x; u)) (R3 := fun x u => SW (x; u)) (R' := fun x u => SX (x; u)) f F (fun x u => df (x; u))
  d D (fun x u => dd (x; u)) g G (fun x u => dg (x; u))
  l hl dhl c hc dhc e he dhe (k z2) (hk z2 a2) (dHK (z2; a2) da2)
  r hr dhr c' hc' dhc' H HH dHH.

Let phH := sigT_hex_pair_factory_normalize P
  (f_equal_eq_existT_curried f F l hl) (eq_refl: (= c; hc) = (= c; hc))
  (f_equal_eq_existT_curried d D e he) (eq_refl: (= k z2; hk z2 a2) = (= k z2; hk z2 a2))
  (f_equal_eq_existT_curried g G r hr) (eq_refl: (= c'; hc') = (= c'; hc')) H HH (fun z => SX (z.1; z.2))
  (sigT_map_eq (p := (= l; hl)) (fun z => df (z.1; z.2)) dhl) dhc (sigT_map_eq (p := (= e; he)) (fun z => dd
    (z.1; z.2)) dhe) (dHK (z2; a2) da2) (sigT_map_eq (p := (= r; hr)) (fun z => dg (z.1; z.2)) dhr) dhc' dHH
  (sigT_dep_path_map_direct f F (fun z => SV (z.1; z.2)) (fun z => SX (z.1; z.2)) (fun z => df (z.1; z.2))
    (p := l) (hp := hl) dhl) eq_refl
  (sigT_dep_path_map_direct d D (fun z => SW (z.1; z.2)) (fun z => SX (z.1; z.2)) (fun z => dd (z.1; z.2))
    (p := e) (hp := he) dhe) eq_refl
  (sigT_dep_path_map_direct g G (fun z => SV'(z.1; z.2)) (fun z => SX (z.1; z.2)) (fun z => dg (z.1; z.2))
    (p := r) (hp := hr) dhr) eq_refl.

Lemma paired_nat_hex_factory: pHH = phH.
Proof.
  unfold pHH, phH.
  now exact (sigT_hex_pair_factory_match (R1 := fun x u => SV (x; u))
    (R2 := fun x u => SV'(x; u)) (R3 := fun x u => SW (x; u)) (R' := fun x u => SX (x; u))
    f F (fun x u => df (x; u)) d D (fun x u => dd (x; u)) g G (fun x u => dg (x; u))
    l hl dhl c hc dhc e he dhe (k z2) (hk z2 a2) (dHK (z2; a2) da2)
    r hr dhr c' hc' dhc' H HH dHH).
Defined.

Definition nat_pair_boundary :=
  layer_square_nat_coherence_dep L R f g d pL pR pf pg pd k phk
    p l r e c c' H ep el er ee ec ec' pHH =
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T SX (x; u)}] e in
    (F (L z1) (RL z1 a1); df (tL (z1; a1)) (dL (z1; a1) da1)) =
    (D w2 aw2; dd (w2; aw2) daw2)] HN in h) paired_nat_left •
    (eq_existT_curried_dep_eq (Q := SX) HN HN1 paired_nat_higher • eq_sym paired_nat_right).

Lemma sigT_layer_square_nat_pair_dep: nat_pair_boundary.
Proof.
  unfold nat_pair_boundary.
  unfold layer_square_nat_coherence_dep at 1.
  unfold square_nat_along_coherence_dep at 1.
  rewrite paired_nat_hex_factory.
  unfold phH.
  rewrite sigT_hex_rect_pair_dep_normalize.
  rewrite (sigT_square_coherence_pair_dep_factory L R f g RL RR F G
    (fun z => SZ (z.1; z.2)) (fun z => SV (z.1; z.2)) (fun z => SV'(z.1; z.2)) (fun z => SX (z.1; z.2))
    (fun z => dL (z.1; z.2)) (fun z => dR (z.1; z.2))
    (fun z => df (z.1; z.2)) (fun z => dg (z.1; z.2)) k hk (fun z => dHK (z.1; z.2)) p hp dhp).
  unfold square_nat_along_dep at 1.
  rewrite (sigT_square_stack_pair_dep_paint_normalized P
    (square_coherence_fill L R f g k p)
    H
    (hk z1 a1) (hk z2 a2) (sigT_map_eq D he)
    (sigT_map_eq F (sigT_map_eq RL hp)) (sigT_map_eq G (sigT_map_eq RR hp))
    (sigT_map_eq F hl ⊙ hc) (sigT_map_eq G hr ⊙ hc')
    (square_coherence_dep_fill L R f g RL RR F G k hk p hp)
    HH
    (eq_refl: (= k z1; hk z1 a1) = (= k z1; hk z1 a1))
    (eq_refl: (= k z2; hk z2 a2) = (= k z2; hk z2 a2))
    (f_equal_eq_existT_curried d D e he)
    (sigT_path_map f F (f_equal_eq_existT_curried L RL p hp))
    (sigT_path_map g G (f_equal_eq_existT_curried R RR p hp))
    (sigT_path_paste (f_equal_eq_existT_curried f F l hl) (eq_refl: (= c; hc) = (= c; hc)))
    (sigT_path_paste (f_equal_eq_existT_curried g G r hr) (eq_refl: (= c'; hc') = (= c'; hc')))
    (fun z => SX (z.1; z.2))).
  rewrite (sigT_map_tail_direct_pair_factory f F
    (sigT_map_eq RL hp) hl hc (f_equal_eq_existT_curried L RL p hp)
    (fun z => SV (z.1; z.2)) (fun z => SX (z.1; z.2)) (fun z => df (z.1; z.2))
    (sigT_map_eq (p := (= p; hp)) (fun z => dL (z.1; z.2)) dhp) dhl dhc
    (sigT_map_eq pL ep)
    (sigT_dep_path_map_direct L RL (fun z => SZ (z.1; z.2)) (fun z => SV (z.1; z.2))
      (fun z => dL (z.1; z.2)) (p := p) (hp := hp) dhp)).
  rewrite (sigT_map_tail_direct_pair_factory g G
    (sigT_map_eq RR hp) hr hc'(f_equal_eq_existT_curried R RR p hp)
    (fun z => SV'(z.1; z.2)) (fun z => SX (z.1; z.2)) (fun z => dg (z.1; z.2))
    (sigT_map_eq (p := (= p; hp)) (fun z => dR (z.1; z.2)) dhp) dhr dhc'
    (sigT_map_eq pR ep)
    (sigT_dep_path_map_direct R RR (fun z => SZ (z.1; z.2)) (fun z => SV'(z.1; z.2))
      (fun z => dR (z.1; z.2)) (p := p) (hp := hp) dhp)).
  rewrite sigT_square_change_sides_pair_dep_paint_normalized.
  unfold sigT_square_dep_normalize.
  rewrite (rew_conjugate_compose
    (fun e: f (L z1) = d w2 => rew [fun x => {u: P x &T SX (x; u)}] e in
      (F (L z1) (RL z1 a1); df (tL (z1; a1)) (dL (z1; a1) da1)) = (D w2 aw2; dd (w2; aw2) daw2)) HN).
  match goal with
  | |- context[sigT_eq_dep_normalize ?RF ?HC ?HC1
      (sigT_path_paste ?NV (f_equal_eq_existT_curried d D e he)) ?NR ?dl0 ?dr0 ?DN] =>
      rewrite (sigT_eq_dep_normalize_change_left RF HC HC1
        (sigT_path_paste NV (f_equal_eq_existT_curried d D e he))
        (sigT_path_paste NV (sigT_path_map d D (p := e) (hp := he) eq_refl)) NR
        (f_equal (fun nb => sigT_path_paste NV nb) (eq_sym (sigT_path_map_refl d D e he))) dl0 dr0 DN)
  end.
  rewrite (path_left_correction_compose
    (fun h => rew [fun e => rew [fun x => {u: P x &T SX (x; u)}] e in
      (F (L z1) (RL z1 a1); df (tL (z1; a1)) (dL (z1; a1) da1)) = (D w2 aw2; dd (w2; aw2) daw2)] HN in h)).
  unfold paired_nat_left, paired_nat_right.
  cbn beta iota zeta.
  unfold sigT_eq_dep_normalize.
  f_equal.
  unfold paired_nat_higher. cbn zeta.
  unfold sigT_layer_square_nat.
  cbn beta iota zeta.
  lazymatch goal with
  | |- _ = eq_existT_curried_dep_eq _ _ ?HIGH • _ =>
    lazymatch HIGH with
    | rew_conjugate _ _ _ _ _ _ ?RAW =>
      lazymatch RAW with
      | @eq_rect ?AA ?XX ?PP ?UU ?ZZ ?NN =>
        lazymatch NN with
        | @eq_trans _ _ _ _ ?E1 ?E2 => rewrite <- (rew_compose PP E1 E2 UU)
        end
      end
    end
  end.
  unfold layer_square_nat_coherence_dep, square_nat_along_coherence_dep, square_nat_along_dep.
  rewrite (square_change_sides_dep_transport SX).
  lazymatch goal with
  | |- _ = eq_existT_curried_dep_eq _ _ ?HIGH • _ =>
    lazymatch HIGH with
    | rew_conjugate _ _ _ _ _ _ ?RAW =>
      lazymatch RAW with
      | @eq_rect _ _ ?PP ?UU _ (@eq_trans _ _ _ _ ?E1 ?E2) =>
        rewrite <- (rew_compose PP E1 E2 UU)
      end
    end
  end.
  lazymatch goal with
  | |- _ = eq_existT_curried_dep_eq _ _ ?HIGH • _ =>
    lazymatch HIGH with
    | rew_conjugate _ _ _ _ _ _ ?RAW =>
      lazymatch RAW with
      | @eq_rect _ _ _ ?INNER _ _ =>
        lazymatch INNER with
        | @eq_rect _ _ _ ?SIDE _ _ =>
          lazymatch SIDE with
          | square_change_sides_dep _ _ _ _ _ _ _ _ _ _ ?DLEFT ?DMID ?DRIGHT =>
            lazymatch DMID with
            | @eq_rect _ _ ?PP ?UU _ (@eq_trans _ _ _ _ ?E1 ?E2) =>
              rewrite <- (rew_compose PP E1 E2 UU)
            end
          end
        end
      end
    end
  end.
  rewrite (square_stack_dep_transport SX).
  now reflexivity.
Defined.

Let NP := sigT_path_paste (sigT_path_map f F (sigT_path_paste (f_equal_eq_existT_curried L RL p hp)
  (eq_refl: (= l; hl) = (= l; hl)))) (eq_refl: (= c; hc) = (= c; hc)).

Let NQ := sigT_path_paste (sigT_path_map g G (sigT_path_paste (f_equal_eq_existT_curried R RR p hp)
  (eq_refl: (= r; hr) = (= r; hr)))) (eq_refl: (= c'; hc') = (= c'; hc')).

Let DPL := sigT_map_eq df (sigT_map_eq dL dhp ⊙ dhl) ⊙ dhc.

Let DPR := sigT_map_eq dg (sigT_map_eq dR dhp ⊙ dhr) ⊙ dhc'.

Let PPL := sigT_map_eq pf (sigT_map_eq pL ep ⊙ el) ⊙ ec.

Let PPR := sigT_map_eq pg (sigT_map_eq pR ep ⊙ er) ⊙ ec'.

Let ELPsrc := sigT_pair_path_paste SV (f_equal_eq_existT_curried L RL p hp)
  (eq_refl: (= l; hl) = (= l; hl)) (sigT_map_eq dL dhp) dhl
  (sigT_dep_path_map_direct L RL SZ SV dL dhp) eq_refl.

Let ELPmap := sigT_pair_path_map f F SV SX df
  (sigT_path_paste (f_equal_eq_existT_curried L RL p hp) (eq_refl: (= l; hl) = (= l; hl)))
  (sigT_map_eq dL dhp ⊙ dhl) ELPsrc.

Definition paired_nat_prefix_left := sigT_pair_path_paste SX
  (sigT_path_map f F (sigT_path_paste (f_equal_eq_existT_curried L RL p hp) (eq_refl: (= l; hl) = (= l; hl))))
  (eq_refl: (= c; hc) = (= c; hc)) (sigT_map_eq df (sigT_map_eq dL dhp ⊙ dhl)) dhc ELPmap eq_refl.

Let ERPsrc := sigT_pair_path_paste SV'(f_equal_eq_existT_curried R RR p hp)
  (eq_refl: (= r; hr) = (= r; hr)) (sigT_map_eq dR dhp) dhr
  (sigT_dep_path_map_direct R RR SZ SV' dR dhp) eq_refl.

Let ERPmap := sigT_pair_path_map g G SV' SX dg
  (sigT_path_paste (f_equal_eq_existT_curried R RR p hp) (eq_refl: (= r; hr) = (= r; hr)))
  (sigT_map_eq dR dhp ⊙ dhr) ERPsrc.

Definition paired_nat_prefix_right := sigT_pair_path_paste SX
  (sigT_path_map g G (sigT_path_paste (f_equal_eq_existT_curried R RR p hp) (eq_refl: (= r; hr) = (= r; hr))))
  (eq_refl: (= c'; hc') = (= c'; hc')) (sigT_map_eq dg (sigT_map_eq dR dhp ⊙ dhr)) dhc' ERPmap eq_refl.

Let Norm := sigT_layer_square_nat L R f g d RL RR F G D k hk
  p l r e c c' H hp hl hr he hc hc' HH.

Definition sigT_layer_square_nat_higher_transport :=
  rew [fun h => rew [fun e => rew [SX] e in df (tL (z1; a1)) (dL (z1; a1) da1) = dd (w2; aw2) daw2] h in
    (DPL ⊙ sigT_map_eq dd dhe) = (dHK (z1; a1) da1 ⊙ DPR)] Norm in
  layer_square_nat_coherence_dep tL tR tf tg td dL dR df dg dd tk dHK
    (= p; hp) (= l; hl) (= r; hr) (= e; he) (= c; hc) (= c'; hc') tH dhp dhl dhr dhe dhc dhc' dHH.

Let RawNat := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T SX (x; u)}] e in
  (F (L z1) (RL z1 a1); df (tL (z1; a1)) (dL (z1; a1) da1)) = (D w2 aw2; dd (w2; aw2) daw2)] HN in h)
  (path_map2
    (fun (h: rew [fun x => {u: P x &T SX (x; u)}](f_equal f (f_equal L p • l) • c) in
      (F (L z1) (RL z1 a1); df (tL (z1; a1)) (dL (z1; a1) da1)) = (D w1 aw1; dd (w1; aw1) daw1))
      (k: rew [fun w => {u: PW w &T SW (w; u)}] e in (aw1; daw1) = (aw2; daw2)) => h ⊙ sigT_map_eq pd k)
    paired_nat_prefix_left (eq_refl: ee = ee)) •
  (sigT_square_map_dep_normalize d P PW SX SW D dd HN HN1
    (eq_refl: (= k z1; hk z1 a1) = (= k z1; hk z1 a1)) (eq_refl: (= e; he) = (= e; he)) NP NQ
    (dHK (z1; a1) da1) dhe DPL DPR sigT_layer_square_nat_higher_transport •
   eq_sym (path_map2 (fun h k => h ⊙ k) (eq_refl: phk z1 (a1; da1) = phk z1 (a1; da1)) paired_nat_prefix_right)).

Lemma sigT_layer_square_nat_pair_factory:
  layer_square_nat_coherence_dep L R f g d pL pR pf pg pd k phk
    p l r e c c' H ep el er ee ec ec' pHH = RawNat.
Proof.
  rewrite sigT_layer_square_nat_pair_dep.
  symmetry. unfold RawNat.
  rewrite (sigT_square_map_dep_paint_computation d P PW SX SW D dd HN HN1
    (eq_refl: (= k z1; hk z1 a1) = (= k z1; hk z1 a1)) (eq_refl: (= e; he) = (= e; he)) NP NQ
    (dHK (z1; a1) da1) dhe DPL DPR sigT_layer_square_nat_higher_transport
    (phk z1 (a1; da1)) ee PPL PPR eq_refl eq_refl paired_nat_prefix_left paired_nat_prefix_right).
  unfold paired_nat_left, paired_nat_right, paired_nat_higher,
    NP, NQ, paired_nat_prefix_left, paired_nat_prefix_right, ELPsrc, ELPmap, ERPsrc, ERPmap, DPL, DPR,
      sigT_layer_square_nat_higher_transport, Norm.
  cbn beta iota zeta.
  rewrite (sigT_pair_path_map_encoded d D SW SX dd (p := e) (hp := he) eq_refl dhe).
  rewrite sigT_dep_path_map_refl_computation.
  rewrite sigT_pair_path_paste_change_right.
  now reflexivity.
Defined.

End PairedNat.

Section RawComposeMapPair.

Context {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
  (F: forall y, Q y -> P (f y))
  (R: {x: X &T P x} -> Type) (S: {y: Y &T Q y} -> Type)
  (V: forall z, S z -> R (f z.1; F z.1 z.2))
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
  {ta: (x0; u0) = (x1; u1)} {tb: (x1; u1) = (x2; u2)}
  {tc: (y0; v0) = (y1; v1)} {td: (y1; v1) = (y2; v2)}
  {tp: (x0; u0) = (f y0; F y0 v0)}
  {tq: (x1; u1) = (f y1; F y1 v1)}
  {tr: (x2; u2) = (f y2; F y2 v2)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Nc: tc = (= c; hc)) (Nd: td = (= d; hd))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq)) (Nr: tr = (= r; hr))
  {r0: R (x0; u0)} {r1: R (x1; u1)} {r2: R (x2; u2)}
  {s0: S (y0; v0)} {s1: S (y1; v1)} {s2: S (y2; v2)}
  (da: rew [R] ta in r0 = r1) (db: rew [R] tb in r1 = r2)
  (dc: rew [S] tc in s0 = s1) (dd: rew [S] td in s1 = s2)
  (dp: rew [R] tp in r0 = V (y0; v0) s0)
  (dq: rew [R] tq in r1 = V (y1; v1) s1)
  (dr: rew [R] tr in r2 = V (y2; v2) s2).

Let tf := fun z: {y: Y &T Q y} => (f z.1; F z.1 z.2) .

Let Htotal := sigT_path_paste Np
    (f_equal (fun e => f_equal tf e) Nc • f_equal_eq_existT_curried f F c hc) •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq)) .

Let Ktotal := sigT_path_paste Nq
    (f_equal (fun e => f_equal tf e) Nd • f_equal_eq_existT_curried f F d hd) •
    (eq_existT_curried_eq K KK • eq_sym (sigT_path_paste Nb Nr)) .

Context
  (DHH: rew [fun e => rew [R] e in r0 = V (y1; v1) s1] Htotal in
    (dp ⊙ sigT_map_eq V dc) = da ⊙ dq)
  (DKK: rew [fun e => rew [R] e in r1 = V (y2; v2) s2] Ktotal in
    (dq ⊙ sigT_map_eq V dd) = db ⊙ dr).

Let PF: forall y, {u: Q y &T S (y; u)} -> {u: P (f y)&T R (f y; u)} :=
  (fun y (uv: {u: Q y &T S (y; u)}) => (F y uv.1; V (y; uv.1) uv.2)) .

Let EL := f_equal (fun h: rew [fun y => {u: Q y &T S (y; u)}](c • d) in (v0; s0) = (v2; s2) =>
  (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in _ = _] Np in dp)) ⊙
  sigT_map_eq PF h)
    (sigT_dep_path_paste_normalize S Nc Nd dc dd) •
    (f_equal (fun h: rew [fun x => {u: P x &T R (x; u)}] f_equal f (c • d) in (F y0 v0; V (y0; v0) s0) = (F
      y2 v2; V (y2; v2) s2) => (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew
      [R] e in _ = _] Np in dp)) ⊙ h)
      (sigT_dep_path_map_normalize f F S R V (sigT_path_paste Nc Nd) (dc ⊙ dd)) •
     sigT_dep_path_paste_normalize R Np (sigT_path_map f F (sigT_path_paste Nc Nd))
       dp (sigT_map_eq V (dc ⊙ dd))) .

Let ER := f_equal (fun h: rew [fun x => {u: P x &T R (x; u)}](a • b) in (u0; r0) = (u2; r2) => h ⊙
  (eq_existT_curried_dep (Q := R) (H := r) (Hu := hr) (Hv := rew [fun e => rew [R] e in _ = _] Nr in dr)))
    (sigT_dep_path_paste_normalize R Na Nb da db) •
    sigT_dep_path_paste_normalize R (sigT_path_paste Na Nb) Nr (da ⊙ db) dr .

Let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha) (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da).

Let eb := eq_existT_curried_dep (Q := R) (H := b) (Hu := hb) (Hv := rew [fun e => rew [R] e in r1 = r2] Nb in db).

Let ec := eq_existT_curried_dep (Q := S) (H := c) (Hu := hc) (Hv := rew [fun e => rew [S] e in s0 = s1] Nc in dc).

Let ed := eq_existT_curried_dep (Q := S) (H := d) (Hu := hd) (Hv := rew [fun e => rew [S] e in s1 = s2] Nd in dd).

Let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r0 = V (y0; v0) s0] Np in dp).

Let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in r1 = V (y1; v1) s1] Nq in dq).

Let er := eq_existT_curried_dep (Q := R) (H := r) (Hu := hr) (Hv := rew [fun e => rew [R] e in r2 = V (y2; v2) s2] Nr in dr).

Let DHp := sigT_square_map_dep_normalize f P Q R S F V H HH Na Nc Np Nq da dc dp dq DHH.

Let DKp := sigT_square_map_dep_normalize f P Q R S F V K KK Nb Nd Nq Nr db dd dq dr DKK.

Context (aa: rew [fun x => {u: P x &T R (x; u)}] a in (u0; r0) = (u1; r1))
  (bb: rew [fun x => {u: P x &T R (x; u)}] b in (u1; r1) = (u2; r2))
  (cc: rew [fun y => {u: Q y &T S (y; u)}] c in (v0; s0) = (v1; s1))
  (ddp: rew [fun y => {u: Q y &T S (y; u)}] d in (v1; s1) = (v2; s2))
  (pp: rew [fun x => {u: P x &T R (x; u)}] p in (u0; r0) = (F y0 v0; V (y0; v0) s0))
  (qq: rew [fun x => {u: P x &T R (x; u)}] q in (u1; r1) = (F y1 v1; V (y1; v1) s1))
  (rr: rew [fun x => {u: P x &T R (x; u)}] r in (u2; r2) = (F y2 v2; V (y2; v2) s2)).

Context (Ea: aa = ea) (Eb: bb = eb) (Ec: cc = ec) (Ed: ddp = ed) (Ep: pp = ep) (Eq: qq = eq) (Er: rr = er).

Let PPX := fun x => {u: P x &T R (x; u)}.

Let PPY := fun y => {u: Q y &T S (y; u)}.

Let RawH := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u0; r0) = (F y1 v1; V (y1; v1) s1)] H in h)
  (path_map2 (fun (h: rew [PPX] p in (u0; r0) = PF y0 (v0; s0)) (k: rew [PPY] c in (v0; s0) = (v1; s1)) => h ⊙
    sigT_map_eq (f := f) (P := PPY) (Q := PPX) PF k) Ep Ec) •
  (DHp • eq_sym (path_map2 (fun h k => h ⊙ k) Ea Eq)).

Let RawK := f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u1; r1) = (F y2 v2; V (y2; v2) s2)] K in h)
  (path_map2 (fun (h: rew [PPX] q in (u1; r1) = PF y1 (v1; s1)) (k: rew [PPY] d in (v1; s1) = (v2; s2)) => h ⊙
    sigT_map_eq (f := f) (P := PPY) (Q := PPX) PF k) Eq Ed) •
  (DKp • eq_sym (path_map2 (fun h k => h ⊙ k) Eb Er)).

Let ELraw := path_map2 (fun (h: rew [PPX] p in (u0; r0) = PF y0 (v0; s0)) (k: rew [PPY](c • d) in (v0; s0) =
  (v2; s2)) => h ⊙ sigT_map_eq (f := f) (P := PPY) (Q := PPX) PF k)
  Ep (path_map2 (fun h k => h ⊙ k) Ec Ed) • EL.

Let ERraw := path_map2 (fun h k => h ⊙ k) (path_map2 (fun h k => h ⊙ k) Ea Eb) Er • ER.

Lemma sigT_square_compose_map_pair_dep_paint_normalized:
  square_compose_map_coherence_dep f
    (fun x => {u: P x &T R (x; u)}) (fun y => {u: Q y &T S (y; u)}) PF H K
    aa bb cc ddp pp qq rr RawH RawK =
  f_equal (fun h => rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in
    (u0; r0) = (F y2 v2; V (y2; v2) s2)] square_compose_map f H K in h) ELraw •
    (eq_existT_curried_dep_eq (Q := R) (square_compose_map f H K)
      (square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK)
      (sigT_square_compose_map_dep_normalize f P Q F R S V H K
        ha hb hc hd hp hq hr HH KK Na Nb Nc Nd Np Nq Nr
        da db dc dd dp dq dr DHH DKK) • eq_sym ERraw).
Proof.
  unfold RawH, RawK, ELraw, ERraw.
  subst aa bb cc ddp pp qq rr.
  cbn[path_map2 f_equal eq_sym].
  rewrite 4 eq_trans_refl_l, 2 eq_trans_refl_r.
  now exact (sigT_square_compose_map_pair_dep_normalize f P Q F R S V H K
    ha hb hc hd hp hq hr HH KK Na Nb Nc Nd Np Nq Nr da db dc dd dp dq dr DHH DKK).
Defined.

Let HC := square_compose_map f H K.

Let HC1 := square_compose_map_coherence_dep f P Q F H K ha hb hc hd hp hq hr HH KK.

Let CompositeTopN := sigT_path_paste Na Nb.

Let CompositeBottomN := sigT_path_paste Nc Nd.

Definition sigT_square_compose_map_higher_transport :=
  rew [fun h => rew [fun e => rew [R] e in r0 = V (y2; v2) s2] h in
    (dp ⊙ sigT_map_eq V (dc ⊙ dd)) = (da ⊙ db) ⊙ dr]
    (sigT_square_compose_map_normalize f P Q F H K
      ha hb hc hd hp hq hr HH KK Na Nb Nc Nd Np Nq Nr) in
    square_compose_map_coherence_dep tf R S V Htotal Ktotal
      da db dc dd dp dq dr DHH DKK.

Let ParentTopE := sigT_pair_path_paste R Na Nb da db Ea Eb.

Let ParentBottomE := sigT_pair_path_paste S Nc Nd dc dd Ec Ed.

Let ParentPaint := sigT_square_map_dep_normalize f P Q R S F V HC HC1
  CompositeTopN CompositeBottomN Np Nr (da ⊙ db) (dc ⊙ dd) dp dr
  sigT_square_compose_map_higher_transport.

Definition compose_map_parent_factory :=
  f_equal (fun h => rew [fun e => rew [PPX] e in (u0; r0) = PF y2 (v2; s2)] HC in h)
    (path_map2 (fun (h: rew [PPX] p in (u0; r0) = PF y0 (v0; s0))
      (k: rew [PPY](c • d) in (v0; s0) = (v2; s2)) => h ⊙ sigT_map_eq (f := f) (P := PPY) (Q := PPX) PF k)
      Ep ParentBottomE) •
    (ParentPaint • eq_sym (path_map2 (fun h k => h ⊙ k) ParentTopE Er)).

Lemma sigT_square_compose_map_pair_parent_factory:
  square_compose_map_coherence_dep f PPX PPY PF H K
    aa bb cc ddp pp qq rr RawH RawK = compose_map_parent_factory.
Proof.
  unfold compose_map_parent_factory, ParentPaint.
  rewrite (sigT_square_map_dep_paint_computation f P Q R S F V HC HC1
    CompositeTopN CompositeBottomN Np Nr (da ⊙ db) (dc ⊙ dd) dp dr
    sigT_square_compose_map_higher_transport
    (aa ⊙ bb) (cc ⊙ ddp) pp rr ParentTopE ParentBottomE Ep Er).
  rewrite sigT_square_compose_map_pair_dep_paint_normalized.
  unfold ParentTopE, ParentBottomE, sigT_pair_path_paste, sigT_pair_path_map,
    ELraw, ERraw, EL, ER, CompositeTopN, CompositeBottomN.
  subst aa bb cc ddp pp qq rr.
  cbn[path_map2 f_equal eq_sym].
  rewrite 4 eq_trans_refl_l.
  rewrite path_map_compose_prefix.
  unfold path_map2.
  cbn [f_equal].
  rewrite eq_trans_refl_l.
  now reflexivity.
Defined.

End RawComposeMapPair.

Lemma sigT_square_dep_paint_computation {X: Type} {P: X -> Type}
  (R: {x: X &T P x} -> Type)
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  {ta: (x0; u0) = (x1; u1)} {tb: (y0; v0) = (y1; v1)}
  {tp: (x0; u0) = (y0; v0)} {tq: (x1; u1) = (y1; v1)}
  (Na: ta = (= a; ha)) (Nb: tb = (= b; hb))
  (Np: tp = (= p; hp)) (Nq: tq = (= q; hq))
  {r0: R (x0; u0)} {r1: R (x1; u1)}
  {s0: R (y0; v0)} {s1: R (y1; v1)}
  (da: rew [R] ta in r0 = r1) (db: rew [R] tb in s0 = s1)
  (dp: rew [R] tp in r0 = s0) (dq: rew [R] tq in r1 = s1)
  (DHH: rew [fun e => rew [R] e in r0 = s1] (sigT_path_paste Np Nb •
    (eq_existT_curried_eq H HH • eq_sym (sigT_path_paste Na Nq))) in
    (dp ⊙ db) = da ⊙ dq):
  let PP := fun x => {u: P x &T R (x; u)} in
  let ea := eq_existT_curried_dep (Q := R) (H := a) (Hu := ha)
    (Hv := rew [fun e => rew [R] e in r0 = r1] Na in da) in
  let eb := eq_existT_curried_dep (Q := R) (H := b) (Hu := hb)
    (Hv := rew [fun e => rew [R] e in s0 = s1] Nb in db) in
  let ep := eq_existT_curried_dep (Q := R) (H := p) (Hu := hp)
    (Hv := rew [fun e => rew [R] e in r0 = s0] Np in dp) in
  let eq := eq_existT_curried_dep (Q := R) (H := q) (Hu := hq)
    (Hv := rew [fun e => rew [R] e in r1 = s1] Nq in dq) in
  forall (aa: rew [PP] a in (u0; r0) = (u1; r1))
    (bb: rew [PP] b in (v0; s0) = (v1; s1))
    (pp: rew [PP] p in (u0; r0) = (v0; s0))
    (qq: rew [PP] q in (u1; r1) = (v1; s1))
    (Ea: aa = ea) (Eb: bb = eb) (Ep: pp = ep) (Eq: qq = eq),
  let Move := fun h => rew [fun e => rew [PP] e in
    (u0; r0) = (v1; s1)] H in h in
  let RawH := f_equal Move (path_map2 (fun h k => h ⊙ k) Ep Eb) •
    (sigT_square_dep_normalize R H HH Na Nb Np Nq da db dp dq DHH •
      eq_sym (path_map2 (fun h k => h ⊙ k) Ea Eq)) in
  let EL := sigT_pair_path_paste R Np Nb dp db Ep Eb in
  let ER := sigT_pair_path_paste R Na Nq da dq Ea Eq in
  RawH = f_equal Move EL •
    (sigT_eq_dep_normalize R H HH (sigT_path_paste Np Nb) (sigT_path_paste Na Nq)
      (dp ⊙ db) (da ⊙ dq) DHH • eq_sym ER).
Proof.
  cbn zeta. intros aa bb pp qq Ea Eb Ep Eq.
  subst aa bb pp qq.
  unfold sigT_pair_path_paste.
  cbn [path_map2 f_equal eq_sym].
  rewrite 3 eq_trans_refl_l, eq_trans_refl_r.
  now reflexivity.
Defined.
