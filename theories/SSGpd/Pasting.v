(** Pasting path comparisons, squares, and layer-coherence cells,
    with their dependent lifts. *)

Import Logic.EqNotations.

Set Warnings"-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas.
From Bonak.Lib Require Export Coh2Shapes.

(** Whiskering composes each boundary of a 2-cell with a fixed path.
    Composition is written in traversal order. *)
Definition whisker_l {X: Type} {x y z: X} (p: x = y)
  {q q': y = z} (H: q = q'): p • q = p • q' :=
  f_equal (fun q => p • q) H.

Definition whisker_r {X: Type} {x y z: X}
  {p p': x = y} (H: p = p') (q: y = z): p • q = p' • q :=
  f_equal (fun p => p • q) H.

(** Paste two edge comparisons and assemble their dependent components. *)
Definition sigT_path_paste {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z}
  {h: rew [P] p in u = v} {k: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; h)) (K: b = (= q; k)):
  a • b = (= p • q; h ⊙ k) :=
  (whisker_r H b • whisker_l (= p; h) K)
  • eq_trans_eq_existT_curried p h q k.

(** Transport through a pasting first transports the two component paths,
    then applies the comparison assembling their composite pair path. *)
Lemma sigT_path_paste_dep {A: Type} {P: A -> Type}
  (R: {x: A &T P x} -> Type)
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z}
  {h: rew [P] p in u = v} {k: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; h)) (K: b = (= q; k))
  {r: R (x; u)} {s: R (y; v)} {t: R (z; w)}
  (ha: rew [R] a in r = s) (hb: rew [R] b in s = t):
  rew [fun e => rew [R] e in r = t] sigT_path_paste H K in (ha ⊙ hb) =
  rew [fun e => rew [R] e in r = t] eq_trans_eq_existT_curried p h q k in
    ((rew [fun e => rew [R] e in r = s] H in ha) ⊙
     (rew [fun e => rew [R] e in s = t] K in hb)).
Proof.
  subst a b. unfold sigT_path_paste.
  cbn [whisker_l whisker_r f_equal].
  now rewrite eq_trans_refl_l.
Defined.

(** Sigma path normalization through maps and composition, with the
    corresponding paired-fiber normalizations. *)
Definition sigT_path_map {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  {x y: A} {a: P x} {b: P y}
  {p: x = y} {hp: rew [P] p in a = b}
  {e: (x; a) = (y; b)} (H: e = (= p; hp)):
  f_equal (fun z: {x: A &T P x} => (f z.1; F z.1 z.2)) e =
  (= f_equal f p; sigT_map_eq F hp) :=
  f_equal (fun e => f_equal (fun z: {x: A &T P x} => (f z.1; F z.1 z.2)) e) H •
  f_equal_eq_existT_curried f F p hp.

Lemma sigT_path_map_refl {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  {x y: A} {u: P x} {v: P y} (p: x = y) (hp: rew [P] p in u = v):
  sigT_path_map f F (p := p) (hp := hp) eq_refl =
  f_equal_eq_existT_curried f F p hp.
Proof.
  unfold sigT_path_map. cbn [f_equal]. now apply eq_trans_refl_l.
Defined.

Lemma sigT_path_map_dep {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {a: P x} {b: P y} {p: x = y} {hp: rew [P] p in a = b}
  {e: (x; a) = (y; b)} (H: e = (= p; hp))
  {r: R (x; a)} {s: R (y; b)} (he: rew [R] e in r = s):
  rew [fun e => rew [S] e in V (x; a) r = V (y; b) s]
    sigT_path_map f F H in sigT_map_eq V he =
  rew [fun e => rew [S] e in V (x; a) r = V (y; b) s]
    f_equal_eq_existT_curried f F p hp in
    sigT_map_eq V (rew [fun e => rew [R] e in r = s] H in he).
Proof.
  unfold sigT_path_map.
  rewrite <- rew_compose.
  now rewrite (sigT_map_eq_transport V H).
Defined.

Lemma sigT_dep_path_map_normalize {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {a: P x} {b: P y} {p: x = y} {hp: rew [P] p in a = b}
  {e: (x; a) = (y; b)} (H: e = (= p; hp))
  {r: R (x; a)} {s: R (y; b)} (he: rew [R] e in r = s): sigT_map_eq
    (fun x (uv: {a: P x &T R (x; a)}) => (F x uv.1; V (x; uv.1) uv.2))
    (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp)
      (Hv := rew [fun e => rew [R] e in r = s] H in he)) =
  eq_existT_curried_dep (Q := S) (H := f_equal f p) (Hu := sigT_map_eq F hp)
    (Hv := rew [fun e => rew [S] e in V (x; a) r = V (y; b) s]
      (sigT_path_map f F H) in sigT_map_eq V he).
Proof.
  subst e. destruct hp, p. cbn in he. now destruct he.
Defined.

Lemma sigT_dep_path_map_direct {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {a: P x} {b: P y} {p: x = y} {hp: rew [P] p in a = b}
  {r: R (x; a)} {s: R (y; b)} (he: rew [R] (= p; hp) in r = s): sigT_map_eq
    (fun x (uv: {a: P x &T R (x; a)}) => (F x uv.1; V (x; uv.1) uv.2))
    (eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := he)) =
  eq_existT_curried_dep (Q := S) (H := f_equal f p) (Hu := sigT_map_eq F hp)
    (Hv := rew [fun e => rew [S] e in V (x; a) r = V (y; b) s]
      (f_equal_eq_existT_curried f F p hp) in sigT_map_eq V he).
Proof. now destruct hp, p, he. Defined.

Lemma sigT_dep_path_paste_normalize {A: Type} {P: A -> Type}
  (R: {x: A &T P x} -> Type)
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z} {hp: rew [P] p in u = v} {hq: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; hp)) (K: b = (= q; hq))
  {r: R (x; u)} {s: R (y; v)} {t: R (z; w)}
  (ha: rew [R] a in r = s) (hb: rew [R] b in s = t):
  eq_existT_curried_dep (Q := R) (H := p) (Hu := hp)
    (Hv := rew [fun e => rew [R] e in r = s] H in ha) ⊙
  eq_existT_curried_dep (Q := R) (H := q) (Hu := hq)
    (Hv := rew [fun e => rew [R] e in s = t] K in hb) =
  eq_existT_curried_dep (Q := R) (H := p • q) (Hu := hp ⊙ hq)
    (Hv := rew [fun e => rew [R] e in r = t] (sigT_path_paste H K) in (ha ⊙ hb)).
Proof.
  rewrite (sigT_trans_eq_existT_curried_dep (Q := R)).
  now rewrite sigT_path_paste_dep.
Defined.

Lemma sigT_eq_dep_normalize {X: Type} {P: X -> Type}
  (R: {x: X &T P x} -> Type) {x y: X} {u: P x} {v: P y}
  {p p': x = y} {h: rew [P] p in u = v} {h': rew [P] p' in u = v}
  (H: p = p') (HH: rew [fun e => rew [P] e in u = v] H in h = h')
  {t t': (x; u) = (y; v)} (N: t = (= p; h)) (N': t' = (= p'; h'))
  {r: R (x; u)} {s: R (y; v)}
  (d: rew [R] t in r = s) (d': rew [R] t' in r = s)
  (D: rew [fun e => rew [R] e in r = s]
    (N • (eq_existT_curried_eq H HH • eq_sym N')) in d = d'):
  rew [fun e => rew [fun x => {u: P x &T R (x; u)}] e in (u; r) = (v; s)] H in
    eq_existT_curried_dep (Q := R) (H := p) (Hu := h)
      (Hv := rew [fun e => rew [R] e in r = s] N in d) =
    eq_existT_curried_dep (Q := R) (H := p') (Hu := h')
      (Hv := rew [fun e => rew [R] e in r = s] N' in d').
Proof.
  refine (eq_existT_curried_dep_eq (Q := R) H HH _).
  now exact (rew_conjugate (fun e: (x; u) = (y; v) => rew [R] e in r = s) N
    (eq_existT_curried_eq H HH) N' d d' D).
Defined.

(** Pasting squares written [p • c = a • q], with horizontal edges [a, c]
    and vertical edges [p, q]. *)
Definition square_compose {X: Type} {x0 x1 x2 y0 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = y0} {q: x1 = y1} {r: x2 = y2}
  (H: p • c = a • q) (K: q • d = b • r):
  p • (c • d) = (a • b) • r :=
  eq_trans_assoc p c d •
  (whisker_r H d •
  (eq_sym (eq_trans_assoc a q d) •
  (whisker_l a K • eq_trans_assoc a b r))).

(** Stack two squares along their common horizontal edge. *)
Definition square_stack {X: Type} {x0 x1 y0 y1 z0 z1: X}
  {a: x0 = x1} {c: y0 = y1} {d: z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  (H: p • c = a • q) (K: r • d = c • s):
  (p • r) • d = a • (q • s) :=
  eq_sym (eq_trans_assoc p r d) •
  (whisker_l p K •
  (eq_trans_assoc p c s •
  (whisker_r H s •
  eq_sym (eq_trans_assoc a q s)))).

(** Reverse square boundaries by pasting inverse and cancellation cells. *)
Definition path_cancel_inverse_r {X: Type} {x y z: X}
  (p: x = y) (q: y = z): (p • q) • eq_sym q = p :=
  eq_sym (eq_trans_assoc p q (eq_sym q)) •
    whisker_l p (eq_trans_sym_inv_r q).

Definition square_reverse {X: Type} {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q): q • eq_sym b = eq_sym a • p :=
  whisker_r (eq_sym (eq_trans_sym_cancel_l a q)) (eq_sym b) •
  (whisker_r (whisker_l (eq_sym a) (eq_sym H)) (eq_sym b) •
  (eq_sym (eq_trans_assoc (eq_sym a) (p • b) (eq_sym b)) •
    whisker_l (eq_sym a) (path_cancel_inverse_r p b))).

Lemma square_reverse_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq):
  rew [fun e => rew [P] e in u1 = v0] square_reverse H in
    (hq ⊙ sigT_sym_eq hb) = sigT_sym_eq ha ⊙ hp.
Proof.
  destruct p, q, hp, hq. cbn in H. destruct H, b.
  destruct ha.
  change (eq_refl ⊙ hb = eq_refl) in HH.
  rewrite sigT_trans_eq_refl in HH.
  pose proof (eq_sym (eq_trans_refl_l hb) • HH) as E.
  destruct E. now reflexivity.
Defined.

Definition square_change_horizontal {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (Ha: a' = a) (H: p • b = a • q) (Hb: b' = b):
  p • b' = a' • q :=
  whisker_l p Hb • (H • eq_sym (whisker_r Ha q)).

Lemma square_change_horizontal_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a a': x0 = x1} {b b': y0 = y1}
  {p: x0 = y0} {q: x1 = y1}
  (Ha: a' = a) (H: p • b = a • q) (Hb: b' = b)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [P] b in v0 = v1) (hb': rew [P] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HHa: rew [fun e => rew [P] e in u0 = u1] Ha in ha' = ha)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (HHb: rew [fun e => rew [P] e in v0 = v1] Hb in hb' = hb):
  rew [fun e => rew [P] e in u0 = v1] square_change_horizontal Ha H Hb in
    (hp ⊙ hb') = ha' ⊙ hq.
Proof.
  subst a' b'. cbn [eq_rect] in HHa, HHb. subst ha' hb'.
  unfold square_change_horizontal; cbn [whisker_l whisker_r f_equal eq_sym].
  rewrite eq_trans_refl_l, eq_trans_refl_r. now exact HH.
Defined.


(** Map a square, using the comparison between mapped composites and
    composites of mapped paths on both boundaries. *)
Definition square_map {X Y: Type} (f: X -> Y) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q):
  f_equal f p • f_equal f b = f_equal f a • f_equal f q :=
  eq_sym (eq_trans_map_distr f p b) •
    (f_equal (fun h => f_equal f h) H • eq_trans_map_distr f a q).

(** Dependent paths respect square pasting. *)
Lemma square_compose_dep {X: Type} (P: X -> Type) {x0 x1 x2 y0 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = y0} {q: x1 = y1} {r: x2 = y2}
  (H: p • c = a • q) (K: q • d = b • r)
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: P y0} {v1: P y1} {v2: P y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [P] c in v0 = v1) (hd: rew [P] d in v1 = v2)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in u2 = v2)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = v2] K in (hq ⊙ hd) = hb ⊙ hr):
  rew [fun e => rew [P] e in u0 = v2] square_compose H K in
    (hp ⊙ (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr.
Proof.

  now exact (sigT_trans_eq_assoc_l hp hc hd ⊙
    (sigT_map_eq (f := fun e => e • d)
      (Q := fun e => rew [P] e in u0 = v2)
      (fun (e: x0 = y1) (h: rew [P] e in u0 = v1) => h ⊙ hd) HH ⊙
    (sigT_sym_eq (sigT_trans_eq_assoc_l ha hq hd) ⊙
    (sigT_map_eq (f := fun e => a • e)
      (Q := fun e => rew [P] e in u0 = v2)
      (fun (e: x1 = y2) (h: rew [P] e in u1 = v2) => ha ⊙ h) KK ⊙
      sigT_trans_eq_assoc_l ha hb hr)))).

Defined.

(** Dependent paths respect vertical square pasting. *)
Lemma square_stack_dep {X: Type} (P: X -> Type) {x0 x1 y0 y1 z0 z1: X}
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
  rew [fun e => rew [P] e in u0 = w1] square_stack H K in
    ((hp ⊙ hr) ⊙ hd) = ha ⊙ (hq ⊙ hs).
Proof.

  now exact (sigT_sym_eq (sigT_trans_eq_assoc_l hp hr hd) ⊙
    (sigT_map_eq (f := fun e => p • e)
      (Q := fun e => rew [P] e in u0 = w1)
      (fun (e: y0 = z1) (h: rew [P] e in v0 = w1) => hp ⊙ h) KK ⊙
    (sigT_trans_eq_assoc_l hp hc hs ⊙
    (sigT_map_eq (f := fun e => e • s)
      (Q := fun e => rew [P] e in u0 = w1)
      (fun (e: x0 = y1) (h: rew [P] e in u0 = v1) => h ⊙ hs) HH ⊙
      sigT_sym_eq (sigT_trans_eq_assoc_l ha hq hs))))).

Defined.

(** A dependent map sends a lifted square to the lift of its image. *)
Lemma square_map_dep {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x)) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq):
  rew [fun e => rew [Q] e in F x0 u0 = F y1 v1] square_map f H in
    (sigT_map_eq F hp ⊙ sigT_map_eq F hb) =
  sigT_map_eq F ha ⊙ sigT_map_eq F hq.
Proof.

  now exact (sigT_sym_eq (sigT_map_eq_comp F hp hb) ⊙
    (sigT_map_eq (f := fun e => f_equal f e)
      (Q := fun e => rew [Q] e in F x0 u0 = F y1 v1)
      (fun (e: x0 = y1) (h: rew [P] e in u0 = v1) => sigT_map_eq F h) HH ⊙
      sigT_map_eq_comp F ha hq)).

Defined.

(** Replace the vertical sides of a square by equal paths. *)
Definition square_change_sides {X: Type} {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (H: p • b = a • q) (Hq: q' = q):
  p' • b = a • q' :=
  whisker_r Hp b • (H • eq_sym (whisker_l a Hq)).

Lemma square_change_sides_dep {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p p': x0 = y0} {q q': x1 = y1}
  (Hp: p' = p) (H: p • b = a • q) (Hq: q' = q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hp': rew [P] p' in u0 = v0)
  (hq: rew [P] q in u1 = v1) (hq': rew [P] q' in u1 = v1)
  (HHp: rew [fun e => rew [P] e in u0 = v0] Hp in hp' = hp)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (HHq: rew [fun e => rew [P] e in u1 = v1] Hq in hq' = hq):
  rew [fun e => rew [P] e in u0 = v1] square_change_sides Hp H Hq in
    (hp' ⊙ hb) = ha ⊙ hq'.
Proof.

  now exact (sigT_map_eq (f := fun e => e • b)
    (Q := fun e => rew [P] e in u0 = v1)
    (fun (e: x0 = y0) (h: rew [P] e in u0 = v0) => h ⊙ hb) HHp ⊙
    (HH ⊙ sigT_sym_eq (sigT_map_eq (f := fun e => a • e)
      (Q := fun e => rew [P] e in u0 = v1)
      (fun (e: x1 = y1) (h: rew [P] e in u1 = v1) => ha ⊙ h) HHq))).

Defined.

(** Expand a mapped composite and associate it with a following path. *)
Definition map_compose_tail {X Y: Type} (f: X -> Y)
  {x y z: X} (p: x = y) (q: y = z) {w: Y} (r: f z = w):
  f_equal f (p • q) • r = f_equal f p • (f_equal f q • r) :=
  whisker_r (eq_trans_map_distr f p q) r • eq_sym (eq_trans_assoc _ _ _).

Lemma map_compose_tail_dep {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  (f: X -> Y) (F: forall x, P x -> Q (f x))
  {x y z: X} {p: x = y} {q: y = z} {w: Y} {r: f z = w}
  {u: P x} {v: P y} {s: P z} {t: Q w}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = s)
  (hr: rew [Q] r in F z s = t):
  rew [fun e => rew [Q] e in F x u = t] map_compose_tail f p q r in
    (sigT_map_eq F (hp ⊙ hq) ⊙ hr) =
  sigT_map_eq F hp ⊙ (sigT_map_eq F hq ⊙ hr).
Proof.

  now exact (sigT_map_eq (f := fun e => e • r)
    (Q := fun e => rew [Q] e in F x u = t)
    (fun (e: f x = f z) (h: rew [Q] e in F x u = F z s) => h ⊙ hr)
    (sigT_map_eq_comp F hp hq) ⊙
    sigT_sym_eq (sigT_trans_eq_assoc_l (sigT_map_eq F hp) (sigT_map_eq F hq) hr)).

Defined.

(** A cube compares two square faces [H, K], with [κ] and [λ] comparing
    their lower and upper edges. The vertical edges are shared. *)
Definition square_cube {X: Type} {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q) (K: p • b' = a' • q)
  (κ: b = b') (λ: a = a'): Prop :=
  H • whisker_r λ q = whisker_l p κ • K.

(** A dependent cube compares its two boundary routes after transport
    along the supplied cube. The lifted square faces and both lifted
    caps are independent witnesses over their respective base faces. *)
Definition square_cube_coherence_dep {X: Type} (P: X -> Type)
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
  (Dλ: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'): Prop :=
  rew [fun h => rew [fun e => rew [P] e in u0 = v1] h in (hp ⊙ hb) = ha' ⊙ hq] C in
    (HH ⊙ sigT_map_eq (fun e h => h ⊙ hq) Dλ) =
  sigT_map_eq (fun e h => hp ⊙ h) Dκ ⊙ KK.

Definition square_cube_refl {X: Type} {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q): square_cube H H eq_refl eq_refl :=
  eq_sym (eq_trans_refl_l H).

Definition square_cube_refl_coherence_dep {X: Type} (P: X -> Type)
  {x0 x1 y0 y1: X} {a: x0 = x1} {b: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • b = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  {ha: rew [P] a in u0 = u1} {hb: rew [P] b in v0 = v1}
  {hp: rew [P] p in u0 = v0} {hq: rew [P] q in u1 = v1}
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq):
  square_cube_coherence_dep P H H eq_refl eq_refl (square_cube_refl H)
    ha ha hb hb hp hq HH HH eq_refl eq_refl :=
  sigT_trans_eq_units HH.

Lemma square_family_cube {A X: Type} {x0 x1 y0 y1: X}
  (a: A -> x0 = x1) (b: A -> y0 = y1)
  (p: x0 = y0) (q: x1 = y1)
  (N: forall z, p • b z = a z • q)
  {z z': A} (H: z = z'):
  square_cube (N z) (N z') (f_equal b H) (f_equal a H).
Proof. destruct H. now apply square_cube_refl. Defined.

Lemma square_family_cube_map {A B C X: Type} {x0 x1 y0 y1: X}
  (a0: A -> B) (b0: A -> C)
  (a1: B -> x0 = x1) (b1: C -> y0 = y1)
  (p: x0 = y0) (q: x1 = y1)
  (N: forall z, p • b1 (b0 z) = a1 (a0 z) • q)
  {z z': A} (H: z = z'):
  square_cube (N z) (N z')
    (f_equal b1 (f_equal b0 H)) (f_equal a1 (f_equal a0 H)).
Proof. destruct H. now apply square_cube_refl. Defined.

Definition square_coherence_cube {T X U Y: Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (α: forall t, f (r t) = j (g t)) {t0 t1: T} {p q: t0 = t1} (H: p = q): square_cube
    (eq_sym (square_coherence_fill r g f j α p))
    (eq_sym (square_coherence_fill r g f j α q))
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) H))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) H)) :=
  square_family_cube_map (fun e => f_equal r e) (fun e => f_equal g e)
    (fun e => f_equal f e) (fun e => f_equal j e) (α t0) (α t1)
    (fun e => eq_sym (square_coherence_fill r g f j α e)) H.

Lemma square_coherence_family_cube {A U V X: Type}
  (u: A -> U) (v: A -> V) (f: U -> X) (g: V -> X)
  (K L: forall z, f (u z) = g (v z))
  (H: forall z, K z = L z) {a b: A} (e: a = b):
  square_cube (square_coherence_fill u v f g K e)
    (square_coherence_fill u v f g L e) (H b) (H a).
Proof.
  destruct e. cbn.
  generalize (H a). generalize (L a).
  intros l h. destruct h.
  now apply square_cube_refl.
Defined.

(** Reverse the canonical lifted naturality square by transporting its
    right boundary along the inverse base square. *)
Lemma square_coherence_dep_reverse_fill
  {A B C D: Type} {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x))
  (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x))
  (K: forall x, f (u x) = g (v x))
  (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a))
  {x y: A} (p: x = y) {a: PA x} {b: PA y} (h: rew [PA] p in a = b):
  rew [fun e => rew [PD] e in F (u x) (U x a) = G (v y) (V y b)]
    eq_sym (square_coherence_fill u v f g K p) in
    (HK x a ⊙ sigT_map_eq G (sigT_map_eq V h)) =
  sigT_map_eq F (sigT_map_eq U h) ⊙ HK y b.
Proof.

  now exact (sigT_sym_eq (square_coherence_dep_fill u v f g U V F G K HK p h)).

Defined.

(** A lifted comparison between homotopy families determines the
    dependent naturality cube along a lifted source path. *)
Lemma square_coherence_family_cube_coherence_dep
  {A U V X: Type} {PA: A -> Type} {PU: U -> Type} {PV: V -> Type} {PX: X -> Type}
  (u: A -> U) (v: A -> V) (f: U -> X) (g: V -> X)
  (U': forall a, PA a -> PU (u a)) (V': forall a, PA a -> PV (v a))
  (F: forall x, PU x -> PX (f x)) (G: forall x, PV x -> PX (g x))
  (K L: forall z, f (u z) = g (v z)) (H: forall z, K z = L z)
  (HK: forall z a, rew [PX] K z in F (u z) (U' z a) = G (v z) (V' z a))
  (HL: forall z a, rew [PX] L z in F (u z) (U' z a) = G (v z) (V' z a))
  (HH: forall z a,
    rew [fun e => rew [PX] e in F (u z) (U' z a) = G (v z) (V' z a)] H z in
      HK z a = HL z a)
  {a b: A} (e: a = b) {aa: PA a} {ab: PA b} (he: rew [PA] e in aa = ab):
  square_cube_coherence_dep PX
    (square_coherence_fill u v f g K e) (square_coherence_fill u v f g L e)
    (H b) (H a) (square_coherence_family_cube u v f g K L H e)
    (HK a aa) (HL a aa) (HK b ab) (HL b ab)
    (sigT_map_eq F (sigT_map_eq U' he)) (sigT_map_eq G (sigT_map_eq V' he))
    (square_coherence_dep_fill u v f g U' V' F G K HK e he)
    (square_coherence_dep_fill u v f g U' V' F G L HL e he) (HH b ab) (HH a aa).
Proof.
  destruct e, he.
  cbn [square_coherence_fill square_coherence_dep_fill square_coherence_family_cube
    eq_rect f_equal sigT_map_eq].
  generalize (HH a aa).
  generalize (HL a aa).
  generalize (H a).
  generalize (L a).
  intros l h hl hh. destruct h, hh.
  now apply square_cube_refl_coherence_dep.
Defined.

(** The displayed cube boundary for the naturality squares of a
    comparison homotopy, with a supplied base cube. *)
Definition square_coherence_cube_dep
  {T X U Y: Type} {PT: T -> Type} {PX: X -> Type} {PU: U -> Type} {PY: Y -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (J: forall u, PU u -> PY (j u))
  (α: forall t, f (r t) = j (g t))
  (Dα: forall t a, rew [PY] α t in F (r t) (R t a) = J (g t) (G t a))
  {t0 t1: T} {p q: t0 = t1} (H: p = q) {v0: PT t0} {v1: PT t1}
  (hp: rew [PT] p in v0 = v1) (hq: rew [PT] q in v0 = v1)
  (DH: rew [fun e => rew [PT] e in v0 = v1] H in hp = hq)
  (C: square_cube (eq_sym (square_coherence_fill r g f j α p))
    (eq_sym (square_coherence_fill r g f j α q))
    (f_equal (fun e => f_equal j e) (f_equal (fun e => f_equal g e) H))
    (f_equal (fun e => f_equal f e) (f_equal (fun e => f_equal r e) H))): Prop :=
  square_cube_coherence_dep PY _ _ _ _ C
    (sigT_map_eq F (sigT_map_eq R hp)) (sigT_map_eq F (sigT_map_eq R hq))
    (sigT_map_eq J (sigT_map_eq G hp)) (sigT_map_eq J (sigT_map_eq G hq))
    (Dα t0 v0) (Dα t1 v1)
    (square_coherence_dep_reverse_fill r g f j R G F J α Dα p hp)
    (square_coherence_dep_reverse_fill r g f j R G F J α Dα q hq) (sigT_map_eq
      (fun (e: g t0 = g t1) (h: rew [PU] e in G t0 v0 = G t1 v1) => sigT_map_eq J h) (sigT_map_eq
        (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq G h) DH)) (sigT_map_eq
      (fun (e: r t0 = r t1) (h: rew [PX] e in R t0 v0 = R t1 v1) => sigT_map_eq F h) (sigT_map_eq
        (fun (e: t0 = t1) (h: rew [PT] e in v0 = v1) => sigT_map_eq R h) DH)).

(** A lifted path comparison determines the dependent naturality cube
    of a comparison homotopy. Both map actions remain separate. *)
Lemma square_coherence_cube_dep_fill
  {T X U Y: Type} {PT: T -> Type} {PX: X -> Type} {PU: U -> Type} {PY: Y -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (J: forall u, PU u -> PY (j u))
  (α: forall t, f (r t) = j (g t))
  (Hα: forall t a, rew [PY] α t in F (r t) (R t a) = J (g t) (G t a))
  {t0 t1: T} {p q: t0 = t1} (H: p = q) {a0: PT t0} {a1: PT t1}
  (hp: rew [PT] p in a0 = a1) (hq: rew [PT] q in a0 = a1)
  (HH: rew [fun e => rew [PT] e in a0 = a1] H in hp = hq):
  square_coherence_cube_dep r g f j R G F J α Hα H hp hq HH
    (square_coherence_cube r g f j α H).
Proof.
  destruct H, HH.
  now apply square_cube_refl_coherence_dep.
Defined.

(** A cube is a square in the path space. Prefix and suffix composition
    map the lifted caps into the two vertical edges below; the supplied
    lifted faces are its horizontal edges:

      L hb   -- HH --> R ha
       | L Dκ          | R Dλ
      L hb'  -- KK --> R ha'

    Relative to the ordinary square convention [p • c = a • q], this
    diagram is rotated: its [p, c, a, q] sides are [H], [whisker_r λ q],
    [whisker_l p κ], and [K]. The base lower-cap comparison [κ] therefore
    becomes the upper edge [whisker_l p κ] of this square in the path space.

    The ordinary dependent square fillers exchange the missing edge.
    The corresponding fiber retraction then recovers the requested cap.
    The same construction applies when [P] is a family of path comparisons. *)
Section Transfer.
Context {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q) (K: p • b' = a' • q) (κ: b = b') (λ: a = a')
  (C: square_cube H K κ λ)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [P] b in v0 = v1) (hb': rew [P] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq).

Local Definition L := fun (e: y0 = y1) (h: rew [P] e in v0 = v1) => hp ⊙ h.
Local Definition R := fun (e: x0 = x1) (h: rew [P] e in u0 = u1) => h ⊙ hq.
Local Definition rL := prefix_retraction P p hp v1.
Local Definition rR := suffix_retraction P q hq u0.

(** Both directions use a dependent square filler in the path family. *)
Definition square_cube_dep_upper
  (D: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'):
  rew [fun e => rew [P] e in u0 = u1] λ in ha = ha' :=
  fiber_back (path_retraction rR ha ha') λ
    (sigT_square_fill C HH (sigT_map_eq L D) KK).

Definition square_cube_dep
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  rew [fun e => rew [P] e in v0 = v1] κ in hb = hb' :=
  fiber_back (path_retraction rL hb hb') κ
    (sigT_square_fill_upper C HH (sigT_map_eq R D) KK).

Lemma square_cube_dep_upper_mapped
  (D: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'):
  sigT_map_eq R (square_cube_dep_upper D) =
    sigT_square_fill C HH (sigT_map_eq L D) KK.
Proof.
  now exact (path_retraction_recovery
    rR (suffix_retraction_recovery P q hq u0) ha ha' λ _).
Defined.

Lemma square_cube_dep_mapped
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  sigT_map_eq L (square_cube_dep D) =
    sigT_square_fill_upper C HH (sigT_map_eq R D) KK.
Proof.
  now exact (path_retraction_recovery (prefix_retraction P p hp v1)
    (prefix_retraction_recovery P p hp v1) hb hb' κ _).
Defined.

Lemma square_cube_dep_upper_coherence
  (D: rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'):
  square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK
    D (square_cube_dep_upper D).
Proof.
  unfold square_cube_coherence_dep.
  rewrite square_cube_dep_upper_mapped.
  now exact (sigT_square_fill_boundary C HH (sigT_map_eq L D) KK).
Defined.

Lemma square_cube_dep_coherence
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  square_cube_coherence_dep P H K κ λ C ha ha' hb hb' hp hq HH KK
    (square_cube_dep D) D.
Proof.
  unfold square_cube_coherence_dep.
  rewrite square_cube_dep_mapped.
  now exact (sigT_square_fill_upper_boundary C HH (sigT_map_eq R D) KK).
Defined.

End Transfer.

(** Pasting when the lower edges are images under a map. *)
Definition square_compose_map {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r):
  p • f_equal f (c • d) = (a • b) • r :=
  whisker_l p (eq_trans_map_distr f c d) • square_compose H K.

Lemma square_collapse_map_dep {X Y: Type} (f: Y -> X)
  (P: X -> Type) (Q: Y -> Type) (F: forall y, Q y -> P (f y))
  {x0 x1: X} {y0 y1 y2: Y} {a: x0 = x1}
  {p: x0 = f y0} {q: x1 = f y2} {c: y0 = y1} {d: y1 = y2}
  (H: p • (f_equal f c • f_equal f d) = a • q)
  {u0: P x0} {u1: P x1} {v0: Q y0} {v1: Q y1} {v2: Q y2}
  {ha: rew [P] a in u0 = u1} {hc: rew [Q] c in v0 = v1}
  {hd: rew [Q] d in v1 = v2} {hp: rew [P] p in u0 = F y0 v0}
  {hq: rew [P] q in u1 = F y2 v2}
  (HH: rew [fun e => rew [P] e in u0 = F y2 v2] H in
    (hp ⊙ (sigT_map_eq F hc ⊙ sigT_map_eq F hd)) = ha ⊙ hq):
  rew [fun e => rew [P] e in u0 = F y2 v2]
    (whisker_l p (eq_trans_map_distr f c d) • H) in
    (hp ⊙ sigT_map_eq F (hc ⊙ hd)) = ha ⊙ hq.
Proof.
  now exact (sigT_map_eq
    (fun (e: f y0 = f y2) (h: rew [P] e in F y0 v0 = F y2 v2) => hp ⊙ h)
    (sigT_map_eq_comp F hc hd) ⊙ HH).
Defined.

Lemma square_compose_map_dep {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r)
  {u0: P x0} {u1: P x1} {u2: P x2}
  {v0: P (f y0)} {v1: P (f y1)} {v2: P (f y2)}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [fun y => P (f y)] c in v0 = v1)
  (hd: rew [fun y => P (f y)] d in v1 = v2)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in u2 = v2)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = v2] K in
    (hq ⊙ sigT_map_eq (Q := P) (fun _ u => u) hd) = hb ⊙ hr):
  rew [fun e => rew [P] e in u0 = v2] square_compose_map f H K in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr.
Proof.

  now exact (sigT_map_eq (f := fun e => p • e)
    (Q := fun e => rew [P] e in u0 = v2)
    (fun (e: f y0 = f y2) (h: rew [P] e in v0 = v2) => hp ⊙ h)
    (sigT_map_eq_comp (Q := P) (fun _ a => a) hc hd) ⊙
    square_compose_dep P H K ha hb
      (sigT_map_eq (Q := P) (fun _ a => a) hc)
      (sigT_map_eq (Q := P) (fun _ a => a) hd) hp hq hr HH KK).

Defined.

Lemma square_cube_map_dep {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1: X} {y0 y1: Y}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f b = a • q) (K: p • f_equal f b' = a' • q)
  (κ: b = b') (λ: a = a')
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ)
  {u0: P x0} {u1: P x1} {v0: P (f y0)} {v1: P (f y1)}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [fun y => P (f y)] b in v0 = v1)
  (hb': rew [fun y => P (f y)] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb') = ha' ⊙ hq)
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  rew [fun e => rew [fun y => P (f y)] e in v0 = v1] κ in hb = hb'.
Proof.
  now exact (pullback_comparison_retract f P κ
    (square_cube_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
      ha ha' (sigT_map_eq (Q := P) (fun _ u => u) hb)
      (sigT_map_eq (Q := P) (fun _ u => u) hb') hp hq HH KK D)).
Defined.

(** The mapped cube filler lifts to the original cube filler, preserving
    its chosen boundary proofs. *)
Lemma square_cube_map_dep_mapped {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1: X} {y0 y1: Y}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f b = a • q) (K: p • f_equal f b' = a' • q)
  (κ: b = b') (λ: a = a')
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ)
  {u0: P x0} {u1: P x1} {v0: P (f y0)} {v1: P (f y1)}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [fun y => P (f y)] b in v0 = v1)
  (hb': rew [fun y => P (f y)] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb') = ha' ⊙ hq)
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'): sigT_map_eq
    (fun (e: y0 = y1) (h: rew [fun y => P (f y)] e in v0 = v1) =>
      sigT_map_eq (Q := P) (fun _ u => u) h)
    (square_cube_map_dep f P H K κ λ C ha ha' hb hb' hp hq HH KK D) =
  square_cube_dep P H K (f_equal (fun e => f_equal f e) κ) λ C ha ha'
    (sigT_map_eq (Q := P) (fun _ u => u) hb)
    (sigT_map_eq (Q := P) (fun _ u => u) hb') hp hq HH KK D.
Proof.
  unfold square_cube_map_dep, pullback_comparison_retract.
  now exact (pullback_comparison_recovery f P v0 v1 hb hb' κ _).
Defined.

(** The mapped cube filler satisfies the displayed cube boundary. *)
Lemma square_cube_map_dep_coherence {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1: X} {y0 y1: Y}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f b = a • q) (K: p • f_equal f b' = a' • q)
  (κ: b = b') (λ: a = a')
  (C: square_cube H K (f_equal (fun e => f_equal f e) κ) λ)
  {u0: P x0} {u1: P x1} {v0: P (f y0)} {v1: P (f y1)}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [fun y => P (f y)] b in v0 = v1)
  (hb': rew [fun y => P (f y)] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb') = ha' ⊙ hq)
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  square_cube_coherence_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq (Q := P) (fun _ u => u) hb)
    (sigT_map_eq (Q := P) (fun _ u => u) hb') hp hq HH KK (sigT_map_eq
      (fun (e: y0 = y1) (h: rew [fun y => P (f y)] e in v0 = v1) =>
        sigT_map_eq (Q := P) (fun _ u => u) h)
      (square_cube_map_dep f P H K κ λ C ha ha' hb hb' hp hq HH KK D)) D.
Proof.
  unfold square_cube_coherence_dep.
  rewrite square_cube_map_dep_mapped.
  now exact (square_cube_dep_coherence P H K _ λ C ha ha'
    (sigT_map_eq (Q := P) (fun _ u => u) hb)
    (sigT_map_eq (Q := P) (fun _ u => u) hb') hp hq HH KK D).
Defined.

(** The layer-coherence path fills its defining square. *)
Lemma layer_square {V V' W X: Type} {S: V -> Type} {S': V' -> Type} {P: X -> Type}
  (f: V -> X) (g: V' -> X) (d: W -> X)
  (F: forall v, S v -> P (f v)) (G: forall v, S' v -> P (g v))
  {m1 m2: V} {n1 n2: V'} (l: m1 = m2) (r: n1 = n2)
  {w1 w2: W} (e: w1 = w2)
  (c: f m2 = d w1) (c': g n2 = d w2) (k: f m1 = g n1)
  {a: S m1} {b: S' n1} (h: rew [P] k in F m1 a = G n1 b)
  (H: hexagonal_coherence f d g l e r c k c'):
  rew [fun e => rew [P] e in F m1 a = rew [P] c' in G n2 (rew [S'] r in b)] H in
    ((sigT_map_eq F (p := l) (u := a) eq_refl ⊙ eq_refl) ⊙
      sigT_map_eq (Q := P) (fun _ u => u)
       (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G) (E1 := e)
         (C2 := l) (D2 := r) (C1 := c) (D1 := c') h H)) =
    h ⊙ (sigT_map_eq G (p := r) (u := b) eq_refl ⊙ eq_refl).
Proof.
  unfold rew_cohLayer_hex.
  rewrite (pullback_path_retraction_recovery d P _ _ e _).
  now apply sigT_square_fill_boundary.
Defined.

(** Map a square and stack it with an explicit naturality square. *)
Definition square_map_along {T X U Y: Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (α: forall t, f (r t) = j (g t))
  {t0 t1: T} (e: t0 = t1) {x0 x1: X} {a: x0 = x1}
  {p: x0 = r t0} {q: x1 = r t1}
  (H: p • f_equal r e = a • q) (N: square_coherence r g f j α e) :=
  square_stack (square_map f H) (eq_sym N).

(** The dependent lift uses the supplied lift of each square. *)
Lemma square_map_along_dep {T X U Y: Type}
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
    (hα0 ⊙ hd) = sigT_map_eq F hb ⊙ hα1):
  rew [fun b => rew [Q] b in F x0 u0 = w1]
    (square_map_along r g f j α e H N) in
    ((sigT_map_eq F hp ⊙ hα0) ⊙ hd) =
  sigT_map_eq F ha ⊙ (sigT_map_eq F hq ⊙ hα1).
Proof.
  unfold square_map_along.
  eapply square_stack_dep.
  - now exact (square_map_dep f F H ha hb hp hq HH).
  - now exact NN.
Defined.

(** Extend a square along an explicit naturality square. The actions of
    the two successive maps remain separate on each side. *)
Definition square_nat_along {Z U V X: Type}
  (L: Z -> U) (R: Z -> V) (f: U -> X) (g: V -> X)
  (k: forall z, f (L z) = g (R z))
  {z0 z1: Z} (e: z0 = z1) {y0 y1: X} {b: y0 = y1}
  {p: f (L z1) = y0} {q: g (R z1) = y1}
  (H: p • b = k z1 • q) (N: square_coherence L R f g k e) :=
  square_stack N H.

Lemma square_nat_along_dep {Z U V X: Type}
  (L: Z -> U) (R: Z -> V) (f: U -> X) (g: V -> X)
  (k: forall z, f (L z) = g (R z))
  (P: X -> Type) {z0 z1: Z} (e: z0 = z1)
  {y0 y1: X} {b: y0 = y1}
  {p: f (L z1) = y0} {q: g (R z1) = y1}
  (H: p • b = k z1 • q) (N: square_coherence L R f g k e)
  {u0: P (f (L z0))} {u1: P (g (R z0))}
  {v0: P (f (L z1))} {v1: P (g (R z1))} {w0: P y0} {w1: P y1}
  (ha: rew [P] k z0 in u0 = u1) (hc: rew [P] k z1 in v0 = v1)
  (hb: rew [P] b in w0 = w1)
  (hL: rew [P] f_equal f (f_equal L e) in u0 = v0)
  (hR: rew [P] f_equal g (f_equal R e) in u1 = v1)
  (hp: rew [P] p in v0 = w0) (hq: rew [P] q in v1 = w1)
  (HH: rew [fun b => rew [P] b in v0 = w1] H in (hp ⊙ hb) = hc ⊙ hq)
  (NN: rew [fun b => rew [P] b in u0 = v1] N in (hL ⊙ hc) = ha ⊙ hR):
  rew [fun b => rew [P] b in u0 = w1]
    (square_nat_along L R f g k e H N) in
    ((hL ⊙ hp) ⊙ hb) = ha ⊙ (hR ⊙ hq).
Proof.
  unfold square_nat_along.
  now exact (square_stack_dep P N H ha hc hb hL hR hp hq NN HH).
Defined.

(** Map a layer-coherence cell, then use the naturality of [α] to identify
    its transported endpoints. *)
Definition layer_square_map
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: hexagonal_coherence s r t p e q v k w)
  (Hnat: square_coherence r g f j α e):
  (f_equal f (f_equal s p • v) • α d) • f_equal j (f_equal g e) =
  f_equal f k • (f_equal f (f_equal t q • w) • α d').
Proof.
  now exact (square_map_along r g f j α e H Hnat).
Defined.


(** Extend a layer-coherence cell along a path in its source, using the
    naturality of the frame and dependent-path coherences. *)
Definition layer_square_nat {Z V V': Type} {W X: Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (k: forall z, f (L z) = g (R z))
  {z1 z2: Z} (p: z1 = z2)
  {m: V} {n: V'} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: hexagonal_coherence f d g l e r c (k z2) c')
  (Hnat: square_coherence L R f g k p):
  (f_equal f (f_equal L p • l) • c) • f_equal d e =
    k z1 • (f_equal g (f_equal R p • r) • c').
Proof.
  now exact (square_change_sides (map_compose_tail f (f_equal L p) l c)
    (square_nat_along L R f g k p H Hnat)
    (map_compose_tail g (f_equal R p) r c')).
Defined.


(** Changing the endpoints of a dependent path. Each correction goes from
    the new endpoint to the old one. *)
Definition dpath_change {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a a': P x} {b b': P y} (s: a' = a)
  (h: rew [P] p in a = b) (t: b' = b):
  rew [P] p in a' = b' :=
  f_equal (fun a => rew [P] p in a) s • (h • eq_sym t).

(** The two copies of the middle endpoint correction cancel in a composite. *)
Lemma dpath_change_comp {X: Type} {P: X -> Type} {x y z: X} {p: x = y} {q: y = z}
  {a a': P x} {b b': P y} {c c': P z}
  (s: a' = a) (t: b' = b) (u: c' = c)
  (h: rew [P] p in a = b) (k: rew [P] q in b = c):
  dpath_change s h t ⊙ dpath_change t k u = dpath_change s (h ⊙ k) u.
Proof.
  destruct s, t, u. unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite 3 eq_trans_refl_l, 3 eq_trans_refl_r.
Defined.

Lemma dpath_change_map {X Y: Type} {P: X -> Type} {Q: Y -> Type} {f: X -> Y}
  (g: forall x, P x -> Q (f x)) {x y: X} {p: x = y}
  {a a': P x} {b b': P y} (s: a' = a) (t: b' = b)
  (h: rew [P] p in a = b):
  sigT_map_eq g (dpath_change s h t) =
  dpath_change (f_equal (g x) s) (sigT_map_eq g h) (f_equal (g y) t).
Proof.
  destruct s, t. unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite 2 eq_trans_refl_l, 2 eq_trans_refl_r.
Defined.

Lemma dpath_change_cell {X: Type} {P: X -> Type} {x y: X} {p q: x = y}
  {a a': P x} {b b': P y} (s: a' = a) (t: b' = b) (K: p = q)
  (h: rew [P] p in a = b) (k: rew [P] q in a = b):
  rew [fun e => rew [P] e in a = b] K in h = k ->
  rew [fun e => rew [P] e in a' = b'] K in dpath_change s h t =
  dpath_change s k t.
Proof.
  intro H. refine (map_subst (fun e h => dpath_change s h t) K h • _).
  now exact (f_equal (fun h => dpath_change s h t) H).
Defined.

Lemma dpath_change_natural {X A: Type} {P: X -> Type} {x y: X} {p: x = y}
  (f: A -> P x) (g: A -> P y) (H: forall a, rew [P] p in f a = g a)
  {a a': A} (s: a' = a):
  dpath_change (f_equal f s) (H a) (f_equal g s) = H a'.
Proof.
  unfold dpath_change.
  rewrite eq_trans_assoc.
  rewrite (square_coherence_fill f g (fun v => rew [P] p in v) (fun v => v) H s).
  rewrite f_equal_id, <- eq_trans_assoc, eq_trans_sym_inv_r.
  now apply eq_trans_refl_r.
Defined.

(** Successive changes of endpoints compose their correction paths. *)
Lemma dpath_change_nest {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a a' a'': P x} {b b' b'': P y}
  (s: a' = a) (s': a'' = a') (t: b' = b) (t': b'' = b')
  (h: rew [P] p in a = b):
  dpath_change s' (dpath_change s h t) t' =
  dpath_change (s' • s) h (t' • t).
Proof.
  destruct s', s, t', t. unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite 4 eq_trans_refl_l, 3 eq_trans_refl_r.
Defined.

Lemma dpath_change_id {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a: P x} {b: P y} (h: rew [P] p in a = b):
  dpath_change eq_refl h eq_refl = h.
Proof.
  unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite eq_trans_refl_l, eq_trans_refl_r.
Defined.

Lemma dpath_change_refl {X: Type} {P: X -> Type} {x y: X} (p: x = y)
  (a: P x) {b: P y} (t: b = rew [P] p in a):
  dpath_change (p := p) eq_refl eq_refl t = eq_sym t.
Proof.
  unfold dpath_change; cbn [f_equal]. now rewrite 2 eq_trans_refl_l.
Defined.

(** Changing the source of a reflexive dependent path cancels the
    transported source correction in its target correction. *)
Lemma dpath_change_transport {X: Type} {P: X -> Type} {x y: X} (p: x = y)
  {a a': P x} (s: a' = a) {b: P y} (t: b = rew [P] p in a'):
  dpath_change s (p := p) eq_refl
    (t • f_equal (fun a => rew [P] p in a) s) = eq_sym t.
Proof.
  destruct s. cbn [f_equal].
  rewrite eq_trans_refl_r. now apply dpath_change_refl.
Defined.

(** A dependent map over a fixed base acts on paths without reindexing the base. *)
Definition dpath_map {X: Type} {P Q: X -> Type} (g: forall x, P x -> Q x)
  {x y: X} {p: x = y} {a: P x} {b: P y} (h: rew [P] p in a = b):
  rew [Q] p in g x a = g y b :=
  map_subst g p a • f_equal (g y) h.

Lemma dpath_map_comp {X: Type} {P Q: X -> Type} (g: forall x, P x -> Q x)
  {x y z: X} {p: x = y} {q: y = z} {a: P x} {b: P y} {c: P z}
  (h: rew [P] p in a = b) (k: rew [P] q in b = c):
  dpath_map g (h ⊙ k) = dpath_map g h ⊙ dpath_map g k.
Proof.
  now destruct p, q, h, k.
Defined.

(** A square of dependent maps commutes on paths, with its endpoint squares. *)
Lemma dpath_map_square {X Y: Type} {P P': X -> Type} {Q Q': Y -> Type} {f: X -> Y}
  (e: forall x, P x -> P' x) (e': forall y, Q y -> Q' y)
  (g: forall x, P x -> Q (f x)) (g': forall x, P' x -> Q' (f x))
  (N: forall x a, e' (f x) (g x a) = g' x (e x a))
  {x y: X} {p: x = y} {a: P x} {b: P y} (h: rew [P] p in a = b):
  dpath_map e' (sigT_map_eq g h) =
  dpath_change (N x a) (sigT_map_eq g' (dpath_map e h)) (N y b).
Proof.
  destruct p, h. unfold dpath_map, dpath_change; cbn.
  now rewrite eq_trans_refl_l, f_equal_id, eq_trans_sym_inv_r.
Defined.

(** Separating the reindexing of the base from the action in each fibre. *)
Lemma sigT_map_eq_dpath_map {X Y: Type} {P: X -> Type} {Q: Y -> Type} {f: X -> Y}
  (g: forall x, P x -> Q (f x)) {x y: X} {p: x = y}
  {a: P x} {b: P y} (h: rew [P] p in a = b):
  sigT_map_eq g h = eq_sym (rew_map Q f p (g x a)) • dpath_map g h.
Proof.
  now destruct p, h.
Defined.

Local Definition map_three {X Y: Type} (f: X -> Y)
  {x0 x1 x2 x3: X} (p: x0 = x1) (q: x1 = x2) (r: x2 = x3):
  f_equal f (p • (q • r)) =
    f_equal f p • (f_equal f q • f_equal f r) :=
  eq_trans_map_distr f p (q • r) •
    whisker_l (f_equal f p) (eq_trans_map_distr f q r).

Local Definition map_three_left {X Y: Type} (f: X -> Y)
  {x0 x1 x2 x3: X} (p: x0 = x1) (q: x1 = x2) (r: x2 = x3):
  f_equal f ((p • q) • r) =
    (f_equal f p • f_equal f q) • f_equal f r :=
  eq_trans_map_distr f (p • q) r •
    whisker_r (eq_trans_map_distr f p q) (f_equal f r).

(** Map the two three-edge routes of a hexagon, expanding the action on
    composition and preserving the association of each route. *)
Definition hexagon_map {X Y: Type} (f: X -> Y)
  {x0 x1 x2 x3 x4 x5: X}
  {p1: x0 = x1} {p2: x1 = x2} {p3: x2 = x3}
  {q1: x0 = x4} {q2: x4 = x5} {q3: x5 = x3}
  (H: (p1 • p2) • p3 = q1 • (q2 • q3)):
  (f_equal f p1 • f_equal f p2) • f_equal f p3 =
  f_equal f q1 • (f_equal f q2 • f_equal f q3) :=
  eq_sym (map_three_left f p1 p2 p3) •
    (f_equal (fun e => f_equal f e) H • map_three f q1 q2 q3).

(** Map a supplied lifted square and stack the canonical dependent
    naturality square of the comparison homotopy. *)
Definition square_map_along_coherence_dep {T X U Y: Type}
  {PT: T -> Type} {PX: X -> Type} {PU: U -> Type} {PY: Y -> Type}
  (r: T -> X) (g: T -> U) (f: X -> Y) (j: U -> Y)
  (R: forall t, PT t -> PX (r t)) (G: forall t, PT t -> PU (g t))
  (F: forall x, PX x -> PY (f x)) (J: forall u, PU u -> PY (j u))
  (α: forall t, f (r t) = j (g t))
  (Hα: forall t a, rew [PY] α t in F (r t) (R t a) = J (g t) (G t a))
  {t0 t1: T} (b: t0 = t1) {x0 x1: X} {a: x0 = x1}
  {p: x0 = r t0} {q: x1 = r t1} (H: p • f_equal r b = a • q)
  {u0: PX x0} {u1: PX x1} {v0: PT t0} {v1: PT t1}
  {ha: rew [PX] a in u0 = u1} (hb: rew [PT] b in v0 = v1)
  {hp: rew [PX] p in u0 = R t0 v0} {hq: rew [PX] q in u1 = R t1 v1}
  (HH: rew [fun e => rew [PX] e in u0 = R t1 v1] H in
    (hp ⊙ sigT_map_eq R hb) = ha ⊙ hq):
  rew [fun e => rew [PY] e in F x0 u0 = J (g t1) (G t1 v1)]
    square_map_along r g f j α b H (square_coherence_fill r g f j α b) in
    ((sigT_map_eq F hp ⊙ Hα t0 v0) ⊙ sigT_map_eq J (sigT_map_eq G hb)) =
  sigT_map_eq F ha ⊙ (sigT_map_eq F hq ⊙ Hα t1 v1) :=
  square_map_along_dep r g f j α PX PY F b H (square_coherence_fill r g f j α b)
    ha (sigT_map_eq R hb) hp hq (Hα t0 v0) (Hα t1 v1)
    (sigT_map_eq J (sigT_map_eq G hb)) HH
    (square_coherence_dep_reverse_fill r g f j R G F J α Hα b hb).

Definition square_nat_along_coherence_dep {Z U V X: Type}
  {PZ: Z -> Type} {PU: U -> Type} {PV: V -> Type} {PX: X -> Type}
  (L: Z -> U) (R: Z -> V) (f: U -> X) (g: V -> X)
  (DL: forall z, PZ z -> PU (L z)) (DR: forall z, PZ z -> PV (R z))
  (F: forall u, PU u -> PX (f u)) (G: forall v, PV v -> PX (g v))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [PX] k z in F (L z) (DL z a) = G (R z) (DR z a))
  {z0 z1: Z} (e: z0 = z1) {y0 y1: X} {b: y0 = y1}
  {p: f (L z1) = y0} {q: g (R z1) = y1} (H: p • b = k z1 • q)
  {a0: PZ z0} {a1: PZ z1} (he: rew [PZ] e in a0 = a1)
  {w0: PX y0} {w1: PX y1} {hb: rew [PX] b in w0 = w1}
  {hp: rew [PX] p in F (L z1) (DL z1 a1) = w0}
  {hq: rew [PX] q in G (R z1) (DR z1 a1) = w1}
  (HH: rew [fun e => rew [PX] e in F (L z1) (DL z1 a1) = w1] H in
    (hp ⊙ hb) = hk z1 a1 ⊙ hq):
  rew [fun e => rew [PX] e in F (L z0) (DL z0 a0) = w1]
    square_nat_along L R f g k e H (square_coherence_fill L R f g k e) in
    ((sigT_map_eq F (sigT_map_eq DL he) ⊙ hp) ⊙ hb) =
  hk z0 a0 ⊙ (sigT_map_eq G (sigT_map_eq DR he) ⊙ hq) :=
  square_nat_along_dep L R f g k PX e H (square_coherence_fill L R f g k e)
    (hk z0 a0) (hk z1 a1) hb (sigT_map_eq F (sigT_map_eq DL he))
    (sigT_map_eq G (sigT_map_eq DR he)) hp hq HH
    (square_coherence_dep_fill L R f g DL DR F G k hk e he).

Lemma layer_square_map_coherence_dep
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
  (HH: hexagonal_coherence_dep S R T' H hp he hq hv hk hw):
  rew [fun h => rew [Q] h in F (s m) (S m am) = J (g d') (G d' ad')]
    layer_square_map r s t f g j α e p q v w k H
      (square_coherence_fill r g f j α e) in
    ((sigT_map_eq F (sigT_map_eq S hp ⊙ hv) ⊙ Hα d ad) ⊙
      sigT_map_eq J (sigT_map_eq G he)) =
  sigT_map_eq F hk ⊙
    (sigT_map_eq F (sigT_map_eq T' hq ⊙ hw) ⊙ Hα d' ad').
Proof.
  unfold layer_square_map.
  now exact (square_map_along_coherence_dep r g f j R G F J α Hα e H he (HH)).
Defined.

(** Extend an arbitrary lifted hexagon along a source path, using the
    canonical dependent naturality square of its connecting homotopy. *)
Lemma layer_square_nat_coherence_dep
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
  (HH: hexagonal_coherence_dep F D G H hl he hr hc (hk z2 a2) hc'):
  rew [fun h => rew [P] h in F (L z1) (RL z1 a1) = D w2 aw2]
    layer_square_nat L R f g d k p l r e c c' H
      (square_coherence_fill L R f g k p) in
    ((sigT_map_eq F (sigT_map_eq RL hp ⊙ hl) ⊙ hc) ⊙ sigT_map_eq D he) =
  hk z1 a1 ⊙ (sigT_map_eq G (sigT_map_eq RR hp ⊙ hr) ⊙ hc').
Proof.
  unfold layer_square_nat.
  eapply square_change_sides_dep.
  - now apply map_compose_tail_dep.
  - now exact (square_nat_along_coherence_dep L R f g RL RR F G k hk p H hp (HH)).
  - now apply map_compose_tail_dep.
Defined.

(** Canonical layer lifts specialize the arbitrary lifts to the identity
    map on the middle fiber. *)
Lemma layer_square_map_dep
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  (P: X -> Type) (Q: Y -> Type) (PM: M -> Type) (PN: N -> Type)
  (F: forall x, P x -> Q (f x))
  (L: forall m, PM m -> P (s m)) (R: forall n, PN n -> P (t n))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: hexagonal_coherence s r t p e q v k w)
  {a: PM m} {b: PN n} (h: rew [P] k in L m a = R n b):
  rew [fun e => rew [Q] e in F (s m) (L m a) =
    rew [Q] α d' in F (r d') (rew [P] w in R n' (rew [PN] q in b))]
    layer_square_map r s t f g j α e p q v w k H
      (square_coherence_fill r g f j α e) in
  ((sigT_map_eq F (sigT_map_eq L (p := p) (u := a) eq_refl ⊙ eq_refl) ⊙ eq_refl)
    ⊙ sigT_map_eq (Q := Q) (fun _ u => u)
      (sigT_map_eq (Q := fun u => Q (j u))
        (fun dd x => rew [Q] α dd in F (r dd) x)
        (rew_cohLayer_hex (P := P) (rf0 := r) (F := L) (G := R)
          (E1 := e) (C2 := p) (D2 := q) (C1 := v) (D1 := w) h H))) =
  sigT_map_eq F h ⊙
    (sigT_map_eq F (sigT_map_eq R (p := q) (u := b) eq_refl ⊙ eq_refl) ⊙ eq_refl).
Proof.
  now exact (layer_square_map_coherence_dep r s t f g j
    (fun _ u => u) L R F
    (fun dd x => rew [Q] α dd in F (r dd) x) (fun _ u => u)
    α (fun _ _ => eq_refl) e p q v w k H
    (rew_cohLayer_hex (P := P) (rf0 := r) (F := L) (G := R)
      (E1 := e) (C2 := p) (D2 := q) (C1 := v) (D1 := w) h H)
    eq_refl eq_refl eq_refl eq_refl h
    (layer_square s t r L R p q e v w k h H)).
Defined.

Lemma layer_square_nat_dep {Z V V': Type} {W X: Type}
  {S: Z -> Type} {QL: V -> Type} {QR: V' -> Type} {P: X -> Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (RL: forall z, S z -> QL (L z)) (RR: forall z, S z -> QR (R z))
  (F: forall v, QL v -> P (f v)) (G: forall v, QR v -> P (g v))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [P] k z in F (L z) (RL z a) = G (R z) (RR z a))
  {z1 z2: Z} (p: z1 = z2)
  {m: V} {n: V'} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: hexagonal_coherence f d g l e r c (k z2) c') (a: S z1):
  rew [fun e => rew [P] e in F (L z1) (RL z1 a) =
    rew [P] c' in G n (rew [QR] r in RR z2 (rew [S] p in a))]
    layer_square_nat L R f g d k p l r e c c' H
      (square_coherence_fill L R f g k p) in ((sigT_map_eq F
       (sigT_map_eq RL (p := p) (u := a) eq_refl ⊙
         (eq_refl: rew [QL] l in RL z2 (rew [S] p in a) = _)) ⊙ eq_refl) ⊙
     sigT_map_eq (Q := P) (fun _ u => u)
       (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G) (E1 := e)
          (C2 := l) (D2 := r) (C1 := c) (D1 := c')
          (hk z2 (rew [S] p in a)) H)) = hk z1 a ⊙ (sigT_map_eq G
        (sigT_map_eq RR (p := p) (u := a) eq_refl ⊙
          (eq_refl: rew [QR] r in RR z2 (rew [S] p in a) = _)) ⊙ eq_refl).
Proof.
  now exact (layer_square_nat_coherence_dep L R f g d RL RR F G (fun _ u => u) k hk
    p l r e c c' H eq_refl eq_refl eq_refl
    (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G)
      (E1 := e) (C2 := l) (D2 := r) (C1 := c) (D1 := c')
      (hk z2 (rew [S] p in a)) H) eq_refl eq_refl
    (layer_square f g d F G l r e c c' (k z2)
      (hk z2 (rew [S] p in a)) H)).
Defined.

(** Paste lifted squares whose lower edges are images under a dependent
    map between arbitrary fiber families. *)
Lemma square_compose_map_coherence_dep {X Y: Type} (f: Y -> X) (P: X -> Type) (Q: Y -> Type)
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
  rew [fun e => rew [P] e in u0 = F y2 v2] square_compose_map f H K in
    (hp ⊙ sigT_map_eq F (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr.
Proof.

  now exact (sigT_map_eq (f := fun e => p • e)
    (Q := fun e => rew [P] e in u0 = F y2 v2)
    (fun (e: f y0 = f y2) (h: rew [P] e in F y0 v0 = F y2 v2) => hp ⊙ h)
    (sigT_map_eq_comp F hc hd) ⊙
    square_compose_dep P H K ha hb (sigT_map_eq F hc) (sigT_map_eq F hd)
      hp hq hr HH KK).

Defined.

(** Combine edge normalizations with pairing, composition, and mapping. *)

Definition sigT_pair_path_paste {A: Type} {P: A -> Type}
  (R: {x: A &T P x} -> Type)
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z} {hp: rew [P] p in u = v} {hq: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; hp)) (K: b = (= q; hq))
  {r: R (x; u)} {s: R (y; v)} {t: R (z; w)}
  (ha: rew [R] a in r = s) (hb: rew [R] b in s = t)
  {da: rew [fun x => {u: P x &T R (x; u)}] p in (u; r) = (v; s)}
  {db: rew [fun x => {u: P x &T R (x; u)}] q in (v; s) = (w; t)}
  (Ea: da = eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r = s] H in ha))
  (Eb: db = eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in s = t] K in hb)):
  da ⊙ db = eq_existT_curried_dep (Q := R) (H := p • q) (Hu := hp ⊙ hq)
    (Hv := rew [fun e => rew [R] e in r = t] (sigT_path_paste H K) in (ha ⊙ hb)) :=
  path_map2 (fun h k => h ⊙ k) Ea Eb • sigT_dep_path_paste_normalize R H K ha hb.

Definition sigT_pair_path_map {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {u: P x} {v: P y} {p: x = y} {hp: rew [P] p in u = v}
  {a: (x; u) = (y; v)} (H: a = (= p; hp))
  {r: R (x; u)} {s: R (y; v)} (ha: rew [R] a in r = s)
  {da: rew [fun x => {u: P x &T R (x; u)}] p in (u; r) = (v; s)}
  (Ea: da = eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r = s] H in ha)):
  sigT_map_eq (fun x (uv: {u: P x &T R (x; u)}) => (F x uv.1; V (x; uv.1) uv.2)) da =
  eq_existT_curried_dep (Q := S) (H := f_equal f p) (Hu := sigT_map_eq F hp)
    (Hv := rew [fun e => rew [S] e in V (x; u) r = V (y; v) s] (sigT_path_map f F H) in sigT_map_eq V ha) :=
  f_equal (fun h => sigT_map_eq (fun x (uv: {u: P x &T R (x; u)}) => (F x uv.1; V (x; uv.1) uv.2)) h) Ea •
    sigT_dep_path_map_normalize f F R S V H ha.

Lemma sigT_pair_path_map_encoded {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {a: P x} {b: P y} {p: x = y} {hp: rew [P] p in a = b}
  {e: (x; a) = (y; b)} (H: e = (= p; hp))
  {r: R (x; a)} {s: R (y; b)} (he: rew [R] e in r = s):
  sigT_pair_path_map f F R S V H he eq_refl =
  sigT_dep_path_map_normalize f F R S V H he.
Proof.
  unfold sigT_pair_path_map. cbn [f_equal]. now apply eq_trans_refl_l.
Defined.

Lemma sigT_dep_path_map_refl_computation {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (F: forall x, P x -> Q (f x))
  (R: {x: A &T P x} -> Type) (S: {y: B &T Q y} -> Type)
  (V: forall z, R z -> S (f z.1; F z.1 z.2))
  {x y: A} {a: P x} {b: P y} {p: x = y} {hp: rew [P] p in a = b}
  {r: R (x; a)} {s: R (y; b)} (he: rew [R] (= p; hp) in r = s):
  sigT_dep_path_map_normalize f F R S V (p := p) (hp := hp) eq_refl he =
  sigT_dep_path_map_direct f F R S V he •
    f_equal (fun n => eq_existT_curried_dep (Q := S) (H := f_equal f p) (Hu := sigT_map_eq F hp)
      (Hv := rew [fun e => rew [S] e in V (x; a) r = V (y; b) s] n in sigT_map_eq V he))
      (eq_sym (sigT_path_map_refl f F p hp)).
Proof. now destruct hp, p, he. Defined.

Lemma sigT_pair_path_paste_change_right {A: Type} {P: A -> Type}
  (R: {x: A &T P x} -> Type)
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z} {hp: rew [P] p in u = v} {hq: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; hp)) (K K1: b = (= q; hq)) (E: K = K1)
  {r: R (x; u)} {s: R (y; v)} {t: R (z; w)}
  (ha: rew [R] a in r = s) (hb: rew [R] b in s = t)
  {da: rew [fun x => {u: P x &T R (x; u)}] p in (u; r) = (v; s)}
  {db: rew [fun x => {u: P x &T R (x; u)}] q in (v; s) = (w; t)}
  (Ea: da = eq_existT_curried_dep (Q := R) (H := p) (Hu := hp) (Hv := rew [fun e => rew [R] e in r = s] H in ha))
  (Eb: db = eq_existT_curried_dep (Q := R) (H := q) (Hu := hq) (Hv := rew [fun e => rew [R] e in s = t] K in hb)):
  sigT_pair_path_paste R H K1 ha hb Ea
    (Eb • f_equal (fun n => eq_existT_curried_dep (Q := R) (H := q) (Hu := hq)
      (Hv := rew [fun e => rew [R] e in s = t] n in hb)) E) =
  sigT_pair_path_paste R H K ha hb Ea Eb •
    f_equal (fun n => eq_existT_curried_dep (Q := R) (H := p • q) (Hu := hp ⊙ hq)
      (Hv := rew [fun e => rew [R] e in r = t] n in (ha ⊙ hb)))
      (f_equal (fun n => sigT_path_paste H n) E).
Proof.
  destruct E. cbn [f_equal]. rewrite 2 eq_trans_refl_r. now reflexivity.
Defined.
