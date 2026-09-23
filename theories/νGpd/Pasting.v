(** Pasting path comparisons, squares, and layer-coherence cells,
    with their dependent lifts. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas.

(** Whiskering composes each boundary of a 2-cell with a fixed path.
    Composition is written in traversal order. *)
Definition whisker_l {X: Type} {x y z: X} (p: x = y)
  {q q': y = z} (H: q = q'): p • q = p • q' :=
  f_equal (fun q => p • q) H.

Definition whisker_r {X: Type} {x y z: X}
  {p p': x = y} (H: p = p') (q: y = z): p • q = p' • q :=
  f_equal (fun p => p • q) H.

(** Change a path's endpoints along comparisons pointing to its old vertices. *)
Definition path_change {X: Type} {x y x' y': X}
  (s: x' = x) (p: x = y) (t: y' = y): x' = y' :=
  s • (p • eq_sym t).

(** Reindex a path at its source. An identity correction returns the
    supplied path by computation, even when that path is a variable. *)
Definition path_reindex_source {A: Type} {x x' y: A}
  (c: x' = x) (r: x = y): x' = y :=
  rew [fun z => z = y] eq_sym c in r.

(** Lift the same source correction to a dependent path. The frame and
    fibre corrections reduce together when both are identities. *)
Definition path_reindex_source_dep {A: Type} (P: A -> Type) {x x' y: A}
  (c: x' = x) (r: x = y) (u: P x) (u': P x') (v: P y)
  (E: u' = rew [P] eq_sym c in u) (h: rew [P] r in u = v):
  rew [P] path_reindex_source c r in u' = v.
Proof.
  destruct c; cbn in E |- *.
  destruct E.
  now exact h.
Defined.

(** Compare two paths with a common target using their given witnesses. *)
Definition path_compare_target {A: Type} {x y z: A} (s: x = z) (t: y = z):
  x = y := s • eq_sym t.

(** Matching endpoint comparisons cancel when paths are pasted. *)
Lemma path_change_comp {X: Type} {x y z x' y' z': X}
  (s: x' = x) (t: y' = y) (u: z' = z) (p: x = y) (q: y = z):
  path_change s p t • path_change t q u = path_change s (p • q) u.
Proof.
  unfold path_change.
  rewrite <- 3 eq_trans_assoc.
  now rewrite eq_trans_sym_cancel_l.
Defined.

Lemma path_change_sym {X: Type} {x y x' y': X}
  (s: x' = x) (p: x = y) (t: y' = y):
  eq_sym (path_change s p t) = path_change t (eq_sym p) s.
Proof.
  unfold path_change.
  now rewrite 2 eq_trans_sym_distr, eq_sym_involutive, <- eq_trans_assoc.
Defined.

Lemma path_change_nest {X: Type} {x y x' y' x'' y'': X}
  (s: x'' = x') (s': x' = x) (p: x = y) (t': y' = y) (t: y'' = y'):
  path_change s (path_change s' p t') t =
  path_change (s • s') p (t • t').
Proof.
  unfold path_change.
  rewrite eq_trans_sym_distr.
  now rewrite <- 3 eq_trans_assoc.
Defined.

Lemma path_change_map {X Y: Type} (f: X -> Y) {x y x' y': X}
  (s: x' = x) (p: x = y) (t: y' = y):
  f_equal f (path_change s p t) =
  path_change (f_equal f s) (f_equal f p) (f_equal f t).
Proof.
  unfold path_change.
  now rewrite 2 eq_trans_map_distr, eq_sym_map_distr.
Defined.

(** Recover an edge from a pasted path with a fixed prefix. *)
Definition path_prefix_solve {X: Type} {x y z: X}
  {p: x = y} {q: y = z} {r: x = z} (H: p • q = r):
  q = eq_sym p • r :=
  eq_sym (eq_trans_sym_cancel_l p q) •
    f_equal (fun r => eq_sym p • r) H.

(** Rotate a commuting square by moving its two boundary paths to the
    opposite side. *)
Lemma square_rotate {X: Type} {x y z w: X}
  {p: x = y} {q: y = z} {r: x = w} {s: w = z}
  (H: p • q = r • s): s • eq_sym q = eq_sym r • p.
Proof.
  pose proof (f_equal (fun h => eq_sym r • (h • eq_sym q)) H) as K.
  cbn beta in K.
  rewrite <- 2 eq_trans_assoc in K.
  rewrite eq_trans_sym_inv_r, eq_trans_refl_r, eq_trans_sym_cancel_l in K.
  now exact (eq_sym K).
Defined.

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

(** Map a square, using the comparison between mapped composites and
    composites of mapped paths on both boundaries. *)
Definition square_map {X Y: Type} (f: X -> Y) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q):
  f_equal f p • f_equal f b = f_equal f a • f_equal f q :=
  eq_sym (eq_trans_map_distr f p b) •
    (f_equal (fun h => f_equal f h) H • eq_trans_map_distr f a q).

(** The naturality square for a homotopy between two composites:
    Lemma 2.4.3 of the HoTT book (The Univalent Foundations Program,
    "Homotopy Type Theory: Univalent Foundations of Mathematics", 2013),
    with the equality reversed and path actions expanded through the composites. *)
Lemma f_equal_naturality {A B C D: Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (K: forall x, f (u x) = g (v x)) {x y: A} (p: x = y):
  f_equal f (f_equal u p) • K y = K x • f_equal g (f_equal v p).
Proof.
  destruct p; cbn. now exact (eq_trans_refl_l (K x)).
Defined.

(** A homotopy changes the endpoints of the action of a path. *)
Lemma path_change_natural {A B: Type} (f g: A -> B)
  (α: forall x, f x = g x) {x y: A} (p: x = y):
  f_equal f p = path_change (α x) (f_equal g p) (α y).
Proof.
  pose proof (f_equal_naturality (fun x => x) (fun x => x) f g α p) as H.
  rewrite f_equal_id in H.
  apply (f_equal (fun q => q • eq_sym (α y))) in H.
  rewrite <- 2 eq_trans_assoc in H.
  rewrite eq_trans_sym_inv_r, eq_trans_refl_r in H.
  now exact H.
Defined.



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
  destruct p, q, r, hp, hq, hr. cbn in H, K. destruct H, K.
  destruct c, d.
  cbn [square_compose whisker_l whisker_r eq_trans_assoc f_equal eq_sym eq_trans eq_rect] in *.
  rewrite 8 sigT_trans_eq_refl, eq_trans_refl_l, eq_trans_refl_r in *.
  now rewrite HH, KK.
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
  destruct p, q, r, s, hp, hq, hr, hs. cbn in H, K.
  destruct H, K, d.
  cbn [square_stack whisker_l whisker_r eq_trans_assoc f_equal eq_sym eq_trans eq_rect] in *.
  rewrite 2 sigT_trans_eq_refl, eq_trans_refl_l in HH, KK.
  rewrite 4 sigT_trans_eq_refl, eq_trans_refl_l.
  now exact (KK • HH).
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
  destruct p, q, hp, hq. cbn in H. destruct H, b.
  cbn [square_map eq_trans_map_distr f_equal eq_sym eq_trans eq_rect] in *.
  rewrite 2 sigT_trans_eq_refl, eq_trans_refl_l in HH.
  rewrite eq_trans_refl_r in HH. subst ha.
  rewrite 2 sigT_trans_eq_refl.
  cbn [sigT_map_eq]. now rewrite eq_trans_refl_l.
Defined.

(** A dependent homotopy lifts the naturality square of its base homotopy. *)
Lemma f_equal_naturality_dep {A B C D: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x))
  (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x))
  (K: forall x, f (u x) = g (v x))
  (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a))
  {x y: A} (p: x = y) {a: PA x} {b: PA y} (h: rew [PA] p in a = b):
  rew [fun e => rew [PD] e in F (u x) (U x a) = G (v y) (V y b)]
    f_equal_naturality u v f g K p in
    (sigT_map_eq F (sigT_map_eq U h) ⊙ HK y b) =
  HK x a ⊙ sigT_map_eq G (sigT_map_eq V h).
Proof.
  destruct p, h. cbn [f_equal_naturality f_equal sigT_map_eq eq_rect].
  generalize (HK x a).
  generalize (K x), (G (v x) (V x a)).
  generalize (g (v x)).
  intros z k w hk. now destruct hk, k.
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
  subst p' q'. cbn [eq_rect] in HHp, HHq. subst hp' hq'.
  unfold square_change_sides; cbn [whisker_l whisker_r f_equal eq_sym].
  rewrite eq_trans_refl_l, eq_trans_refl_r. now exact HH.
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
  unfold map_compose_tail, whisker_r.
  rewrite <- (rew_compose (fun e => rew [Q] e in F x u = t)).
  rewrite <- (rew_map _ (fun e => e • r) _ _).
  rewrite (rew_sigT_trans_eq_l (P := Q)), sigT_map_eq_comp.
  now apply sigT_trans_eq_assoc.
Defined.

(** A commuting cube transfers a dependent equality between opposite edges.
    Its base coherence compares the two pastings around the cube. *)
Lemma square_cube_dep {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q) (K: p • b' = a' • q) (κ: b = b') (λ: a = a')
  (C: H • whisker_r λ q = whisker_l p κ • K)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [P] b in v0 = v1) (hb': rew [P] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq)
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'.
Proof.
  unfold whisker_l, whisker_r in C.
  destruct p, q, hp, hq. cbn in H, K. destruct H, K.
  destruct κ, b.
  cbn [f_equal eq_trans] in C.
  rewrite f_equal_id, eq_trans_refl_l in C.
  rewrite C in D.
  cbn in D.
  rewrite sigT_trans_eq_refl in HH, KK.
  cbn in HH, KK |- *.
  rewrite eq_trans_refl_l in HH, KK.
  rewrite HH, KK. now rewrite D.
Defined.

(** Pasting when the lower edges are images under a map. *)
Definition square_compose_map {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r):
  p • f_equal f (c • d) = (a • b) • r :=
  whisker_l p (eq_trans_map_distr f c d) • square_compose H K.

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
  unfold square_compose_map, whisker_l.
  rewrite <- (rew_compose (fun e => rew [P] e in u0 = v2)
    (f_equal (fun e => p • e) (eq_trans_map_distr f c d)) (square_compose H K) _).
  rewrite <- (rew_map (fun e => rew [P] e in u0 = v2) (fun e => p • e) _ _).
  rewrite rew_sigT_trans_eq_r.
  rewrite (sigT_map_eq_comp (Q := P) (fun _ u => u) hc hd).
  now exact (square_compose_dep P H K ha hb
    (sigT_map_eq (Q := P) (fun _ u => u) hc)
    (sigT_map_eq (Q := P) (fun _ u => u) hd) hp hq hr HH KK).
Defined.

Lemma square_cube_map_dep {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1: X} {y0 y1: Y}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f b = a • q) (K: p • f_equal f b' = a' • q)
  (κ: b = b') (λ: a = a')
  (C: H • whisker_r λ q =
      whisker_l p (f_equal (fun e => f_equal f e) κ) • K)
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
  apply (sigT_map_eq_id_inj f P).
  pose proof (square_cube_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq (Q := P) (fun _ u => u) hb)
    (sigT_map_eq (Q := P) (fun _ u => u) hb') hp hq HH KK D) as E.
  rewrite <- (rew_map (fun e => rew [P] e in v0 = v1)
    (fun e => f_equal f e) κ _) in E.
  rewrite (map_subst
    (fun e (h: rew [fun y => P (f y)] e in v0 = v1) =>
      sigT_map_eq (Q := P) (fun _ u => u) h) κ hb) in E.
  now exact E.
Defined.

(** The layer-coherence path fills its defining square. *)
Lemma layer_square {V V' W X: Type} {S: V -> Type} {S': V' -> Type} {P: X -> Type}
  (f: V -> X) (g: V' -> X) (d: W -> X)
  (F: forall v, S v -> P (f v)) (G: forall v, S' v -> P (g v))
  {m1 m2: V} {n1 n2: V'} (l: m1 = m2) (r: n1 = n2)
  {w1 w2: W} (e: w1 = w2)
  (c: f m2 = d w1) (c': g n2 = d w2) (k: f m1 = g n1)
  {a: S m1} {b: S' n1} (h: rew [P] k in F m1 a = G n1 b)
  (H: f_equal f l • (c • f_equal d e) = k • (f_equal g r • c')):
  rew [fun e => rew [P] e in F m1 a = rew [P] c' in G n2 (rew [S'] r in b)]
    (eq_sym (eq_trans_assoc _ _ _) • H) in
    ((sigT_map_eq F (p := l) (u := a) eq_refl ⊙ eq_refl) ⊙
      sigT_map_eq (Q := P) (fun _ u => u)
       (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G) (E1 := e)
         (C2 := l) (D2 := r) (C1 := c) (D1 := c') h H)) =
    h ⊙ (sigT_map_eq G (p := r) (u := b) eq_refl ⊙ eq_refl).
Proof.
  rewrite (sigT_map_eq_id (P := P) d).
  unfold rew_cohLayer_hex.
  rewrite eq_trans_sym_cancel_l.
  now apply sigT_square_fill_boundary.
Defined.

(** Map a layer-coherence cell, then use the naturality of [α] to identify
    its transported endpoints. *)
Definition layer_square_map
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: f_equal s p • (v • f_equal r e) = k • (f_equal t q • w))
  (Hnat: f_equal f (f_equal r e) • α d' = α d • f_equal j (f_equal g e)):
  (f_equal f (f_equal s p • v) • α d) • f_equal j (f_equal g e) =
  f_equal f k • (f_equal f (f_equal t q • w) • α d').
Proof.
  now exact (square_stack
    (square_map f (eq_sym (eq_trans_assoc _ _ _) • H)) (eq_sym Hnat)).
Defined.

Lemma layer_square_map_dep
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  (P: X -> Type) (Q: Y -> Type) (PM: M -> Type) (PN: N -> Type)
  (F: forall x, P x -> Q (f x))
  (L: forall m, PM m -> P (s m)) (R: forall n, PN n -> P (t n))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: f_equal s p • (v • f_equal r e) = k • (f_equal t q • w))
  {a: PM m} {b: PN n} (h: rew [P] k in L m a = R n b):
  rew [fun e => rew [Q] e in F (s m) (L m a) =
    rew [Q] α d' in F (r d') (rew [P] w in R n' (rew [PN] q in b))]
    layer_square_map r s t f g j α e p q v w k H
      (f_equal_naturality r g f j α e) in
  ((sigT_map_eq F (sigT_map_eq L (p := p) (u := a) eq_refl ⊙ eq_refl) ⊙ eq_refl)
    ⊙ sigT_map_eq (Q := Q) (fun _ u => u)
      (sigT_map_eq (Q := fun u => Q (j u))
        (fun dd x => rew [Q] α dd in F (r dd) x)
        (rew_cohLayer_hex (P := P) (rf0 := r) (F := L) (G := R)
          (E1 := e) (C2 := p) (D2 := q) (C1 := v) (D1 := w) h H))) =
  sigT_map_eq F h ⊙
    (sigT_map_eq F (sigT_map_eq R (p := q) (u := b) eq_refl ⊙ eq_refl) ⊙ eq_refl).
Proof.
  unfold layer_square_map.
  eapply square_stack_dep.
  - eapply square_map_dep.
    now exact (layer_square s t r L R p q e v w k h H).
  - pose proof (f_equal_naturality_dep r g f j
      (fun _ u => u) (fun dd x => rew [Q] α dd in F (r dd) x)
      F (fun _ u => u) α (fun _ _ => eq_refl) e
      (rew_cohLayer_hex (P := P) (rf0 := r) (F := L) (G := R)
        (E1 := e) (C2 := p) (D2 := q) (C1 := v) (D1 := w) h H)) as Hlift.
    rewrite <- Hlift. now exact (rew_opp_l _ _ _).
Defined.

(** Extend a layer-coherence cell along a path in its source, using the
    naturality of the frame and dependent-path coherences. *)
Definition layer_square_nat {Z V V' W X: Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (k: forall z, f (L z) = g (R z))
  {z1 z2: Z} (p: z1 = z2)
  {m: V} {n: V'} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: f_equal f l • (c • f_equal d e) = k z2 • (f_equal g r • c'))
  (Hnat: f_equal f (f_equal L p) • k z2 = k z1 • f_equal g (f_equal R p)):
  (f_equal f (f_equal L p • l) • c) • f_equal d e =
    k z1 • (f_equal g (f_equal R p • r) • c').
Proof.
  now exact (square_change_sides (map_compose_tail f (f_equal L p) l c)
    (square_stack Hnat (eq_sym (eq_trans_assoc _ _ _) • H))
    (map_compose_tail g (f_equal R p) r c')).
Defined.

Lemma layer_square_nat_dep {Z V V' W X: Type}
  {S: Z -> Type} {Q: V -> Type} {Q': V' -> Type} {P: X -> Type}
  (L: Z -> V) (R: Z -> V') (f: V -> X) (g: V' -> X) (d: W -> X)
  (RL: forall z, S z -> Q (L z)) (RR: forall z, S z -> Q' (R z))
  (F: forall v, Q v -> P (f v)) (G: forall v, Q' v -> P (g v))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [P] k z in F (L z) (RL z a) = G (R z) (RR z a))
  {z1 z2: Z} (p: z1 = z2)
  {m: V} {n: V'} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: f_equal f l • (c • f_equal d e) = k z2 • (f_equal g r • c'))
  (a: S z1):
  rew [fun e => rew [P] e in F (L z1) (RL z1 a) =
    rew [P] c' in G n (rew [Q'] r in RR z2 (rew [S] p in a))]
    layer_square_nat L R f g d k p l r e c c' H
      (f_equal_naturality L R f g k p) in
    ((sigT_map_eq F
       (sigT_map_eq RL (p := p) (u := a) eq_refl ⊙
         (eq_refl: rew [Q] l in RL z2 (rew [S] p in a) = _)) ⊙ eq_refl) ⊙
     sigT_map_eq (Q := P) (fun _ u => u)
       (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G) (E1 := e)
          (C2 := l) (D2 := r) (C1 := c) (D1 := c')
          (hk z2 (rew [S] p in a)) H)) =
    hk z1 a ⊙
      (sigT_map_eq G
        (sigT_map_eq RR (p := p) (u := a) eq_refl ⊙
          (eq_refl: rew [Q'] r in RR z2 (rew [S] p in a) = _)) ⊙ eq_refl).
Proof.
  unfold layer_square_nat.
  eapply square_change_sides_dep.
  - now apply map_compose_tail_dep.
  - eapply square_stack_dep.
    + now exact (f_equal_naturality_dep L R f g RL RR F G k hk p eq_refl).
    + now exact (layer_square f g d F G l r e c c' (k z2)
        (hk z2 (rew [S] p in a)) H).
  - now apply map_compose_tail_dep.
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

(** A shared middle endpoint correction cancels between two dependent paths. *)
Lemma dpath_middle_cancel {X: Type} {P: X -> Type}
  {x y z: X} {p: x = y} {q: y = z}
  {u: P x} {v v': P y} {w: P z}
  (h: rew [P] p in u = v) (t: v' = v) (k: rew [P] q in v = w):
  (h • eq_sym t) ⊙ (f_equal (fun v => rew [P] q in v) t • k) = h ⊙ k.
Proof.
  pose proof (dpath_change_comp (P := P) eq_refl t eq_refl h k) as H.
  unfold dpath_change in H; cbn [f_equal eq_sym] in H.
  rewrite 2 eq_trans_refl_l, 2 eq_trans_refl_r in H.
  now exact H.
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
  rewrite (f_equal_naturality f g (fun v => rew [P] p in v) (fun v => v) H s).
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

(** A transported identity square changes both endpoints by the same path. *)
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
(** A section lifts path composition and path comparisons coherently. *)
Lemma section_path_comp {X: Type} (P: X -> Type) (s: forall x, P x)
  {x y z: X} (p: x = y) (q: y = z):
  f_equal_dep P s (p • q) = f_equal_dep P s p ⊙ f_equal_dep P s q.
Proof.
  now destruct p, q.
Defined.

Definition section_path_cell {X: Type} (P: X -> Type) (s: forall x, P x)
  {x y: X} {p q: x = y} (H: p = q):
  rew [fun e => rew [P] e in s x = s y] H in f_equal_dep P s p =
  f_equal_dep P s q :=
  f_equal_dep (fun e => rew [P] e in s x = s y)
    (fun e => f_equal_dep P s e) H.

Lemma section_path_map {A X: Type} {R: A -> Type}
  (P: X -> Type) (s: forall x, P x) (f: A -> X)
  {x y: A} {u: R x} {v: R y} {p: x = y} (h: rew [R] p in u = v):
  sigT_map_eq (P := R) (Q := P) (f := f) (fun a _ => s (f a)) h =
  f_equal_dep P s (f_equal f p).
Proof.
  now destruct h, p.
Defined.

Lemma section_path_reindex {A X: Type} (P: X -> Type)
  (s: forall x, P x) (f: A -> X) {x y: A} (p: x = y):
  sigT_map_eq (P := fun a => P (f a)) (Q := P) (f := f) (fun _ u => u)
    (f_equal_dep (fun a => P (f a)) (fun a => s (f a)) p) =
  f_equal_dep P s (f_equal f p).
Proof.
  now destruct p.
Defined.

(** Pure transport is a section path whose final endpoint comparison
    has been removed. *)
Lemma section_path_transport {X: Type} (P: X -> Type) (s: forall x, P x)
  {x y: X} (p: x = y):
  (eq_refl: rew [P] p in s x = rew [P] p in s x) =
  dpath_change (P := P) (p := p) eq_refl (f_equal_dep P s p) (f_equal_dep P s p).
Proof.
  unfold dpath_change; cbn [f_equal].
  now rewrite eq_trans_sym_inv_r, eq_trans_refl_l.
Defined.

Lemma section_transport_paste {X: Type} (P: X -> Type) (s: forall x, P x)
  {x y z: X} (p: x = y) (q: y = z):
  f_equal_dep P s p ⊙ (eq_refl: rew [P] q in s y = rew [P] q in s y) =
  dpath_change (P := P) eq_refl (f_equal_dep P s (p • q)) (f_equal_dep P s q).
Proof.
  rewrite (section_path_transport P s q).
  rewrite <- (dpath_change_id (f_equal_dep P s p)).
  rewrite dpath_change_comp.
  now rewrite section_path_comp.
Defined.

(** A section fills a square by its action on the fourth edge. Changing
    the two lower vertices retains exactly their endpoint comparisons. *)
Lemma section_square_fill {X: Type} (P: X -> Type) (s: forall x, P x)
  {x0 x1 y0 y1: X} {a: x0 = x1} {c: y0 = y1}
  {p: x0 = y0} {q: x1 = y1} (H: p • c = a • q)
  {v0: P y0} {v1: P y1} (l: v0 = s y0) (r: v1 = s y1):
  sigT_square_fill H
    (dpath_change (P := P) eq_refl (f_equal_dep P s p) l)
    (f_equal_dep P s a)
    (dpath_change (P := P) eq_refl (f_equal_dep P s q) r) =
  dpath_change (P := P) l (f_equal_dep P s c) r.
Proof.
  symmetry. apply sigT_square_fill_unique.
  rewrite dpath_change_comp.
  rewrite <- (dpath_change_id (f_equal_dep P s a)).
  rewrite dpath_change_comp.
  apply dpath_change_cell.
  rewrite <- 2 section_path_comp.
  now exact (section_path_cell P s H).
Defined.

(** The layer filler for a section is its path action with the two
    exterior transport comparisons. The given frame cell is retained
    by the coherent section lift used in [section_square_fill]. *)
Lemma rew_cohLayer_hex_section {T1 T2 T3 X: Type}
  (P: X -> Type) (s: forall x, P x) {S2: T2 -> Type} {S3: T3 -> Type}
  (rf0: T1 -> X) (rfF: T2 -> X) (rfG: T3 -> X)
  {d1 d2: T1} (E: d1 = d2) {m1 m2: T2} (C2: m1 = m2)
  {n1 n2: T3} (D2: n1 = n2)
  (C1: rfF m2 = rf0 d1) (D1: rfG n2 = rf0 d2) (K: rfF m1 = rfG n1)
  (aL: S2 m1) (aR: S3 n1)
  (HH: f_equal rfF C2 • (C1 • f_equal rf0 E) = K • (f_equal rfG D2 • D1)):
  rew_cohLayer_hex (P := P) (rf0 := rf0)
    (F := fun m (_: S2 m) => s (rfF m)) (G := fun n (_: S3 n) => s (rfG n))
    (E1 := E) (C2 := C2) (D2 := D2) (C1 := C1) (D1 := D1) (K := K)
    (aL := aL) (aR := aR) (f_equal_dep P s K) HH =
  dpath_change (P := fun d => P (rf0 d)) (f_equal_dep P s C1)
    (f_equal_dep (fun d => P (rf0 d)) (fun d => s (rf0 d)) E)
    (f_equal_dep P s D1).
Proof.
  apply (sigT_map_eq_id_inj rf0 P).
  rewrite sigT_map_eq_id.
  unfold rew_cohLayer_hex.
  rewrite eq_trans_sym_cancel_l.
  rewrite dpath_change_map, 2 f_equal_id, section_path_reindex.
  rewrite 2 section_path_map, 2 section_transport_paste.
  now apply section_square_fill.
Defined.
(** Recover an edge from a pasted path with a fixed suffix. *)
Lemma path_suffix_solve {X: Type} {x y z: X}
  {p: x = y} {q: y = z} {r: x = z} (H: p • q = r):
  p = r • eq_sym q.
Proof.
  pose proof (f_equal (fun h => h • eq_sym q) H) as K.
  cbn beta in K.
  now rewrite <- eq_trans_assoc, eq_trans_sym_inv_r, eq_trans_refl_r in K.
Defined.

(** Reindexing a path-valued family changes the corresponding endpoint. *)
Lemma path_reindex_left {I X: Type} (f: I -> X) {i j: I} (p: i = j)
  {x: X} (h: f i = x):
  rew [fun i => f i = x] p in h = eq_sym (f_equal f p) • h.
Proof.
  destruct p; cbn [f_equal eq_sym].
  now rewrite eq_trans_refl_l.
Defined.

Lemma path_reindex_right {I X: Type} (g: I -> X) {i j: I} (p: i = j)
  {x: X} (h: x = g i):
  rew [fun i => x = g i] p in h = h • f_equal g p.
Proof.
  destruct p; cbn [f_equal].
  now rewrite eq_trans_refl_r.
Defined.

(** Evaluation of a reindexed homotopy is the reindexing of its component. *)
Lemma homotopy_reindex_left {I A B: Type} (f: I -> A -> B) (g: A -> B)
  {i j: I} (p: i = j) (h: forall a, f i a = g a) (a: A):
  (rew [fun i => forall a, f i a = g a] p in h) a =
  eq_sym (f_equal (fun i => f i a) p) • h a.
Proof.
  rewrite <- (map_subst (fun i (h: forall a, f i a = g a) => h a) p h).
  now exact (path_reindex_left (fun i => f i a) p (h a)).
Defined.

Lemma homotopy_reindex_right {I A B: Type} (f: A -> B) (g: I -> A -> B)
  {i j: I} (p: i = j) (h: forall a, f a = g i a) (a: A):
  (rew [fun i => forall a, f a = g i a] p in h) a =
  h a • f_equal (fun i => g i a) p.
Proof.
  rewrite <- (map_subst (fun i (h: forall a, f a = g i a) => h a) p h).
  now exact (path_reindex_right (fun i => g i a) p (h a)).
Defined.

(** Reindex a commuting face square along pointwise comparisons of its
    three vertex maps. Matching intermediate endpoint corrections cancel. *)
Lemma face_square_reindex {A0 A1 A2 X0 X1 X2: Type}
  (v0 w0: A0 -> X0) (v1 w1: A1 -> X1) (v2 w2: A2 -> X2)
  (η0: forall a, w0 a = v0 a) (η1: forall a, w1 a = v1 a)
  (η2: forall a, w2 a = v2 a)
  (F G: X1 -> X0) (F' G': X2 -> X1)
  (K: forall x, F (G' x) = G (F' x))
  (t: A2) (ur uq: A1) (ub ud: A0)
  (Pr: G' (v2 t) = v1 ur) (Pqr: F (v1 ur) = v0 ub)
  (Pq: F' (v2 t) = v1 uq) (Prq: G (v1 uq) = v0 ud) (C: ub = ud)
  (H: (f_equal F Pr • Pqr) • f_equal v0 C = K (v2 t) • (f_equal G Pq • Prq)):
  (f_equal F (path_change (f_equal G' (η2 t)) Pr (η1 ur))
    • path_change (f_equal F (η1 ur)) Pqr (η0 ub)) • f_equal w0 C =
  K (w2 t) • (f_equal G (path_change (f_equal F' (η2 t)) Pq (η1 uq))
    • path_change (f_equal G (η1 uq)) Prq (η0 ud)).
Proof.
  rewrite (path_change_map F), (path_change_map G), 2 path_change_comp.
  rewrite (path_change_natural w0 v0 η0 C), path_change_comp.
  unfold path_change.
  rewrite H, <- eq_trans_assoc.
  rewrite (eq_trans_assoc (f_equal F (f_equal G' (η2 t)))).
  rewrite (f_equal_naturality G' F' F G K (η2 t)).
  now rewrite <- eq_trans_assoc.
Defined.

(** The identity dependent map preserves its path argument. *)
Lemma dpath_map_id {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {u: P x} {v: P y} (h: rew [P] p in u = v):
  dpath_map (fun _ u => u) h = h.
Proof.
  destruct p. unfold dpath_map; cbn [map_subst].
  now rewrite f_equal_id, eq_trans_refl_l.
Defined.

(** A homotopy between fibre maps changes the endpoints of their path actions. *)
Lemma sigT_map_eq_homotopy {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (g g': forall x, P x -> Q (f x))
  (N: forall x u, g x u = g' x u)
  {x y: X} {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  sigT_map_eq g h = dpath_change (N x u) (sigT_map_eq g' h) (N y v).
Proof.
  pose proof (dpath_map_square (P := P) (P' := P) (Q := Q) (Q' := Q)
    (f := f) (fun _ u => u) (fun _ u => u) g g' N h) as H.
  rewrite 2 dpath_map_id in H.
  now exact H.
Defined.
(** Reindex a hexagon with its displayed witness, and recover a chosen
    source cell from the inverse boundary presentation. *)
Definition cell_reindex {A: Type} {x x' y y': A}
  (l: x = x') (r: y = y') (K: x' = y'): x = y.
Proof. destruct l, r. now exact K. Defined.

Lemma cell_reindex_dep {A: Type} (P: A -> Type)
  {x x' y y': A} (l: x = x') (r: y = y') (K: x' = y')
  {u: P x} {u': P x'} {v: P y} {v': P y'}
  (Hl: rew [P] l in u = u') (Hr: rew [P] r in v = v')
  (H: rew [P] K in u' = v'):
  rew [P] cell_reindex l r K in u = v.
Proof. destruct l, r, Hl, Hr. now exact H. Defined.

(** The chosen comparison of composites and its displayed lift. *)
Definition path_compose_cell {A: Type} {x y z: A}
  {p p': x = y} {q q': y = z} (Hp: p = p') (Hq: q = q'):
  p • q = p' • q' :=
  f_equal (fun p => p • q) Hp • f_equal (fun q => p' • q) Hq.

Lemma path_compose_cell_dep {A: Type} (P: A -> Type) {x y z: A}
  {p p': x = y} {q q': y = z} (Hp: p = p') (Hq: q = q')
  {u: P x} {v: P y} {w: P z}
  {hp: rew [P] p in u = v} {hp': rew [P] p' in u = v}
  {hq: rew [P] q in v = w} {hq': rew [P] q' in v = w}
  (HHp: rew [fun e => rew [P] e in u = v] Hp in hp = hp')
  (HHq: rew [fun e => rew [P] e in v = w] Hq in hq = hq'):
  rew [fun e => rew [P] e in u = w] path_compose_cell Hp Hq in
    (hp ⊙ hq) = hp' ⊙ hq'.
Proof. destruct Hp, Hq, HHp, HHq. now reflexivity. Defined.

Definition hex_reindex_cell {A: Type} {x0 x1 x2 x3 y1 y2: A}
  {a1 a1': x0 = x1} (Ha1: a1 = a1')
  {a2 a2': x1 = x2} (Ha2: a2 = a2')
  {a3 a3': x2 = x3} (Ha3: a3 = a3')
  {b1 b1': x0 = y1} (Hb1: b1 = b1')
  {b2 b2': y1 = y2} (Hb2: b2 = b2')
  {b3 b3': y2 = x3} (Hb3: b3 = b3')
  (K: a1' • (a2' • a3') = b1' • (b2' • b3')):
  a1 • (a2 • a3) = b1 • (b2 • b3) :=
  cell_reindex (path_compose_cell Ha1 (path_compose_cell Ha2 Ha3))
    (path_compose_cell Hb1 (path_compose_cell Hb2 Hb3)) K.

Lemma hex_reindex_cell_dep {A: Type} (P: A -> Type)
  {x0 x1 x2 x3 y1 y2: A}
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3} {v1: P y1} {v2: P y2}
  {a1 a1': x0 = x1} (Ha1: a1 = a1')
  {a2 a2': x1 = x2} (Ha2: a2 = a2')
  {a3 a3': x2 = x3} (Ha3: a3 = a3')
  {b1 b1': x0 = y1} (Hb1: b1 = b1')
  {b2 b2': y1 = y2} (Hb2: b2 = b2')
  {b3 b3': y2 = x3} (Hb3: b3 = b3')
  (c1: rew [P] a1' in u0 = u1) (c2: rew [P] a2' in u1 = u2)
  (c3: rew [P] a3' in u2 = u3)
  (d1: rew [P] b1' in u0 = v1) (d2: rew [P] b2' in v1 = v2)
  (d3: rew [P] b3' in v2 = u3)
  {K: a1' • (a2' • a3') = b1' • (b2' • b3')}
  (H: rew [fun e => rew [P] e in u0 = u3] K in
    (c1 ⊙ (c2 ⊙ c3)) = d1 ⊙ (d2 ⊙ d3)):
  rew [fun e => rew [P] e in u0 = u3]
    hex_reindex_cell Ha1 Ha2 Ha3 Hb1 Hb2 Hb3 K in
    ((rew <- [fun e => rew [P] e in u0 = u1] Ha1 in c1) ⊙
      ((rew <- [fun e => rew [P] e in u1 = u2] Ha2 in c2) ⊙
        (rew <- [fun e => rew [P] e in u2 = u3] Ha3 in c3))) =
    (rew <- [fun e => rew [P] e in u0 = v1] Hb1 in d1) ⊙
      ((rew <- [fun e => rew [P] e in v1 = v2] Hb2 in d2) ⊙
        (rew <- [fun e => rew [P] e in v2 = u3] Hb3 in d3)).
Proof.
  unfold hex_reindex_cell.
  refine (cell_reindex_dep (fun e: x0 = x3 => rew [P] e in u0 = u3)
    (path_compose_cell Ha1 (path_compose_cell Ha2 Ha3))
    (path_compose_cell Hb1 (path_compose_cell Hb2 Hb3)) K _ _ H).
  - refine (path_compose_cell_dep P Ha1 (path_compose_cell Ha2 Ha3) _ _).
    + now exact (rew_opp_r (fun e: x0 = x1 => rew [P] e in u0 = u1) Ha1 c1).
    + refine (path_compose_cell_dep P Ha2 Ha3 _ _).
      * now exact (rew_opp_r (fun e: x1 = x2 => rew [P] e in u1 = u2) Ha2 c2).
      * now exact (rew_opp_r (fun e: x2 = x3 => rew [P] e in u2 = u3) Ha3 c3).
  - refine (path_compose_cell_dep P Hb1 (path_compose_cell Hb2 Hb3) _ _).
    + now exact (rew_opp_r (fun e: x0 = y1 => rew [P] e in u0 = v1) Hb1 d1).
    + refine (path_compose_cell_dep P Hb2 Hb3 _ _).
      * now exact (rew_opp_r (fun e: y1 = y2 => rew [P] e in v1 = v2) Hb2 d2).
      * now exact (rew_opp_r (fun e: y2 = x3 => rew [P] e in v2 = u3) Hb3 d3).
Defined.

(** The stored cell is chosen by moving the selected source cell to its
    target boundary. The reverse comparison uses these exact composites. *)
Definition hex_reindex_inverse_cell {A: Type} {x0 x1 x2 x3 y1 y2: A}
  {a1 a1': x0 = x1} (Ha1: a1 = a1')
  {a2 a2': x1 = x2} (Ha2: a2 = a2')
  {a3 a3': x2 = x3} (Ha3: a3 = a3')
  {b1 b1': x0 = y1} (Hb1: b1 = b1')
  {b2 b2': y1 = y2} (Hb2: b2 = b2')
  {b3 b3': y2 = x3} (Hb3: b3 = b3')
  (K: a1 • (a2 • a3) = b1 • (b2 • b3)):
  a1' • (a2' • a3') = b1' • (b2' • b3') :=
  cell_reindex
    (eq_sym (path_compose_cell Ha1 (path_compose_cell Ha2 Ha3)))
    (eq_sym (path_compose_cell Hb1 (path_compose_cell Hb2 Hb3))) K.

Lemma cell_reindex_roundtrip {A: Type} {x x' y y': A}
  (l: x = x') (r: y = y') (K: x = y):
  cell_reindex l r (cell_reindex (eq_sym l) (eq_sym r) K) = K.
Proof. now destruct l, r. Defined.

Lemma hex_reindex_recover_dep {A: Type} (P: A -> Type)
  {x0 x1 x2 x3 y1 y2: A}
  {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3} {v1: P y1} {v2: P y2}
  {a1 a1': x0 = x1} (Ha1: a1 = a1')
  {a2 a2': x1 = x2} (Ha2: a2 = a2')
  {a3 a3': x2 = x3} (Ha3: a3 = a3')
  {b1 b1': x0 = y1} (Hb1: b1 = b1')
  {b2 b2': y1 = y2} (Hb2: b2 = b2')
  {b3 b3': y2 = x3} (Hb3: b3 = b3')
  (c1: rew [P] a1' in u0 = u1) (c2: rew [P] a2' in u1 = u2)
  (c3: rew [P] a3' in u2 = u3)
  (d1: rew [P] b1' in u0 = v1) (d2: rew [P] b2' in v1 = v2)
  (d3: rew [P] b3' in v2 = u3)
  (K: a1 • (a2 • a3) = b1 • (b2 • b3))
  (H: rew [fun e => rew [P] e in u0 = u3]
    (hex_reindex_inverse_cell Ha1 Ha2 Ha3 Hb1 Hb2 Hb3 K) in
    (c1 ⊙ (c2 ⊙ c3)) = d1 ⊙ (d2 ⊙ d3)):
  rew [fun e => rew [P] e in u0 = u3]
    K in
    ((rew <- [fun e => rew [P] e in u0 = u1] Ha1 in c1) ⊙
      ((rew <- [fun e => rew [P] e in u1 = u2] Ha2 in c2) ⊙
        (rew <- [fun e => rew [P] e in u2 = u3] Ha3 in c3))) =
    (rew <- [fun e => rew [P] e in u0 = v1] Hb1 in d1) ⊙
      ((rew <- [fun e => rew [P] e in v1 = v2] Hb2 in d2) ⊙
        (rew <- [fun e => rew [P] e in v2 = u3] Hb3 in d3)).
Proof.
  pose proof (hex_reindex_cell_dep P Ha1 Ha2 Ha3 Hb1 Hb2 Hb3
    c1 c2 c3 d1 d2 d3 H) as HH.
  unfold hex_reindex_cell, hex_reindex_inverse_cell in HH.
  rewrite (cell_reindex_roundtrip
    (path_compose_cell Ha1 (path_compose_cell Ha2 Ha3))
    (path_compose_cell Hb1 (path_compose_cell Hb2 Hb3)) K) in HH.
  now exact HH.
Defined.



(** Paste two naturality squares and one corner square onto a hexagon.
    The exterior corrections are the same on its two boundary routes. *)
Lemma hex_paste_side_cells {T: Type}
  {v0 v1 v2 v3 v4 v5 t1 t2 t3 t4 t5 t6: T}
  (A: v0 = v1) (B: v1 = v2) (C: v2 = v3)
  (D: v0 = v4) (E: v4 = v5) (F: v5 = v3)
  (u: t1 = v1) (x: t2 = v2) (v: t3 = t2)
  (w: t6 = v5) (y: t5 = v3) (z: t4 = t5)
  (B': t1 = t2) (C': t3 = t4) (F': t6 = t5)
  (HB: u • B = B' • x) (HF: w • F = F' • y)
  (HC: C' • (z • y) = (v • x) • C)
  (H: A • (B • C) = D • (E • F)):
  (A • eq_sym u) • ((B' • eq_sym v) • C') =
  D • ((E • eq_sym w) • (F' • eq_sym z)).
Proof.
  pose proof (path_suffix_solve (eq_sym HB)) as Bcell.
  pose proof (path_suffix_solve (eq_sym HF)) as Fcell.
  pose proof (path_suffix_solve HC) as Ccell.
  rewrite <- eq_trans_assoc in Bcell.
  rewrite <- eq_trans_assoc in Fcell.
  rewrite <- eq_trans_assoc in Ccell.
  rewrite Bcell, Fcell, Ccell, eq_trans_sym_distr.
  rewrite <- 8 eq_trans_assoc.
  rewrite (eq_trans_sym_cancel_l u), (eq_trans_sym_cancel_l v),
    (eq_trans_sym_cancel_l x), (eq_trans_sym_cancel_l w).
  pose proof (f_equal (fun p => p • (eq_sym y • eq_sym z)) H) as K.
  cbn beta in K.
  rewrite <- 4 eq_trans_assoc in K.
  now exact K.
Defined.
(** View the expanded endpoint corrections as a dependent path change. *)
Lemma dpath_change_fold {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a a': P x} {b b': P y} (s: a' = a)
  (h: rew [P] p in a = b) (t: b' = b):
  f_equal (fun a => rew [P] p in a) s • (h • eq_sym t) = dpath_change s h t.
Proof. now reflexivity. Defined.

(** Two successive endpoint corrections may be written as one flat chain. *)
Lemma dpath_change_flat {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a0 a1 a2: P x} {b0 b1 b2: P y}
  (s: a0 = a1) (s': a1 = a2) (h: rew [P] p in a2 = b2)
  (t': b1 = b2) (t: b0 = b1):
  f_equal (fun a => rew [P] p in a) s •
    (f_equal (fun a => rew [P] p in a) s' • (h • (eq_sym t' • eq_sym t))) =
  dpath_change (s • s') h (t • t').
Proof.
  unfold dpath_change.
  now rewrite eq_trans_map_distr, eq_trans_sym_distr, <- eq_trans_assoc.
Defined.

Lemma dpath_change_flat_map {X A B: Type} {P: X -> Type}
  {x y: X} {p: x = y} (F: A -> P x) (G: B -> P y)
  {a a': A} {b b': B} (s': a' = a) (t': b' = b)
  {u: P x} {v: P y} (s: u = F a') (t: v = G b')
  (h: rew [P] p in F a = G b):
  f_equal (fun u => rew [P] p in u) s •
    (f_equal (fun a => rew [P] p in F a) s' •
      (h • (eq_sym (f_equal G t') • eq_sym t))) =
  dpath_change (s • f_equal F s') h (t • f_equal G t').
Proof.
  rewrite <- (f_equal_compose F (fun u => rew [P] p in u) s').
  now apply dpath_change_flat.
Defined.

(** A homotopy cell reindexed along a path is its endpoint conjugate. *)
Lemma homotopy_cell_reindex {A B: Type} (f g: A -> B)
  (h: forall x, f x = g x) {x y: A} (p: x = y):
  h x = path_change (f_equal f p) (h y) (f_equal g p).
Proof.
  pose proof (f_equal_naturality (fun x => x) (fun x => x) f g h p) as N.
  rewrite f_equal_id in N.
  pose proof (path_suffix_solve (eq_sym N)) as H.
  now rewrite <- eq_trans_assoc in H.
Defined.

Definition path_reindex_source_unlift {A: Type} (P: A -> Type)
  {x x' y: A} (c: x' = x) (r: x = y) (u: P x') (v: P y)
  (h: rew [P] path_reindex_source c r in u = v):
  rew [P] r in rew [P] c in u = v.
Proof.
  destruct c.
  now exact h.
Defined.

Definition path_reindex_source_unlift_along {A: Type} (P: A -> Type)
  {x x' y: A} (c: x' = x) (r: x = y) (s: x' = y)
  (K: s = path_reindex_source c r) (u: P x') (v: P y)
  (h: rew [P] s in u = v):
  rew [P] r in rew [P] c in u = v :=
  path_reindex_source_unlift P c r u v
    (rew [fun e => rew [P] e in u = v] K in h).

Definition sigT_triangle
  {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  {x y: A} {z: B} {u: P x} {v: P y} {w: Q z}
  {p: f x = z} {q: z = f y} {r: x = y}
  {hp: rew [Q] p in g x u = w}
  {hq: rew [Q] q in w = g y v} {hr: rew [P] r in u = v}
  (K: p • q = f_equal f r)
  (H: rew [fun s => rew [Q] s in g x u = g y v] K in
    (hp ⊙ hq) = sigT_map_eq g hr):
  (=p; hp) • (=q; hq) =
    f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) (=r; hr) :=
  eq_trans_eq_existT_curried p hp q hq •
    (eq_existT_curried_eq K H • eq_sym (f_equal_eq_existT_curried f g r hr)).

Lemma sigT_triangle_dep
  {A B: Type} {P: A -> Type} {Q: B -> Type}
  {R: {a: A &T P a} -> Type} {S: {b: B &T Q b} -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  (h: forall z: {a: A &T P a}, R z -> S (f z.1; g z.1 z.2))
  {x y: A} {z: B} {u: P x} {v: P y} {w: Q z}
  {a: R (x; u)} {b: R (y; v)} {c: S (z; w)}
  {p: f x = z} {q: z = f y} {r: x = y}
  {hp: rew [Q] p in g x u = w}
  {hq: rew [Q] q in w = g y v} {hr: rew [P] r in u = v}
  (K: p • q = f_equal f r)
  (H: rew [fun s => rew [Q] s in g x u = g y v] K in
    (hp ⊙ hq) = sigT_map_eq g hr)
  (kp: rew [S] (=p; hp) in h (x; u) a = c)
  (kq: rew [S] (=q; hq) in c = h (y; v) b)
  (kr: rew [R] (=r; hr) in a = b)
  (HH: rew [fun e => rew [S] e in h (x; u) a = h (y; v) b]
    sigT_triangle f g K H in (kp ⊙ kq) = sigT_map_eq h kr):
  rew [fun e => rew [fun z => {w: Q z &T S (z; w)}] e in
      (g x u; h (x; u) a) = (g y v; h (y; v) b)] K in
    (eq_existT_curried_dep (H := p) (Hu := hp) (Hv := kp) ⊙
      eq_existT_curried_dep (H := q) (Hu := hq) (Hv := kq)) =
  sigT_map_eq
    (P := fun x => {u: P x &T R (x; u)})
    (Q := fun y => {v: Q y &T S (y; v)})
    (fun x c => (g x c.1; h (x; c.1) c.2))
    (eq_existT_curried_dep (H := r) (Hu := hr) (Hv := kr)).
Proof.
  rewrite sigT_trans_eq_existT_curried_dep.
  refine (eq_trans _ (eq_sym
    (sigT_map_eq_existT_curried_dep_curried
      (P := P) (R := fun x u => R (x; u))
      (P' := Q) (R' := fun y v => S (y; v))
      f g (fun x u a => h (x; u) a) r hr kr))).
  apply (eq_existT_curried_dep_eq K H).
  now exact (rew_conjugate _ _ _ _ _ _ HH).
Defined.

Definition path_reindex_source_comp {A: Type} (P: A -> Type)
  {x x' y: A} (c: x' = x) (r: x = y)
  {u': P x'} {u: P x} {v: P y}
  (hc: rew [P] c in u' = u) (hr: rew [P] r in u = v):
  rew [P] path_reindex_source c r in u' = v.
Proof. destruct c, hc. now exact hr. Defined.

Lemma path_reindex_source_comp_unlift {A: Type} (P: A -> Type)
  {x x' y: A} (c: x' = x) (r: x = y) (u: P x') (v: P y)
  (h: rew [P] path_reindex_source c r in u = v):
  path_reindex_source_comp P c r eq_refl
    (path_reindex_source_unlift P c r u v h) = h.
Proof. now destruct c. Defined.

Definition source_unmap {X Y: Type} (P: Y -> Type) (f: X -> Y)
  {x y: X} (p: x = y) {u: P (f x)} {v: P (f y)}
  (h: rew [P] f_equal f p in u = v):
  rew [fun x => P (f x)] p in u = v.
Proof. destruct p. now exact h. Defined.

Lemma source_unmap_map {X Y: Type} (P: Y -> Type) (f: X -> Y)
  {x y: X} (p: x = y) {u: P (f x)} {v: P (f y)}
  (h: rew [P] f_equal f p in u = v):
  sigT_map_eq (P := fun x => P (f x)) (Q := P) (f := f)
    (fun _ u => u) (source_unmap P f p h) = h.
Proof.
  destruct p. cbn [source_unmap].
  now rewrite sigT_map_eq_refl, f_equal_id.
Defined.

Definition source_triangle_fill {T X: Type} (P: X -> Type) (f: T -> X)
  {t0 t1: T} {a b: X} (c: a = f t0) (r: t0 = t1)
  {p: a = b} {q: b = f t1}
  (K: p • q = path_reindex_source c (f_equal f r))
  {u: P a} {v: P b} {w: P (f t1)}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w):
  rew [fun t => P (f t)] r in rew [P] c in u = w :=
  source_unmap P f r
    (path_reindex_source_unlift P c (f_equal f r) u w
      (rew [fun e => rew [P] e in u = w] K in (hp ⊙[P] hq))).

Lemma source_triangle_fill_boundary {T X: Type} (P: X -> Type) (f: T -> X)
  {t0 t1: T} {a b: X} (c: a = f t0) (r: t0 = t1)
  {p: a = b} {q: b = f t1}
  (K: p • q = path_reindex_source c (f_equal f r))
  {u: P a} {v: P b} {w: P (f t1)}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w):
  rew [fun e => rew [P] e in u = w] K in (hp ⊙[P] hq) =
  path_reindex_source_comp P c (f_equal f r)
    (eq_refl: rew [P] c in u = rew [P] c in u)
    (sigT_map_eq (P := fun t => P (f t)) (Q := P) (f := f)
      (fun _ u => u) (source_triangle_fill P f c r K hp hq)).
Proof.
  unfold source_triangle_fill. rewrite source_unmap_map.
  now exact (eq_sym (path_reindex_source_comp_unlift P c (f_equal f r) u w _)).
Defined.

Lemma source_triangle_fill_boundary_conv {T X: Type} (P: X -> Type) (f: T -> X)
  {t0 t1: T} {a b: X} (c: a = f t0) (r: t0 = t1)
  {p: a = b} {q: b = f t1}
  (K: p • q = path_reindex_source c (f_equal f r))
  {u: P a} {v: P b} {w: P (f t1)}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w):
  rew [fun e => rew [P] e in u = w] K in (hp ⊙[P] hq) =
  path_reindex_source_comp P c (f_equal f r)
    (eq_refl: rew [P] c in u = rew [P] c in u)
    (eq_sym (rew_map P f r (rew [P] c in u)) •
      source_triangle_fill P f c r K hp hq).
Proof.
  refine (source_triangle_fill_boundary P f c r K hp hq • _).
  now exact (f_equal (fun hh: rew [P] f_equal f r in rew [P] c in u = w =>
    path_reindex_source_comp P c (f_equal f r) eq_refl hh)
    (sigT_map_eq_id (P := P) f (source_triangle_fill P f c r K hp hq))).
Defined.

Definition sigT_triangle_reindex
  {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  {x y: A} {z: B} {u: P x} {v: P y} {w: Q z}
  {p: f x = z} {q: z = f y} {r: x = y}
  {hp: rew [Q] p in g x u = w}
  {hq: rew [Q] q in w = g y v} {hr: rew [P] r in u = v}
  {P1: ((f x; g x u): {b: B &T Q b}) = (z; w)}
  (D1: P1 = (=p; hp))
  {P3: ((x; u): {a: A &T P a}) = (y; v)}
  (D3: P3 = (=r; hr))
  (K: p • q = f_equal f r)
  (H: rew [fun s => rew [Q] s in g x u = g y v]
      K in
    (hp ⊙[Q] hq) = sigT_map_eq (P := P) (Q := Q) (f := f) g hr):
  P1 • (=q; hq) =
    f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) P3.
Proof.
  subst P1 P3.
  now exact (sigT_triangle f g K H).
Defined.

Lemma sigT_triangle_reindex_dep
  {A B: Type} {P: A -> Type} {Q: B -> Type}
  {R: {a: A &T P a} -> Type} {S: {b: B &T Q b} -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  (h: forall z: {a: A &T P a}, R z -> S (f z.1; g z.1 z.2))
  {x y: A} {z: B} {u: P x} {v: P y} {w: Q z}
  {a: R (x; u)} {b: R (y; v)} {c: S (z; w)}
  {p: f x = z} {q: z = f y} {r: x = y}
  {hp: rew [Q] p in g x u = w}
  {hq: rew [Q] q in w = g y v} {hr: rew [P] r in u = v}
  {P1: ((f x; g x u): {b: B &T Q b}) = (z; w)}
  (D1: P1 = (=p; hp))
  {P3: ((x; u): {a: A &T P a}) = (y; v)}
  (D3: P3 = (=r; hr))
  (K: p • q = f_equal f r)
  (H: rew [fun s => rew [Q] s in g x u = g y v]
      K in
    (hp ⊙[Q] hq) = sigT_map_eq (P := P) (Q := Q) (f := f) g hr)
  (kp: rew [S] P1 in h (x; u) a = c)
  (kq: rew [S] (=q; hq) in c = h (y; v) b)
  (kr: rew [R] P3 in a = b)
  (HH: rew [fun e => rew [S] e in h (x; u) a = h (y; v) b]
    sigT_triangle_reindex f g D1 D3 K H in (kp ⊙[S] kq) =
      sigT_map_eq (P := R) (Q := S)
          (f := fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) h kr):
  rew [fun e => rew [fun z => {w: Q z &T S (z; w)}] e in
      (g x u; h (x; u) a) = (g y v; h (y; v) b)] K in
    (eq_existT_curried_dep (P := Q) (Q := S) (H := p) (Hu := hp)
      (Hv := rew [fun e => rew [S] e in h (x; u) a = c] D1 in kp)
     ⊙[fun z => {w: Q z &T S (z; w)}]
      eq_existT_curried_dep (P := Q) (Q := S) (H := q) (Hu := hq) (Hv := kq)) =
  sigT_map_eq
    (f := f) (P := fun x => {u: P x &T R (x; u)})
    (Q := fun y => {v: Q y &T S (y; v)})
    (fun x c => (g x c.1; h (x; c.1) c.2))
    (eq_existT_curried_dep (P := P) (Q := R) (H := r) (Hu := hr)
      (Hv := rew [fun e => rew [R] e in a = b] D3 in kr)).
Proof.
  subst P1 P3.
  now exact (sigT_triangle_dep f g h K H kp kq kr HH).
Defined.
