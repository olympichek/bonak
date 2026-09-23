(** The backward round trip from selected component squares.

    Frame paths and displayed paths share the same geometric pastes.
    The component construction reads the existing restriction datum and
    returns the next restriction datum through its chosen layer cells. *)

Import Logic.EqNotations.
Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation
  νGpd.HGpd νGpd.Layer νGpd.Lemmas νGpd.Pasting νGpd Presheaf.Gpd.Presentation.
From Bonak.Lib Require Import Equiv.
From Bonak Require Import Limit.
From Bonak.Equiv.Gpd Require Import PathAlgebra νGpdOfPresheaf PresheafOfνGpd νGpdEquiv.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Translation Canonical SelectedNaturality Exchange Coherence.
Set Primitive Projections.
Set Keyed Unification.
Local Lemma residue_component_boundary {Y T1 D: Type} (P: T1 -> Type) {Dp: D -> Type}
  (r: Y -> T1) (phi: D -> T1) (pe: forall d, Dp d -> P (phi d))
  {y1 y2: Y} (E: y1 = y2)
  {a: T1} (w: P a) (e1: a = r y1)
  {c1: D} (a2: a = phi c1) {v1: Dp c1}
  {c2: D} {n: Dp c2} (hp: ((c1; v1): {d: D &T Dp d}) = (c2; n))
  (trR: phi c2 = r y2)
  (hr: (a2 • f_equal phi (projT1_eq hp)) • trR = e1 • f_equal r E)
  (fp: rew [P] a2 in w = pe c1 v1)
  {u: P (r y1)} {v: P (r y2)}
  (cA: u = rew [P] e1 in w) (cB: v = rew [P] trR in pe c2 n):
  rew [fun edge => rew [P] edge in w = v] hr in
    ((fp ⊙ sigT_map_eq pe (projT2_eq hp)) ⊙ eq_sym cB) =
  eq_sym cA ⊙ sigT_map_eq (Q := P) (fun _ u => u)
    (dpath_change cA (residueFill P r phi pe E w e1 a2 hp trR hr fp) cB).
Proof.
  subst u v.
  refine (residueFill_boundary P r phi pe E w e1 a2 hp trR hr fp • _).
  now exact (f_equal (fun h: rew [fun y => P (r y)] E in
      rew [P] e1 in w = rew [P] trR in pe c2 n =>
      (eq_refl: rew [P] e1 in w = rew [P] e1 in w)
        ⊙ sigT_map_eq (Q := P) (f := r) (fun _ u => u) h)
    (eq_sym (dpath_change_id (residueFill P r phi pe E w e1 a2 hp trR hr fp)))).
Defined.

Local Definition square_strip_prefix {X: Type} {x x' y z w: X}
  {a: x = x'} {p: x' = y} {b: y = w} {q: x = z} {r: z = w}
  (H: a • (p • b) = q • r): p • b = (eq_sym a • q) • r :=
  path_prefix_solve H • eq_trans_assoc _ _ _.

Local Lemma square_strip_prefix_dep {X: Type} (P: X -> Type) {x x' y z w: X}
  {a: x = x'} {p: x' = y} {b: y = w} {q: x = z} {r: z = w}
  (H: a • (p • b) = q • r)
  {u: P x} {u': P x'} {v: P y} {s: P z} {t: P w}
  (ha: rew [P] a in u = u') (hp: rew [P] p in u' = v)
  (hb: rew [P] b in v = t) (hq: rew [P] q in u = s)
  (hr: rew [P] r in s = t)
  (HH: rew [fun e => rew [P] e in u = t] H in
    (ha ⊙ (hp ⊙ hb)) = hq ⊙ hr):
  rew [fun e => rew [P] e in u' = t] square_strip_prefix H in
    (hp ⊙ hb) = (sigT_sym_eq ha ⊙ hq) ⊙ hr.
Proof.
  now exact (sigT_prefix_solve_dep P ha (hp ⊙ hb) (hq ⊙ hr) H HH
    ⊙ sigT_trans_assoc (sigT_sym_eq ha) hq hr).
Defined.

Local Definition square_prepend {X: Type} {x x' y z w: X}
  (a: x = x') {p: x' = y} {b: y = w} {q: x' = z} {r: z = w}
  (H: p • b = q • r): (a • p) • b = (a • q) • r :=
  eq_sym (eq_trans_assoc _ _ _) •
    (whisker_l a H • eq_trans_assoc _ _ _).

Local Lemma square_prepend_dep {X: Type} (P: X -> Type) {x x' y z w: X}
  (a: x = x') {p: x' = y} {b: y = w} {q: x' = z} {r: z = w}
  (H: p • b = q • r)
  {u: P x} {u': P x'} {v: P y} {s: P z} {t: P w}
  (ha: rew [P] a in u = u') (hp: rew [P] p in u' = v)
  (hb: rew [P] b in v = t) (hq: rew [P] q in u' = s)
  (hr: rew [P] r in s = t)
  (HH: rew [fun e => rew [P] e in u' = t] H in (hp ⊙ hb) = hq ⊙ hr):
  rew [fun e => rew [P] e in u = t] square_prepend a H in
    ((ha ⊙ hp) ⊙ hb) = (ha ⊙ hq) ⊙ hr.
Proof.
  pose (HM := sigT_map_eq
    (P := fun e: x' = w => rew [P] e in u' = t)
    (Q := fun e: x = w => rew [P] e in u = t)
    (f := fun e => a • e) (fun e h => ha ⊙ h) HH).
  now exact (sigT_trans_eq_assoc ha hp hb ⊙
    (HM ⊙ sigT_trans_assoc ha hq hr)).
Defined.

Local Lemma section_unit_action {U X: Type} {P: X -> Type}
  (f: U -> X) (s: forall u, P (f u)) {x y: U} (p: x = y):
  sigT_map_eq (P := fun _ => unit) (Q := P) (f := f)
    (fun u _ => s u) (p := p) (u := tt) eq_refl = f_equal_dep_sigT f s p.
Proof. now destruct p. Defined.

Section SourceSectionCoherence.
Context {T U V X: Type} {P: X -> Type} {S: V -> Type}
  (f: U -> X) (s: forall u, P (f u)) (g: V -> X) (r: T -> X)
  (G: forall v, S v -> P (g v))
  {d0 d1: T} (E: d0 = d1) {u0 u1: U} (e: u0 = u1)
  {v0 v1: V} (p: v0 = v1) (cq: f u1 = r d0) (cr: g v1 = r d1)
  (k: f u0 = g v0) (a: S v0) (hk: rew [P] k in s u0 = G v0 a)
  (H: f_equal f e • (cq • f_equal r E) = k • (f_equal g p • cr))
  (b: S v1) (cb: b = rew [S] p in a)
  {w0: P (r d0)} {w1: P (r d1)}
  (c0: w0 = rew [P] cq in s u1) (c1: w1 = rew [P] cr in G v1 b).

Local Definition section_coherence_edge:
  rew [fun d => P (r d)] E in w0 = w1 :=
  f_equal (fun w => rew [fun d => P (r d)] E in w) c0
  • (eq_refl • (rew_cohLayer_hex (P := P) (rf0 := r)
      (F := fun u (_: unit) => s u) (G := G) (E1 := E)
      (C2 := e) (D2 := p) (C1 := cq) (D1 := cr) (aL := tt) hk H
    • (eq_sym (f_equal (fun b => rew [P] cr in G v1 b) cb) • eq_sym c1))).

Local Definition section_coherence_square:
  (f_equal f e • cq) • f_equal r E = k • (f_equal g p • cr) :=
  eq_sym (eq_trans_assoc _ _ _) • H.

Local Lemma section_coherence_boundary:
  rew [fun path => rew [P] path in s u0 = w1] section_coherence_square in
    ((f_equal_dep_sigT f s e ⊙[P] eq_sym c0)
      ⊙[P] sigT_map_eq (Q := P) (f := r) (fun _ u => u) section_coherence_edge) =
  hk ⊙[P] (sigT_map_eq (Q := P) G (eq_sym cb) ⊙[P] eq_sym c1).
Proof.
  pose (Hcore := rew_coh2Painting_restr0_edges (P := P)
    (fun u (_: unit) => s u) G E e p cq cr k tt a hk H
    (rew [fun _ => unit] e in tt) eq_refl b cb w0 c0 w1 c1
    (f_equal_dep_sigT f s e) (eq_sym (section_unit_action f s e))
    (eq_sym c0) eq_refl (sigT_map_eq (Q := P) G (eq_sym cb)) eq_refl
    (eq_sym c1) eq_refl).
  unfold section_coherence_square.
  rewrite <- (rew_compose (fun path => rew [P] path in s u0 = w1)).
  rewrite sigT_trans_eq_assoc.
  unfold section_coherence_edge.
  rewrite sigT_map_eq_id.
  now exact Hcore.
Defined.
End SourceSectionCoherence.

Local Definition exchange_left_route {B A: Type} (f: B -> A)
  {b0 b1 b2 b3: B} {x z: A} (i: x = f b0)
  (p: b0 = b1) (q: b1 = b2) (r: b3 = b2) (t: f b3 = z):
  ((i • f_equal f p) • f_equal f q) • (eq_sym (f_equal f r) • t) =
  (i • f_equal f (p • (q • eq_sym r))) • t.
Proof. now destruct r, q, p, t. Defined.

Local Lemma exchange_left_route_dep {B A: Type} (f: B -> A)
  (PA: A -> Type) (PB: B -> Type) (F: forall b, PB b -> PA (f b))
  {b0 b1 b2 b3: B} {x z: A} (i: x = f b0)
  (p: b0 = b1) (q: b1 = b2) (r: b3 = b2) (t: f b3 = z)
  {u: PA x} {v: PA z} {v0: PB b0} {v1: PB b1} {v2: PB b2} {v3: PB b3}
  (hi: rew [PA] i in u = F b0 v0)
  (hp: rew [PB] p in v0 = v1) (hq: rew [PB] q in v1 = v2)
  (hr: rew [PB] r in v3 = v2) (ht: rew [PA] t in F b3 v3 = v):
  rew [fun e => rew [PA] e in u = v] exchange_left_route f i p q r t in
    (((hi ⊙ sigT_map_eq F hp) ⊙ sigT_map_eq F hq)
      ⊙ (sigT_sym_eq (sigT_map_eq F hr) ⊙ ht)) =
  (hi ⊙ sigT_map_eq F (hp ⊙ (hq ⊙ sigT_sym_eq hr))) ⊙ ht.
Proof.
  destruct r, q, p.
  cbn in hp, hq, hr.
  subst v1 v2 v3.
  destruct ht, t.
  now reflexivity.
Defined.

(** A restriction map distributes over the previous identification and
    the mapped canonical pair, keeping their common composition witness. *)
Local Definition exchange_right_route {B X A: Type} (f: X -> A) (g: B -> X)
  {b0 b1: B} {x: X} {z: A} (k: z = f x)
  (p: x = g b0) (j: b0 = b1):
  k • f_equal f (p • f_equal g j) =
  (k • f_equal f p) • f_equal (fun b => f (g b)) j.
Proof. now destruct j. Defined.

Local Lemma exchange_right_route_dep {B X A: Type} (f: X -> A) (g: B -> X)
  (PA: A -> Type) (PX: X -> Type) (PB: B -> Type)
  (F: forall x, PX x -> PA (f x)) (G: forall b, PB b -> PX (g b))
  {b0 b1: B} {x: X} {z: A} (k: z = f x)
  (p: x = g b0) (j: b0 = b1)
  {u: PA z} {v: PX x} {b: PB b0} {b': PB b1}
  (hk: rew [PA] k in u = F x v)
  (hp: rew [PX] p in v = G b0 b) (hj: rew [PB] j in b = b'):
  rew [fun e => rew [PA] e in u = F (g b1) (G b1 b')]
    exchange_right_route f g k p j in
    (hk ⊙ sigT_map_eq F (hp ⊙ sigT_map_eq G hj)) =
  (hk ⊙ sigT_map_eq F hp) ⊙
    sigT_map_eq (P := PB) (Q := PA) (f := fun b => f (g b))
      (fun b v => F (g b) (G b v)) hj.
Proof.
  destruct j.
  cbn in hj. subst b'.
  now reflexivity.
Defined.


(** The actual endpoint is read through the same geometric comparison
    in the frame path and its displayed painting. *)
Local Definition target_identification {B A: Type} (f: B -> A)
  {x: A} {b b': B} (alpha: b = b') (p: x = f b'):
  x = f b := rew [fun z => x = f z] eq_sym alpha in p.

Local Definition target_identification_dep {B A: Type} {P: A -> Type}
  (f: B -> A) (g: forall b, P (f b)) {x: A} {u: P x}
  {b b': B} (alpha: b = b') (p: x = f b')
  (hp: rew [P] p in u = g b'):
  rew [P] target_identification f alpha p in u = g b.
Proof. destruct alpha. now exact hp. Defined.

Local Lemma restricted_target_identification {B A C: Type}
  (f: B -> A) (r: A -> C) {x: A}
  {b b': B} (alpha: b = b') (p: x = f b')
  {y: C} (s: y = r x):
  (s • f_equal r p) • f_equal (fun b => r (f b)) (eq_sym alpha) =
  s • f_equal r (target_identification f alpha p).
Proof. destruct alpha. now reflexivity. Defined.

Local Lemma restricted_target_identification_dep {B A C: Type}
  {P: A -> Type} {Q: C -> Type}
  (f: B -> A) (g: forall b, P (f b))
  (r: A -> C) (rp: forall a, P a -> Q (r a))
  {x: A} {u: P x} {b b': B} (alpha: b = b')
  (p: x = f b') (hp: rew [P] p in u = g b')
  {y: C} {v: Q y} (s: y = r x) (hs: rew [Q] s in v = rp x u):
  rew [fun e => rew [Q] e in v = rp (f b) (g b)]
    restricted_target_identification f r alpha p s in
    ((hs ⊙ sigT_map_eq (P := P) (Q := Q) (f := r) rp hp) ⊙
      f_equal_dep_sigT (fun b => r (f b)) (fun b => rp (f b) (g b)) (eq_sym alpha)) =
  hs ⊙ sigT_map_eq (P := P) (Q := Q) (f := r) rp
    (target_identification_dep f g alpha p hp).
Proof. destruct alpha. now reflexivity. Defined.

Local Definition frame_split_beta {A: Type} {L: A -> Type}
  {x y: A} {u: L x} {v: L y} (p: x = y) (h: rew [L] p in u = v)
  (P: (x; u) = (y; v)) (split: P = (=p; h)):
  projT1_eq P = p :=
  f_equal (@projT1_eq A L (x; u) (y; v)) split
    • projT1_eq (totalPathDecodeEncode p h).

Local Lemma frame_split_beta_dep {A: Type} {L: A -> Type}
  {R: {a: A &T L a} -> Type} {x y: A} {u: L x} {v: L y}
  {cu: R (x; u)} {cv: R (y; v)}
  (p: x = y) (h: rew [L] p in u = v)
  (P: (x; u) = (y; v)) (split: P = (=p; h))
  (paint: rew [R] P in cu = cv)
  (previous: rew [fun a => {l: L a &T R (a; l)}] p in (u; cu) = (v; cv))
  (painting_split: previous = @eq_existT_curried_dep A x L R y p u cu v cv h
    (rew [fun e => rew [R] e in cu = cv] split in paint)):
  rew [fun e => rew [fun a => {l: L a &T R (a; l)}] e in
      (u; cu) = (v; cv)] frame_split_beta p h P split in
    pair_path_display P paint = previous.
Proof. subst P. destruct h, p. now exact (eq_sym painting_split). Defined.

Local Lemma pair_path_display_rebase {A: Type} {L: A -> Type}
  {R: {a: A &T L a} -> Type} {x y: {a: A &T L a}}
  {u: R x} {v: R y} {p q: x = y} (E: p = q)
  (h: rew [R] p in u = v):
  rew [fun e => rew [fun a => {l: L a &T R (a; l)}] e in
      (x.2; u) = (y.2; v)] f_equal (@projT1_eq A L x y) E in
    pair_path_display p h =
  pair_path_display q (rew [fun e => rew [R] e in u = v] E in h).
Proof. destruct E. now reflexivity. Defined.

Local Definition target_identification_map {B A C: Type}
  (f: B -> A) (r: A -> C) {x: A} {b b': B}
  (alpha: b = b') (p: x = f b'):
  f_equal r (target_identification f alpha p) =
  target_identification (fun b => r (f b)) alpha (f_equal r p).
Proof. destruct alpha. now reflexivity. Defined.

Local Lemma target_identification_map_dep {B A: Type} {L: A -> Type}
  {R: {a: A &T L a} -> Type}
  (f: B -> {a: A &T L a}) (g: forall b, R (f b))
  {x: {a: A &T L a}} {u: R x} {b b': B}
  (alpha: b = b') (p: x = f b') (hp: rew [R] p in u = g b'):
  rew [fun e => rew [fun a => {l: L a &T R (a; l)}] e in
      (x.2; u) = ((f b).2; g b)]
    target_identification_map f (fun z => z.1) alpha p in
    pair_path_display (target_identification f alpha p)
      (target_identification_dep f g alpha p hp) =
  target_identification_dep (fun b => (f b).1) (fun b => ((f b).2; g b))
    alpha (projT1_eq p) (pair_path_display p hp).
Proof. destruct alpha. now reflexivity. Defined.

Local Lemma target_identification_parameter_dep {B A: Type} {P: A -> Type}
  (f: B -> A) (g: forall b, P (f b)) {x: A} {u: P x}
  {b b': B} (alpha: b = b') {p q: x = f b'} (E: p = q)
  {hp: rew [P] p in u = g b'} {hq: rew [P] q in u = g b'}
  (HE: rew [fun r => rew [P] r in u = g b'] E in hp = hq):
  rew [fun r => rew [P] r in u = g b]
    f_equal (target_identification f alpha) E in
    target_identification_dep f g alpha p hp =
  target_identification_dep f g alpha q hq.
Proof. destruct alpha, E. now exact HE. Defined.

Local Definition target_identification_domain {B B' A: Type}
  (f: B' -> A) (v: B -> B') {x: A} {b b': B}
  (alpha: b = b') (p: x = f (v b')):
  target_identification f (f_equal v alpha) p =
  target_identification (fun b => f (v b)) alpha p.
Proof. destruct alpha. now reflexivity. Defined.

Local Lemma target_identification_domain_dep {B B' A: Type} {P: A -> Type}
  (f: B' -> A) (g: forall b, P (f b)) (v: B -> B')
  {x: A} {u: P x} {b b': B} (alpha: b = b')
  (p: x = f (v b')) (hp: rew [P] p in u = g (v b')):
  rew [fun r => rew [P] r in u = g (v b)]
    target_identification_domain f v alpha p in
    target_identification_dep f g (f_equal v alpha) p hp =
  target_identification_dep (fun b => f (v b)) (fun b => g (v b)) alpha p hp.
Proof. destruct alpha. now reflexivity. Defined.

Local Lemma target_identification_path_dep {B A: Type} {P: A -> Type}
  (f: B -> A) (g: forall b, P (f b)) {x: A} {u: P x}
  {b b': B} {alpha beta: b = b'} (E: alpha = beta)
  (p: x = f b') (hp: rew [P] p in u = g b'):
  rew [fun r => rew [P] r in u = g b]
    f_equal (fun c => target_identification f c p) E in
    target_identification_dep f g alpha p hp =
  target_identification_dep f g beta p hp.
Proof. destruct E. now reflexivity. Defined.

Local Definition frame_view_prefix {B A: Type} {L: A -> Type}
  (f: B -> {a: A &T L a}) {x: {a: A &T L a}} {b b': B}
  (alpha: b = b') (P: x = f b) (Q: x = f b')
  (p: x.1 = (f b).1) (h: rew [L] p in x.2 = (f b).2)
  (q: x.1 = (f b').1) (k: rew [L] q in x.2 = (f b').2)
  (SP: P = (=p; h)) (SQ: Q = (=q; k))
  (V: P = target_identification f alpha Q):
  p = target_identification (fun b => (f b).1) alpha q :=
  eq_sym (frame_split_beta p h P SP)
  • (f_equal (@projT1_eq A L x (f b)) V
  • (target_identification_map f (fun z => z.1) alpha Q
  • f_equal (target_identification (fun b => (f b).1) alpha)
      (frame_split_beta q k Q SQ))).

Local Lemma frame_view_prefix_dep {B A: Type} {L: A -> Type}
  {R: {a: A &T L a} -> Type}
  (f: B -> {a: A &T L a}) (g: forall b, R (f b))
  {x: {a: A &T L a}} {u: R x} {b b': B}
  (alpha: b = b') (P: x = f b) (Q: x = f b')
  (p: x.1 = (f b).1) (h: rew [L] p in x.2 = (f b).2)
  (q: x.1 = (f b').1) (k: rew [L] q in x.2 = (f b').2)
  (SP: P = (=p; h)) (SQ: Q = (=q; k))
  (V: P = target_identification f alpha Q)
  (HP: rew [R] P in u = g b) (HQ: rew [R] Q in u = g b')
  (hp: rew [fun a => {l: L a &T R (a; l)}] p in (x.2; u) = ((f b).2; g b))
  (hq: rew [fun a => {l: L a &T R (a; l)}] q in (x.2; u) = ((f b').2; g b'))
  (PS: hp = eq_existT_curried_dep (H := p) (Hu := h)
    (Hv := rew [fun e => rew [R] e in u = g b] SP in HP))
  (QS: hq = eq_existT_curried_dep (H := q) (Hu := k)
    (Hv := rew [fun e => rew [R] e in u = g b'] SQ in HQ))
  (HV: rew [fun e => rew [R] e in u = g b] V in HP =
    target_identification_dep f g alpha Q HQ):
  rew [fun e => rew [fun a => {l: L a &T R (a; l)}] e in
      (x.2; u) = ((f b).2; g b)]
    frame_view_prefix f alpha P Q p h q k SP SQ V in hp =
  target_identification_dep (fun b => (f b).1) (fun b => ((f b).2; g b))
    alpha q hq.
Proof.
  refine (sigT_sym_eq (frame_split_beta_dep p h P SP HP hp PS) ⊙ _).
  refine ((pair_path_display_rebase V HP
    • f_equal (pair_path_display (target_identification f alpha Q)) HV) ⊙ _).
  refine (target_identification_map_dep f g alpha Q HQ ⊙ _).
  now exact (target_identification_parameter_dep
    (fun b => (f b).1) (fun b => ((f b).2; g b)) alpha
    (frame_split_beta q k Q SQ) (frame_split_beta_dep q k Q SQ HQ hq QS)).
Defined.

(** Mapping the displayed component of a pair path and acting on the
    corresponding section use the same map-composition comparison. *)
Local Lemma pair_map_section_dep {B A: Type} {PB: B -> Type} {PA: A -> Type}
  (f: B -> A) (F: forall b, PB b -> PA (f b))
  {u v: {b: B &T PB b}} (j: u = v):
  rew [fun e => rew [PA] e in F u.1 u.2 = F v.1 v.2]
    (f_equal_compose (fun z: {b: B &T PB b} => z.1) f j) in
    sigT_map_eq (P := PB) (Q := PA) (f := f) F (projT2_eq j) =
  f_equal_dep_sigT (fun z: {b: B &T PB b} => f z.1)
    (fun z => F z.1 z.2) j.
Proof. now destruct j, u. Defined.

(** Restrict the owned frame-view comparison. The pair-map composition
    comparison is selected before its painting companion is used. *)
Local Definition view_restriction_cell {E X A: Type} {PE: E -> Type}
  (f: E -> X) (r: X -> A) {z z': {e: E &T PE e}} (alpha: z = z')
  {x: X} (canonical: x = f z'.1) (actual: x = f z.1)
  (view: actual = target_identification (fun z => f z.1) alpha canonical)
  {a: A} (s: a = r x):
  (s • f_equal r canonical) •
    f_equal (fun e => r (f e)) (projT1_eq (eq_sym alpha)) = s • f_equal r actual :=
  whisker_l (s • f_equal r canonical)
    (f_equal_compose (fun z: {e: E &T PE e} => z.1) (fun e => r (f e)) (eq_sym alpha))
  • (restricted_target_identification (fun z => f z.1) r alpha canonical s
  • whisker_l s (f_equal (fun p => f_equal r p) (eq_sym view))).

Local Lemma view_restriction_cell_dep {E X A: Type} {PE: E -> Type}
  (f: E -> X) (r: X -> A) (PX: X -> Type) (PA: A -> Type)
  (F: forall e, PE e -> PX (f e)) (R: forall x, PX x -> PA (r x))
  {z z': {e: E &T PE e}} (alpha: z = z')
  {x: X} (canonical: x = f z'.1) (actual: x = f z.1)
  (view: actual = target_identification (fun z => f z.1) alpha canonical)
  {a: A} (s: a = r x) {u: PX x} {v: PA a}
  (hc: rew [PX] canonical in u = F z'.1 z'.2)
  (ha: rew [PX] actual in u = F z.1 z.2)
  (hs: rew [PA] s in v = R x u)
  (Hview: DPathCellOver (P := PX) ha
    (target_identification_dep (fun z => f z.1) (fun z => F z.1 z.2)
      alpha canonical hc) view):
  DPathCellOver (P := PA)
    ((hs ⊙[PA] sigT_map_eq R hc) ⊙[PA]
      sigT_map_eq (P := PE) (Q := PA) (f := fun e => r (f e))
        (fun e v => R (f e) (F e v)) (projT2_eq (eq_sym alpha)))
    (hs ⊙[PA] sigT_map_eq R ha)
    (view_restriction_cell f r alpha canonical actual view s).
Proof.
  pose (H0 := displayed_whisker_left PA (s • f_equal r canonical) _
    (hs ⊙[PA] sigT_map_eq R hc)
    (pair_map_section_dep (fun e => r (f e))
      (fun e v => R (f e) (F e v)) (eq_sym alpha))).
  pose (H1 := restricted_target_identification_dep
    (fun z => f z.1) (fun z => F z.1 z.2) r R alpha canonical hc s hs).
  pose (HM := sigT_map_eq
    (P := fun p: x = f z.1 => rew [PX] p in u = F z.1 z.2)
    (Q := fun p: r x = r (f z.1) => rew [PA] p in R x u = R (f z.1) (F z.1 z.2))
    (f := fun p => f_equal r p) (fun p h => sigT_map_eq R h)
    (sigT_sym_eq Hview)).
  pose (H2 := displayed_whisker_left PA s _ hs HM).
  now exact (H0 ⊙ (H1 ⊙ H2)).
Defined.

(** Carry a selected restriction cell to the actual endpoint view,
    using the translation's naturality and the same identification law. *)
Local Definition retarget_restriction_cell {E B A: Type}
  (phi: B -> A) (r: E -> B) (g: E -> A)
  (t: forall e, phi (r e) = g e)
  {e0 e1: E} (c: e0 = e1) {a: A} {b0: B}
  (i: a = phi b0) (b: b0 = r e0) (n0: a = g e0) (n1: a = g e1)
  (HN: (i • f_equal phi b) • t e0 = n0)
  (HT: f_equal phi (f_equal r c) • t e1 = t e0 • f_equal g c)
  (HA: n0 • f_equal g c = n1):
  (i • f_equal phi (b • f_equal r c)) • t e1 = n1 :=
  eq_sym (eq_trans_assoc _ _ _)
  • (whisker_l i (map_compose_tail phi b (f_equal r c) (t e1))
  • (eq_trans_assoc _ _ _
  • (whisker_l (i • f_equal phi b) HT
  • (eq_trans_assoc _ _ _
  • (whisker_r HN (f_equal g c) • HA))))).

Local Lemma retarget_restriction_cell_dep {E B A: Type}
  (phi: B -> A) (r: E -> B) (g: E -> A)
  (t: forall e, phi (r e) = g e)
  {e0 e1: E} (c: e0 = e1) {a: A} {b0: B}
  (i: a = phi b0) (b: b0 = r e0) (n0: a = g e0) (n1: a = g e1)
  (HN: (i • f_equal phi b) • t e0 = n0)
  (HT: f_equal phi (f_equal r c) • t e1 = t e0 • f_equal g c)
  (HA: n0 • f_equal g c = n1)
  (PA: A -> Type) (PB: B -> Type) (F: forall b, PB b -> PA (phi b))
  {u: PA a} {v: PB b0} {v0: PB (r e0)} {v1: PB (r e1)}
  {w0: PA (g e0)} {w1: PA (g e1)}
  (hi: rew [PA] i in u = F b0 v) (hb: rew [PB] b in v = v0)
  (hc: rew [PB] f_equal r c in v0 = v1)
  (hg: rew [PA] f_equal g c in w0 = w1)
  (ht0: rew [PA] t e0 in F (r e0) v0 = w0)
  (ht1: rew [PA] t e1 in F (r e1) v1 = w1)
  (hn0: rew [PA] n0 in u = w0) (hn1: rew [PA] n1 in u = w1)
  (DHN: DPathCellOver ((hi ⊙ sigT_map_eq F hb) ⊙ ht0) hn0 HN)
  (DHT: DPathCellOver (sigT_map_eq F hc ⊙ ht1) (ht0 ⊙ hg) HT)
  (DHA: DPathCellOver (hn0 ⊙ hg) hn1 HA):
  DPathCellOver ((hi ⊙ sigT_map_eq F (hb ⊙ hc)) ⊙ ht1) hn1
    (retarget_restriction_cell phi r g t c i b n0 n1 HN HT HA).
Proof.
  pose (H0 := sigT_trans_eq_assoc hi (sigT_map_eq F (hb ⊙ hc)) ht1).
  pose (H1 := displayed_whisker_left PA i _ hi
    (map_compose_tail_dep phi F hb hc ht1)).
  pose (H2 := sigT_trans_assoc hi (sigT_map_eq F hb) (sigT_map_eq F hc ⊙ ht1)).
  pose (H3 := displayed_whisker_left PA (i • f_equal phi b) _
    (hi ⊙ sigT_map_eq F hb) DHT).
  pose (H4 := sigT_trans_assoc (hi ⊙ sigT_map_eq F hb) ht0 hg).
  pose (H5 := displayed_whisker_r PA HN (f_equal g c) hg DHN).
  now exact (H0 ⊙ (H1 ⊙ (H2 ⊙ (H3 ⊙ (H4 ⊙ (H5 ⊙ DHA)))))).
Defined.

Local Definition exchange_section_cell {U B A: Type}
  (f: U -> A) (c: U -> B) (phi: B -> A)
  (i: forall u, f u = phi (c u)) {x y: U} (h: x = y):
  f_equal f h • i y = i x • f_equal phi (f_equal c h).
Proof. destruct h. now exact (eq_trans_refl_l (i x)). Defined.

Local Lemma exchange_section_cell_dep {U B A: Type}
  (f: U -> A) (c: U -> B) (phi: B -> A)
  (i: forall u, f u = phi (c u))
  (PA: A -> Type) (PB: B -> Type) (F: forall b, PB b -> PA (phi b))
  (sa: forall u, PA (f u)) (sb: forall u, PB (c u))
  (hi: forall u, rew [PA] i u in sa u = F (c u) (sb u))
  {x y: U} (h: x = y):
  rew [fun e => rew [PA] e in sa x = F (c y) (sb y)]
    exchange_section_cell f c phi i h in
    (f_equal_dep_sigT f sa h ⊙[PA] hi y) =
  hi x ⊙[PA] sigT_map_eq F (f_equal_dep_sigT c sb h).
Proof.
  destruct h.
  now exact (displayed_left_unit PA (i x) (hi x)).
Defined.

Local Definition exchange_map_cell {E B A: Type}
  (r: E -> B) (phi: B -> A) (g: E -> A)
  (t: forall e, phi (r e) = g e) {x y: E} (j: x = y):
  f_equal phi (f_equal r j) • t y = t x • f_equal g j.
Proof. destruct j. now exact (eq_trans_refl_l (t x)). Defined.

Local Lemma exchange_map_cell_dep {E B A: Type}
  (r: E -> B) (phi: B -> A) (g: E -> A)
  (t: forall e, phi (r e) = g e)
  (PE: E -> Type) (PB: B -> Type) (PA: A -> Type)
  (R: forall e, PE e -> PB (r e)) (F: forall b, PB b -> PA (phi b))
  (G: forall e, PE e -> PA (g e))
  (ht: forall e v, rew [PA] t e in F (r e) (R e v) = G e v)
  {x y: E} (j: x = y) {u: PE x} {v: PE y} (hj: rew [PE] j in u = v):
  rew [fun e => rew [PA] e in F (r x) (R x u) = G y v]
    exchange_map_cell r phi g t j in
    (sigT_map_eq F (sigT_map_eq R hj) ⊙[PA] ht y v) =
  ht x u ⊙[PA] sigT_map_eq G hj.
Proof.
  destruct hj, j.
  now exact (displayed_left_unit PA (t x) (ht x u)).
Defined.

Local Lemma swap_as_inverse {A: Type} (P: A -> Type) {x y: A} (p: x = y)
  {u: P x} {v: P y} (h: v = rew [P] p in u):
  rewSwapSym P p h = sigT_sym_eq (eq_sym h).
Proof. destruct p. cbn in h. subst v. now reflexivity. Defined.

(** Decode a supplied geometric pair-cell once, retaining its two
    components and the exact common computation witness. *)
Local Definition pair_cell_code {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} {p q: x = y}
  {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  (H: (=p; hp) = (=q; hq)):
  ((p; hp): {e: x = y &T rew [P] e in u = v}) = (q; hq) :=
  eq_sym (totalPathDecodeEncode p hp)
  • (f_equal (fun e: ((x; u): {a: A &T P a}) = (y; v) =>
      (projT1_eq e; projT2_eq e)) H • totalPathDecodeEncode q hq).

Local Definition pair_cell_frame {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} {p q: x = y}
  {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  (H: (=p; hp) = (=q; hq)): p = q :=
  projT1_eq (pair_cell_code H).

Local Definition pair_cell_frame_dep {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} {p q: x = y}
  {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  (H: (=p; hp) = (=q; hq)):
  DPathCellOver hp hq (pair_cell_frame H) :=
  projT2_eq (pair_cell_code H).

Local Definition geometric_square_frame {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {l r: ((x; u): {a: A &T P a}) = (y; v)}
  {p q: x = y} {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  (EL: l = (=p; hp)) (ER: r = (=q; hq)) (H: l = r): p = q :=
  pair_cell_frame (eq_sym EL • (H • ER)).

Local Definition geometric_square_frame_dep {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {l r: ((x; u): {a: A &T P a}) = (y; v)}
  {p q: x = y} {hp: rew [P] p in u = v} {hq: rew [P] q in u = v}
  (EL: l = (=p; hp)) (ER: r = (=q; hq)) (H: l = r):
  DPathCellOver hp hq (geometric_square_frame EL ER H) :=
  pair_cell_frame_dep (eq_sym EL • (H • ER)).

(** The exchange transfer pastes the two naturality squares around the
    mapped exchange square, then uses the selected restriction cell. *)
Local Definition restriction_exchange_paste {U B E A: Type}
  (P: U -> A) (C: U -> B) (Psi: B -> A) (R: E -> B) (G: E -> A)
  (I: forall u, P u = Psi (C u)) (T: forall z, Psi (R z) = G z)
  {x y: U} (h: x = y) {z z': E} (j: z = z')
  (d: C y = R z') (b: C x = R z) (n: P x = G z)
  (HI: f_equal P h • I y = I x • f_equal Psi (f_equal C h))
  (HT: f_equal Psi (f_equal R j) • T z' = T z • f_equal G j)
  (HS: f_equal C h • d = b • f_equal R j)
  (HN: (I x • f_equal Psi b) • T z = n):
  f_equal P h • ((I y • f_equal Psi d) • T z') = n • f_equal G j :=
  square_compose (square_compose HI (square_map Psi HS)) HT
    • whisker_r HN (f_equal G j).

(** Every displayed input is over the corresponding selected square.
    The result is over the exact exchange transfer chosen above. *)
Local Lemma restriction_exchange_paste_dep {U B E A: Type}
  (P: U -> A) (C: U -> B) (Psi: B -> A) (R: E -> B) (G: E -> A)
  (I: forall u, P u = Psi (C u)) (T: forall z, Psi (R z) = G z)
  {x y: U} (h: x = y) {z z': E} (j: z = z')
  (d: C y = R z') (b: C x = R z) (n: P x = G z)
  (HI: f_equal P h • I y = I x • f_equal Psi (f_equal C h))
  (HT: f_equal Psi (f_equal R j) • T z' = T z • f_equal G j)
  (HS: f_equal C h • d = b • f_equal R j)
  (HN: (I x • f_equal Psi b) • T z = n)
  (PA: A -> Type) (PB: B -> Type) (F: forall a, PB a -> PA (Psi a))
  {ux: PA (P x)} {uy: PA (P y)} {vx: PB (C x)} {vy: PB (C y)}
  {vz: PB (R z)} {vz': PB (R z')} {wz: PA (G z)} {wz': PA (G z')}
  (hh: rew [PA] f_equal P h in ux = uy)
  (hc: rew [PB] f_equal C h in vx = vy)
  (hj: rew [PB] f_equal R j in vz = vz')
  (hg: rew [PA] f_equal G j in wz = wz')
  (hd: rew [PB] d in vy = vz') (hb: rew [PB] b in vx = vz)
  (ix: rew [PA] I x in ux = F (C x) vx)
  (iy: rew [PA] I y in uy = F (C y) vy)
  (tz: rew [PA] T z in F (R z) vz = wz)
  (tz': rew [PA] T z' in F (R z') vz' = wz')
  (hn: rew [PA] n in ux = wz)
  (DHI: rew [fun e => rew [PA] e in ux = F (C y) vy] HI in
    (hh ⊙ iy) = ix ⊙ sigT_map_eq F hc)
  (DHT: rew [fun e => rew [PA] e in F (R z) vz = wz'] HT in
    (sigT_map_eq F hj ⊙ tz') = tz ⊙ hg)
  (DHS: rew [fun e => rew [PB] e in vx = vz'] HS in
    (hc ⊙ hd) = hb ⊙ hj)
  (DHN: rew [fun e => rew [PA] e in ux = wz] HN in
    ((ix ⊙ sigT_map_eq F hb) ⊙ tz) = hn):
  rew [fun e => rew [PA] e in ux = wz']
    restriction_exchange_paste P C Psi R G I T h j d b n HI HT HS HN in
    (hh ⊙ ((iy ⊙ sigT_map_eq F hd) ⊙ tz')) = hn ⊙ hg.
Proof.
  pose (SM := square_map_dep (P := PB) (Q := PA) Psi F HS hb hd hc hj DHS).
  pose (H1 := square_compose_dep PA HI (square_map Psi HS)
    ix (sigT_map_eq F hb) iy (sigT_map_eq F hd)
    hh (sigT_map_eq F hc) (sigT_map_eq F hj) DHI SM).
  pose (H2 := square_compose_dep PA (square_compose HI (square_map Psi HS)) HT
    (ix ⊙ sigT_map_eq F hb) tz (iy ⊙ sigT_map_eq F hd) tz'
    hh (sigT_map_eq F hj) hg H1 DHT).
  pose (H3 := sigT_map_eq
    (P := fun e: P x = G z => rew [PA] e in ux = wz)
    (Q := fun e: P x = G z' => rew [PA] e in ux = wz')
    (f := fun e => e • f_equal G j) (fun e hh => hh ⊙ hg) DHN).
  now exact (H2 ⊙ H3).
Defined.

Module Positive (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Import A.
Module K.
Import A.
Module Export SN := SelectedNaturality.SelectedNaturality A Base Translations.
Module C := SN.C.
Module Core := C.Association.Succ.RT.
Module MapKit.
Import A.
Module Export L := LayerGpdTheory A.
Definition mapped_layer_square {T U X Y: Type}
  (r: arity -> T -> X) (s: arity -> U -> Y)
  (f: T -> U) (phi: X -> Y)
  (eta: forall d ω, phi (r ω d) = s ω (f d))
  {d0 d1: T} (p: d0 = d1) (ω: arity):
  f_equal phi (f_equal (r ω) p) • eta d1 ω =
  eta d0 ω • f_equal (s ω) (f_equal f p) :=
  f_equal_naturality (r ω) f phi (s ω) (fun d => eta d ω) p.

Lemma layer_map_value {T U: Type} {B: T -> arity -> HGpd}
  {C: U -> arity -> HGpd} (f: T -> U)
  (G: forall d ω, B d ω -> C (f d) ω)
  {d0 d1: T} (p: d0 = d1) {l0: Layer (B d0)} {l1: Layer (B d1)}
  (h: rew [fun d => Layer (B d)] p in l0 = l1) (ω: arity):
  sigT_map_eq (P := fun d => GDom (Layer (B d)))
    (Q := fun u => GDom (C u ω)) (f := f)
    (fun d l => nth (lmap (G d) l) ω) h =
  nth_dpath (Bd := C)
    (sigT_map_eq (P := fun d => GDom (Layer (B d)))
      (Q := fun u => GDom (Layer (C u))) (f := f)
      (fun d l => lmap (G d) l) h) ω.
Proof. now destruct h, p. Defined.

Lemma mapped_layer_square_dep {T U X Y: Type}
  (r: arity -> T -> X) (s: arity -> U -> Y)
  (f: T -> U) (phi: X -> Y)
  (eta: forall d ω, phi (r ω d) = s ω (f d))
  (P: X -> HGpd) (Q: Y -> HGpd) (F: forall x, P x -> Q (phi x))
  {d0 d1: T} (p: d0 = d1)
  {l0: Layer (fun ω => P (r ω d0))} {l1: Layer (fun ω => P (r ω d1))}
  (h: rew [fun d => Layer (fun ω => P (r ω d))] p in l0 = l1)
  (ω: arity):
  let G := fun d ζ v => rew [fun y => GDom (Q y)] eta d ζ in F (r ζ d) v in
  rew [fun e => rew [fun y => GDom (Q y)] e in F (r ω d0) (nth l0 ω) =
    nth (lmap (G d1) l1) ω] mapped_layer_square r s f phi eta p ω in
    (sigT_map_eq (Q := fun y => GDom (Q y)) F
      (sigT_map_eq (P := fun d => GDom (Layer (fun ζ => P (r ζ d))))
        (Q := fun x => GDom (P x)) (f := r ω) (fun d l => nth l ω) h)
      ⊙[fun y => GDom (Q y)] eq_sym (nth_lmap (G d1) l1 ω)) =
  eq_sym (nth_lmap (G d0) l0 ω) ⊙[fun y => GDom (Q y)]
    sigT_map_eq (P := fun u => GDom (Q (s ω u)))
      (Q := fun y => GDom (Q y)) (f := s ω) (fun _ u => u)
      (nth_dpath (Bd := fun u ζ => Q (s ζ u))
        (sigT_map_eq
          (P := fun d => GDom (Layer (fun ζ => P (r ζ d))))
          (Q := fun u => GDom (Layer (fun ζ => Q (s ζ u))))
          (f := f) (fun d l => lmap (G d) l) h) ω).
Proof.
  intro G.
  pose (HN := f_equal_naturality_dep
    (PA := fun d => GDom (Layer (fun ζ => P (r ζ d))))
    (PB := fun x => GDom (P x)) (PC := fun u => GDom (Q (s ω u)))
    (PD := fun y => GDom (Q y))
    (r ω) f phi (s ω) (fun d l => nth l ω)
    (fun d l => nth (lmap (G d) l) ω) F (fun _ u => u)
    (fun d => eta d ω) (fun d l => eq_sym (nth_lmap (G d) l ω)) p h).
  refine (HN • _).
  now exact (f_equal (fun hp: rew [fun u => GDom (Q (s ω u))] f_equal f p in
      nth (lmap (G d0) l0) ω = nth (lmap (G d1) l1) ω =>
      eq_sym (nth_lmap (G d0) l0 ω) ⊙[fun y => GDom (Q y)]
        sigT_map_eq (Q := fun y => GDom (Q y)) (f := s ω) (fun _ u => u) hp)
    (layer_map_value f G p h ω)).
Defined.
End MapKit.

Module Tri.
Import A.
Module Export L := LayerGpdTheory A.
Section SeparateTriangle.

Context {T X U V: Type} {P: X -> HGpd} {Sq: U -> HGpd} {Sr: V -> HGpd}
  {rq: U -> X} {rr: V -> X} {rf0: arity -> T -> X}
  {F: forall m, Sq m -> P (rq m)} {G: forall n, Sr n -> P (rr n)}
  {d1 d2: T} {E1: d1 = d2}
  {m1 m2: arity -> U} {n1 n2: arity -> V}
  {e2: forall θ, m1 θ = m2 θ} {e5: forall θ, n1 θ = n2 θ}
  {pQ: forall θ, rq (m2 θ) = rf0 θ d1}
  {pR: forall θ, rr (n2 θ) = rf0 θ d2}
  {B: arity -> HGpd} {l: Layer B}
  {aL: forall θ, B θ -> Sq (m1 θ)} {aR: forall θ, B θ -> Sr (n1 θ)}.

Let F1 θ a := rew [Sq] e2 θ in aL θ a.
Let F2 θ b := rew [P] pQ θ in F (m2 θ) b.
Let G1 θ a := rew [Sr] e5 θ in aR θ a.
Let G2 θ b := rew [P] pR θ in G (n2 θ) b.

Context {HL: forall θ a,
  rew [fun d => P (rf0 θ d)] E1 in F2 θ (F1 θ a) = G2 θ (G1 θ a)}
  {θ: arity} {KA: rq (m1 θ) = rr (n1 θ)}
  {HK: rew [P] KA in F (m1 θ) (aL θ (nth l θ)) = G (n1 θ) (aR θ (nth l θ))}
  {κ: f_equal rq (e2 θ) • (pQ θ • f_equal (rf0 θ) E1) =
    KA • (f_equal rr (e5 θ) • pR θ)}.

Definition separate_triangle_pointwise: Type :=
  rew [fun π => rew [P] π in F (m1 θ) (aL θ (nth l θ)) =
    G2 θ (G1 θ (nth l θ))] κ in
  (sigT_map_eq (Q := fun x => GDom (P x)) F (p := e2 θ) eq_refl
   ⊙[fun x => GDom (P x)] (eq_refl ⊙[fun x => GDom (P x)]
     sigT_map_eq (P := fun d => GDom (P (rf0 θ d)))
       (Q := fun x => GDom (P x)) (f := rf0 θ) (fun _ a => a) (HL θ (nth l θ)))) =
  HK ⊙[fun x => GDom (P x)]
    (sigT_map_eq (Q := fun x => GDom (P x)) G (p := e5 θ) eq_refl
     ⊙[fun x => GDom (P x)] eq_refl).

(** Evaluating a layer triangle cancels the computation corrections at
    its shared vertices, leaving the pointwise triangle. *)
Lemma separate_triangle_boundary:
  separate_triangle_pointwise ->
  rew [fun π => rew [P] π in F (m1 θ) (aL θ (nth l θ)) =
    nth (lmap G2 (lmap G1 l)) θ] κ in
  (sigT_map_eq (Q := fun x => GDom (P x)) F (eq_sym (nth_lmap F1 l θ))
   ⊙[fun x => GDom (P x)]
     (eq_sym (nth_lmap F2 (lmap F1 l) θ)
      ⊙[fun x => GDom (P x)]
        sigT_map_eq (P := fun d => GDom (Layer (fun ω => P (rf0 ω d))))
          (Q := fun x => GDom (P x)) (f := rf0 θ) (fun d u => nth u θ)
          (lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := E1) HL))) =
  HK ⊙[fun x => GDom (P x)]
    (sigT_map_eq (Q := fun x => GDom (P x)) G (eq_sym (nth_lmap G1 l θ))
     ⊙[fun x => GDom (P x)] eq_sym (nth_lmap G2 (lmap G1 l) θ)).
Proof.
  intro Hpointwise.
  rewrite (sigT_map_eq_lmap2_rew_eq (P := P) (rf0 := rf0) (θ := θ) (l := l)
    (F1 := F1) (F2 := F2) (G1 := G1) (G2 := G2) HL).
  rewrite <- (dpath_change_refl (P := fun x => GDom (Sq x)) (e2 θ)
    (aL θ (nth l θ)) (nth_lmap F1 l θ)).
  rewrite <- (dpath_change_refl (P := fun x => GDom (Sr x)) (e5 θ)
    (aR θ (nth l θ)) (nth_lmap G1 l θ)).
  rewrite <- (dpath_change_transport (P := fun x => GDom (P x)) (pQ θ)
    (f_equal (F (m2 θ)) (nth_lmap F1 l θ)) (nth_lmap F2 (lmap F1 l) θ)).
  rewrite <- (dpath_change_transport (P := fun x => GDom (P x)) (pR θ)
    (f_equal (G (n2 θ)) (nth_lmap G1 l θ)) (nth_lmap G2 (lmap G1 l) θ)).
  rewrite 2 dpath_change_map, 2 f_equal_compose.
  cbn [f_equal].
  rewrite <- (dpath_change_id (P := fun x => GDom (P x)) HK).
  rewrite 4 dpath_change_comp.
  now apply (dpath_change_cell (P := fun x => GDom (P x))).
Defined.

End SeparateTriangle.
End Tri.

#[local] Arguments Desc {X} {n} {Xpre} _.
#[local] Arguments DescS {X} {n} {Xpre} {S0} _.
#[local] Arguments FgFrp {X} m W frt.
#[local] Arguments FgFrt {X} m W.
#[local] Arguments FgLevel {X} m.
#[local] Arguments FgLevel0Datum {X}.
#[local] Arguments FgPrefix {X} m.
#[local] Arguments FgRestrData {X} m W frt frp.
#[local] Arguments FgTower {X} m.
#[local] Arguments FrtDeps {X} M {XpB0} {S0} HD {p} {k} {dcB} cB.
#[local] Arguments FrtDepsCohs {X} M {XpB0} {S0} HD {p} {k} {dcB} cB.
#[local] Arguments FrtFramesNextType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB'.
#[local] Arguments FrtFramesPrevType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtFramesType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtPaintingTopType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F {XA} {XB} TX PX top val H.
#[local] Arguments FrtPaintingsNextType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' frames.
#[local] Arguments FrtPairLawAt {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtRestr0At {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair.
#[local] Arguments FrtRestrBlock {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments FrtRestrDataDef {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {F} {FrtRestrBlock}.
#[local] Arguments FrtRestrFramesDef {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {F} {FrtRestrBlock} _.
#[local] Arguments FrtRestrLayerStepAtChosen {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev.
#[local] Arguments FrtRestrPaintingCellSelected {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t HP {a} {b} vl vr.
#[local] Arguments FrtRestrPrevData {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings.
#[local] Arguments FrtRpZeroType {p} {k} {DR} Xe rp.
#[local] Arguments FrtSplitDataAt {X} M {XpB0} {S0} HD p {k} {dcB} cB F top frames.
#[local] Arguments FrtSplitStep {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top frames.
#[local] Arguments PshRpZeroType {X} {m} {p} {k} P {Xe} PX {rp} pshRp Hrp.
#[local] Arguments RestrNext {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} B sp.
#[local] Arguments StepInput {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f.
#[local] Arguments StepLayer {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f sp q Hq Hqp epsilon t.
#[local] Arguments StepPrevious {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f _.
#[local] Arguments TrRpZeroType {p} {k} T {XA} {XB} TX {rpA} {rpB} trRp HrpA HrpB.
#[local] Arguments _fcCohsA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcF {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPX {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPshCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPshRp {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcRpA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcTX {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcTrRp {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcXA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcXB {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _frBound {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frDepsA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frFrameEqvs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPaintingEqvs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPaintings {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPshRestrs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frTrRestrs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments descAt {X} m.
#[local] Arguments descCanonicalPaintingConsCell_dep {X} {M} {XpB0} {S0} HD {p} {k} {dc3} a Hlen q Hq Hdim epsilon t.
#[local] Arguments descCanonicalPaintingPaired {X} {M} {XpB0} {S0} HD q {p} {k} {dc3} a Hlen Hq Hdim epsilon t.
#[local] Arguments descCanonicalZeroRpChoice {p} {k} dc3 Hq ζ d c.
#[local] Arguments descCell {X} {m} {XpB} {SB} HD t.
#[local] Arguments descCellPairRestrAt {X} {n} {XpB0} {S0} HD {pB} {kB} {dcB} cB dim Hdim Hlen ε t.
#[local] Arguments descCells {X} {m} {XpB} {SB} HD t.
#[local] Arguments descChain {X} {n} {Xpre} {S0} D.
#[local] Arguments descChainLen {X} {n} {Xpre} {S0} D.
#[local] Arguments descQcells {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} cB Hlen q Hq Hqp ε t.
#[local] Arguments descQcellsCons {X} {n} {XpB0} {S0} HD {P} {k} {dcB} cB Hlen q Hq Hqp Hq' Hqp' ε t.
#[local] Arguments descTop {X} {M} {XpB0} {S0} HD {p} {k} {dcB} cB _.
#[local] Arguments fgDeps {X} m W frt frp.
#[local] Arguments fgFrpNextOf {X} m s.
#[local] Arguments fgFrpOf {X} m W frt frp Q.
#[local] Arguments fgFrtNextOf {X} m s.
#[local] Arguments fgFrtOf {X} m W frt frp Q.
#[local] Arguments fgPrefixNext {X} m s.
#[local] Arguments fgPtChain {X} m P frt frp Q RP.
#[local] Arguments fgQNext {X} m s.
#[local] Arguments fgRpBase {X}.
#[local] Arguments fgRpBaseCanonical {X}.
#[local] Arguments fgSplitOf {X} m P frt frp Q.
#[local] Arguments fgSqChain {X} m P frt frp Q RP HC.
#[local] Arguments fgThis0 {X} d.
#[local] Arguments fgTowerAt {X} m P.
#[local] Arguments frTr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments frp0List {X}.
#[local] Arguments frt0List {X}.
#[local] Arguments frtDcB {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtPairLawPrev {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings ε t.
#[local] Arguments frtPshCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtPshCohsOf {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F XA PX rpA pshRp cohsA.
#[local] Arguments frtPshDeps {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments frtRestr0 {X} q Hq Hqp ε t.
#[local] Arguments frtRestrBaseCell {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp epsilon t.
#[local] Arguments frtRestrCell {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t HP.
#[local] Arguments frtRestrData0Next {X} M {XpB0} {S0} {HD} {k} {dcB} {cB} FC cB' Hlen' frames paintings q Hq Hqp ε t.
#[local] Arguments frtRestrLayerLeft {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR q Hq Hqp ε t prev HRPrev.
#[local] Arguments frtRestrLayerRight {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings q Hq Hqp ε t prev HRPrev.
#[local] Arguments frtRestrLeftNorm {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t.
#[local] Arguments frtRestrPaintingStepSelectedOf {X} M XpB0 S0 HD p k dcB cB F XA XB TX PX rpA rpB trRp pshRp HrpA HrpB HtrRp HpshRp top val prev Hpair HR E ε t.
#[local] Arguments frtRestrPrevBlock {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings.
#[local] Arguments frtRestrPrevClause {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp ε t.
#[local] Arguments frtRestrPrevFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Qprev.
#[local] Arguments frtRestrPrevPair {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev t.
#[local] Arguments frtRestrPrevZero {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev ε t.
#[local] Arguments frtRestrRightNorm {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp epsilon t.
#[local] Arguments frtSplitHead {X} {M} {XpB0} {S0} HD p {k} {dcB} cB F top frames SD.
#[local] Arguments frtSplitOfQ {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F Q.
#[local] Arguments frtTopNext {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' _.
#[local] Arguments frtTrBase {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtTrCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments lvFrp {X} {m} f.
#[local] Arguments lvFrt {X} {m} f.
#[local] Arguments lvP {X} {m} f.
#[local] Arguments lvQ {X} {m} f.
#[local] Arguments lvSP {X} {m} f.
#[local] Arguments lvW {X} {m} s.
#[local] Arguments mkCellFramesOf {X} M {P} {K} {depsTop} {p} {k} {deps} c top.
#[local] Arguments mkCellValues {X} M {p} {k} deps extraDeps top val.
#[local] Arguments mkCellValuesOf {X} M {P} {K} {depsTop} {extTop} {p} {k} {deps} {ext} c top val.
#[local] Arguments mkFrtDepsOf {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' frames paintings.
#[local] Arguments mkFrtFrameStep {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev lay.
#[local] Arguments mkFrtLayerOfRestr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair HR t.
#[local] Arguments mkFrtPaintingStepDown {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F XA XB TX PX top val prev lay E t.
#[local] Arguments mkFrtPaintingTypes {X} M {p} {k} {framesA} {framesB} {eqvs} {pshFrames} {cells} frt {paintingsA} {paintingsB} pEqvs pshPaintings cellValues.
#[local] Arguments mkFrtPaintingsOfRestr {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F XA XB TX PX val Q E.
#[local] Arguments mkFrtRestrTypeStep {X} {M} {p} {k} {framesA} {framesB} {eqvs} {pshFrames} {cells} frt {prevA} {prevB} {prevPsh} {prevTr} {RA} {RB} Qpsh Qtr cellsNext frtNext Qcells.
#[local] Arguments mkFrtRestrTypesAndFrames {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F.
#[local] Arguments mkFrtStepTypesAndRestrNext {X} M {XpB0} {S0} HD p {k} {dcB} cB FC cB' Hlen' frames paintings SD.
#[local] Arguments proj1FrtDeps {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments proj1FrtDepsCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments pshRc {X} m.
#[local] Arguments pshRp {X} m.
#[local] Arguments pshRpZeroChainOf {X} p {m} {k} {PC2} {XC} PCX.
#[local] Arguments pshTw {X} m.
#[local] Arguments rpZeroChainOf p {k} {depsCohs} XC.
#[local] Arguments towerFrtDepsCohs {X} m s.
#[local] Arguments towerFrtDepsCohsOf {X} m W frt frp Q.
#[local] Arguments trRpZeroChainOf p {k} {TC} {XCA} {XCB} TCX.
#[local] Arguments _frPshFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPshPaintings {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments mkFrtResidueOfRestr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair HR t ω.
#[local] Arguments nth_dpath_lamLmapRewEq {T} {Y} {P} {rf0} {d1} {d2} E f {B} l G H ω.

Lemma mapped_nth_component {T X: Type} {P: X -> HGpd}
  {r: arity -> T -> X} {d0 d1: T} {p: d0 = d1}
  {l0: Layer (fun z => P (r z d0))} {l1: Layer (fun z => P (r z d1))}
  (h: rew [fun d => Layer (fun z => P (r z d))] p in l0 = l1) (w: arity):
  sigT_map_eq (Q := fun x => GDom (P x)) (f := r w) (fun _ u => u)
    (nth_dpath (Bd := fun d z => P (r z d)) h w) =
  sigT_map_eq (P := fun d => GDom (Layer (fun z => P (r z d))))
    (Q := fun x => GDom (P x)) (f := r w) (fun d l => nth l w) h.
Proof. now destruct h, p. Defined.
Section FG.
Variable X: νGpds.
Section ActualResidueLayerBoundary.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB}
  (F: FrtDeps (X := X) M HD cB)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (prev: FrtFramesPrevType (X := X) F top)
  (Hpair: FrtPairLawAt (X := X) F top) (HR: FrtRestr0At (X := X) F top prev Hpair)
  (t: (g X).(G0) M.+1) (ω: arity).

Let Pf := fun x: F.(_frDepsA).(_frames).2 =>
  (F.(_frDepsA).(_paintings).2 x).(GDom).
Let read := fun d => F.(_frDepsA).(_restrFrames).2 0 leR_O ω d.
Let phi := fun x => F.(_frFrameEqvs).2 x.
Let pe := fun d v => F.(_frPaintingEqvs).2 d v.
Let source := fun ζ => rew [Pf]
  (F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ζ t) in
  F.(_frPshPaintings).2 ((g X).(GFace) M p (⇓ F.(_frBound)) ζ t).
Let target := fun ζ => compEquiv
  (F.(_frPaintingEqvs).2
    ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O ζ (top t).1))
  (rewEquiv Pf (F.(_frTrRestrs).2 0 leR_O ζ (top t).1)).
Let ca := nth_lam source ω.
Let cb := nth_lmap target (top t).2 ω.
Let face := (g X).(GFace) M p (⇓ F.(_frBound)) ω t.

(** The actual layer component satisfies its selected zero restriction
    square. Endpoint evaluation is included in the displayed boundary. *)
Lemma frtResidueLayerBoundary:
  rew [fun edge => rew [Pf] edge in F.(_frPshPaintings).2 face =
    nth (lmap target (top t).2) ω] (HR ω t) in
    ((F.(_frPaintings).2 face ⊙[Pf] sigT_map_eq (Q := Pf) (f := phi) pe (projT2_eq (Hpair ω t)))
      ⊙[Pf] eq_sym cb) =
  eq_sym ca ⊙[Pf] sigT_map_eq (Q := Pf) (fun _ u => u)
    (nth_dpath (Bd := fun a ζ => F.(_frDepsA).(_paintings).2
      (F.(_frDepsA).(_restrFrames).2 0 leR_O ζ a))
      (mkFrtLayerOfRestr F top prev Hpair HR t) ω).
Proof.
  refine (residue_component_boundary Pf read phi pe (prev.2 t)
    (F.(_frPshPaintings).2 face)
    (F.(_frPshRestrs).2 0 leR_O (⇓ F.(_frBound)) ω t)
    (F.(_frFrames).2 face) (Hpair ω t)
    (F.(_frTrRestrs).2 0 leR_O ω (top t).1) (HR ω t)
    (F.(_frPaintings).2 face) ca cb • _).
  apply (f_equal (fun h => eq_sym ca ⊙[Pf] sigT_map_eq (Q := Pf) (fun _ u => u) h)).
  now exact (eq_sym (nth_dpath_lamLmapRewEq (prev.2 t) source (top t).2 target
    (fun ζ => mkFrtResidueOfRestr F top prev Hpair HR t ζ) ω)).
Defined.
End ActualResidueLayerBoundary.

Section ActualTranslationTriangle.
Context {p k} (TC: TrDepsCohsBase p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohsBase TC)) (HC: mkTrCohType TC Q)
  (q: nat) (Hq: q <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC)))).

Let P := fun x => TC.(_trDeps).(_depsA).(_paintings).2 x.
Let Sq := fun x => TC.(_trDeps).(_depsB).(_paintings).2 x.
Let Sr := fun x => (mkPaintings (TC.(_trDeps).(_depsA); TC.(_tExtA))).2 x.
Let rf0 := fun ω x => TC.(_trDeps).(_depsA).(_restrFrames).2 0 leR_O ω x.
Let F := fun x c => TC.(_trDeps).(_paintingEqvs).2 x c.
Let G := fun x c => TC.(_tRpA).2 q Hq ε x c.
Let rb0 := fun ω => (mkRestrFrames
  (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).2 0 leR_O ω d.1.
Let rbq := (mkRestrFrames
  (depsCohs := trDepsCohsB (proj1TrDepsCohsBase TC))).2 q.+1 (⇑ Hq) ε d.1.
Let da := ((mkTrFrameEqvsNext (proj1TrDepsCohsBase TC) Q).2 d).1.
Let E := Q.2 q.+1 (⇑ Hq) ε d.1.
Let eb := fun ω => TC.(_tCohsB).2 q Hq 0 leR_O ε ω d.1.
Let ea := fun ω => Q.2 0 leR_O ω d.1.
Let pq := fun ω => TC.(_trDeps).(_trRestrs).2 0 leR_O ω rbq.
Let pr := fun ω => TC.(_tCohsA).2 q Hq 0 leR_O ε ω da.
Let al := fun ω a => TC.(_tRpB).2 q Hq ε (rb0 ω) a.
Let ar := fun ω a => mkPaintingEqv (AddTrDep TC.(_trDeps) TC.(_trExt)) (rb0 ω) a.
Let ka := fun ω => TC.(_trDeps).(_trRestrs).2 q Hq ε (rb0 ω).
Let hk := fun ω a => TC.(_trRestrPaintings).2 q Hq ε (rb0 ω) a.
Let cell := fun ω => HC q Hq 0 leR_O ε ω d.1.
Let core := fun ω a => rew_cohLayer_hex (P := fun x => GDom (P x))
  (rf0 := rf0 ω) (F := F) (G := G) (E1 := E)
  (C2 := eb ω) (D2 := ea ω) (C1 := pq ω) (D1 := pr ω)
  (hk ω a) (cell ω).

Definition actualTranslationPointwise (ω: arity) :=
  rew_coh2Painting_restr0 (P := fun x => GDom (P x)) F G E
    (eb ω) (ea ω) (pq ω) (pr ω) (ka ω)
    (al ω (nth d.2 ω)) (ar ω (nth d.2 ω))
    (hk ω (nth d.2 ω)) (cell ω).

(** This boundary keeps the translation's selected coherence cell and
    the four lmap evaluation witnesses around its constructed layer. *)
Definition actualTranslationBoundary (ω: arity) :=
  Tri.separate_triangle_boundary
    (P := P) (Sq := Sq) (Sr := Sr) (rf0 := rf0)
    (F := F) (G := G) (E1 := E) (e2 := eb) (e5 := ea)
    (pQ := pq) (pR := pr) (l := d.2) (aL := al) (aR := ar)
    (HL := core) (θ := ω) (KA := ka ω) (HK := hk ω (nth d.2 ω))
    (κ := cell ω) (actualTranslationPointwise ω).
End ActualTranslationTriangle.

Section ActualPshLayerBoundary.
Variable psh: νGpdPresentation arity.
Context {m p k} (PC: PshDepsCohs psh m p.+1 k)
  (Q: mkPshRestrFramesType psh (proj1PshDepsCohs psh PC))
  (HC: mkPshRestrLayerCohType psh PC Q)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= m.+1)
  (ε: arity) (d: psh.(G0) m.+2) (ω: arity).

Let Pf := fun x => (PC.(_pshDeps _).(_pdeps _).(_paintings).2 x).(GDom).
Let f := PC.(_pshDeps _).(_pshFrames _).2.
Let sec := PC.(_pshDeps _).(_pshPaintings _).2.
Let r := fun x => PC.(_pshDeps _).(_pdeps _).(_restrFrames).2 0 leR_O ω x.
Let gq := fun x => PC.(_pshDeps _).(_pdeps _).(_restrFrames).2 q Hq ε x.
Let G := PC.(_pRestrPaintings _).2 q Hq ε.
Let dim := pshFaceDimIrr psh (eq_sym (plus_n_Sm q p))
  (Hq := Hqp) (Hq' := leR_add_shift Hqp) ε d.
Let h := psh.(GFaceCoh) m (q + p) (⇓ leR_add_shift Hqp) p
  (leR_add_l q) ε ω d • eq_sym
    (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps _).(_pshBound _)) ω) dim).
Let ebase := f_equal (fun a => (mkPshFrame psh PC.(_pshDeps _) a).1) dim
  • Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d.
Let eprev := Q.2 0 leR_O (⇓ (⇑ (proj1PshDepsCohs psh PC).(_pshDeps _).(_pshBound _))) ω d.
Let cq := PC.(_pshDeps _).(_pshRestrs _).2 0 leR_O
  (⇓ PC.(_pshDeps _).(_pshBound _)) ω (psh.(GFace) m.+1 (q + p.+1) Hqp ε d).
Let cr := PC.(_pCohs _).2 q Hq 0 leR_O ε ω
  ((mkPshFramesNext psh (proj1PshDepsCohs psh PC) Q).2 d).1.
Let face0 := psh.(GFace) m.+1 p
  (⇓ (⇑ (proj1PshDepsCohs psh PC).(_pshDeps _).(_pshBound _))) ω d.
Let kk := PC.(_pshDeps _).(_pshRestrs _).2 q Hq (⇓ leR_add_shift Hqp) ε face0.
Let hk := PC.(_pshRestrPaintings _).2 q Hq (⇓ leR_add_shift Hqp) ε face0.
Let cell := mkPshRestrLayerFrameSquare psh PC Q HC q Hq (plus_n_Sm q p)
  Hqp (leR_add_shift Hqp) ε d ω.
Let b := nth ((mkPshFramesNext psh (proj1PshDepsCohs psh PC) Q).2 d).2 ω.
Let cb := nth_mkPshFrame psh (pshDepsRestrNext psh (proj1PshDepsCohs psh PC) Q) d ω.
Let ca := nth_mkPshFrame psh PC.(_pshDeps _) (psh.(GFace) m.+1 (q + p.+1) Hqp ε d) ω.
Let ct := mkPshRestrLayerChainRmap psh PC Q q Hq ε d ω.

Definition actualPshFrameSquare :=
  section_coherence_square f gq r ebase h eprev cq cr kk cell.
Definition actualPshSectionEdge :=
  section_coherence_edge f sec gq r G ebase h eprev cq cr kk _ hk cell b cb ca ct.

Lemma actualPshComponentSection:
  nth_dpath (Bd := fun a ζ => PC.(_pshDeps _).(_pdeps _).(_paintings).2
    (PC.(_pshDeps _).(_pdeps _).(_restrFrames).2 0 leR_O ζ a))
    (mkPshRestrLayerMerged psh PC Q HC q Hq Hqp ε d) ω = actualPshSectionEdge.
Proof.
  rewrite (nth_dpath_mkPshRestrLayerMerged psh).
  now exact (mkPshRestrLayerChainB_sec psh PC Q q Hq (plus_n_Sm q p)
    Hqp (leR_add_shift Hqp) ε d ω ebase cell).
Defined.

Definition actualPshSectionBoundary :=
  section_coherence_boundary f sec gq r G ebase h eprev cq cr kk _ hk cell b cb ca ct.

(** The frame square and component boundary are over the same stored
    coherence, now read through the actual merged layer constructor. *)
Lemma actualPshLayerBoundary:
  rew [fun path => rew [Pf] path in
    sec (psh.(GFace) m (q + p) (⇓ leR_add_shift Hqp) ε face0) =
    nth (mkRestrLayer PC.(_pRestrPaintings _).2 PC.(_pCohs _).2 q Hq ε
      ((mkPshFramesNext psh (proj1PshDepsCohs psh PC) Q).2 d).1
      ((mkPshFramesNext psh (proj1PshDepsCohs psh PC) Q).2 d).2) ω]
    actualPshFrameSquare in
    ((f_equal_dep_sigT f sec h ⊙[Pf] eq_sym ca)
      ⊙[Pf] sigT_map_eq (Q := Pf) (f := r) (fun _ u => u)
        (nth_dpath (Bd := fun a ζ => PC.(_pshDeps _).(_pdeps _).(_paintings).2
          (PC.(_pshDeps _).(_pdeps _).(_restrFrames).2 0 leR_O ζ a))
          (mkPshRestrLayerMerged psh PC Q HC q Hq Hqp ε d) ω)) =
  hk ⊙[Pf] (sigT_map_eq (Q := Pf) G (eq_sym cb) ⊙[Pf] eq_sym ct).
Proof.
  rewrite actualPshComponentSection.
  now exact actualPshSectionBoundary.
Defined.
End ActualPshLayerBoundary.

Section RestrictionStepSelection.
Context {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs (X := X) M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType (X := X) FC cB')
  (paintings: FrtPaintingsNextType (X := X) FC cB' frames)
  (Hpair: FrtPairLawAt (X := X) FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At (X := X) FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair).


Let PreviousData := @Core.FrtRestrPrevData X M XpB0 S0 HD p k dcB cB
  FC cB' Hlen' frames paintings.
Let previousFrames := @Core.frtRestrPrevFrames X M XpB0 S0 HD p k dcB cB
  FC cB' Hlen' frames paintings.
Let previousZero := @Core.frtRestrPrevZero X M XpB0 S0 HD p k dcB cB
  FC cB' Hlen' frames paintings Hpair HR.
Let selectedBaseCell := @Core.frtRestrBaseCell X M XpB0 S0 HD p k dcB cB
  FC cB' Hlen' frames paintings Hpair HR.
Let leftLayer := @Core.frtRestrLayerLeft X M XpB0 S0 HD p k dcB cB
  FC cB' Hlen' frames paintings Hpair HR.
Let rightLayer := @Core.frtRestrLayerRight X M XpB0 S0 HD p k dcB cB
  FC cB' Hlen' frames paintings.
Section ActualMappedLayerAtoms.
Context (Qprev: PreviousData)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (ε: arity) (t: (g X).(G0) M.+2) (ω: arity).

Let rb := fun ζ d => (frTr FC.(_fcF)).(_depsB).(_restrFrames).2 0 leR_O ζ d.
Let ra := fun ζ d => (frTr FC.(_fcF)).(_depsA).(_restrFrames).2 0 leR_O ζ d.
Let fm := fun d => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 d.
Let phi := fun d => (frTr FC.(_fcF)).(_frameEqvs).2 d.
Let eta := fun d ζ => (frTr FC.(_fcF)).(_trRestrs).2 0 leR_O ζ d.
Let PB := fun x => (frTr FC.(_fcF)).(_depsB).(_paintings).2 x.
Let PA := fun x => (frTr FC.(_fcF)).(_depsA).(_paintings).2 x.
Let pe := fun x c => (frTr FC.(_fcF)).(_paintingEqvs).2 x c.
Let dc := descQcells cB' Hlen' q Hq Hqp ε t.

(** The mapped descent component uses the translation's own zero
    naturality cell and the layer component of the chosen descent path. *)
Definition actualMappedDescSquare :=
  MapKit.mapped_layer_square rb ra fm phi eta (projT1_eq dc) ω.
Definition actualMappedDescBoundary :=
  MapKit.mapped_layer_square_dep rb ra fm phi eta PB PA pe
    (projT1_eq dc) (projT2_eq dc) ω.

Let rprev := fun ζ d =>
  (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
    0 leR_O ζ d.
Let rnow := fun ζ d => (trDepsCohsA (frtTrBase FC)).(_deps).(_restrFrames).2
  0 leR_O ζ d.
Let rq := fun d => (mkRestrFrames
  (depsCohs := proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2 q.+1 (⇑ Hq) ε d.
Let rqfull := fun d => (trDepsCohsA (frtTrBase FC)).(_deps).(_restrFrames).2 q Hq ε d.
Let etaq := fun d ζ => (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq 0 leR_O ε ζ d.
Let Pprev := fun x =>
  (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).(1).(_paintings).2 x.
Let Pnow := fun x => (trDepsCohsA (frtTrBase FC)).(_deps).(_paintings).2 x.
Let rpq := fun x c => (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2 q Hq ε x c.
Let previousLayer := mkFrtLayerOfRestr
  (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
  (descTop (DescS HD) (DepsCohsChainCons cB')) (previousFrames Qprev)
  (frtPairLawPrev FC cB' Hlen' frames paintings) (previousZero Qprev) t.

(** The same boundary construction maps the previous generated residue
    through restriction q, using the actual (q,0) coherence. *)
Definition actualMappedPreviousSquare :=
  MapKit.mapped_layer_square rprev rnow rq rqfull etaq
    ((previousFrames Qprev).2 t) ω.
Definition actualMappedPreviousBoundary :=
  MapKit.mapped_layer_square_dep rprev rnow rq rqfull etaq Pprev Pnow rpq
    ((previousFrames Qprev).2 t) previousLayer ω.

Let scalarP := fun x => GDom (Pnow x).
Let lowerMap := rnow ω.
Let face := (g X).(GFace) M.+1 (q + p.+1) Hqp ε t.
Let PC := frtPshCohs FC.
Let PQ := mkPshRestrFrames (g X) (proj1PshDepsCohs (g X) PC) FC.(_fcPshCohs).1.

Definition actualPshSquare :=
  actualPshFrameSquare (g X) PC PQ FC.(_fcPshCohs).2 q Hq Hqp ε t ω.
Definition actualPshBoundary :=
  actualPshLayerBoundary (g X) PC PQ FC.(_fcPshCohs).2 q Hq Hqp ε t ω.

Definition actualSourcePath := ltac:(
  let T := type of actualPshSquare in
  lazymatch T with (?h • ?p) • _ = _ => now exact h end).
Definition actualSourceLift := ltac:(
  let T := type of actualPshBoundary in
  lazymatch T with rew [_] _ in ((?h ⊙ _) ⊙ _) = _ => now exact h end).

Definition actualResidueA :=
  frtResidueLayerBoundary FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR face ω.
Definition actualResidueN :=
  frtResidueLayerBoundary (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
    (descTop (DescS HD) (DepsCohsChainCons cB')) (previousFrames Qprev)
    (frtPairLawPrev FC cB' Hlen' frames paintings) (previousZero Qprev) t ω.

Definition actualTrSquare :=
  square_strip_prefix ((frtTrCohs FC).(_trCohs).2 q Hq 0 leR_O ε ω
    (descTop (DescS HD) cB' t).1.1).
Definition actualTrBoundary := ltac:(
  pose proof (actualTranslationBoundary (frtTrCohs FC).(_trBase)
    (mkTrRestrFrames (proj1TrDepsCohs (frtTrCohs FC))) (frtTrCohs FC).(_trCohs).2
    q Hq ε (descTop (DescS HD) cB' t).1 ω) as H;
  rewrite <- mapped_nth_component in H;
  now exact (square_strip_prefix_dep scalarP _ _ _ _ _ _ H)).

Definition actualLeftSquare :=
  square_prepend actualSourcePath
    (square_compose_map lowerMap
      (square_compose_map lowerMap (eq_sym (HR ω face)) (eq_sym actualMappedDescSquare))
      actualTrSquare).

Definition actualLeftBoundary := ltac:(
  pose (HAD := square_compose_map_dep lowerMap scalarP _ _ _ _ _ _ _ _ _
    (sigT_sym_eq actualResidueA) (sigT_sym_eq actualMappedDescBoundary));
  pose (HADT := square_compose_map_dep lowerMap scalarP _ _ _ _ _ _ _ _ _
    HAD actualTrBoundary);
  pose (H := square_prepend_dep scalarP actualSourcePath _ actualSourceLift
    _ _ _ _ HADT);
  lazymatch type of H with
  | rew [?D] _ in ?l = ?r => now exact (H: rew [D] actualLeftSquare in l = r)
  end).

Definition actualPreviousSquare :=
  square_stack (square_map rqfull (eq_sym (previousZero Qprev ω t)))
    (eq_sym actualMappedPreviousSquare).

Definition actualPreviousBoundary := ltac:(
  pose proof actualMappedPreviousBoundary as HN;
  rewrite <- mapped_nth_component in HN;
  pose (HM := square_map_dep (P := fun x => GDom (Pprev x)) (Q := scalarP)
    rqfull rpq _ _ _ _ _ (sigT_sym_eq actualResidueN));
  pose (H := square_stack_dep scalarP _ _ _ _ _ _ _ _ _
    HM (sigT_sym_eq HN));
  lazymatch type of H with
  | rew [?D] _ in ?l = ?r => now exact (H: rew [D] actualPreviousSquare in l = r)
  end).

Definition actualRightSquare :=
  square_compose_map lowerMap actualPshSquare actualPreviousSquare.
Definition actualRightBoundary := ltac:(
  pose (H := square_compose_map_dep lowerMap scalarP _ _ _ _ _ _ _ _ _
    actualPshBoundary actualPreviousBoundary);
  lazymatch type of H with
  | rew [?D] _ in ?l = ?r => now exact (H: rew [D] actualRightSquare in l = r)
  end).



(** The upper comparison is a frame cell between the two explicit
    boundary pastes. Its painting witness is a separate input. *)
Definition ActualUpperCell: Type := ltac:(
  let L := type of actualLeftSquare in
  let R := type of actualRightSquare in
  lazymatch L with ?p • _ = ?a • ?q =>
    lazymatch R with ?p' • _ = ?a' • ?q' =>
      unify p p'; unify q q'; now exact (a = a')
    end
  end).

Definition actualFrameCube (lambda: ActualUpperCell) := ltac:(
  let L := type of actualLeftSquare in
  lazymatch L with ?p • _ = _ • ?last =>
    let T := constr:(actualLeftSquare • whisker_r lambda last =
      whisker_l p (f_equal (fun e => f_equal lowerMap e)
        (selectedBaseCell Qprev q Hq Hqp ε t)) • actualRightSquare) in
    now exact ((@GUIP (trDepsCohsA (frtTrBase FC)).(_deps).(_frames).2 _ _ _ _ _ _): T)
  end).

Definition ActualUpperWitness (lambda: ActualUpperCell): Type := ltac:(
  let L := type of actualLeftBoundary in
  let R := type of actualRightBoundary in
  lazymatch L with rew [_] _ in _ = ?a ⊙ ?q =>
    lazymatch R with rew [_] _ in _ = ?a' ⊙ ?q' =>
      unify q q'; now exact (DPathCellOver (P := scalarP) a a' lambda)
    end
  end).

(** This dependent consumer uses the named frame cube exactly. *)
Definition actualComponentOfUpper (lambda: ActualUpperCell)
  (Hupper: ActualUpperWitness lambda) :=
  square_cube_map_dep lowerMap scalarP actualLeftSquare actualRightSquare
    (selectedBaseCell Qprev q Hq Hqp ε t) lambda (actualFrameCube lambda)
    _ _ _ _ _ _ actualLeftBoundary actualRightBoundary Hupper.

Lemma actualLayerComponentOfUpper (lambda: ActualUpperCell)
  (Hupper: ActualUpperWitness lambda):
  DPathCellOver (P := fun a => scalarP (lowerMap a))
    (nth_dpath (Bd := fun a ζ => (trDepsCohsA (frtTrBase FC)).(_deps).(_paintings).2
      ((trDepsCohsA (frtTrBase FC)).(_deps).(_restrFrames).2 0 leR_O ζ a))
      (leftLayer q Hq Hqp ε t (previousFrames Qprev)
        (previousZero Qprev)) ω)
    (nth_dpath (Bd := fun a ζ => (trDepsCohsA (frtTrBase FC)).(_deps).(_paintings).2
      ((trDepsCohsA (frtTrBase FC)).(_deps).(_restrFrames).2 0 leR_O ζ a))
      (rightLayer q Hq Hqp ε t (previousFrames Qprev)
        (previousZero Qprev)) ω)
    (selectedBaseCell Qprev q Hq Hqp ε t).
Proof.
  unfold DPathCellOver, leftLayer, rightLayer, Core.frtRestrLayerLeft, Core.frtRestrLayerRight.
  rewrite 3 nth_dpath_trans.
  now exact (actualComponentOfUpper lambda Hupper).
Defined.



(** The two upper frame paths are normalized by the same typed map
    operations as their displayed paths. *)
Definition actualLeftUpperNormal := ltac:(
  let T := type of actualLeftSquare in
  lazymatch T with
  | _ = (?s • (((?i • f_equal ?f0 ?p0) • f_equal ?f1 ?p1)
      • (eq_sym (f_equal ?f2 ?p2) • ?last))) • _ =>
    unify f0 f1; unify f0 f2;
    now exact (whisker_l s (exchange_left_route f0 i p0 p1 p2 last))
  end).

Definition actualLeftUpperNormal_dep := ltac:(
  let T := type of actualLeftBoundary in
  lazymatch T with
  | rew [_] _ in _ = (?hs ⊙ (((?hi ⊙ ?mh0) ⊙ ?mh1)
      ⊙ (sigT_sym_eq ?mh2 ⊙ ?ht))) ⊙ _ =>
    lazymatch mh0 with
    | @sigT_map_eq _ _ ?PB ?PA ?f ?F _ _ _ _ _ ?h0 =>
      lazymatch mh1 with
      | @sigT_map_eq _ _ _ _ _ _ _ _ _ _ _ ?h1 =>
        lazymatch mh2 with
        | @sigT_map_eq _ _ _ _ _ _ _ _ _ _ _ ?h2 =>
          let H0 := constr:(exchange_left_route_dep f PA PB F
            _ _ _ _ _ hi h0 h1 h2 ht) in
          let H := constr:(displayed_whisker_left scalarP actualSourcePath _ hs H0) in
          lazymatch type of H with
          | rew [?D] _ in ?l = ?r => now exact (H: rew [D] actualLeftUpperNormal in l = r)
          end
        end
      end
    end
  end).

Definition actualRightUpperNormal := ltac:(
  let T := type of actualRightSquare in
  lazymatch T with
  | _ = (?k0 • f_equal ?f (?p0 • f_equal ?g ?j)) • _ =>
    now exact (exchange_right_route f g k0 p0 j)
  end).

Definition actualRightUpperNormal_dep := ltac:(
  let T := type of actualRightBoundary in
  lazymatch T with
  | rew [_] _ in _ = (?hk ⊙ ?mh) ⊙ _ =>
    lazymatch mh with
    | @sigT_map_eq _ _ ?PX ?PA ?f ?F _ _ _ _ _ (?hp ⊙ ?mg) =>
      lazymatch mg with
      | @sigT_map_eq _ _ ?PB _ ?g ?G _ _ _ _ _ ?hj =>
        let H := constr:(exchange_right_route_dep f g PA PX PB F G
          _ _ _ hk hp hj) in
        lazymatch type of H with
        | rew [?D] _ in ?l = ?r => now exact (H: rew [D] actualRightUpperNormal in l = r)
        end
      end
    end
  end).

Definition ActualExchangeCell: Type := ltac:(
  let L := type of actualLeftUpperNormal in
  let R := type of actualRightUpperNormal in
  lazymatch L with _ = ?l =>
    lazymatch R with _ = ?r => now exact (l = r) end
  end).

Definition ActualExchangeWitness (lambda: ActualExchangeCell): Type := ltac:(
  let L := type of actualLeftUpperNormal_dep in
  let R := type of actualRightUpperNormal_dep in
  lazymatch L with rew [_] _ in _ = ?l =>
    lazymatch R with rew [_] _ in _ = ?r =>
      now exact (DPathCellOver (P := scalarP) l r lambda)
    end
  end).

Definition actualUpperFromExchange (lambda: ActualExchangeCell): ActualUpperCell :=
  actualLeftUpperNormal • (lambda • eq_sym actualRightUpperNormal).
Definition actualUpperFromExchange_dep (lambda: ActualExchangeCell)
  (H: ActualExchangeWitness lambda): ActualUpperWitness (actualUpperFromExchange lambda) :=
  actualLeftUpperNormal_dep ⊙ (H ⊙ sigT_sym_eq actualRightUpperNormal_dep).

Definition actualComponentFromExchange (lambda: ActualExchangeCell)
  (H: ActualExchangeWitness lambda) :=
  actualLayerComponentOfUpper (actualUpperFromExchange lambda)
    (actualUpperFromExchange_dep lambda H).


End ActualMappedLayerAtoms.


End RestrictionStepSelection.
End FG.
End K.
Import K.
Module Export SN := K.SN.
Module C := K.C.
Module Core := K.Core.
Module SharedExchange := Exchange.ExchangeOn A Base Translations C.
Module Geometry := Coherence.CoherenceOn A Base Translations C SharedExchange.
#[local] Arguments Desc {X} {n} {Xpre} _.
#[local] Arguments DescS {X} {n} {Xpre} {S0} _.
#[local] Arguments FgFrp {X} m W frt.
#[local] Arguments FgFrt {X} m W.
#[local] Arguments FgLevel {X} m.
#[local] Arguments FgLevel0Datum {X}.
#[local] Arguments FgPrefix {X} m.
#[local] Arguments FgRestrData {X} m W frt frp.
#[local] Arguments FgTower {X} m.
#[local] Arguments FrtDeps {X} M {XpB0} {S0} HD {p} {k} {dcB} cB.
#[local] Arguments FrtDepsCohs {X} M {XpB0} {S0} HD {p} {k} {dcB} cB.
#[local] Arguments FrtFramesNextType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB'.
#[local] Arguments FrtFramesPrevType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtFramesType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtPaintingTopType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F {XA} {XB} TX PX top val H.
#[local] Arguments FrtPaintingsNextType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' frames.
#[local] Arguments FrtPairLawAt {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtRestr0At {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair.
#[local] Arguments FrtRestrBlock {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments FrtRestrDataDef {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {F} {FrtRestrBlock}.
#[local] Arguments FrtRestrFramesDef {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {F} {FrtRestrBlock} _.
#[local] Arguments FrtRestrLayerStepAtChosen {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev.
#[local] Arguments FrtRestrPaintingCellSelected {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t HP {a} {b} vl vr.
#[local] Arguments FrtRestrPrevData {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings.
#[local] Arguments FrtRpZeroType {p} {k} {DR} Xe rp.
#[local] Arguments FrtSplitDataAt {X} M {XpB0} {S0} HD p {k} {dcB} cB F top frames.
#[local] Arguments FrtSplitStep {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top frames.
#[local] Arguments PshRpZeroType {X} {m} {p} {k} P {Xe} PX {rp} pshRp Hrp.
#[local] Arguments RestrNext {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} B sp.
#[local] Arguments StepInput {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f.
#[local] Arguments StepLayer {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f sp q Hq Hqp epsilon t.
#[local] Arguments StepPrevious {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f _.
#[local] Arguments TrRpZeroType {p} {k} T {XA} {XB} TX {rpA} {rpB} trRp HrpA HrpB.
#[local] Arguments _fcCohsA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcF {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPX {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPshCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPshRp {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcRpA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcTX {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcTrRp {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcXA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcXB {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _frBound {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frDepsA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frFrameEqvs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPaintingEqvs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPaintings {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPshRestrs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frTrRestrs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments descAt {X} m.
#[local] Arguments descCanonicalPaintingConsCell_dep {X} {M} {XpB0} {S0} HD {p} {k} {dc3} a Hlen q Hq Hdim epsilon t.
#[local] Arguments descCanonicalPaintingPaired {X} {M} {XpB0} {S0} HD q {p} {k} {dc3} a Hlen Hq Hdim epsilon t.
#[local] Arguments descCanonicalZeroRpChoice {p} {k} dc3 Hq ζ d c.
#[local] Arguments descCell {X} {m} {XpB} {SB} HD t.
#[local] Arguments descCellPairRestrAt {X} {n} {XpB0} {S0} HD {pB} {kB} {dcB} cB dim Hdim Hlen ε t.
#[local] Arguments descCells {X} {m} {XpB} {SB} HD t.
#[local] Arguments descChain {X} {n} {Xpre} {S0} D.
#[local] Arguments descChainLen {X} {n} {Xpre} {S0} D.
#[local] Arguments descQcells {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} cB Hlen q Hq Hqp ε t.
#[local] Arguments descQcellsCons {X} {n} {XpB0} {S0} HD {P} {k} {dcB} cB Hlen q Hq Hqp Hq' Hqp' ε t.
#[local] Arguments descTop {X} {M} {XpB0} {S0} HD {p} {k} {dcB} cB _.
#[local] Arguments fgDeps {X} m W frt frp.
#[local] Arguments fgFrpNextOf {X} m s.
#[local] Arguments fgFrpOf {X} m W frt frp Q.
#[local] Arguments fgFrtNextOf {X} m s.
#[local] Arguments fgFrtOf {X} m W frt frp Q.
#[local] Arguments fgPrefixNext {X} m s.
#[local] Arguments fgPtChain {X} m P frt frp Q RP.
#[local] Arguments fgQNext {X} m s.
#[local] Arguments fgRpBase {X}.
#[local] Arguments fgRpBaseCanonical {X}.
#[local] Arguments fgSplitOf {X} m P frt frp Q.
#[local] Arguments fgSqChain {X} m P frt frp Q RP HC.
#[local] Arguments fgThis0 {X} d.
#[local] Arguments fgTowerAt {X} m P.
#[local] Arguments frTr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments frp0List {X}.
#[local] Arguments frt0List {X}.
#[local] Arguments frtDcB {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtPairLawPrev {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings ε t.
#[local] Arguments frtPshCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtPshCohsOf {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F XA PX rpA pshRp cohsA.
#[local] Arguments frtPshDeps {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments frtRestr0 {X} q Hq Hqp ε t.
#[local] Arguments frtRestrBaseCell {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp epsilon t.
#[local] Arguments frtRestrCell {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t HP.
#[local] Arguments frtRestrData0Next {X} M {XpB0} {S0} {HD} {k} {dcB} {cB} FC cB' Hlen' frames paintings q Hq Hqp ε t.
#[local] Arguments frtRestrLayerLeft {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR q Hq Hqp ε t prev HRPrev.
#[local] Arguments frtRestrLayerRight {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings q Hq Hqp ε t prev HRPrev.
#[local] Arguments frtRestrLeftNorm {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t.
#[local] Arguments frtRestrPaintingStepSelectedOf {X} M XpB0 S0 HD p k dcB cB F XA XB TX PX rpA rpB trRp pshRp HrpA HrpB HtrRp HpshRp top val prev Hpair HR E ε t.
#[local] Arguments frtRestrPrevBlock {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings.
#[local] Arguments frtRestrPrevClause {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp ε t.
#[local] Arguments frtRestrPrevFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Qprev.
#[local] Arguments frtRestrPrevPair {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev t.
#[local] Arguments frtRestrPrevZero {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev ε t.
#[local] Arguments frtRestrRightNorm {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp epsilon t.
#[local] Arguments frtSplitHead {X} {M} {XpB0} {S0} HD p {k} {dcB} cB F top frames SD.
#[local] Arguments frtSplitOfQ {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F Q.
#[local] Arguments frtTopNext {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' _.
#[local] Arguments frtTrBase {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtTrCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments lvFrp {X} {m} f.
#[local] Arguments lvFrt {X} {m} f.
#[local] Arguments lvP {X} {m} f.
#[local] Arguments lvQ {X} {m} f.
#[local] Arguments lvSP {X} {m} f.
#[local] Arguments lvW {X} {m} s.
#[local] Arguments mkCellFramesOf {X} M {P} {K} {depsTop} {p} {k} {deps} c top.
#[local] Arguments mkCellValues {X} M {p} {k} deps extraDeps top val.
#[local] Arguments mkCellValuesOf {X} M {P} {K} {depsTop} {extTop} {p} {k} {deps} {ext} c top val.
#[local] Arguments mkFrtDepsOf {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' frames paintings.
#[local] Arguments mkFrtFrameStep {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev lay.
#[local] Arguments mkFrtLayerOfRestr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair HR t.
#[local] Arguments mkFrtPaintingStepDown {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F XA XB TX PX top val prev lay E t.
#[local] Arguments mkFrtPaintingTypes {X} M {p} {k} {framesA} {framesB} {eqvs} {pshFrames} {cells} frt {paintingsA} {paintingsB} pEqvs pshPaintings cellValues.
#[local] Arguments mkFrtPaintingsOfRestr {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F XA XB TX PX val Q E.
#[local] Arguments mkFrtRestrTypeStep {X} {M} {p} {k} {framesA} {framesB} {eqvs} {pshFrames} {cells} frt {prevA} {prevB} {prevPsh} {prevTr} {RA} {RB} Qpsh Qtr cellsNext frtNext Qcells.
#[local] Arguments mkFrtRestrTypesAndFrames {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F.
#[local] Arguments mkFrtStepTypesAndRestrNext {X} M {XpB0} {S0} HD p {k} {dcB} cB FC cB' Hlen' frames paintings SD.
#[local] Arguments proj1FrtDeps {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments proj1FrtDepsCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments pshRc {X} m.
#[local] Arguments pshRp {X} m.
#[local] Arguments pshRpZeroChainOf {X} p {m} {k} {PC2} {XC} PCX.
#[local] Arguments pshTw {X} m.
#[local] Arguments rpZeroChainOf p {k} {depsCohs} XC.
#[local] Arguments towerFrtDepsCohs {X} m s.
#[local] Arguments towerFrtDepsCohsOf {X} m W frt frp Q.
#[local] Arguments trRpZeroChainOf p {k} {TC} {XCA} {XCB} TCX.
#[local] Arguments _frPshFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPshPaintings {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments mkFrtResidueOfRestr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair HR t ω.
#[local] Arguments nth_dpath_lamLmapRewEq {T} {Y} {P} {rf0} {d1} {d2} E f {B} l G H ω.

#[local] Arguments _fcRpB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcXB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments _fcCohsB {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments mkFrtDepsCohsGen {X M XpB0 S0 HD p k dc2}.
#[local] Arguments frtTrBaseOf {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments frtPairLawAlignU {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments frtCellPairDeepCell {X M XpB0 S0} HD {p k dc3}.

#[local] Arguments FrtStepDataAt {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments frtCellPair {X M XpB0 S0} HD {p k dcB}.
#[local] Arguments descCellPairRestrTotal {X M XpB0 S0} HD {p k dc3}.
#[local] Arguments frtChainUp {M XpB0 S0 p k dc3M}.
#[local] Arguments frtTopAlignU {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments _fcTrCohs {X M XpB0 S0 HD p k dcB cB}.
#[local] Arguments fgRpChainOfChains {X}.
#[local] Arguments rpBChainOf {X}.
Section Stage.
Context (X: νGpds) {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB}
  (FC: FrtDepsCohs (X := X) M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType (X := X) FC cB')
  (paintings: FrtPaintingsNextType (X := X) FC cB' frames)
  (Hpair: FrtPairLawAt (X := X) FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At (X := X) FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair).

(** The old level's selected naturality and owned view supply this
    family before any previous-stage restriction data is chosen. *)
Definition SelectedExchangeComponents: Type :=
  forall q (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
    (epsilon: arity) (t: (g X).(G0) M.+2) (omega: arity),
  {lambda: K.ActualExchangeCell X FC cB' Hlen' frames paintings Hpair
      q Hq Hqp epsilon t omega &T
    K.ActualExchangeWitness X FC cB' Hlen' frames paintings Hpair
      q Hq Hqp epsilon t omega lambda}.

Definition selectedLayerOfExchange
  (Qprev: @Core.FrtRestrPrevData X M XpB0 S0 HD p k dcB cB FC cB' Hlen' frames paintings)
  (H: SelectedExchangeComponents):
  @Core.FrtRestrLayerStepAtChosen X M XpB0 S0 HD p k dcB cB
    FC cB' Hlen' frames paintings Hpair HR Qprev.
Proof.
  intros q Hq Hqp epsilon t.
  unfold DPathCellOver.
  apply (layer_dpath2_eq (Bd := fun a omega =>
    (trDepsCohsA (frtTrBase FC)).(_deps).(_paintings).2
      ((trDepsCohsA (frtTrBase FC)).(_deps).(_restrFrames).2 0 leR_O omega a))).
  intro omega.
  now exact (K.actualComponentFromExchange X FC cB' Hlen' frames paintings Hpair
    HR Qprev q Hq Hqp epsilon t omega
    (H q Hq Hqp epsilon t omega).1 (H q Hq Hqp epsilon t omega).2).
Defined.
End Stage.
Section Builder.
Context (X: νGpds).
Fixpoint SelectedExchangeChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames), Type.
Proof.
  destruct p as [|p]; intros k dcB cB FC cB' Hlen' frames paintings SD.
  - now exact (SelectedExchangeComponents X FC cB' Hlen' frames paintings SD.1).
  - now exact
      { _: @SelectedExchangeChain M XpB0 S0 HD p k.+1 _ (DepsCohsChainCons cB)
          (proj1FrtDepsCohs FC) (DepsCohsChainCons cB')
          (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
          frames.1 paintings.1 SD.1 &T
        SelectedExchangeComponents X FC cB' Hlen' frames paintings SD.2.1 }.
Defined.

Fixpoint selectedStepDataOfComponents (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
    (FC: FrtDepsCohs M HD cB)
    (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen cB' + p.+1)%nat)
    (frames: FrtFramesNextType FC cB')
    (paintings: FrtPaintingsNextType FC cB' frames)
    (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
    (components: SelectedExchangeChain M HD p cB FC cB' Hlen' frames paintings SD),
  @Core.FrtStepDataAt X M XpB0 S0 HD p k dcB cB FC cB' Hlen' frames paintings SD.
Proof.
  destruct p as [|p]; intros k dcB cB FC cB' Hlen' frames paintings SD components.
  - refine (frtRestrData0Next M FC cB' Hlen' frames paintings; _).
    now exact (selectedLayerOfExchange X FC cB' Hlen' frames paintings
      SD.1 SD.2.1 (frtRestrData0Next M FC cB' Hlen' frames paintings) components).
  - pose (spPrev := @selectedStepDataOfComponents M XpB0 S0 HD p k.+1 _ (DepsCohsChainCons cB)
      (proj1FrtDepsCohs FC) (DepsCohsChainCons cB')
      (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
      frames.1 paintings.1 SD.1 components.1).
    refine (spPrev; _).
    now exact (selectedLayerOfExchange X FC cB' Hlen' frames paintings
      SD.2.1 SD.2.2.1
      (RestrNext (mkFrtStepTypesAndRestrNext M HD p (DepsCohsChainCons cB)
        (proj1FrtDepsCohs FC) (DepsCohsChainCons cB')
        (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p.+1))
        frames.1 paintings.1 SD.1) spPrev) components.2).
Defined.

Section Initial.
Let P0: FgPrefix (X := X) 0 := (tt; fgThis0).
Let W0 := fgTowerAt 0 P0.
Let FC0 := towerFrtDepsCohsOf 0 W0 frt0List frp0List frtRestr0.
Let frames0 := fgFrtOf 0 W0 frt0List frp0List frtRestr0.
Let paintings0 := fgFrpOf 0 W0 frt0List frp0List frtRestr0.
Let split0 := fgSplitOf 0 P0 frt0List frp0List frtRestr0.
Definition FgInitialExchangeComponents: Type :=
  SelectedExchangeComponents X FC0 DepsCohsChainNil
    (descChainLen (descAt 1)) frames0 paintings0 split0.1.
Definition fgInitialDataOfComponents (components: FgInitialExchangeComponents): FgLevel0Datum (X := X) :=
  selectedStepDataOfComponents 0 (descAt 0) 0 DepsCohsChainNil FC0 DepsCohsChainNil
    (descChainLen (descAt 1)) frames0 paintings0 split0 components.
End Initial.

Definition FgSelectedExchangeData: Type := forall (m: nat) (s: FgLevel (X := X) m),
  let N := m.+1 in
  let W := fgTowerAt N (fgPrefixNext m s) in
  let ft := fgFrtNextOf m s in
  let fp := fgFrpNextOf m s in
  let Q := fgQNext m s in
  SelectedExchangeChain N (descAt N) N DepsCohsChainNil
    (towerFrtDepsCohsOf N W ft fp Q) DepsCohsChainNil
    (descChainLen (descAt N.+1)) (fgFrtOf N W ft fp Q)
    (fgFrpOf N W ft fp Q) (fgSplitOf N (fgPrefixNext m s) ft fp Q).

Definition fgStepDataOfComponents (components: FgSelectedExchangeData): Core.FgStepData X.
Proof.
  intros m s.
  now exact (selectedStepDataOfComponents m.+1 (descAt m.+1) m.+1 DepsCohsChainNil
    (towerFrtDepsCohsOf m.+1 (fgTowerAt m.+1 (fgPrefixNext m s))
      (fgFrtNextOf m s) (fgFrpNextOf m s) (fgQNext m s)) DepsCohsChainNil
    (descChainLen (descAt m.+2))
    (fgFrtOf m.+1 (fgTowerAt m.+1 (fgPrefixNext m s))
      (fgFrtNextOf m s) (fgFrpNextOf m s) (fgQNext m s))
    (fgFrpOf m.+1 (fgTowerAt m.+1 (fgPrefixNext m s))
      (fgFrtNextOf m s) (fgFrpNextOf m s) (fgQNext m s))
    (fgSplitOf m.+1 (fgPrefixNext m s) (fgFrtNextOf m s) (fgFrpNextOf m s) (fgQNext m s))
    (components m s)).
Defined.
End Builder.

Section FG.
Variable X: νGpds.
(** The top pair comparison is chosen so its child is the already used
    lower-cell comparison. Its projection law is therefore by cases. *)
Definition frtOwnedTopPair {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (t: (g X).(G0) M.+1):
  frtCellPair (DescS HD) (frtChainUp a) t =
  ((descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) t;
    (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2)
    : {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
        mkPainting (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) d}).
Proof.
  destruct a as [|parent_p parent_k parent_dc parent_a].
  - now reflexivity.
  - now exact (frtCellPairDeepCell HD parent_a t).
Defined.

Lemma frtOwnedTopPair_below {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (t: (g X).(G0) M.+1):
  f_equal unassoc (frtOwnedTopPair HD a t) = frtCellPairDeepCell HD a t.
Proof. destruct a; now reflexivity. Defined.

Section OwnedFrameView.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let canonicalTop := descTop HD cb.
Let canonicalFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Let rawTop := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1.
Context (frames: FrtFramesType F rawTop).

Let frameTranslate
  (z: {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
    mkPainting (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) d}) :=
  mkFrameEqv (frTr F) z.1.

(** This comparison is constructed before the top painting datum E. *)
Definition FrtOwnedFrameView: Type := forall t: (g X).(G0) M.+1,
  frames.2 t = target_identification frameTranslate (frtOwnedTopPair HD a t)
    (canonicalFrames.2 t).
End OwnedFrameView.

Section OwnedPaintingView.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb) (XA: DepsRestrExtension p.+1 k F.(_frDepsA)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Context (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let canonicalTop := descTop HD cb.
Let canonicalValue: forall t, mkPainting XB (canonicalTop t) := fun t =>
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2.
Let canonicalFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Context (E: FrtPaintingTopType F TX PX canonicalTop canonicalValue canonicalFrames).
Let rawTop := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1.
Let rawValue := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).2.
Context (frames: FrtFramesType F rawTop)
  (paintings: mkFrtPaintingTypes (X := X) M.+1 frames
    (mkPaintingEqvs TX) (mkPshPaintings (g X) PX)
    (mkCellValues (X := X) M.+1 (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))
      XB rawTop rawValue))
  (frameView: FrtOwnedFrameView HD a Hlen F Q frames).
Let frameTranslate
  (z: {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
    mkPainting XB d}) := mkFrameEqv (frTr F) z.1.
Let paintingTranslate
  (z: {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
    mkPainting XB d}) := mkPaintingEqv TX z.1 z.2.

(** The painting comparison is over the frame witness already chosen. *)
Definition FrtOwnedPaintingView: Type := forall t: (g X).(G0) M.+1,
  rew [fun e => rew [fun d => GDom (mkPainting XA d)] e in
      mkPshPainting (g X) PX t = mkPaintingEqv TX (rawTop t) (rawValue t)]
    frameView t in paintings.2 t =
  target_identification_dep frameTranslate paintingTranslate
    (frtOwnedTopPair HD a t) (canonicalFrames.2 t) (E t).
End OwnedPaintingView.

Definition frtOwnedFrameViewRoot {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  (F: FrtDeps M HD (DepsCohsChainNil (dcTop := νDepsCohsAt S0)))
  (Q: (mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrDataDef)):
  FrtOwnedFrameView HD DepsCohs3ChainNil (descChainLen HD) F Q
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q).
Proof. intro t. now reflexivity. Defined.

Definition frtOwnedPaintingViewRoot {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  (F: FrtDeps M HD (DepsCohsChainNil (dcTop := νDepsCohsAt S0)))
  (XA: DepsRestrExtension M.+1 0 F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs (νDepsCohs3At S0).(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (Q: (mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD DepsCohsChainNil)
    (fun t => (descCell (DescS HD) t).2)
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q)):
  FrtOwnedPaintingView HD DepsCohs3ChainNil (descChainLen HD) F XA TX PX Q E
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD M DepsCohsChainNil (descChainLen HD) F XA
      (mkDepsCohs (νDepsCohs3At S0).(_depsCohs2)).(_extraDeps) TX PX
      (fun t => (descCell (DescS HD) t).2) Q E)
    (frtOwnedFrameViewRoot HD F Q).
Proof. intro t. now reflexivity. Defined.

Section OwnedLowerFrameView.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Let canonicalTop := descTop HD cb.
Let canonicalFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Let rawTop := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1.
Context (frames: FrtFramesType F rawTop).
Let lowerFrameTranslate
  (z: {d: (mkFrames (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))).1.2 &T
    (mkPaintings XB).1.2 d}) := (mkFrameEqvs (frTr F)).1.2 z.1.

Definition FrtOwnedLowerFrameView: Type := forall t: (g X).(G0) M.+1,
  frames.1.2 t = target_identification lowerFrameTranslate
    (frtCellPairDeepCell HD a t) (canonicalFrames.1.2 t).

Let frameTranslate
  (z: {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
    mkPainting XB d}) := mkFrameEqv (frTr F) z.1.
Let canonicalSplit := frtSplitHead HD p cb F canonicalTop canonicalFrames
  (frtSplitOfQ M HD p cb Hlen F Q).

Definition frtOwnedLowerFrameViewOfSplit
  (SD: FrtSplitStep F rawTop frames)
  (V: FrtOwnedFrameView HD a Hlen F Q frames): FrtOwnedLowerFrameView.
Proof.
  intro t.
  refine (frame_view_prefix frameTranslate (frtOwnedTopPair HD a t)
    (frames.2 t) (canonicalFrames.2 t)
    (frames.1.2 t) (mkFrtLayerOfRestr F rawTop frames.1 SD.1 SD.2.1 t)
    (canonicalFrames.1.2 t)
      (mkFrtLayerOfRestr F canonicalTop canonicalFrames.1
        canonicalSplit.1 canonicalSplit.2.1 t)
    (SD.2.2 t) (canonicalSplit.2.2 t) (V t) • _).
  refine (eq_sym (target_identification_domain lowerFrameTranslate unassoc
    (frtOwnedTopPair HD a t) (canonicalFrames.1.2 t)) • _).
  now exact (f_equal
    (fun alpha: frtCellPair (DescS HD) (DepsCohsChainCons (frtChainUp a)) t =
      deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t) =>
      target_identification lowerFrameTranslate alpha (canonicalFrames.1.2 t))
    (frtOwnedTopPair_below HD a t)).
Defined.
End OwnedLowerFrameView.

Section OwnedLowerPaintingView.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb) (XA: DepsRestrExtension p.+1 k F.(_frDepsA)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Context (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let canonicalTop := descTop HD cb.
Let canonicalValue: forall t, mkPainting XB (canonicalTop t) := fun t =>
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2.
Let canonicalFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Context (E: FrtPaintingTopType F TX PX canonicalTop canonicalValue canonicalFrames).
Let canonicalPaintings := mkFrtPaintingsOfRestr M HD p cb Hlen F XA XB TX PX canonicalValue Q E.
Let rawTop := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1.
Let rawValue := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).2.
Context (frames: FrtFramesType F rawTop)
  (paintings: mkFrtPaintingTypes (X := X) M.+1 frames (mkPaintingEqvs TX)
    (mkPshPaintings (g X) PX)
    (mkCellValues (X := X) M.+1 (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))
      XB rawTop rawValue)).
Let lowerFrameTranslate
  (z: {d: (mkFrames (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))).1.2 &T
    (mkPaintings XB).1.2 d}) := (mkFrameEqvs (frTr F)).1.2 z.1.
Let lowerPaintingTranslate
  (z: {d: (mkFrames (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))).1.2 &T
    (mkPaintings XB).1.2 d}) := (mkPaintingEqvs TX).1.2 z.1 z.2.

Definition FrtOwnedLowerPaintingView
  (V: FrtOwnedLowerFrameView HD a Hlen F Q frames): Type := forall t: (g X).(G0) M.+1,
  rew [fun e => rew [fun d => GDom ((mkPaintings XA).1.2 d)] e in
    (mkPshPaintings (g X) PX).1.2 t = lowerPaintingTranslate
      (frtCellPair (DescS HD) (DepsCohsChainCons (frtChainUp a)) t)]
    V t in paintings.1.2 t =
  target_identification_dep lowerFrameTranslate lowerPaintingTranslate
    (frtCellPairDeepCell HD a t) (canonicalFrames.1.2 t) (canonicalPaintings.1.2 t).

Let frameTranslate
  (z: {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
    mkPainting XB d}) := mkFrameEqv (frTr F) z.1.
Let paintingTranslate
  (z: {d: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))) &T
    mkPainting XB d}) := mkPaintingEqv TX z.1 z.2.
Let canonicalSplit := frtSplitHead HD p cb F canonicalTop canonicalFrames
  (frtSplitOfQ M HD p cb Hlen F Q).

Definition frtOwnedLowerPaintingViewOfSplit
  (SD: FrtSplitStep F rawTop frames)
  (PS: SN.FrtPaintingSplitAt X F XA XB TX PX rawTop rawValue frames paintings SD)
  (V: FrtOwnedFrameView HD a Hlen F Q frames)
  (HV: FrtOwnedPaintingView HD a Hlen F XA TX PX Q E frames paintings V):
  FrtOwnedLowerPaintingView (frtOwnedLowerFrameViewOfSplit HD a Hlen F Q frames SD V).
Proof.
  intro t.
  refine (frame_view_prefix_dep frameTranslate paintingTranslate (frtOwnedTopPair HD a t)
    (frames.2 t) (canonicalFrames.2 t)
    (frames.1.2 t) (mkFrtLayerOfRestr F rawTop frames.1 SD.1 SD.2.1 t)
    (canonicalFrames.1.2 t)
      (mkFrtLayerOfRestr F canonicalTop canonicalFrames.1
        canonicalSplit.1 canonicalSplit.2.1 t)
    (SD.2.2 t) (canonicalSplit.2.2 t) (V t)
    (paintings.2 t) (E t) (paintings.1.2 t) (canonicalPaintings.1.2 t)
    (PS t) (SN.frtPaintingSplitOfRestr X M HD p cb Hlen F XA XB TX PX canonicalValue Q E t)
    (HV t) ⊙ _).
  refine (sigT_sym_eq (target_identification_domain_dep lowerFrameTranslate
    lowerPaintingTranslate unassoc (frtOwnedTopPair HD a t)
    (canonicalFrames.1.2 t) (canonicalPaintings.1.2 t)) ⊙ _).
  now exact (target_identification_path_dep lowerFrameTranslate lowerPaintingTranslate
    (frtOwnedTopPair_below HD a t) (canonicalFrames.1.2 t) (canonicalPaintings.1.2 t)).
Defined.
End OwnedLowerPaintingView.

Section OwnedViewChild.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p.+1 k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p.+1)%nat)
  (F: FrtDeps M HD cb)
  (Q: (mkFrtRestrTypesAndFrames M HD p.+1 cb Hlen F).(FrtRestrDataDef)).
Let canonicalTop := descTop HD cb.
Let canonicalFrames := (mkFrtRestrTypesAndFrames M HD p.+1 cb Hlen F).(FrtRestrFramesDef) Q.
Let rawTop := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1.
Context (frames: FrtFramesType F rawTop)
  (V: FrtOwnedLowerFrameView HD a Hlen F Q frames).
Let childHlen := Hlen • eq_sym (plus_n_Sm (cohsChainLen cb) p).

Definition frtOwnedFrameViewChild:
  FrtOwnedFrameView HD (DepsCohs3ChainCons a) childHlen (proj1FrtDeps F) Q.1 frames.1.
Proof. now exact V. Defined.

Context (XA: DepsRestrExtension p.+2 k F.(_frDepsA)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Context (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA).
Let canonicalValue: forall t, mkPainting XB (canonicalTop t) := fun t =>
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2.
Context (E: FrtPaintingTopType F TX PX canonicalTop canonicalValue canonicalFrames).
Let canonicalPaintings := mkFrtPaintingsOfRestr M HD p.+1 cb Hlen F XA XB TX PX canonicalValue Q E.
Let rawValue := fun t => (frtCellPair (DescS HD) (frtChainUp a) t).2.
Context (paintings: mkFrtPaintingTypes (X := X) M.+1 frames (mkPaintingEqvs TX)
    (mkPshPaintings (g X) PX)
    (mkCellValues (X := X) M.+1 (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))
      XB rawTop rawValue))
  (HV: FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E frames paintings V).

Definition frtOwnedPaintingViewChild:
  FrtOwnedPaintingView HD (DepsCohs3ChainCons a) childHlen (proj1FrtDeps F)
    (F.(_frDepsA); XA)%extradepsrestr (AddTrDep (frTr F) TX)
    (AddPshDep (g X) M (frtPshDeps F) PX) Q.1 (canonicalPaintings.1.2)
    frames.1 paintings.1 frtOwnedFrameViewChild.
Proof. now exact HV. Defined.
End OwnedViewChild.

Fixpoint FrtOwnedFrameViewChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
    (Hlen: cohs3ChainLen (descChain HD).2 =
      (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (Q: (mkFrtRestrTypesAndFrames M HD p
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrDataDef))
    (frames: FrtFramesType F (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1)), Type.
Proof.
  destruct p as [|p]; intros k dc3 a Hlen F Q frames.
  - now exact (FrtOwnedLowerFrameView HD a Hlen F Q frames).
  - now exact
      { _: @FrtOwnedFrameViewChain M XpB0 S0 HD p k.+1 _ (DepsCohs3ChainCons a)
          (Hlen • eq_sym (plus_n_Sm
            (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p))
          (proj1FrtDeps F) Q.1 frames.1 &T
        FrtOwnedLowerFrameView HD a Hlen F Q frames }.
Defined.

Fixpoint frtOwnedFrameViewsFromTop (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
    (Hlen: cohs3ChainLen (descChain HD).2 =
      (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (Q: (mkFrtRestrTypesAndFrames M HD p
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrDataDef))
    (frames: FrtFramesType F (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1))
    (SD: FrtSplitDataAt M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) F
      (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1) frames)
    (V: FrtOwnedFrameView HD a Hlen F Q frames),
  FrtOwnedFrameViewChain M HD p a Hlen F Q frames.
Proof.
  destruct p as [|p]; intros k dc3 a Hlen F Q frames SD V.
  - now exact (frtOwnedLowerFrameViewOfSplit HD a Hlen F Q frames SD V).
  - pose (lower := frtOwnedLowerFrameViewOfSplit HD a Hlen F Q frames SD.2 V).
    refine (@existT
      (FrtOwnedFrameViewChain M HD p (DepsCohs3ChainCons a)
        (Hlen • eq_sym (plus_n_Sm
          (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p))
        (proj1FrtDeps F) Q.1 frames.1)
      (fun _ => FrtOwnedLowerFrameView HD a Hlen F Q frames) _ lower).
    now exact (@frtOwnedFrameViewsFromTop M XpB0 S0 HD p k.+1 _ (DepsCohs3ChainCons a)
      (Hlen • eq_sym (plus_n_Sm
        (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p))
      (proj1FrtDeps F) Q.1 frames.1 SD.1
      (frtOwnedFrameViewChild HD a Hlen F Q frames lower)).
Defined.

Definition frtOwnedFrameViewsRoot {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  (F: FrtDeps M HD (DepsCohsChainNil (dcTop := νDepsCohsAt S0)))
  (Q: (mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrDataDef)):
  FrtOwnedFrameViewChain M HD M DepsCohs3ChainNil (descChainLen HD) F Q
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q) :=
  frtOwnedFrameViewsFromTop M HD M DepsCohs3ChainNil (descChainLen HD) F Q
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q)
    (frtSplitOfQ M HD M DepsCohsChainNil (descChainLen HD) F Q)
    (frtOwnedFrameViewRoot HD F Q).

Fixpoint FrtOwnedPaintingViewChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps))
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (Q: (mkFrtRestrTypesAndFrames M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) (fun t => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2) ((mkFrtRestrTypesAndFrames M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrFramesDef) Q))
    (frames: FrtFramesType F (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1))
    (paintings: mkFrtPaintingTypes (X := X) M.+1 frames (mkPaintingEqvs TX)
      (mkPshPaintings (g X) PX)
      (mkCellValues (X := X) M.+1 (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))
        (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1) (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).2)))
    (FV: FrtOwnedFrameViewChain M HD p a Hlen F Q frames), Type.
Proof.
  destruct p as [|p]; intros k dc3 a Hlen F XA TX PX Q E frames paintings FV.
  - now exact (FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E frames paintings FV).
  - now exact
      { _: @FrtOwnedPaintingViewChain M XpB0 S0 HD p k.+1 _ (DepsCohs3ChainCons a)
          (Hlen • eq_sym (plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p))
          (proj1FrtDeps F) (F.(_frDepsA); XA)%extradepsrestr
          (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX) Q.1
          (mkFrtPaintingsOfRestr M HD p.+1 (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) TX PX (fun t => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2) Q E).1.2
          frames.1 paintings.1 FV.1 &T
        FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E frames paintings FV.2 }.
Defined.

Fixpoint frtOwnedPaintingViewsFromTop (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
    (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps))
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (Q: (mkFrtRestrTypesAndFrames M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX (descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) (fun t => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2) ((mkFrtRestrTypesAndFrames M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrFramesDef) Q))
    (frames: FrtFramesType F (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1))
    (paintings: mkFrtPaintingTypes (X := X) M.+1 frames (mkPaintingEqvs TX)
      (mkPshPaintings (g X) PX)
      (mkCellValues (X := X) M.+1 (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs)))
        (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1) (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).2)))
    (SD: FrtSplitDataAt M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) F (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1) frames)
    (PS: SN.FrtPaintingSplitChainAt X M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) F XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps)
      TX PX (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).1) (fun t => (frtCellPair (DescS HD) (frtChainUp a) t).2) frames paintings SD)
    (V: FrtOwnedFrameView HD a Hlen F Q frames)
    (HV: FrtOwnedPaintingView HD a Hlen F XA TX PX Q E frames paintings V),
  FrtOwnedPaintingViewChain M HD p a Hlen F XA TX PX Q E frames paintings
    (frtOwnedFrameViewsFromTop M HD p a Hlen F Q frames SD V).
Proof.
  destruct p as [|p]; intros k dc3 a Hlen F XA TX PX Q E frames paintings SD PS V HV.
  - now exact (frtOwnedLowerPaintingViewOfSplit HD a Hlen F XA TX PX Q E
      frames paintings SD PS V HV).
  - pose (lower := frtOwnedLowerFrameViewOfSplit HD a Hlen F Q frames SD.2 V).
    pose (lowerPainting := frtOwnedLowerPaintingViewOfSplit HD a Hlen F XA TX PX Q E
      frames paintings SD.2 PS.2 V HV).
    refine (@existT _
      (fun _ => FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E
        frames paintings lower) _ lowerPainting).
    now exact (@frtOwnedPaintingViewsFromTop M XpB0 S0 HD p k.+1 _ (DepsCohs3ChainCons a)
          (Hlen • eq_sym (plus_n_Sm (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a))) p))
          (proj1FrtDeps F) (F.(_frDepsA); XA)%extradepsrestr
          (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX) Q.1
          (mkFrtPaintingsOfRestr M HD p.+1 (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) TX PX (fun t => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2) Q E).1.2
          frames.1 paintings.1
      SD.1 PS.1 (frtOwnedFrameViewChild HD a Hlen F Q frames lower)
      (frtOwnedPaintingViewChild HD a Hlen F Q frames lower XA TX PX E paintings lowerPainting)).
Defined.

Definition frtOwnedPaintingViewsRoot {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0)
  (F: FrtDeps M HD (DepsCohsChainNil (dcTop := νDepsCohsAt S0)))
  (XA: DepsRestrExtension M.+1 0 F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs (νDepsCohs3At S0).(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (Q: (mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD DepsCohsChainNil)
    (fun t => (descCell (DescS HD) t).2)
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q)):
  FrtOwnedPaintingViewChain M HD M DepsCohs3ChainNil (descChainLen HD) F XA TX PX Q E
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD M DepsCohsChainNil (descChainLen HD) F XA
      (mkDepsCohs (νDepsCohs3At S0).(_depsCohs2)).(_extraDeps) TX PX
      (fun t => (descCell (DescS HD) t).2) Q E)
    (frtOwnedFrameViewsRoot HD F Q) :=
  frtOwnedPaintingViewsFromTop M HD M DepsCohs3ChainNil (descChainLen HD) F XA TX PX Q E
    ((mkFrtRestrTypesAndFrames M HD M DepsCohsChainNil (descChainLen HD) F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD M DepsCohsChainNil (descChainLen HD) F XA
      (mkDepsCohs (νDepsCohs3At S0).(_depsCohs2)).(_extraDeps) TX PX
      (fun t => (descCell (DescS HD) t).2) Q E)
    (frtSplitOfQ M HD M DepsCohsChainNil (descChainLen HD) F Q)
    (SN.frtPaintingSplitChainOfRestr X M HD M DepsCohsChainNil
      (descChainLen HD) F XA (mkDepsCohs (νDepsCohs3At S0).(_depsCohs2)).(_extraDeps)
      TX PX (fun t => (descCell (DescS HD) t).2) Q E)
    (frtOwnedFrameViewRoot HD F Q) (frtOwnedPaintingViewRoot HD F XA TX PX Q E).

Definition fgOwnedFrameViews (m: nat) (W: FgTower (X := X) m)
  (ft: FgFrt m W) (fp: FgFrp m W ft) (Q: FgRestrData m W ft fp) :=
  frtOwnedFrameViewsRoot (descAt m) (fgDeps m W ft fp) Q.

Definition fgOwnedPaintingViews (m: nat) (W: FgTower (X := X) m)
  (ft: FgFrt m W) (fp: FgFrp m W ft) (Q: FgRestrData m W ft fp) :=
  let FC := towerFrtDepsCohsOf m W ft fp Q in
  frtOwnedPaintingViewsRoot (descAt m) (fgDeps m W ft fp)
    FC.(_fcXA) FC.(_fcTX) FC.(_fcPX) Q (SN.fgPaintingTopDirect X m W ft fp Q).

Section SelectedRestrictionRetarget.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Let dcB := dc3.(_depsCohs2).(_depsCohs).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb) (XA: DepsRestrExtension p.+1 k F.(_frDepsA)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Let rpB := (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings).
Context (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let canonicalTop := descTop HD cb.
Let canonicalValue: forall u, mkPainting XB (canonicalTop u) := fun u =>
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) u)).2.2.
Let canonicalFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Context (E: FrtPaintingTopType F TX PX canonicalTop canonicalValue canonicalFrames).
Let canonicalPaintings := mkFrtPaintingsOfRestr M HD p cb Hlen F XA XB TX PX canonicalValue Q E.
Let rawTop := fun u => (frtCellPair (DescS HD) (frtChainUp a) u).1.
Let rawValue := fun u => (frtCellPair (DescS HD) (frtChainUp a) u).2.
Context (frames: FrtFramesType F rawTop)
  (paintings: mkFrtPaintingTypes (X := X) M.+1 frames
    (mkPaintingEqvs TX) (mkPshPaintings (g X) PX)
    (mkCellValues (X := X) M.+1 (mkDepsRestr (depsCohs := dcB)) XB rawTop rawValue)).

Let PE := fun d => GDom (mkPainting (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr d).
Let PXlow := fun d => GDom (mkPainting (F.(_frDepsA); XA)%extradepsrestr d).
Let PA := fun d => GDom (F.(_frDepsA).(_paintings).2 d).
Let PB := fun d => GDom ((mkDepsRestr (depsCohs := dcB)).(_paintings).2 d).
Let f := fun d => (mkFrameEqvs (frTr F)).1.2 d.
Let fp := fun d c => mkPaintingEqv (AddTrDep (frTr F) TX) d c.
Let alpha := fun u => frtCellPairDeepCell HD a u.
Let identify := fun z: {d: mkFrame (mkDepsRestr (depsCohs := dcB)).(1) &T PE d} => f z.1.
Let identifyPaint := fun z: {d: mkFrame (mkDepsRestr (depsCohs := dcB)).(1) &T PE d} => fp z.1 z.2.

Context (view: FrtOwnedLowerFrameView HD a Hlen F Q frames)
  (q: nat) (Hq: q <= k) (Hdim: q + p <= M)
  (epsilon: arity) (u: (g X).(G0) M.+1).
Let rA := F.(_frDepsA).(_restrFrames).2 q Hq epsilon.
Let rB := (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq epsilon.
Let rpAq := rpA.2 q Hq epsilon.
Let rpBq := rpB.2 q Hq epsilon.
Let phi := fun d => F.(_frFrameEqvs).2 d.
Let phip := fun d c => F.(_frPaintingEqvs).2 d c.
Let gq := fun d => rA (f d).
Let gp := fun d c => rpAq (f d) (fp d c).
Let tq := F.(_frTrRestrs).2 q Hq epsilon.
Let tp := trRp.2 q Hq epsilon.
Let c := projT1_eq (eq_sym (alpha u)).
Let cp := projT2_eq (eq_sym (alpha u)).
Let face := (g X).(GFace) M (q + p) Hdim epsilon u.
Let i := F.(_frFrames).2 face.
Let hi := F.(_frPaintings).2 face.
Let b := descQcells cb Hlen q Hq Hdim epsilon u.
Let hb := descCanonicalPaintingPaired HD q a Hlen Hq Hdim epsilon u.
Let ps := F.(_frPshRestrs).2 q Hq Hdim epsilon u.
Let hps := pshRp.2 q Hq Hdim epsilon u.
Let canonicalId := canonicalFrames.1.2 u.
Let canonicalPaint := canonicalPaintings.1.2 u.
Let actualId := frames.1.2 u.
Let actualPaint := paintings.1.2 u.
Let n0 := ps • f_equal rA canonicalId.
Let n1 := ps • f_equal rA actualId.
Let hn0 := hps ⊙[PA] sigT_map_eq (P := PXlow) (Q := PA) (f := rA) rpAq canonicalPaint.
Let hn1 := hps ⊙[PA] sigT_map_eq (P := PXlow) (Q := PA) (f := rA) rpAq actualPaint.
Let stored := @SN.frtRestrictionClauseOf X M XpB0 S0 HD p k dcB cb Hlen F Q
  q Hq Hdim epsilon u.
Let trNatural := exchange_map_cell rB phi gq tq c.
Let viewRestrict := view_restriction_cell f rA (alpha u) canonicalId actualId (view u) ps.

(** The selected frame recipe only reads the frame part of the owned view. *)
Definition frtSelectedRawCell :=
  retarget_restriction_cell phi rB gq tq c i b n0 n1 stored trNatural viewRestrict.

Definition frtSelectedRawLeft :=
  (hi ⊙[PA] sigT_map_eq (P := PB) (Q := PA) (f := phi) phip
    (hb ⊙[PB] sigT_map_eq (P := PE) (Q := PB) (f := rB) rpBq cp))
    ⊙[PA] tp (rawTop u).1 ((rawTop u).2; rawValue u).
Definition frtSelectedRawRight := hn1.

Lemma frtSelectedRawCell_dep
  (viewPaint: FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E frames paintings view)
  (H: @SN.FrtRestrictionPaintingSelected X M XpB0 S0 HD p k dc3 a Hlen F
    XA TX PX rpA trRp pshRp Q E q Hq Hdim epsilon u):
  DPathCellOver (P := PA) frtSelectedRawLeft frtSelectedRawRight frtSelectedRawCell.
Proof.
  pose (HT := exchange_map_cell_dep rB phi gq tq PE PB PA rpBq phip gp tp c cp).
  pose (HA := view_restriction_cell_dep f rA PXlow PA fp rpAq
    (alpha u) canonicalId actualId (view u) ps canonicalPaint actualPaint hps (viewPaint u)).
  now exact (retarget_restriction_cell_dep phi rB gq tq c i b n0 n1
    stored trNatural viewRestrict PA PB phip hi hb
    (sigT_map_eq (P := PE) (Q := PB) (f := rB) rpBq cp)
    (sigT_map_eq (P := PE) (Q := PA) (f := gq) gp cp)
    (tp (canonicalTop u).1 ((canonicalTop u).2; canonicalValue u))
    (tp (rawTop u).1 ((rawTop u).2; rawValue u)) hn0 hn1 H HT HA).
Defined.
End SelectedRestrictionRetarget.



Section InitialSelectedCertificate.
Let initialPrefix: FgPrefix (X := X) 0 := (tt; fgThis0).
Let initialTower := fgTowerAt (X := X) 0 initialPrefix.
Let initialF := fgDeps (X := X) 0 initialTower frt0List frp0List.
Let initialFC := towerFrtDepsCohsOf (X := X) 0 initialTower frt0List frp0List frtRestr0.
Let initialHD := descAt (X := X) 0.
Let initialDC := νDepsCohs3At (νGpdPack 0 X).2.
Let initialChain: DepsCohs3Chain initialDC initialDC := DepsCohs3ChainNil.
Let initialLength := descChainLen (X := X) initialHD.
Let initialPaintingTop := @SN.fgPaintingTopDirect X 0 initialTower frt0List frp0List frtRestr0.

(** The initial stage has only the zero restriction. Its selected
    painting certificate uses the zero laws already generated by the
    three towers and the clause stored in the initial restriction data. *)
Definition fgInitialRestrictionPaintingSelected:
  @SN.FrtRestrictionPaintingSelectedChain X 0
    (νGpdPack 0 X).1 (νGpdPack 0 X).2 initialHD 0 0 initialDC initialChain
    initialLength initialF initialFC.(_fcXA) initialFC.(_fcTX) initialFC.(_fcPX)
    initialFC.(_fcRpA) initialFC.(_fcTrRp) initialFC.(_fcPshRp)
    frtRestr0 initialPaintingTop.
Proof.
  intros [|q] Hq Hdim epsilon u.
  - now exact (@SN.frtRestrictionPaintingZero X 0
      (νGpdPack 0 X).1 (νGpdPack 0 X).2 initialHD 0 0 initialDC initialChain
      initialLength initialF initialFC.(_fcXA) initialFC.(_fcTX) initialFC.(_fcPX)
      initialFC.(_fcRpA) initialFC.(_fcTrRp) initialFC.(_fcPshRp)
      frtRestr0 initialPaintingTop
      (@rpAChainOf X 0 initialTower frt0List frp0List frtRestr0).2
      (@trRpChainOf X 0 initialPrefix frt0List frp0List frtRestr0).2
      (@pshRpChain0 X).2 epsilon u).
  - now destruct (leR_O_contra Hq).
Defined.
End InitialSelectedCertificate.




Section ExchangeSourceIndex.
Variable ps: νGpdPresentation arity.

(** Reverse the negative index change through a mapped face using the
    same dimension equality and its inverse. *)
Definition mappedReverseFaceIndex {n q q'} (e: q = q')
  (Hq: q <= n) (Hq': q' <= n) (epsilon: arity) (t: ps.(G0) n.+1)
  {T: Type} (R: ps.(G0) n -> T):
  eq_sym (f_equal R (pshFaceDimIrr ps (eq_sym e)
    (Hq := Hq') (Hq' := Hq) epsilon t)) =
  f_equal R (pshFaceDimIrr ps e (Hq := Hq) (Hq' := Hq') epsilon t) :=
  f_equal (fun h => eq_sym (f_equal R h))
    (eq_sym (pshFaceDimIrr_sym ps e (Hq := Hq) (Hq' := Hq') epsilon t))
  • (eq_sym_f_equal R
      (eq_sym (pshFaceDimIrr ps e (Hq := Hq) (Hq' := Hq') epsilon t))
    • f_equal (fun h => f_equal R h)
      (eq_sym_involutive (pshFaceDimIrr ps e
        (Hq := Hq) (Hq' := Hq') epsilon t))).

Definition frtExchangeSourceIndex {M p q}
  (Hqp: q + p.+1 <= M.+1) (epsilon omega: arity) (t: ps.(G0) M.+2):
  (ps.(GFaceCoh) M (q + p) (⇓ leR_add_shift Hqp)
      p (leR_add_l q) epsilon omega t
    • eq_sym (f_equal (ps.(GFace) M p
        (leR_add_l q ↕ (⇓ leR_add_shift Hqp)) omega)
      (pshFaceDimIrr ps (eq_sym (plus_n_Sm q p))
        (Hq := Hqp) (Hq' := leR_add_shift Hqp) epsilon t))) =
  (ps.(GFaceCoh) M (q + p) (⇓ leR_add_shift Hqp)
      p (leR_add_l q) epsilon omega t
    • f_equal (ps.(GFace) M p
        (leR_add_l q ↕ (⇓ leR_add_shift Hqp)) omega)
      (pshFaceDimIrr ps (plus_n_Sm q p)
        (Hq := ⇑ (⇓ leR_add_shift Hqp)) (Hq' := Hqp) epsilon t)) :=
  whisker_l (ps.(GFaceCoh) M (q + p) (⇓ leR_add_shift Hqp)
      p (leR_add_l q) epsilon omega t)
    (mappedReverseFaceIndex (plus_n_Sm q p)
      (leR_add_shift Hqp) Hqp epsilon t
      (ps.(GFace) M p (leR_add_l q ↕ (⇓ leR_add_shift Hqp)) omega)).
End ExchangeSourceIndex.

Section ActualBExchangeBoundary.
Context {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs (X := X) M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType (X := X) FC cB')
  (paintings: FrtPaintingsNextType (X := X) FC cB' frames)
  (Hpair: FrtPairLawAt (X := X) FC.(_fcF) (frtTopNext FC cB'))
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (epsilon: arity) (t: (g X).(G0) M.+2) (omega: arity).
Let PB := fun d => GDom (mkPainting dcB.(_extraDeps) d).
Let PD := fun d => GDom (Layer (fun zeta =>
  (mkDepsRestr (depsCohs := dcB)).(_paintings).2
    ((mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O zeta d))).
Let PE := fun d => GDom ((mkPaintings
  (mkDepsRestr (depsCohs := dcB); FC.(_fcXB))%extradepsrestr).2 d).
Let rb0 := (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 0 leR_O omega.
Let rbq := (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq epsilon.
Let rpq := FC.(_fcRpB).2 q Hq epsilon.
Let valueAt := fun d (l: PD d) => nth l omega.
Let D := descQcells cB' Hlen' q Hq Hqp epsilon t.
Let W := (descTop (DescS HD) cB' t).1.
Let face := (g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t.
Let hp := Hpair omega face.
Let gamma := FC.(_fcCohsB).2 q Hq 0 leR_O epsilon omega W.1.
Let pairAt := @Core.frtCellPair X M XpB0 S0 HD p k dcB cB.
Let readAt := fun z: mkFrame (mkDepsRestr (depsCohs := dcB)) =>
  ((rb0 z.1; valueAt z.1 z.2): {d: mkFrame dcB.(_deps) &T PB d}).
Let restrAt := fun z: {d: mkFrame (mkDepsRestr (depsCohs := dcB)).(1) &T PE d} =>
  ((rbq z.1; rpq z.1 z.2): {d: mkFrame dcB.(_deps) &T PB d}).
Let J := frtPairLawPrev FC cB' Hlen' frames paintings omega t.

(** The exchange value is the existing geometric constructor. Its
    displayed inverse is normalized with the inverse companion once. *)
Definition actualBExchangeTotal:
  readAt ((mkDepsRestr (depsCohs := frtDcB FC)).(_restrFrames).2 q Hq epsilon W) =
  restrAt ((mkDepsRestr (depsCohs := proj1DepsCohs (frtDcB FC))).(_restrFrames).2
    0 leR_O omega W.1; nth W.2 omega) :=
  (= eq_sym gamma; rewSwapSym PB gamma (nth_lmap _ W.2 omega)).
Definition actualBExchangeNth := ltac:(
  let e := eval cbv delta [actualBExchangeTotal] in actualBExchangeTotal in
  lazymatch e with
  | context [rewSwapSym _ _ ?h] => now exact h
  end).
Definition actualBExchangeBack := eq_sym actualBExchangeNth.
Definition actualBExchangeEncode:
  actualBExchangeTotal = (=eq_sym gamma; sigT_sym_eq (P := PB) (p := gamma) actualBExchangeBack).
Proof.
  pose (H := swap_as_inverse PB gamma actualBExchangeNth).
  let T := type of H in
  lazymatch T with
  | @eq ?D _ _ =>
    now exact (f_equal (fun k: D => eq_existT_curried (P := PB) (eq_sym gamma) k) H)
  end.
Defined.

Definition actualDTotal := hp • (f_equal readAt D • actualBExchangeTotal).
Definition actualDFrame :=
  projT1_eq hp • (f_equal rb0 (projT1_eq D) • eq_sym gamma).
Definition actualDValue := projT2_eq hp ⊙[PB]
  (sigT_map_eq (P := PD) (Q := PB) (f := rb0) valueAt (projT2_eq D)
    ⊙[PB] sigT_sym_eq (P := PB) (p := gamma) actualBExchangeBack).
Definition actualDEncode: actualDTotal = (=actualDFrame; actualDValue).
Proof.
  now exact (sigT_path_paste (P := PB)
    (eq_sym (totalPathReencode hp))
    (sigT_path_paste (P := PB)
      (sigT_total_map_cell (P := PD) (Q := PB) rb0 valueAt D)
      actualBExchangeEncode)).
Defined.
Definition actualJEncode:
  f_equal restrAt J =
  (= f_equal rbq (projT1_eq J);
     sigT_map_eq (P := PE) (Q := PB) (f := rbq) rpq (projT2_eq J)) :=
  sigT_total_map_cell (P := PE) (Q := PB) rbq rpq J.



Section SelectedBExchangeDecode.
Let u := (g X).(GFace) M.+1 p
  (leR_add_l q ↕ ↑ (⇓ leR_add_shift Hqp)) omega t.
Let x := (g X).(GFace) M (q + p) (⇓ leR_add_shift Hqp) epsilon u.
Let y := (g X).(GFace) M p (⇓ FC.(_fcF).(_frBound)) omega face.
Let jsource := @Core.frtCellPair X M.+1 _ _ (DescS HD) p k.+1 _
  (DepsCohsChainCons cB') u.
Let tailD := f_equal readAt D • actualBExchangeTotal.
Context (h h0: x = y) (Hh: h = h0)
  (b: (pairAt x).1 = rbq jsource.1)
  (hb: rew [PB] b in (pairAt x).2 = rpq jsource.1 jsource.2)
  (bTotal: pairAt x = restrAt jsource) (EB: bTotal = (=b; hb))
  (pairCanonical: pairAt y = readAt (frtTopNext FC cB' face))
  (HPC: hp = pairCanonical)
  (BSQ: f_equal pairAt h0 • (pairCanonical • tailD) =
    bTotal • f_equal restrAt J).

(** The geometric source and pair-law presentations are changed once,
    before decoding their common total square. *)
Definition actualBExchangeRebase:
  f_equal pairAt h • actualDTotal = bTotal • f_equal restrAt J :=
  whisker_r (f_equal (fun e => f_equal pairAt e) Hh) actualDTotal
    • (whisker_l (f_equal pairAt h0) (whisker_r HPC tailD) • BSQ).

Definition actualBExchangeFrame:
  f_equal (fun v => (pairAt v).1) h • actualDFrame =
  b • f_equal rbq (projT1_eq J) :=
  geometric_square_frame (P := PB)
    (sigT_path_paste (P := PB) (f_equal_sigma_decompose pairAt h) actualDEncode)
    (sigT_path_paste (P := PB) EB actualJEncode) actualBExchangeRebase.

Definition actualBExchangeFrame_dep:
  DPathCellOver (P := PB)
    (f_equal_dep_sigT (fun v => (pairAt v).1) (fun v => (pairAt v).2) h
      ⊙[PB] actualDValue)
    (hb ⊙[PB] sigT_map_eq (P := PE) (Q := PB) (f := rbq) rpq (projT2_eq J))
    actualBExchangeFrame :=
  geometric_square_frame_dep (P := PB)
    (sigT_path_paste (P := PB) (f_equal_sigma_decompose pairAt h) actualDEncode)
    (sigT_path_paste (P := PB) EB actualJEncode) actualBExchangeRebase.
End SelectedBExchangeDecode.

End ActualBExchangeBoundary.
Section SelectedRawBTotal.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Let dcB := dc3.(_depsCohs2).(_depsCohs).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Let rpB := (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (q: nat) (Hq: q <= k) (Hdim: q + p <= M)
  (epsilon: arity) (u: (g X).(G0) M.+1).
Let PE := fun d => GDom (mkPainting (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr d).
Let PB := fun d => GDom ((mkDepsRestr (depsCohs := dcB)).(_paintings).2 d).
Let r := (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq epsilon.
Let rp := rpB.2 q Hq epsilon.
Let alpha := frtCellPairDeepCell HD a u.
Let c := projT1_eq (eq_sym alpha).
Let cp := projT2_eq (eq_sym alpha).
Let b := descQcells cb Hlen q Hq Hdim epsilon u.
Let hb := descCanonicalPaintingPaired HD q a Hlen Hq Hdim epsilon u.

(** The geometric B leg is normalized using the canonical pair chosen
    frame path and the component encoding of the same endpoint correction. *)
Lemma descCellPairRestrTotalSelected:
  @descCellPairRestrTotal X M XpB0 S0 HD p k dc3 a
    q Hq (q + p) Hdim eq_refl Hlen epsilon u =
  (=b • f_equal r c;
    hb ⊙[PB] sigT_map_eq (P := PE) (Q := PB) (f := r) rp cp).
Proof.
  change ((=b; hb) •
    f_equal (fun z: {d: mkFrame (mkDepsRestr (depsCohs := dcB)).(1) &T PE d} =>
      (r z.1; rp z.1 z.2)) (eq_sym alpha) =
    (=b • f_equal r c;
      hb ⊙[PB] sigT_map_eq (P := PE) (Q := PB) (f := r) rp cp)).
  now exact (sigT_path_paste (P := PB) (p := b) (q := f_equal r c)
    (h := hb) (k := sigT_map_eq (P := PE) (Q := PB) (f := r) rp cp)
    eq_refl (sigT_total_map_cell (P := PE) (Q := PB) r rp (eq_sym alpha))).
Defined.
End SelectedRawBTotal.

Section GeneratedBExchange.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (F: FrtDeps (X := X) M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
    (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA
    (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) TX rpA
    (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings) trRp cohsA
    (mkDepsCohs dc3.(_depsCohs2)).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA)).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Let FC := mkFrtDepsCohsGen (cohs3ChainDepsCohs2 a) F XA TX PX rpA trRp pshRp
  cohsA trCohs pshCohs.
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen (frtChainUp a) + p.+1)%nat)
  (frames: FrtFramesNextType (X := X) FC (frtChainUp a))
  (paintings: FrtPaintingsNextType (X := X) FC (frtChainUp a) frames)
  (Hpair: FrtPairLawAt (X := X) F (frtTopNext FC (frtChainUp a)))
  (HPC: forall epsilon u, Hpair epsilon u = frtPairLawAlignU HD a Hlen F epsilon u)
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (epsilon: arity) (t: (g X).(G0) M.+2) (omega: arity).
Let u := (g X).(GFace) M.+1 p
  (leR_add_l q ↕ ↑ (⇓ leR_add_shift Hqp)) omega t.
Let face := (g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t.
Let dcB := dc3.(_depsCohs2).(_depsCohs).
Let Bpaint := fun d => GDom ((mkDepsRestr (depsCohs := dcB)).(_paintings).2 d).
Let Epaint := fun d => GDom ((mkPaintings (mkDepsRestr (depsCohs := dcB);
  (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps))%extradepsrestr).2 d).
Let r := (mkDepsRestr (depsCohs := dcB)).(_restrFrames).2 q Hq epsilon.
Let rp := (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings).2 q Hq epsilon.
Let alpha := frtCellPairDeepCell HD a u.
Let b := descQcells cb Hlen q Hq (⇓ leR_add_shift Hqp) epsilon u
  • f_equal r (projT1_eq (eq_sym alpha)).
Let hb := descCanonicalPaintingPaired HD q a Hlen Hq (⇓ leR_add_shift Hqp) epsilon u
  ⊙[Bpaint] sigT_map_eq (P := Epaint) (Q := Bpaint) (f := r) rp (projT2_eq (eq_sym alpha)).
Let rawB := @descCellPairRestrTotal X M XpB0 S0 HD p k dc3 a q Hq
  (q + p) (⇓ leR_add_shift Hqp) eq_refl Hlen epsilon u.
Let EB := descCellPairRestrTotalSelected HD a Hlen q Hq (⇓ leR_add_shift Hqp) epsilon u.
Let Hsource := frtExchangeSourceIndex (g X) Hqp epsilon omega t.
Let h := ltac:(let T := type of Hsource in lazymatch T with ?h = _ => now exact h end).
Let h0 := ltac:(let T := type of Hsource in lazymatch T with _ = ?h0 => now exact h0 end).
Let BSQ := @Geometry.frtPairSqTotalLadder X M XpB0 S0 HD p k dc3 a F XA TX PX
  rpA trRp pshRp cohsA trCohs pshCohs Hlen Hlen' frames paintings q Hq Hqp epsilon omega t.

(** The actual geometric producer supplies the square. Every change of
    presentation is the selected source, pair-law, or edge companion. *)
Definition generatedBExchangeFrame :=
  @actualBExchangeFrame M XpB0 S0 HD p k dcB cb FC (frtChainUp a) Hlen'
    frames paintings Hpair q Hq Hqp epsilon t omega h h0 Hsource b hb rawB EB
    (frtPairLawAlignU HD a Hlen F omega face) (HPC omega face) BSQ.
Definition generatedBExchangeFrame_dep :=
  @actualBExchangeFrame_dep M XpB0 S0 HD p k dcB cb FC (frtChainUp a) Hlen'
    frames paintings Hpair q Hq Hqp epsilon t omega h h0 Hsource b hb rawB EB
    (frtPairLawAlignU HD a Hlen F omega face) (HPC omega face) BSQ.
Section GeneratedSelectedComponent.
Context (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Context (E: FrtPaintingTopType F TX PX (descTop HD cb)
    (fun v => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) v)).2.2)
    ((mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q))
  (view: FrtOwnedLowerFrameView HD a Hlen F Q frames).
Let PA := fun d => GDom (F.(_frDepsA).(_paintings).2 d).
Let PXlower := fun d => GDom (mkPainting (F.(_frDepsA); XA)%extradepsrestr d).
Let phi := fun d => F.(_frFrameEqvs).2 d.
Let pe := fun d c => F.(_frPaintingEqvs).2 d c.
Let prefixMap := fun d => (mkFrameEqvs (frTr F)).1.2 d.
Let prefixPaint := fun d c => mkPaintingEqv (AddTrDep (frTr F) TX) d c.
Let raq := F.(_frDepsA).(_restrFrames).2 q Hq epsilon.
Let rap := rpA.2 q Hq epsilon.
Let pairAt := @Core.frtCellPair X M XpB0 S0 HD p k dcB cb.
Let P := F.(_frPshFrames).2.
Let psection := F.(_frPshPaintings).2.
Let Cframe := fun v => (pairAt v).1.
Let csection := fun v => (pairAt v).2.
Let I := F.(_frFrames).2.
Let ip := F.(_frPaintings).2.
Let G := fun d => raq (prefixMap d).
Let gp := fun d c => rap (prefixMap d) (prefixPaint d c).
Let T := F.(_frTrRestrs).2 q Hq epsilon.
Let tp := trRp.2 q Hq epsilon.
Let n := F.(_frPshRestrs).2 q Hq (⇓ leR_add_shift Hqp) epsilon u
  • f_equal raq (frames.1.2 u).
Let hn := pshRp.2 q Hq (⇓ leR_add_shift Hqp) epsilon u
  ⊙[PA] sigT_map_eq (P := PXlower) (Q := PA) (f := raq) rap (paintings.1.2 u).
Let x := (g X).(GFace) M (q + p) (⇓ leR_add_shift Hqp) epsilon u.
Let y := (g X).(GFace) M p (⇓ F.(_frBound)) omega face.
Let J := frtPairLawPrev FC (frtChainUp a) Hlen' frames paintings omega t.
Let jsource := ltac:(let JJ := type of J in
  lazymatch JJ with @eq _ ?z _ => now exact z end).
Let jtarget := ltac:(let JJ := type of J in
  lazymatch JJ with @eq _ _ ?z => now exact z end).
Let d := actualDFrame FC (frtChainUp a) Hlen' Hpair q Hq Hqp epsilon t omega.
Let hd := actualDValue FC (frtChainUp a) Hlen' Hpair q Hq Hqp epsilon t omega.
Let HI := exchange_section_cell P Cframe phi I h.
Let HT := exchange_map_cell r phi G T (projT1_eq J).
Let HN := @frtSelectedRawCell M XpB0 S0 HD p k dc3 a Hlen F Q frames view
  q Hq (⇓ leR_add_shift Hqp) epsilon u.

(** The selected C certificate and the generated B exchange determine
    the exact upper cell and its painting companion. *)
Definition frtSelectedExchangeCell:
  K.ActualExchangeCell X FC (frtChainUp a) Hlen' frames paintings Hpair
    q Hq Hqp epsilon t omega :=
  restriction_exchange_paste P Cframe phi r G I T h (projT1_eq J)
    d b n HI HT generatedBExchangeFrame HN.

Lemma frtSelectedExchangeCell_dep
  (viewPaint: FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E frames paintings view)
  (NC: SN.FrtRestrictionPaintingSelected X HD a Hlen F XA TX PX rpA trRp pshRp
    Q E q Hq (⇓ leR_add_shift Hqp) epsilon u):
  K.ActualExchangeWitness X FC (frtChainUp a) Hlen' frames paintings Hpair
    q Hq Hqp epsilon t omega frtSelectedExchangeCell.
Proof.
  pose (DHI := exchange_section_cell_dep P Cframe phi I PA Bpaint pe
    psection csection ip h).
  pose (DHT := exchange_map_cell_dep r phi G T Epaint Bpaint PA rp pe gp tp
    (projT1_eq J) (projT2_eq J)).
  pose (DHN := @frtSelectedRawCell_dep M XpB0 S0 HD p k dc3 a Hlen F
    XA TX PX rpA trRp pshRp Q E frames paintings view
    q Hq (⇓ leR_add_shift Hqp) epsilon u viewPaint NC).
  now exact (restriction_exchange_paste_dep P Cframe phi r G I T h (projT1_eq J)
    d b n HI HT generatedBExchangeFrame HN PA Bpaint pe
    (f_equal_dep_sigT (Q := PA) P psection h)
    (f_equal_dep_sigT (Q := Bpaint) Cframe csection h)
    (sigT_map_eq (P := Epaint) (Q := Bpaint) (f := r) rp (projT2_eq J))
    (sigT_map_eq (P := Epaint) (Q := PA) (f := G) gp (projT2_eq J))
    hd hb (ip x) (ip y) (tp jsource.1 jsource.2)
    (tp jtarget.1 jtarget.2) hn DHI DHT generatedBExchangeFrame_dep DHN).
Defined.
End GeneratedSelectedComponent.

End GeneratedBExchange.

Section GeneratedExchangeComponents.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
  (F: FrtDeps (X := X) M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps))
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
    (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings))
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (cohsA: mkCohFrameTypes rpA)
  (trCohs: mkTrCohTypes (frtTrBaseOf F XA
    (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) TX rpA
    (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings) trRp cohsA
    (mkDepsCohs dc3.(_depsCohs2)).(_cohs)))
  (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA)).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Let FC := mkFrtDepsCohsGen (cohs3ChainDepsCohs2 a) F XA TX PX rpA trRp pshRp
  cohsA trCohs pshCohs.
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen (frtChainUp a) + p.+1)%nat)
  (frames: FrtFramesNextType (X := X) FC (frtChainUp a))
  (paintings: FrtPaintingsNextType (X := X) FC (frtChainUp a) frames)
  (Hpair: FrtPairLawAt (X := X) F (frtTopNext FC (frtChainUp a)))
  (HPC: forall epsilon u, Hpair epsilon u = frtPairLawAlignU HD a Hlen F epsilon u)
.
Context (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cb)
    (fun v => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) v)).2.2)
    ((mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q))
  (NC: forall q (Hq: q <= k) (Hdim: q + p <= M)
    (epsilon: arity) (u: (g X).(G0) M.+1),
    SN.FrtRestrictionPaintingSelected X HD a Hlen F XA TX PX rpA trRp pshRp
      Q E q Hq Hdim epsilon u)
  (view: FrtOwnedLowerFrameView HD a Hlen F Q frames)
  (viewPaint: FrtOwnedLowerPaintingView HD a Hlen F XA TX PX Q E frames paintings view).

Definition frtSelectedExchangeComponents:
  SelectedExchangeComponents X FC (frtChainUp a) Hlen' frames paintings Hpair.
Proof.
  intros q Hq Hqp epsilon t omega.
  pose (u := (g X).(GFace) M.+1 p
    (leR_add_l q ↕ ↑ (⇓ leR_add_shift Hqp)) omega t).
  pose (H := @frtSelectedExchangeCell_dep M XpB0 S0 HD p k dc3 a F XA TX PX
    rpA trRp pshRp cohsA trCohs pshCohs Hlen Hlen' frames paintings Hpair HPC
    q Hq Hqp epsilon t omega Q E view viewPaint
    (NC q Hq (⇓ leR_add_shift Hqp) epsilon u)).
  now exact (_; H).
Defined.
End GeneratedExchangeComponents.

#[local] Arguments FrtPtChain {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments FrtCanonicalSquare {X} M {XpB0 S0} HD p {k dcB}.
#[local] Arguments frtTopAlignUCons {X M XpB0 S0} HD {p k dc3M}.
#[local] Arguments mkFrtDepsCohsGen {X M XpB0 S0 HD p k dc2}.

Fixpoint frtSelectedExchangeChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dc3M: DepsCohs3 p k}
    (aH: DepsCohs3Chain (νDepsCohs3At S0) dc3M)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps))
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
             (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings))
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (cohsA: mkCohFrameTypes rpA)
    (trCohs: mkTrCohTypes (frtTrBaseOf F XA
               (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX rpA
               (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp cohsA
               (mkDepsCohs dc3M.(_depsCohs2)).(_cohs)))
    (pshCohs: mkPshRestrCohData (g X) (frtPshCohsOf F XA PX rpA pshRp cohsA))
    (Hlen: cohs3ChainLen (descChain HD).2
           = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) + p)%nat)
    (Hlen': cohs3ChainLen (descChain (DescS HD)).2
            = (cohsChainLen (frtChainUp aH) + p.+1)%nat)
    (frames: FrtFramesNextType
               (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp
                  pshRp cohsA trCohs pshCohs)
               (frtChainUp aH))
    (paintings: FrtPaintingsNextType
                  (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp
                     pshRp cohsA trCohs pshCohs)
                  (frtChainUp aH) frames)
    (SD: FrtSplitDataAt M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) F
           (frtTopNext (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA
              trRp pshRp cohsA trCohs pshCohs)
              (frtChainUp aH)) frames)
    (PT: FrtPtChain M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))
           (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
              cohsA trCohs pshCohs)
           (frtChainUp aH) Hlen' frames paintings SD)
    (Hal: forall t, descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) t
          = frtTopNext (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA
              trRp pshRp cohsA trCohs pshCohs)
              (frtChainUp aH) t)
    (HH: forall t, Hal t = frtTopAlignU HD aH t)
    (SC: FrtCanonicalSquare M HD p (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) Hlen F XA
           (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX PX rpA
           (mkDepsCohs dc3M.(_depsCohs2)).(_restrPaintings) trRp pshRp
           (rpZeroChainOf p dc3M.(_depsCohs2).(_extraDepsCohs))
           (frtTopNext (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA
              trRp pshRp cohsA trCohs pshCohs)
              (frtChainUp aH)) Hal
           ((mkCellValuesOf M.+1 (cohsChainExt (frtChainUp aH))
               (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).2)
           frames paintings SD PT)
    (Q: (mkFrtRestrTypesAndFrames M HD p
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX
      (descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)))
      (fun t => (deepCell (cohs3ChainDepsCohs2 aH) (descCell (DescS HD) t)).2.2)
      ((mkFrtRestrTypesAndFrames M HD p
        (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) Hlen F).(FrtRestrFramesDef) Q))
    (NC: SN.FrtRestrictionPaintingSelectedChain X M HD p aH Hlen
      F XA TX PX rpA trRp pshRp Q E)
    (FV: FrtOwnedFrameViewChain M HD p aH Hlen F Q frames)
    (PV: FrtOwnedPaintingViewChain M HD p aH Hlen F XA TX PX Q E frames paintings FV),
  SelectedExchangeChain X M HD p
    (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH))
    (mkFrtDepsCohsGen (cohs3ChainDepsCohs2 aH) F XA TX PX rpA trRp pshRp
      cohsA trCohs pshCohs)
    (frtChainUp aH) Hlen' frames paintings SD.
Proof.
  destruct p as [|p]; intros k dc3M aH F XA TX PX rpA trRp pshRp cohsA trCohs pshCohs
    Hlen Hlen' frames paintings SD PT Hal HH SC Q E NC FV PV.
  - refine (frtSelectedExchangeComponents HD aH F XA TX PX rpA trRp pshRp
      cohsA trCohs pshCohs Hlen Hlen' frames paintings SD.1 _ Q E NC FV PV).
    intros epsilon t.
    unfold frtPairLawAlignU.
    rewrite <- (HH t).
    now exact (SC.1 epsilon t).
  - split.
    + refine (@frtSelectedExchangeChain M XpB0 S0 HD p k.+1
        (proj1DepsCohs3 dc3M) (DepsCohs3ChainCons aH) (proj1FrtDeps F)
        (F.(_frDepsA); XA)%extradepsrestr
        (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
        rpA.1 trRp.1 pshRp.1 cohsA.1 trCohs.1 pshCohs.1
        (Hlen • eq_sym (plus_n_Sm _ p))
        (Hlen' • eq_sym (plus_n_Sm _ p.+1))
        frames.1 paintings.1 SD.1 PT.1
        (fun t => f_equal (fun d => d.1) (Hal t)) _ SC.1 Q.1
        (mkFrtPaintingsOfRestr M HD p.+1
          (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 aH)) Hlen F XA
          (mkDepsCohs dc3M.(_depsCohs2)).(_extraDeps) TX PX
          (fun t => (deepCell (cohs3ChainDepsCohs2 aH) (descCell (DescS HD) t)).2.2)
          Q E).1.2 NC.1 FV.1 PV.1).
      intro t.
      rewrite (frtTopAlignUCons HD aH t).
      now rewrite (HH t).
    + refine (frtSelectedExchangeComponents HD aH F XA TX PX rpA trRp pshRp
        cohsA trCohs pshCohs Hlen Hlen' frames paintings SD.2.1 _ Q E NC.2 FV.2 PV.2).
      intros epsilon t.
      unfold frtPairLawAlignU.
      rewrite <- (HH t).
      now exact (SC.2.1 epsilon t).
Defined.

#[local] Arguments fgRpStepCanonical {X} m s.
#[local] Arguments frtCanonicalSquareOf {X} SP M {XpB0 S0} HD p {k dcB}.

(** The initial component family uses the existing zero certificate
    and the initial Q-owned views. *)
Definition fgInitialExchangeData: FgInitialExchangeComponents X.
Proof.
  let P0 := constr:(((tt; fgThis0): FgPrefix (X := X) 0)) in
  let W0 := constr:(fgTowerAt (X := X) 0 P0) in
  let F0 := constr:(fgDeps (X := X) 0 W0 frt0List frp0List) in
  let FC0 := constr:(towerFrtDepsCohsOf (X := X) 0 W0 frt0List frp0List frtRestr0) in
  let frames := constr:(fgFrtOf (X := X) 0 W0 frt0List frp0List frtRestr0) in
  let paintings := constr:(fgFrpOf (X := X) 0 W0 frt0List frp0List frtRestr0) in
  let split := constr:(fgSplitOf (X := X) 0 P0 frt0List frp0List frtRestr0) in
  refine (@frtSelectedExchangeComponents 0 (νGpdPack 0 X).1 (νGpdPack 0 X).2
    (descAt (X := X) 0) 0 0 (νDepsCohs3At (νGpdPack 0 X).2) DepsCohs3ChainNil
    F0 FC0.(_fcXA) FC0.(_fcTX) FC0.(_fcPX) FC0.(_fcRpA) FC0.(_fcTrRp)
    FC0.(_fcPshRp) FC0.(_fcCohsA) FC0.(_fcTrCohs) FC0.(_fcPshCohs)
    (descChainLen (X := X) (descAt (X := X) 0))
    (descChainLen (X := X) (descAt (X := X) 1)) frames paintings split.1 _ frtRestr0
    (@SN.fgPaintingTopDirect X 0 W0 frt0List frp0List frtRestr0)
    fgInitialRestrictionPaintingSelected
    (fgOwnedFrameViews 0 W0 frt0List frp0List frtRestr0)
    (fgOwnedPaintingViews 0 W0 frt0List frp0List frtRestr0)).
  intros epsilon t.
  now reflexivity.
Defined.

(** The next component family reads the selected C and paired view
    chains generated from the level's existing Q. *)
Definition fgSelectedExchangeData: FgSelectedExchangeData X.
Proof.
  intros m s.
  destruct (fgRpStepCanonical (X := X) m s) as (SP & HA & HT & HP & HRP).
  let N := constr:(m.+1) in
  let P := constr:(fgPrefixNext (X := X) m s) in
  let W := constr:(fgTowerAt (X := X) N P) in
  let ft := constr:(fgFrtNextOf (X := X) m s) in
  let fp := constr:(fgFrpNextOf (X := X) m s) in
  let Q := constr:(fgQNext (X := X) m s) in
  let FC := constr:(towerFrtDepsCohsOf (X := X) N W ft fp Q) in
  now exact (@frtSelectedExchangeChain N (νGpdPack N X).1 (νGpdPack N X).2
    (descAt (X := X) N) N 0 (νDepsCohs3At (νGpdPack N X).2) DepsCohs3ChainNil
    FC.(_fcF) FC.(_fcXA) FC.(_fcTX) FC.(_fcPX)
    FC.(_fcRpA) FC.(_fcTrRp) FC.(_fcPshRp)
    FC.(_fcCohsA) FC.(_fcTrCohs) FC.(_fcPshCohs)
    (descChainLen (X := X) (descAt (X := X) N))
    (descChainLen (X := X) (descAt (X := X) N.+1))
    (fgFrtOf (X := X) N W ft fp Q) (fgFrpOf (X := X) N W ft fp Q)
    (fgSplitOf (X := X) N P ft fp Q)
    (fgPtChain N P ft fp Q
      (fgRpChainOfChains SP N P ft fp Q HA (rpBChainOf N W ft fp Q) HT HP))
    (fun t => eq_refl) (fun t => eq_refl)
    (frtCanonicalSquareOf SP N (descAt (X := X) N) N DepsCohsChainNil
      (descChainLen (X := X) (descAt (X := X) N)) (fgDeps (X := X) N W ft fp)
      _ _ _ _ _ _ _ _ HA (rpBChainOf N W ft fp Q) HT HP _ Q _)
    Q (@SN.fgPaintingTopDirect X N W ft fp Q)
    (@SN.fgRestrictionPaintingSelectedChain X m s)
    (fgOwnedFrameViews N W ft fp Q) (fgOwnedPaintingViews N W ft fp Q)).
Defined.

Definition fg: νGpdsEquiv (f (g X)) X :=
  Core.fgOfData X (fgInitialDataOfComponents X fgInitialExchangeData)
    (fgStepDataOfComponents X fgSelectedExchangeData).

End FG.
End Positive.
