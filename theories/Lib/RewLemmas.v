(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation Lib.Coh2Shapes.

(** Apply a binary function to paths in its two arguments. *)
Definition path_map2 {A B C: Type} (f: A -> B -> C)
  {x x': A} {y y': B} (p: x = x') (q: y = y'):
  f x y = f x' y' :=
  f_equal (fun a => f a y) p • f_equal (f x') q.

(** Apply a dependent binary map to two lifted paths. *)
Lemma path_map2_dep {A B C: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type}
  (f: A -> B -> C) (F: forall ax dy, PA ax -> PB dy -> PC (f ax dy))
  {ax ax': A} {dy dy': B} (p: ax = ax') (q: dy = dy')
  {a: PA ax} {a': PA ax'} {b: PB dy} {b': PB dy'}
  (hp: rew [PA] p in a = a') (hq: rew [PB] q in b = b'):
  rew [PC] path_map2 f p q in F ax dy a b = F ax' dy' a' b'.
Proof. now destruct p, q, hp, hq. Defined.

(** Transport along a pointwise equality commutes with transport in the
    indexing type, for any family [El] over the common codomain. *)
Lemma rew_permute_ll {S: Type} (El: S -> Type)
  (A: Type) (P Q: A -> S) (x y: A)
  (H: forall z: A, P z = Q z) (H': x = y) (a: El (P x)):
  rew [El] H y in rew [fun z => El (P z)] H' in a =
  rew [fun z => El (Q z)] H' in rew [El] H x in a.
Proof.
  now destruct H'.
Defined.

(** Transport along [p • (h • eq_sym q)] is equivalent to transporting
    both endpoints along [p] and [q] before comparing them over [h]. *)
Lemma rew_conjugate {A: Type} (P: A -> Type)
  {x x' y y': A} (p: x = x') (h: x' = y') (q: y = y')
  (u: P x) (v: P y):
  rew [P] (p • (h • eq_sym q)) in u = v ->
  rew [P] h in rew [P] p in u = rew [P] q in v.
Proof.
  intro H; rewrite <- 2 rew_compose in H.
  refine (eq_sym (rew_opp_r P q _) • _).
  now exact (f_equal (fun v => rew [P] q in v) H).
Defined.

Lemma rew_swap: forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  now destruct H.
Defined.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x):
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Defined.

Lemma map_subst_app {A B} {x y} {θ: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall θ, P θ x):
  rew [P θ] H in f θ = (rew [fun x => forall θ, P θ x] H in f) θ.
Proof.
  now destruct H.
Defined.

Lemma f_equal_id {A} {x y: A} (e: x = y): f_equal (fun x => x) e = e.
Proof.
  now destruct e.
Defined.

Lemma eq_trans_sym_cancel_l {A: Type} {x y z: A} (e: x = y) (h: y = z):
  eq_sym e • (e • h) = h.
Proof.
  now destruct e, h.
Defined.

Lemma eq_trans_shift_l {A} {x y z: A} (p: x = y) (q: y = z) (r: x = z):
  p • q = r -> q = eq_sym p • r.
Proof.
  destruct p, q. intro H. now destruct H.
Defined.

(** Cancelling a common prefix under an inversion *)
Lemma eq_trans_sym_cancel_common {A: Type} {x y z w: A} (a: x = y) (o: y = z)
  (p: y = w):
  eq_sym (a • o) • (a • p) = eq_sym o • p.
Proof.
  now destruct a, o, p.
Qed.

(** Conjugating by a composite is conjugating twice: writing [c u v r] for
    [eq_sym u • (r • v)], this states [c aA aB P • sB = sA • c (aA • sA)
    (aB • sB) P], the form in which the two halves are met. *)
Lemma eq_trans_conj_comp {A: Type} {x0 x1 x2 y0 y1 y2: A}
  (aA: x0 = x1) (sA: x1 = x2) (P: x0 = y0) (aB: y0 = y1) (sB: y1 = y2):
  (eq_sym aA • (P • aB)) • sB = sA • (eq_sym (aA • sA) • (P • (aB • sB))).
Proof.
  now destruct aA, sA, P, aB, sB.
Qed.

Lemma eq_trans_nat_id {A} {f: A -> A} (α: forall a, f a = a) {x y: A}
  (p: x = y): α x • p = f_equal f p • α y.
Proof.
  destruct p. symmetry. apply eq_trans_refl_l.
Defined.

Lemma rew_align {A: Type} {P: A -> Type} {x x' y: A}
  {e: x = y} {e': x' = y} (b: x = x') {v: P x} {v': P x'}
  (Hv: rew [P] b in v = v') (Hcoh: e = b • e'):
  rew [P] e in v = rew [P] e' in v'.
Proof.
  destruct Hv, b. now rewrite Hcoh, eq_trans_refl_l.
Qed.

Lemma rew_sym_cancel {A: Type} {P: A -> Type} {x y: A} (e: x = y) (a: P x):
  rew [P] (eq_sym e) in rew [P] e in a = a.
Proof.
  now destruct e.
Qed.

Lemma rew_sym_cancel_r {A: Type} {P: A -> Type} {x y: A} (e: x = y)
  (b: P y): rew [P] e in rew [P] (eq_sym e) in b = b.
Proof.
  now destruct e.
Qed.

Lemma eq_sym_f_equal {A B: Type} (f: A -> B) {x y: A} (e: x = y):
  eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
  now destruct e.
Defined.

(** Transport in a family of path types between two maps: the
    transported path is the conjugate by the images of the base path. *)
Lemma rew_between {T U: Type} (f g: T -> U) {x y: T} (e: x = y)
  (q: f x = g x):
  rew [fun a => f a = g a] e in q =
  eq_sym (f_equal f e) • (q • f_equal g e).
Proof.
  destruct e; cbn. now rewrite eq_trans_refl_l.
Qed.

(** The case of [rew_between] where the right map is constant, so only the
    left image contributes. *)
Lemma rew_between_const_r {T U: Type} (f: T -> U) {x y: T} (e: x = y) {u: U}
  (q: f x = u):
  rew [fun a => f a = u] e in q = eq_sym (f_equal f e) • q.
Proof.
  destruct e; cbn. now rewrite eq_trans_refl_l.
Qed.

Local Lemma retract_adjoint {A B: Type} (F: A -> B) (G: B -> A)
  (R: forall a, G (F a) = a) (S: forall b, F (G b) = b) (a: A):
  f_equal F (R a) =
    eq_sym (S (F (G (F a)))) • (f_equal F (R (G (F a))) • S (F a)).
Proof.
  apply eq_trans_shift_l.
  rewrite (eq_trans_nat_id S (f_equal F (R a))), f_equal_compose.
  rewrite <- (eq_id_comm_r (fun a => G (F a)) R a).
  now exact (f_equal (fun p => p • S (F a))
    (eq_sym (f_equal_compose (fun a => G (F a)) F (R a)))).
Defined.

Lemma ap_retract_recovery {A B: Type} (F: A -> B) (G: B -> A)
  (R: forall a, G (F a) = a) (S: forall b, F (G b) = b)
  {a b: A} (H: F a = F b):
  f_equal F (eq_sym (R a) • (f_equal G H • R b)) = H.
Proof.
  pose (T := fun b => eq_sym (S (F (G b))) • (f_equal F (R (G b)) • S b)).
  assert (adj: forall a, f_equal F (R a) = T (F a)).
  { intro x. now exact (retract_adjoint F G R S x). }
  rewrite 2 eq_trans_map_distr, <- eq_sym_f_equal, 2 adj.
  rewrite f_equal_compose.
  pose proof (eq_trans_nat_id (f := fun b => F (G b)) T H) as N.
  change (T (F a) • H = f_equal (fun b => F (G b)) H • T (F b)) in N.
  rewrite <- N.
  now apply eq_trans_sym_cancel_l.
Defined.

(** Both round trips of a fiber map lift to dependent path comparisons. *)
Lemma path_retraction_recovery {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} {F: forall x, P x -> Q (f x)}
  (r: fiber_retraction F) (S: fiber_recovery r)
  {x y: X} (a: P x) (b: P y):
  fiber_recovery (path_retraction r a b).
Proof.
  intros p H. destruct p.
  change (sigT_map_eq (f := f) (Q := Q) F (p := eq_refl)
    (eq_sym (fiber_section r x a) •
      (f_equal (fiber_back r x) H • fiber_section r x b)) = H).
  rewrite sigT_map_eq_refl.
  now exact (ap_retract_recovery (F x) (fiber_back r x) (fiber_section r x) (S x) H).
Defined.

Lemma pullback_path_retraction_recovery {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x y: Y} (a: P (f x)) (b: P (f y)):
  fiber_recovery (pullback_path_retraction f P a b).
Proof.
  intros e h. cbn [pullback_path_retraction fiber_back].
  rewrite sigT_map_eq_id.
  now apply eq_trans_sym_cancel_l.
Defined.

Lemma prefix_retraction_recovery {X: Type} (P: X -> Type)
  {x0 x1 x2: X} (p: x0 = x1) {a: P x0} {b: P x1} (hp: rew [P] p in a = b)
  (c: P x2): fiber_recovery (prefix_retraction P p hp c).
Proof. intros e h. now exact (sigT_trans_eq_inv_l_cancel hp h). Defined.

Lemma suffix_retraction_recovery {X: Type} (P: X -> Type)
  {x0 x1 x2: X} (q: x1 = x2) {b: P x1} {c: P x2}
  (hq: rew [P] q in b = c) (a: P x0):
  fiber_recovery (suffix_retraction P q hq a).
Proof. intros e h. now exact (sigT_trans_eq_inv_r_cancel hq h). Defined.

Lemma pullback_comparison_retract {X Y: Type} (f: Y -> X) (P: X -> Type)
  {y0 y1: Y} {a: P (f y0)} {b: P (f y1)}
  {p q: y0 = y1}
  {h: rew [fun y => P (f y)] p in a = b}
  {k: rew [fun y => P (f y)] q in a = b}
  (C: p = q)
  (E: rew [fun e => rew [P] e in a = b]
    f_equal (fun e => f_equal f e) C in
    sigT_map_eq (f := f) (Q := P) (fun _ u => u) h =
    sigT_map_eq (f := f) (Q := P) (fun _ u => u) k):
  rew [fun e => rew [fun y => P (f y)] e in a = b] C in h = k.
Proof.
  now exact (fiber_back
    (path_retraction (pullback_path_retraction f P a b) h k) C E).
Defined.

Lemma pullback_comparison_recovery {X Y: Type} (f: Y -> X) (P: X -> Type)
  {y0 y1: Y} (a: P (f y0)) (b: P (f y1))
  {p q: y0 = y1}
  (h: rew [fun y => P (f y)] p in a = b)
  (k: rew [fun y => P (f y)] q in a = b):
  fiber_recovery (path_retraction (pullback_path_retraction f P a b) h k).
Proof.
  now exact (path_retraction_recovery _
    (pullback_path_retraction_recovery f P a b) h k).
Defined.

(** Fused transport-chain lemmas

    [rew_cohLayer_hex] equates two chains of three transport steps from
    identified starting elements. The square variants
    [rew_cohLayer_sq_13], [rew_cohLayer_sq_31], and [rew_cohLayer_sq_22]
    split four transport steps as 1 = 3, 3 = 1, and 2 = 2.
    Each lemma assumes an equality between the transported elements and
    a coherence between the corresponding paths in the base. *)

Lemma rew_cohLayer_hex {T1 T2 T3 X: Type} {P: X -> Type}
  {S2: T2 -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfF: T2 -> X} {rfG: T3 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2: m1 = m2}
  {n1 n2: T3} {D2: n1 = n2}
  {C1: rfF m2 = rf0 d1}
  {D1: rfG n2 = rf0 d2}
  {K: rfF m1 = rfG n1}
  {aL: S2 m1} {aR: S3 n1}:
  rew [P] K in F m1 aL = G n1 aR -> (* Equality of the transported elements. *)
  hexagonal_coherence rfF rf0 rfG C2 E1 D2 C1 K D1 ->
  (* Coherence of the base paths. *)
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  refine (fiber_back (pullback_path_retraction rf0 P _ _) E1 _).
  now exact (sigT_square_fill Hpath
    (sigT_map_eq (Q := P) F (p := C2) (u := aL) eq_refl ⊙ eq_refl)
    HC (sigT_map_eq (Q := P) G (p := D2) (u := aR) eq_refl ⊙ eq_refl)).
Defined.

(** The [rew_cohLayer*] lemmas for square-shaped coherences can be considered an
    instance of the hexagon-shaped one, with 2 arrows trivial. *)

Lemma rew_cohLayer_sq_13 {T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfG: T3 -> X}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {n1 n2: T3} {D2: n1 = n2}
  {D1: rfG n2 = rf0 d2}
  {K: rf0 d1 = rfG n1}
  {aL: P (rf0 d1)} {aR: S3 n1}:
  rew [P] K in aL = G n1 aR ->
  f_equal rf0 E1 = K • (f_equal rfG D2 • D1) ->
  rew [fun d => P (rf0 d)] E1 in aL
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  refine (fiber_back (pullback_path_retraction rf0 P _ _) E1 _).
  now exact (sigT_square_fill (eq_trans_refl_l _ • Hpath) eq_refl
    HC (sigT_map_eq (Q := P) G (p := D2) (u := aR) eq_refl ⊙ eq_refl)).
Defined.

Lemma rew_cohLayer_sq_22 {T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfG: T3 -> X}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {n1 n2: T3} {D2: n1 = n2}
  {E0: rfG n1 = rf0 d1}
  {D1: rfG n2 = rf0 d2}
  {aL: P (rfG n1)} {aR: S3 n1}:
  aL = G n1 aR ->
  E0 • f_equal rf0 E1 = f_equal rfG D2 • D1 ->
  rew [fun d => P (rf0 d)] E1 in rew [P] E0 in aL
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  refine (fiber_back (pullback_path_retraction rf0 P _ _) E1 _).
  now exact (sigT_square_fill (Hpath • eq_sym (eq_trans_refl_l _)) eq_refl
    HC (sigT_map_eq (Q := P) G (p := D2) (u := aR) eq_refl ⊙ eq_refl)).
Defined.

Lemma rew_cohLayer_sq_31 {T1 T2 X: Type} {P: X -> Type} {S2: T2 -> Type}
  {rf0: T1 -> X} {rfF: T2 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2: m1 = m2}
  {C1: rfF m2 = rf0 d1}
  {D1: rfF m1 = rf0 d2}
  {aL: S2 m1} {aR: P (rfF m1)}:
  F m1 aL = aR ->
  (f_equal rfF C2 • C1) • f_equal rf0 E1 = D1 ->
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in aR.
Proof.
  intros HC Hpath.
  refine (fiber_back (pullback_path_retraction rf0 P _ _) E1 _).
  now exact (sigT_square_fill (Hpath • eq_sym (eq_trans_refl_l _))
    (sigT_map_eq (Q := P) F (p := C2) (u := aL) eq_refl ⊙ eq_refl) HC eq_refl).
Defined.

(** Normalize paths through a map homotopic to the identity. *)
Local Lemma rew_path_source_cancel {A: Type} {x y t: A} (r: x = y) (h: x = t):
  r • (rew [fun e => e = t] r in h) = h.
Proof. destruct r, h. now reflexivity. Defined.

Lemma homotopy_path_normalize {A: Type} (F: A -> A) (R: forall a, F a = a)
  {x t: A} (H: F x = t):
  f_equal F (rew [fun e => e = t] R x in H) • R t = H.
Proof.
  pose (h := rew [fun e => e = t] R x in H).
  assert (N: f_equal F h • R t = R x • h).
  { destruct h. cbn. now exact (eq_trans_refl_l (R x)). }
  now exact (N • rew_path_source_cancel (R x) H).
Defined.

Local Lemma rew_equality_source {A B: Type} (f: A -> B)
  {x y: A} {z: B} (p: x = y) (q: f x = z) (r: f y = z)
  (H: f_equal f p • r = q):
  rew [fun w => f w = z] p in q = r.
Proof.
  destruct p. cbn in H |- *.
  now exact (eq_sym H • eq_trans_refl_l r).
Defined.

Definition homotopy_path_ind {A: Type} (F: A -> A) (R: forall x, F x = x)
  {t: A} (P: forall x, F x = t -> Type) (u: P t (R t))
  (x: A) (q: F x = t): P x q.
Proof.
  pose (n := rew [fun e => e = t] R x in q).
  pose (N := homotopy_path_normalize F R q).
  pose (E := rew_equality_source F n q (R t) N).
  now exact (@eq_rect {x: A &T F x = t} (t; R t)
    (fun z => P z.1 z.2) u (x; q)
    (eq_sym (@eq_existT_curried A (fun x => F x = t) x t q (R t) n E))).
Defined.

Definition homotopy_path_ind_r {A: Type} (F: A -> A) (R: forall x, F x = x)
  {t: A} (P: forall x, t = F x -> Type) (u: P t (eq_sym (R t)))
  (x: A) (q: t = F x): P x q :=
  rew [fun s => P x s] eq_sym_involutive q in
    homotopy_path_ind F R (fun x s => P x (eq_sym s)) u x (eq_sym q).

(** Actions on several paths and composition of endpoint changes. *)

Definition path_map3 {A B C D: Type}(f: A -> B -> C -> D)
  {a a': A} {b b': B} {c c': C}(p: a = a') (q: b = b') (r: c = c'):
  f a b c = f a' b' c' := path_map2 (fun x y => f x y c) p q • f_equal (f a' b') r.

Lemma rew_conjugate_compose {X:Type}(P:X->Type)
  {x y:X}(H:x=y){a0 a1 a2:P x}{b0 b1 b2:P y}
  (L1:a0=a1)(L2:a1=a2)(R1:b0=b1)(R2:b1=b2)
  (M:rew[P]H in a2=b2):
  f_equal(fun z=>rew[P]H in z)L1 •
    ((f_equal(fun z=>rew[P]H in z)L2 •(M •eq_sym R2)) •eq_sym R1) =
  f_equal(fun z=>rew[P]H in z)(L1 •L2) •(M •eq_sym(R1 •R2)).
Proof.
  destruct L1,L2,R1,R2. cbn [f_equal eq_sym].
  now rewrite 3 eq_trans_refl_l.
Defined.

Lemma path_left_correction_compose {A B:Type}(F:A->B)
  {a0 a1 a2:A}{b0 b1:B}(L:a0=a1)(M:a1=a2)(N:F a2=b0)(R:b0=b1):
  f_equal F L • ((f_equal F M • N) • R)=f_equal F(L • M) • (N • R).
Proof. now destruct L,M,R,N. Defined.

Lemma path_map2_compose_r_prefix {A B C: Type} (f: A -> B -> C)
  {a a': A} {b b' b'': B} {c: C}
  (p: a = a') (q: b = b') (r: b' = b'') (s: f a' b'' = c):
  path_map2 f p q • (f_equal (f a') r • s) =
  path_map2 f p (q • r) • s.
Proof. now destruct p, q, r, s. Defined.

Lemma path_map_compose_prefix {A B C: Type} (f: A -> B) (g: B -> C)
  {a a': A} {b: B} {c: C} (p: a = a') (q: f a' = b) (r: g b = c):
  f_equal (fun x => g (f x)) p • (f_equal g q • r) =
  f_equal g (f_equal f p • q) • r.
Proof. now destruct p, q, r. Defined.
