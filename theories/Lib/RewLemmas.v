(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation.

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
Qed.

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
Qed.

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
Qed.

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

(** Fused transport-chain lemmas for layer coherence proofs

    [rew_cohLayer_hex] equates two chains of three transport steps, whose
    starting elements are identified by the painting coherence. The three
    square variants [rew_cohLayer_sq_13], [rew_cohLayer_sq_31], and
    [rew_cohLayer_sq_22] split the four transport steps between the two
    sides as 1 = 3, 3 = 1, and 2 = 2, respectively.
    A call site supplies only the two premises: the painting coherence and
    the 2-dimensional frame coherence ([UIP] in the HSet development). *)

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
  rew [P] K in F m1 aL = G n1 aR -> (* painting coherence *)
  f_equal rfF C2 • (C1 • f_equal rf0 E1) = K • (f_equal rfG D2 • D1) ->
  (* 2-dimensional frame coherence, UIP for HSets *)
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  refine (rew_map P rf0 E1 _ • _).
  now exact (sigT_square_fill (eq_sym (eq_trans_assoc _ _ _) • Hpath)
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
  refine (rew_map P rf0 E1 _ • _).
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
  refine (rew_map P rf0 E1 _ • _).
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
  f_equal rfF C2 • (C1 • f_equal rf0 E1) = D1 ->
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in aR.
Proof.
  intros HC Hpath.
  refine (rew_map P rf0 E1 _ • _).
  now exact (sigT_square_fill
    (eq_sym (eq_trans_assoc _ _ _) • (Hpath • eq_sym (eq_trans_refl_l _)))
    (sigT_map_eq (Q := P) F (p := C2) (u := aL) eq_refl ⊙ eq_refl) HC eq_refl).
Defined.

(** Path composition and naturality of homotopies. *)

Polymorphic Definition eqTransAssoc {T: Type} {x y z t: T} (p: x = y) (q: y = z) (r: z = t):
  (p • q) • r = p • (q • r) := eq_sym (eq_trans_assoc p q r).

Polymorphic Lemma homotopyNat {X Y: Type} (u v: X -> Y) (H: forall z, u z = v z)
  {z1 z2: X} (p: z1 = z2): f_equal u p • H z2 = H z1 • f_equal v p.
Proof. destruct p. now exact (eq_trans_refl_l (H z1)). Defined.

(** The image of an inverse path, oriented for rewriting under [f_equal]. *)
Polymorphic Definition fEqualSym {X Y: Type} (h: X -> Y) {x y: X} (p: x = y):
  f_equal h (eq_sym p) = eq_sym (f_equal h p) :=
  eq_sym (eq_sym_map_distr h p).

Polymorphic Lemma fEqualConst {A B: Type} (b: B) {x y: A} (e: x = y):
  f_equal (fun _ => b) e = eq_refl.
Proof.
  now destruct e.
Qed.

Polymorphic Lemma symTransCancel {Z: Type} {x y: Z} (a b: x = y)
  (H: eq_sym a • (eq_refl • b) = eq_refl): a = b.
Proof.
  destruct b; simpl in H.
  now exact (eq_sym (eq_sym_involutive a) • f_equal (@eq_sym _ _ _) H).
Defined.

Polymorphic Lemma transCancelL {T: Type} {x y z: T} (p: x = y) (q r: y = z)
  (H: p • q = p • r): q = r.
Proof.
  destruct p. now exact (eq_sym (eq_trans_refl_l q) • (H • eq_trans_refl_l r)).
Defined.

Polymorphic Lemma transCongL {T: Type} {x y z: T} (p: x = y) {q r: y = z} (H: q = r):
  p • q = p • r.
Proof. now destruct H. Defined.

Polymorphic Lemma transCongR {T: Type} {x y z: T} {p p': x = y} (H: p = p') (q: y = z):
  p • q = p' • q.
Proof. now destruct H. Defined.

Polymorphic Lemma transSymCancelR {T: Type} {x y z: T} (p: x = y) (q: y = z):
  (p • q) • eq_sym q = p.
Proof. now destruct q. Defined.

Polymorphic Lemma transCancelMid {T: Type} {x y z t: T} (p: x = y) (q: y = z) (r: y = t):
  (p • q) • (eq_sym q • r) = p • r.
Proof. now destruct q, r. Defined.

Polymorphic Lemma transCancelMid2 {T: Type} {x y z t: T} (p: x = y) (q: z = y) (r: y = t):
  (p • eq_sym q) • (q • r) = p • r.
Proof. now destruct q, r. Defined.

Polymorphic Lemma transCancelR {T: Type} {x y z: T} (p q: x = y) (s: y = z)
  (H: p • s = q • s): p = q.
Proof. now destruct s. Defined.

Polymorphic Lemma transSymCancelR2 {T: Type} {x y z: T} (p: x = y) (q: z = y):
  (p • eq_sym q) • q = p.
Proof. now destruct q. Defined.

Polymorphic Lemma transSymCancelL {T: Type} {x y z: T} (p: x = y) (q: x = z):
  p • (eq_sym p • q) = q.
Proof. now destruct p, q. Defined.

Polymorphic Lemma eqIndRPath {W T: Type} (ψ: W -> T) {w w': W} (e: w = w') {t: T}
  (body: ψ w' = t):
  eq_ind_r (fun z => ψ z = t) body e = f_equal ψ e • body.
Proof. destruct e. now exact (eq_sym (eq_trans_refl_l body)). Defined.

Polymorphic Lemma fEqualCompEq {W1 W2 T: Type} (ϕ: W1 -> W2) (ψ: W2 -> T) {w w': W1}
  (e: w = w') {t0: T} (Θ: t0 = ψ (ϕ w)) (R: t0 = ψ (ϕ w'))
  (H: Θ • f_equal (fun z => ψ (ϕ z)) e = R):
  Θ • f_equal ψ (f_equal ϕ e) = R.
Proof. now rewrite f_equal_compose. Defined.


Polymorphic Lemma symCancelF {X Y: Type} (F: X -> Y) {u v: X} (ι: u = v) {w: Y}
  (Θ: F u = w) (τ: w = F v) (IH: Θ • τ = f_equal F ι):
  (f_equal F (eq_sym ι) • Θ) • τ = eq_refl.
Proof.
  destruct ι. now exact (f_equal (fun z => z • τ) (eq_trans_refl_l Θ) • IH).
Defined.

Polymorphic Lemma assoc5S {T: Type} {y0 y1 y2 y3 y4 y5: T} (a: y0 = y1) (b: y1 = y2)
  (c: y2 = y3) (d1: y4 = y3) (d2: y5 = y4):
  a • ((b • (c • eq_sym d1)) • eq_sym d2) = (a • b) • (c • eq_sym (d2 • d1)).
Proof. now destruct d1, d2, c, b, a. Defined.

Polymorphic Lemma prependEq {T: Type} {x0 x1 x2 x2' x3: T} (a: x0 = x1) (u1: x1 = x2)
  (u2: x2 = x3) (v1: x1 = x2') (v2: x2' = x3) (H: u1 • u2 = v1 • v2):
  (a • u1) • u2 = (a • v1) • v2.
Proof.
  now exact (eqTransAssoc a u1 u2
    • (f_equal (fun z => a • z) H • eq_sym (eqTransAssoc a v1 v2))).
Defined.

Polymorphic Lemma alphaTrans {S1 S2: Type} (Fv SF: S1 -> S2) (hv: forall z, Fv z = SF z)
  {y Y z2: S1} (p: y = Y) (g2: Y = z2):
  hv y • (f_equal SF p • f_equal SF g2)
  = f_equal Fv p • (hv Y • f_equal SF g2).
Proof. destruct g2, p. now exact (eq_sym (eq_trans_refl_l (hv y))). Defined.

Polymorphic Lemma fEqualSkipSplit {W1 W2 T: Type} (ϕ: W1 -> W2) (ψ: W2 -> T) {w1 w2 w3: W1}
  (p: w1 = w2) (q: w3 = w2):
  f_equal ψ (f_equal ϕ (p • eq_sym q))
  = f_equal (fun z => ψ (ϕ z)) p • eq_sym (f_equal (fun z => ψ (ϕ z)) q).
Proof. now destruct q, p. Defined.

Polymorphic Lemma movePath {T: Type} {x y z: T} (u: x = y) (c: z = y) (P: x = z)
  (H: P = u • eq_sym c): P • c = u.
Proof. now destruct c. Defined.

Polymorphic Lemma conjTrans3 {T: Type} {y1 y2 y3 y4: T} (e1: y1 = y2) (e2: y2 = y3)
  (e3: y3 = y4) {x1 x2 x3 x4: T} (t1: x1 = y1) (t2: x2 = y2) (t3: x3 = y3)
  (t4: x4 = y4):
  (t1 • (e1 • eq_sym t2))
  • ((t2 • (e2 • eq_sym t3)) • (t3 • (e3 • eq_sym t4)))
  = t1 • ((e1 • (e2 • e3)) • eq_sym t4).
Proof. now destruct e1, e2, e3, t1, t2, t3, t4. Defined.

Polymorphic Lemma conjCancel {T: Type} {x1 x4 y1 y4: T} (t1: x1 = y1) (t4: x4 = y4)
  (M M': y1 = y4) (H: M = M'):
  t1 • (M • eq_sym t4) = t1 • (M' • eq_sym t4).
Proof. now destruct H. Defined.

Polymorphic Lemma fEqualUIP {W T: Type}
  (uip: forall (x y: W) (h g: x = y), h = g) (ϕ: W -> T)
  {g1 g2 g3 g4 g2' g3': W}
  (e1: g1 = g2) (e2: g2 = g3) (e3: g3 = g4)
  (e1': g1 = g2') (e2': g2' = g3') (e3': g3' = g4):
  f_equal ϕ e1 • (f_equal ϕ e2 • f_equal ϕ e3)
  = f_equal ϕ e1' • (f_equal ϕ e2' • f_equal ϕ e3').
Proof.
  rewrite <- !eq_trans_map_distr.
  now rewrite (uip _ _ (e1 • (e2 • e3)) (e1' • (e2' • e3'))).
Defined.

Polymorphic Lemma hexRotate {X: Type} {w0 w1 w2 w3 v1 v2: X}
  (P1: w0 = w1) (P2: w1 = w2) (P3: w2 = w3)
  (Q1: w0 = v1) (Q2: v1 = v2) (Q3: v2 = w3)
  (h: P1 • (P2 • P3) = Q1 • (Q2 • Q3)):
  Q2 • (Q3 • (eq_sym P3 • (eq_sym P2 • eq_sym P1))) = eq_sym Q1.
Proof.
  destruct P1, P2, P3, Q1. simpl in h |- *.
  rewrite eq_trans_refl_l in h. now exact (eq_sym h).
Defined.

Polymorphic Lemma tailSubst {X: Type} {a b c d: X} (P: a = d) (Q1: a = b) (Q2: b = c)
  (R1 R2: c = d) (e: R1 = R2) (ih: P = Q1 • (Q2 • R1)): P = Q1 • (Q2 • R2).
Proof. now destruct e. Defined.
