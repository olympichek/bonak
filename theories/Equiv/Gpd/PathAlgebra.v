(** Path composition, dependent-pair paths, and transport identities. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet Notation νGpd.HGpd νGpd.Lemmas νGpd.Pasting.
From Bonak.Lib Require Import Equiv.
Import Logic.EqNotations.

From Bonak.Lib Require Import NatLemmas.

Set Primitive Projections.
Set Keyed Unification.

(** Naturality of a path-valued comparison. *)
Lemma eq_trans_natural {A B: Type} (f g: A -> B)
  (α: forall x, f x = g x) {x y: A} (e: x = y):
  f_equal f e • α y = α x • f_equal g e.
Proof.
  pose proof (f_equal_naturality (fun x => x) (fun x => x) f g α e) as H.
  now rewrite f_equal_id in H.
Defined.







Definition f_equal_dep_sigT {A B: Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, Q (f a)) {x y: A} (e: x = y):
  rew [Q] f_equal f e in g x = g y.
Proof.
  now destruct e.
Defined.

(** The dependent action of a section obtained by applying a fibre map
    is the mapped dependent action of the argument section. *)
Lemma f_equal_dep_sigT_apply {A B C: Type}
  {P: B -> Type} {Q: C -> Type}
  (u: A -> B) (f: A -> C)
  (g: forall a, P (u a) -> Q (f a))
  (s: forall a, P (u a)) {x y: A} (e: x = y):
  f_equal_dep_sigT f (fun a => g a (s a)) e =
  sigT_map_eq g (f_equal_dep (fun a => P (u a)) s e).
Proof.
  now destruct e.
Defined.

(** Changing a dependent section conjugates its action on paths by
    the pointwise comparison. *)
Lemma f_equal_dep_sigT_change_section {A B: Type} {Q: B -> Type}
  (f: A -> B) (g h: forall a, Q (f a))
  (alpha: forall a, g a = h a) {x y: A} (e: x = y):
  f_equal_dep_sigT f g e =
  f_equal (fun z => rew [Q] f_equal f e in z) (alpha x)
  • (f_equal_dep_sigT f h e • eq_sym (alpha y)).
Proof.
  rewrite (f_equal_dep_sigT_apply (P := fun _: A => unit)
    (fun a => a) f (fun a (_: unit) => g a) (fun _ => tt) e),
    (f_equal_dep_sigT_apply (P := fun _: A => unit)
      (fun a => a) f (fun a (_: unit) => h a) (fun _ => tt) e).
  now exact (sigT_map_eq_homotopy (fun a (_: unit) => g a)
    (fun a (_: unit) => h a) (fun a _ => alpha a)
    (f_equal_dep (fun _: A => unit) (fun _ => tt) e)).
Defined.

(** Left unit for dependent composition over an arbitrary base path. *)

Lemma sigT_trans_eq_refl_l {A: Type} {P: A -> Type} {x y: A}
  {u: P x} {v: P y} (p: x = y) (h: rew [P] p in u = v):
  (eq_refl: rew [P] eq_refl in u = u) ⊙[P] h
  = rew [fun e => rew [P] e in u = v] (eq_sym (eq_trans_refl_l p)) in h.
Proof.
  destruct p, h. now reflexivity.
Defined.

(** The transport-composition law for an identity prefix is the action
    of the corresponding left-unit path. *)
Lemma rew_unit_base {A: Type} (P: A -> Type) {x y: A} (p: x = y) (u: P x):
  rew_compose P eq_refl p u =
  f_equal (fun q => rew [P] q in u) (eq_sym (eq_trans_refl_l p)).
Proof.
  now destruct p.
Defined.

Lemma rewBaseAsTrans {A: Type} {P: A -> Type} {x y: A} {u: P x} {Z: P y}
  {pL pR: x = y} (h: pL = pR) (Y: rew [P] pL in u = Z):
  rew [fun pia: x = y => rew [P] pia in u = Z] h in Y
  = f_equal (fun pia: x = y => rew [P] pia in u) (eq_sym h) • Y.
Proof.
  rewrite (path_reindex_left (fun pia => rew [P] pia in u) h Y).
  now rewrite eq_sym_map_distr.
Qed.

(** Changing a dependent pair of arguments transports the value of a
    dependent function along the corresponding base path. *)

Lemma dep_arg_irr {A: Type} {B C: A -> Type}
  (f: forall a, B a -> C a) {a a': A} (Hb: a = a')
  (x: B a) (x': B a') (Hx: rew [B] Hb in x = x'):
  rew [C] Hb in f a x = f a' x'.
Proof.
  now exact (map_subst f Hb x • f_equal (f a') Hx).
Defined.

Lemma f_equal_sigT_dep {A B: Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, Q (f a)) {x y: A} (e: x = y):
  f_equal (fun a => (f a; g a)) e =
  (= f_equal f e; f_equal_dep_sigT f g e).
Proof.
  now destruct e.
Defined.

Lemma f_equal_sigma_decompose {A B: Type} {Q: B -> Type}
  (F: A -> {b: B &T Q b}) {x y: A} (e: x = y):
  f_equal F e =
  (= f_equal (fun a => (F a).1) e;
     f_equal_dep_sigT (fun a => (F a).1) (fun a => (F a).2) e).
Proof.
  change
    (f_equal (fun a => ((F a).1; (F a).2)) e =
     (= f_equal (fun a => (F a).1) e;
        f_equal_dep_sigT (fun a => (F a).1) (fun a => (F a).2) e)).
  now exact (f_equal_sigT_dep (fun a => (F a).1) (fun a => (F a).2) e).
Defined.

Definition sigT_trans3 {A: Type} {P: A -> Type}
  {x0 x1 x2 x3: A} {u0: P x0} {u1: P x1} {u2: P x2} {u3: P x3}
  (p1: x0 = x1) (q1: rew [P] p1 in u0 = u1)
  (p2: x1 = x2) (q2: rew [P] p2 in u1 = u2)
  (p3: x2 = x3) (q3: rew [P] p3 in u2 = u3):
  rew [P] (p1 • (p2 • p3)) in u0 = u3 :=
  @sigT_trans_eq A P x0 x1 x3 u0 u1 u3 p1 q1 (p2 • p3)
    (@sigT_trans_eq A P x1 x2 x3 u1 u2 u3 p2 q2 p3 q3).

(** A dependent-pair hexagon with one mapped edge and two explicit
    pair edges. The explicit edges retain their fibre components as
    [sigT_map_eq] terms over the base paths. *)
Lemma sigT_hex1 {A1 B: Type} {Q: B -> Type}
  (f1: A1 -> B) (g1: forall a, Q (f1 a))
  {x1 y1: A1} (K1: x1 = y1)
  {b2 b3 b4 b5: B} {c2: Q b2} {c3: Q b3} {c4: Q b4} {c5: Q b5}
  (H2: f1 y1 = b2) (U2: rew [Q] H2 in g1 y1 = c2)
  (B3: b2 = b3) (V3: rew [Q] B3 in c2 = c3)
  (H1': f1 x1 = b4) (U1': rew [Q] H1' in g1 x1 = c4)
  (B2: b4 = b5) (V2: rew [Q] B2 in c4 = c5)
  (H3': b5 = b3) (U3': rew [Q] H3' in c5 = c3)
  (HH: f_equal f1 K1 • (H2 • B3) = H1' • (B2 • H3'))
  (HHu: rew [fun h => rew [Q] h in g1 x1 = c3] HH in
      sigT_trans3 (f_equal f1 K1) (f_equal_dep_sigT f1 g1 K1) H2 U2 B3 V3 =
      sigT_trans3 H1' U1' B2 V2 H3' U3'):
  f_equal (fun a => (f1 a; g1 a)) K1 • ((= H2; U2) • (= B3; V3)) =
  (= H1'; U1') • ((= B2; V2) • (= H3'; U3')).
Proof.
  rewrite (f_equal_sigT_dep f1 g1 K1).
  repeat rewrite eq_trans_eq_existT_curried.
  now exact (eq_existT_curried_eq HH HHu).
Defined.

(** The action of a section into a dependent sum, expressed as
    [sigT_map_eq] along the identity fibre map. *)

Lemma sigT_map_eq_id_dep_sigT {A B: Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, Q (f a)) {x y: A} (e: x = y):
  sigT_map_eq (P := fun a => Q (f a)) (Q := Q) (f := f) (fun _ u => u)
    (f_equal_dep (fun a => Q (f a)) g e)
  = f_equal_dep_sigT f g e.
Proof.
  now destruct e.
Defined.

(** Retain the selected prefix and displayed layer cells of a section hexagon. *)
Definition section_hex_parts {A B: Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, Q (f a))
  {x y: A} (p: x = y)
  {b2 b3 b4 b5: B} {c2: Q b2} {c3: Q b3} {c4: Q b4} {c5: Q b5}
  (a2: f y = b2) (h2: rew [Q] a2 in g y = c2)
  (a3: b2 = b3) (h3: rew [Q] a3 in c2 = c3)
  (b1: f x = b4) (k1: rew [Q] b1 in g x = c4)
  (b2p: b4 = b5) (k2: rew [Q] b2p in c4 = c5)
  (b3p: b5 = b3) (k3: rew [Q] b3p in c5 = c3)
 : Type :=
  {K: f_equal f p • (a2 • a3) = b1 • (b2p • b3p) &T
   rew [fun e => rew [Q] e in g x = c3] K in
     (f_equal_dep_sigT f g p ⊙ (h2 ⊙ h3)) = k1 ⊙ (k2 ⊙ k3)}.


Lemma section_hex_layer_map_first {A B: Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, Q (f a))
  {x y: A} (p: x = y)
  {b2 b3 b4 b5: B} {c2: Q b2} {c3: Q b3} {c4: Q b4} {c5: Q b5}
  (a2: f y = b2) (h2: rew [Q] a2 in g y = c2)
  (a3: b2 = b3) (h3: rew [Q] a3 in c2 = c3)
  (b1: f x = b4) (k1: rew [Q] b1 in g x = c4)
  (b2p: b4 = b5) (k2: rew [Q] b2p in c4 = c5)
  (b3p: b5 = b3) (k3: rew [Q] b3p in c5 = c3)

  (K: f_equal f p • (a2 • a3) = b1 • (b2p • b3p))
  (H: rew [fun e => rew [Q] e in g x = c3] K in
    (f_equal_dep_sigT f g p ⊙ (h2 ⊙ h3)) = k1 ⊙ (k2 ⊙ k3)):
  rew [fun e => rew [Q] e in g x = c3] K in
    (sigT_map_eq (P := fun a => Q (f a)) (Q := Q) (f := f) (fun _ u => u)
      (f_equal_dep (fun a => Q (f a)) g p) ⊙ (h2 ⊙ h3)) = k1 ⊙ (k2 ⊙ k3).
Proof.
  rewrite (sigT_map_eq_id_dep_sigT f g p).
  now exact H.
Defined.



(** Splitting a section into a dependent sum into its two components, so that
    its action on a path is an explicit [eq_existT_curried_dep]. *)

Definition f_equal_dep2 {A: Type} {P0: A -> Type} {R0: forall a, P0 a -> Type}
  (s1: forall a, P0 a) (s2: forall a, R0 a (s1 a)) {x y: A} (e: x = y):
  rew [fun z: {a: A &T P0 a} => R0 z.1 z.2]
      (= e; f_equal_dep P0 s1 e) in
    (s2 x: (fun z: {a: A &T P0 a} => R0 z.1 z.2) (x; s1 x)) = s2 y.
Proof.
  now destruct e.
Defined.

Lemma f_equal_dep_as_existT {A: Type} {P0: A -> Type}
  {R0: forall a, P0 a -> Type}
  (s1: forall a, P0 a) (s2: forall a, R0 a (s1 a)) {x y: A} (e: x = y):
  f_equal_dep (fun a => {u: P0 a &T R0 a u}) (fun a => (s1 a; s2 a)) e
  = eq_existT_curried_dep (Q := fun z: {a: A &T P0 a} => R0 z.1 z.2)
      (H := e) (Hu := f_equal_dep P0 s1 e) (Hv := f_equal_dep2 s1 s2 e).
Proof.
  now destruct e.
Defined.

(** Align two transports whose base paths share a target. This
    transparent form of [rew_align] reduces when the paths are identities. *)

Lemma rew_align_dep {A: Type} {P: A -> Type} {x x' y: A}
  {e: x = y} {e': x' = y} (b: x = x') {v: P x} {v': P x'}
  (Hv: rew [P] b in v = v') (Hcoh: e = b • e'):
  rew [P] e in v = rew [P] e' in v'.
Proof.
  now exact (f_equal (fun p => rew [P] p in v) Hcoh •
    (eq_sym (rew_compose P b e' v) • f_equal (fun v => rew [P] e' in v) Hv)).
Defined.

(** At an identity source correction, alignment reduces to the action
    on the supplied equality between base paths. *)

Lemma rew_align_dep_refl_eq {A: Type} {P: A -> Type} {x y: A}
  {e e': x = y} {v: P x} (Hcoh: e = eq_refl • e'):
  rew_align_dep (P := P) (e := e) (e' := e') (v := v) (v' := v)
    eq_refl eq_refl Hcoh
  = f_equal (fun π: x = y => rew [P] π in v) (Hcoh • eq_trans_refl_l e').
Proof.
  unfold rew_align_dep; cbn [f_equal].
  rewrite eq_trans_refl_r, rew_unit_base.
  now rewrite eq_sym_map_distr, eq_sym_involutive, <- eq_trans_map_distr.
Defined.

(** The selected inverse left-unit boundary gives identity alignment. *)
Lemma rew_align_dep_identity_base {A: Type} {P: A -> Type} {x y: A}
  (e: x = y) (v: P x):
  rew_align_dep (P := P) (e := e) (e' := e) (v := v) (v' := v)
    eq_refl eq_refl (eq_sym (eq_trans_refl_l e)) = eq_refl.
Proof.
  rewrite rew_align_dep_refl_eq, eq_trans_sym_inv_l.
  now reflexivity.
Defined.


Lemma rew_align_dep_rebase {A: Type} {P: A -> Type} {x x' y: A}
  {e e0: x = y} (He: e = e0) {e': x' = y} (b: x = x')
  {v: P x} {v': P x'} (Hv: rew [P] b in v = v') (Hcoh: e0 = b • e'):
  rew <- [fun π: x = y => rew [P] π in v = rew [P] e' in v'] He in
    rew_align_dep b Hv Hcoh
  = rew_align_dep b Hv (He • Hcoh).
Proof.
  unfold eq_rect_r.
  rewrite rewBaseAsTrans, eq_sym_involutive.
  unfold rew_align_dep.
  now rewrite eq_trans_map_distr, <- eq_trans_assoc.
Defined.

(** The displayed alignment over this comparison uses the same witnesses. *)
Lemma rew_align_dep_compare {A: Type} {P: A -> Type} {x x' y: A}
  {e e0: x = y} {e': x' = y} (b: x = x')
  {v: P x} {v': P x'} (Hv: rew [P] b in v = v')
  (Hcoh: e0 = b • e') (Hcohg: e = b • e'):
  rew <- [fun π: x = y => rew [P] π in v = rew [P] e' in v']
    (path_compare_target Hcohg Hcoh) in rew_align_dep b Hv Hcoh
  = rew_align_dep b Hv Hcohg.
Proof.
  rewrite rew_align_dep_rebase.
  apply (f_equal (fun H => rew_align_dep b Hv H)).
  unfold path_compare_target.
  now rewrite <- eq_trans_assoc, eq_trans_sym_inv_l, eq_trans_refl_r.
Defined.

Lemma sigT_map_eq_rebase {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y} {p p0: x = y} (Hp: p = p0)
  (c: rew [P] p0 in u = v):
  sigT_map_eq g (rew <- [fun π: x = y => rew [P] π in u = v] Hp in c)
  = rew <- [fun π: f x = f y => rew [Q] π in g x u = g y v]
      (f_equal (fun z: x = y => f_equal f z) Hp) in sigT_map_eq g c.
Proof.
  unfold eq_rect_r.
  rewrite (eq_sym_map_distr (fun z: x = y => f_equal f z) Hp).
  now exact (eq_sym (map_subst_map (fun z: x = y => f_equal f z)
    (fun p (h: rew [P] p in u = v) => sigT_map_eq g h) (eq_sym Hp) c)).
Defined.

Lemma totalPathDecodeEncode {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  existT (fun pi: x = y => rew [P] pi in u = v)
    (projT1_eq (=p; q)) (projT2_eq (=p; q)) = (p; q).
Proof.
  now destruct q, p.
Defined.

Lemma totalPathReencode {A: Type} {P: A -> Type}
  {u v: {x: A &T P x}} (q: u = v):
  (=projT1_eq q; projT2_eq q) = q.
Proof.
  now destruct q, u.
Defined.

(** A source change of a pair path carries its projected frame and its
    combined layer-and-painting witness through the same comparison. *)
Definition source_projection_cell {A: Type} {P: A -> Type}
  {u v w: {a: A &T P a}} (s: u = v) (p: v = w):
  projT1_eq (path_reindex_source s p) =
  path_reindex_source (projT1_eq s) (projT1_eq p).
Proof. now destruct s. Defined.

Definition source_reindex_cancel {A: Type} {u v w: A}
  (s: u = v) (p: u = w):
  path_reindex_source s (path_reindex_source (eq_sym s) p) = p.
Proof. now destruct s. Defined.

Definition source_projection_recover {A: Type} {P: A -> Type}
  {u v w: {a: A &T P a}} (s: u = v) (p: u = w):
  projT1_eq p = path_reindex_source (projT1_eq s)
    (projT1_eq (path_reindex_source (eq_sym s) p)) :=
  eq_sym (f_equal (@projT1_eq A P u w) (source_reindex_cancel s p))
  • source_projection_cell s (path_reindex_source (eq_sym s) p).

Definition source_reindex_as_comp {A: Type} {u v w: A}
  (s: u = v) (p: v = w): path_reindex_source s p = s • p.
Proof.
  destruct s.
  now exact (eq_sym (eq_trans_refl_l p)).
Defined.

Definition source_projection_recover_comp {A: Type} {P: A -> Type}
  {u v w: {a: A &T P a}} (s: u = v) (p: u = w):
  projT1_eq p = projT1_eq s •
    projT1_eq (path_reindex_source (eq_sym s) p) :=
  source_projection_recover s p • source_reindex_as_comp
    (projT1_eq s) (projT1_eq (path_reindex_source (eq_sym s) p)).

Lemma source_projection_recover_comp_dep {A: Type} {P: A -> Type}
  {u v w: {a: A &T P a}} (s: u = v) (p: u = w):
  rew [fun e: u.1 = w.1 => rew [P] e in u.2 = w.2]
    source_projection_recover_comp s p in projT2_eq p =
  projT2_eq s ⊙[P] projT2_eq (path_reindex_source (eq_sym s) p).
Proof. now destruct s, p. Defined.

Definition pair_path_parameter_cell {A: Type} {P: A -> Type}
  {u v: {a: A &T P a}} {p q: u = v} (K: p = q):
  projT1_eq p = projT1_eq q := f_equal (@projT1_eq A P u v) K.

Lemma pair_path_parameter_cell_dep {A: Type} {P: A -> Type}
  {u v: {a: A &T P a}} {p q: u = v} (K: p = q):
  rew [fun e: u.1 = v.1 => rew [P] e in u.2 = v.2]
    pair_path_parameter_cell K in projT2_eq p = projT2_eq q.
Proof. now destruct K. Defined.

Definition pair_path_display {A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type} {u v: {a: A &T P a}}
  (p: u = v) {cu: R u} {cv: R v} (hp: rew [R] p in cu = cv):
  rew [fun a => {b: P a &T R (a; b)}] projT1_eq p in
    (u.2; cu) = (v.2; cv) :=
  @eq_existT_curried_dep A u.1 P R v.1 (projT1_eq p)
    u.2 cu v.2 cv (projT2_eq p)
    (rew [fun e => rew [R] e in cu = cv]
      (eq_sym (totalPathReencode p)) in hp).

Lemma pair_path_display_refl {A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type} (u: {a: A &T P a}) (cu: R u):
  pair_path_display (eq_refl: u = u) (eq_refl: cu = cu) = eq_refl.
Proof. destruct u. now reflexivity. Defined.

Definition source_display_inverse {A: Type} (R: A -> Type)
  {u v: A} (s: u = v) {cu: R u} {cv: R v}
  (hs: rew [R] s in cu = cv):
  cv = rew [R] eq_sym (eq_sym s) in cu.
Proof. destruct s. now exact (eq_sym hs). Defined.

Definition source_reindex_display {A: Type} (R: A -> Type)
  {u v w: A} (s: u = v) (p: u = w)
  {cu: R u} {cv: R v} {cw: R w}
  (hs: rew [R] s in cu = cv) (hp: rew [R] p in cu = cw):
  rew [R] path_reindex_source (eq_sym s) p in cv = cw :=
  path_reindex_source_dep R (eq_sym s) p cu cv cw
    (source_display_inverse R s hs) hp.

Definition source_reindex_combined {A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type} {u v w: {a: A &T P a}}
  (s: u = v) (p: u = w) {cu: R u} {cv: R v} {cw: R w}
  (hs: rew [R] s in cu = cv) (hp: rew [R] p in cu = cw):
  rew [fun a => {b: P a &T R (a; b)}]
    projT1_eq (path_reindex_source (eq_sym s) p) in
      (v.2; cv) = (w.2; cw) :=
  pair_path_display (path_reindex_source (eq_sym s) p)
    (source_reindex_display R s p hs hp).

Lemma source_projection_recover_comp_dep2 {A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type} {u v w: {a: A &T P a}}
  (s: u = v) (p: u = w) {cu: R u} {cv: R v} {cw: R w}
  (hs: rew [R] s in cu = cv) (hp: rew [R] p in cu = cw):
  rew [fun e => rew [fun a => {b: P a &T R (a; b)}] e in
      (u.2; cu) = (w.2; cw)]
    source_projection_recover_comp s p in pair_path_display p hp =
  pair_path_display s hs ⊙ source_reindex_combined s p hs hp.
Proof. destruct s, p, hs, hp, u as [a b]. now reflexivity. Defined.

Lemma pair_path_parameter_cell_dep2 {I A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type} {u v: {a: A &T P a}}
  (p: I -> u = v) {cu: R u} {cv: R v}
  (hp: forall i, rew [R] p i in cu = cv)
  {i j: I} (e: i = j):
  rew [fun q => rew [fun a => {b: P a &T R (a; b)}] q in
      (u.2; cu) = (v.2; cv)]
    pair_path_parameter_cell (f_equal p e) in pair_path_display (p i) (hp i)
  = pair_path_display (p j) (hp j).
Proof. now destruct e. Defined.

Lemma source_reindex_section_total {I A: Type} {P: A -> Type}
  (f: I -> A) (h: forall i, P (f i)) {i j: I} (e: i = j)
  {z: A} (p: f i = z) {cz: P z} (hp: rew [P] p in h i = cz):
  (=path_reindex_source (eq_sym (f_equal f e)) p;
    source_reindex_display P (f_equal f e) p (f_equal_dep_sigT f h e) hp) =
  path_reindex_source (eq_sym (f_equal (fun i => (f i; h i)) e)) (=p; hp).
Proof. now destruct e. Defined.

Lemma pair_path_section_whisker_dep2 {I A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type}
  (f: I -> {a: A &T P a}) (h: forall i, R (f i))
  {i j: I} (e: i = j) {z: A}
  {cz: {b: P z &T R (z; b)}} (r: (f j).1 = z)
  (hr: rew [fun a => {b: P a &T R (a; b)}] r in ((f j).2; h j) = cz):
  rew [fun q => rew [fun a => {b: P a &T R (a; b)}] q in
      ((f i).2; h i) = cz]
    (f_equal (fun q => q • r) (f_equal_compose f (fun z => z.1) e)) in
    (pair_path_display (f_equal f e) (f_equal_dep_sigT f h e) ⊙ hr) =
  f_equal_dep_sigT (fun i => (f i).1) (fun i => ((f i).2; h i)) e ⊙ hr.
Proof.
  destruct e.
  cbn [f_equal f_equal_compose f_equal_dep_sigT].
  now rewrite pair_path_display_refl.
Defined.

Lemma totalPathRew {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} {p p': x = y}
  (K: p = p') (q: rew [P] p in u = v):
  (=p'; rew [fun pi: x = y => rew [P] pi in u = v] K in q) = (=p; q).
Proof.
  now destruct K.
Defined.



(** The image of a dependent path of the reindexed family in the family
    itself: [rew_map] turns the reindexed transport into a transport along
    the mapped path. *)
Definition convP {XT T: Type} {P: XT -> Type} {rf0: T -> XT}
  {d1 d2: T} (e: d1 = d2) {x: P (rf0 d1)} {y: P (rf0 d2)}
  (u: rew [fun d => P (rf0 d)] e in x = y):
  rew [P] (f_equal rf0 e) in x = y :=
  eq_sym (rew_map P rf0 e x) • u.

(** [convP] is injective, and moves a transport along a 2-cell of the index
    to the transport along its image. *)
Lemma dpath_to_P {XT T: Type} {P: XT -> Type} {rf0: T -> XT}
  {d1 d2: T} {e1 e2: d1 = d2} (kappa: e1 = e2)
  {x: P (rf0 d1)} {y: P (rf0 d2)}
  (u: rew [fun d => P (rf0 d)] e1 in x = y)
  (v: rew [fun d => P (rf0 d)] e2 in x = y):
  rew [fun π: rf0 d1 = rf0 d2 => rew [P] π in x = y]
      (f_equal (fun z: d1 = d2 => f_equal rf0 z) kappa) in convP e1 u
  = convP e2 v ->
  rew [fun e: d1 = d2 => rew [fun d => P (rf0 d)] e in x = y] kappa in u = v.
Proof.
  intro H.
  rewrite <- (rew_map (fun π => rew [P] π in x = y)
    (fun e: d1 = d2 => f_equal rf0 e) kappa (convP e1 u)) in H.
  rewrite (map_subst (fun e (h: rew [fun d => P (rf0 d)] e in x = y) =>
    convP e h) kappa u) in H.
  apply (sigT_map_eq_id_inj rf0 P).
  rewrite 2 sigT_map_eq_id.
  now exact H.
Defined.

(** Associativity of [⊙], over the associativity of the base. *)
Lemma sigT_trans_assoc {A: Type} {P: A -> Type} {x y z t: A}
  {u: P x} {v: P y} {w: P z} {s: P t}
  {p: x = y} (q: rew [P] p in u = v)
  {p': y = z} (r: rew [P] p' in v = w)
  {p'': z = t} (c: rew [P] p'' in w = s):
  rew [fun π: x = t => rew [P] π in u = s] (eq_trans_assoc p p' p'') in
    (q ⊙ (r ⊙ c)) = (q ⊙ r) ⊙ c.
Proof.
  pose proof (sigT_trans_eq_assoc q r c) as H.
  apply (f_equal (fun h => rew [fun π => rew [P] π in u = s]
    eq_trans_assoc p p' p'' in h)) in H.
  rewrite rew_opp_r in H.
  now exact (eq_sym H).
Defined.

(** Comparison of dependent paths over every equality of their base
    paths. When parallel 2-cells in the base are equal, a comparison over
    one such equality determines the comparison over any other. *)

Definition DPathEq {A: Type} {Bd: A -> Type} {a1 a2: A} {x: Bd a1} {y: Bd a2}
  {pL pR: a1 = a2} (u: rew [Bd] pL in x = y) (v: rew [Bd] pR in x = y): Type :=
  forall HH: pL = pR,
  rew [fun r: a1 = a2 => rew [Bd] r in x = y] HH in u = v.

Local Arguments rew_cohLayer_hex {T1 T2 T3 X} P {S2 S3} rf0 {rfF rfG} F G
  {d1 d2} E1 {m1 m2} C2 {n1 n2} D2 C1 D1 K aL aR _ _.

Definition sigT_sym_eq {A: Type} {P: A -> Type} {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v): rew [P] (eq_sym p) in v = u.
Proof.
  now destruct q, p.
Defined.

Lemma totalPathSym {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  (=eq_sym p; sigT_sym_eq q) = eq_sym (=p; q).
Proof.
  now destruct q, p.
Defined.

(** The dependent cancellation uses the same chosen prefix comparison. *)
Lemma sigT_prefix_solve_dep {A: Type} (P: A -> Type)
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z} {r: x = z}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w)
  (hr: rew [P] r in u = w) (K: p • q = r)
  (H: rew [fun e => rew [P] e in u = w] K in (hp ⊙ hq) = hr):
  rew [fun e => rew [P] e in v = w] path_prefix_solve K in hq =
    sigT_sym_eq hp ⊙ hr.
Proof.
  destruct hp, p, hq, q.
  cbn in K. destruct K.
  cbn in H. destruct H.
  now reflexivity.
Defined.

(** Selected path operations and their displayed lifts. *)
Definition homotopy_id_cell {X: Type} (f: X -> X)
  (eta: forall x, x = f x) {x y: X} (p: x = y):
  p • eta y = eta x • f_equal f p.
Proof. destruct p. now exact (eq_trans_refl_l (eta x)). Defined.

Lemma homotopy_id_cell_dep {X: Type} (P: X -> Type) (f: X -> X)
  (F: forall x, P x -> P (f x)) (eta: forall x, x = f x)
  (Eta: forall x u, rew [P] eta x in u = F x u)
  {x y: X} (p: x = y) {u: P x} {v: P y}
  (hp: rew [P] p in u = v):
  rew [fun e => rew [P] e in u = F y v] homotopy_id_cell f eta p in
    (hp ⊙[P] Eta y v) = Eta x u ⊙[P] sigT_map_eq (P := P) (Q := P) (f := f) F hp.
Proof.
  destruct p, hp.
  change (rew [fun e: x = f x => rew [P] e in u = F x u]
    eq_trans_refl_l (eta x) in
    ((eq_refl: rew [P] eq_refl in u = u) ⊙[P] Eta x u) = Eta x u).
  pose (D := fun e: x = f x => rew [P] e in u = F x u).
  pose (U := eq_trans_refl_l (eta x)).
  refine (f_equal (fun h => rew [D] U in h)
    (sigT_trans_eq_refl_l (P := P) (eta x) (Eta x u)) • _).
  now exact (rew_opp_r D U (Eta x u)).
Defined.

Lemma displayed_whisker_left {X: Type} (P: X -> Type)
  {x y z: X} (p: x = y) {q q': y = z} (K: q = q')
  {u: P x} {v: P y} {w: P z}
  (hp: rew [P] p in u = v)
  {hq: rew [P] q in v = w} {hq': rew [P] q' in v = w}
  (HK: rew [fun e => rew [P] e in v = w] K in hq = hq'):
  rew [fun e => rew [P] e in u = w] whisker_l p K in
    (hp ⊙[P] hq) = hp ⊙[P] hq'.
Proof.
  destruct K; cbn in HK |- *.
  now exact (f_equal (fun h => hp ⊙[P] h) HK).
Defined.

Lemma displayed_left_unit {X: Type} (P: X -> Type)
  {x y: X} (p: x = y) {u: P x} {v: P y}
  (h: rew [P] p in u = v):
  rew [fun e => rew [P] e in u = v] eq_trans_refl_l p in
    ((eq_refl: rew [P] eq_refl in u = u) ⊙[P] h) = h.
Proof.
  pose (D := fun e: x = y => rew [P] e in u = v).
  refine (f_equal (fun q => rew [D] eq_trans_refl_l p in q)
    (sigT_trans_eq_refl_l (P := P) p h) • _).
  now exact (rew_opp_r D (eq_trans_refl_l p) h).
Defined.

Lemma displayed_inverse_cancel {X: Type} (P: X -> Type)
  {x y z: X} (p: x = y) (q: y = z)
  {u: P x} {v: P y} {w: P z}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w):
  rew [fun e => rew [P] e in v = w] eq_trans_sym_cancel_l p q in
    (sigT_sym_eq hp ⊙[P] (hp ⊙[P] hq)) = hq.
Proof. now destruct p, hp, q, hq. Defined.

Lemma displayed_assoc_forward {A: Type} (P: A -> Type)
  {x y z t: A} {p: x = y} {q: y = z} {r: z = t}
  {u: P x} {v: P y} {w: P z} {a: P t}
  (hp: rew [P] p in u = v) (hq: rew [P] q in v = w)
  (hr: rew [P] r in w = a):
  rew [fun e => rew [P] e in u = a] eq_trans_assoc p q r in
    (hp ⊙[P] (hq ⊙[P] hr)) = (hp ⊙[P] hq) ⊙[P] hr.
Proof.
  refine (f_equal (fun h => rew [fun e => rew [P] e in u = a]
      eq_trans_assoc p q r in h) (eq_sym (sigT_trans_eq_assoc hp hq hr)) • _).
  now exact (rew_opp_r _ (eq_trans_assoc p q r) _).
Defined.

Lemma displayed_whisker_r {A: Type} (P: A -> Type)
  {x y z: A} {p p': x = y} (H: p = p') (q: y = z)
  {u: P x} {v: P y} {w: P z}
  {hp: rew [P] p in u = v} {hp': rew [P] p' in u = v}
  (hq: rew [P] q in v = w)
  (HH: rew [fun e => rew [P] e in u = v] H in hp = hp'):
  rew [fun e => rew [P] e in u = w] whisker_r H q in
    (hp ⊙[P] hq) = hp' ⊙[P] hq.
Proof.
  destruct H; cbn in HH |- *.
  now exact (f_equal (fun hp => hp ⊙[P] hq) HH).
Defined.

Definition square_transfer_cells {A: Type}
  {a b c d e f t w: A}
  (pq: a = b) (pp: c = b) (qq: d = e) (qp: f = e)
  (etaX: a = d) (etaY: b = e) (etaZ: c = f)
  (k: f = t) (r: t = w) (dd: e = w) (s: c = t)
  (NP: pp • etaY = etaZ • qp)
  (NQ: pq • etaY = etaX • qq)
  (H: qp • dd = k • r) (HS: etaZ • k = s):
  etaX • (qq • dd) = pq • (eq_sym pp • (s • r)) :=
  square_compose (eq_sym NQ)
    (path_prefix_solve (square_compose NP H • whisker_r HS r)) •
    eq_sym (eq_trans_assoc pq (eq_sym pp) (s • r)).

Lemma square_transfer_cells_dep {A: Type} (P: A -> Type)
  {a b c d e f t w: A}
  (pq: a = b) (pp: c = b) (qq: d = e) (qp: f = e)
  (etaX: a = d) (etaY: b = e) (etaZ: c = f)
  (k: f = t) (r: t = w) (dd: e = w) (s: c = t)
  (NP: pp • etaY = etaZ • qp)
  (NQ: pq • etaY = etaX • qq)
  (H: qp • dd = k • r) (HS: etaZ • k = s)
  {ua: P a} {ub: P b} {uc: P c} {ud: P d}
  {ue: P e} {uf: P f} {ut: P t} {uw: P w}
  (hpq: rew [P] pq in ua = ub) (hpp: rew [P] pp in uc = ub)
  (hqq: rew [P] qq in ud = ue) (hqp: rew [P] qp in uf = ue)
  (hetaX: rew [P] etaX in ua = ud)
  (hetaY: rew [P] etaY in ub = ue)
  (hetaZ: rew [P] etaZ in uc = uf)
  (hk: rew [P] k in uf = ut) (hr: rew [P] r in ut = uw)
  (hdd: rew [P] dd in ue = uw) (hs: rew [P] s in uc = ut)
  (HNP: rew [fun e => rew [P] e in uc = ue] NP in
    (hpp ⊙[P] hetaY) = hetaZ ⊙[P] hqp)
  (HNQ: rew [fun e => rew [P] e in ua = ue] NQ in
    (hpq ⊙[P] hetaY) = hetaX ⊙[P] hqq)
  (HH: rew [fun e => rew [P] e in uf = uw] H in
    (hqp ⊙[P] hdd) = hk ⊙[P] hr)
  (HHS: rew [fun e => rew [P] e in uc = ut] HS in
    (hetaZ ⊙[P] hk) = hs):
  rew [fun e => rew [P] e in ua = uw]
    square_transfer_cells pq pp qq qp etaX etaY etaZ k r dd s NP NQ H HS in
    (hetaX ⊙[P] (hqq ⊙[P] hdd)) =
    hpq ⊙[P] (sigT_sym_eq hpp ⊙[P] (hs ⊙[P] hr)).
Proof.
  pose (EC := square_compose NP H • whisker_r HS r).
  pose proof (square_compose_dep P NP H hetaZ hk hetaY hdd
    hpp hqp hr HNP HH) as E1.
  pose proof (displayed_whisker_r P HS r hr HHS) as E2.
  pose proof (E1 ⊙[fun e => rew [P] e in uc = uw] E2) as ECdep.
  pose proof (sigT_prefix_solve_dep P hpp (hetaY ⊙[P] hdd)
    (hs ⊙[P] hr) EC ECdep) as Fdep.
  pose proof (square_compose_dep P (eq_sym NQ) (path_prefix_solve EC)
    hpq (sigT_sym_eq hpp) hqq hdd hetaX hetaY (hs ⊙[P] hr)
    (sigT_sym_eq (P := fun e => rew [P] e in ua = ue) HNQ) Fdep) as Cdep.
  now exact (Cdep ⊙[fun e => rew [P] e in ua = uw]
    sigT_trans_eq_assoc hpq (sigT_sym_eq hpp) (hs ⊙[P] hr)).
Defined.

Section ScalarSigma.
Context {X X' TL TM: Type} {P: X -> Type} {P': X' -> Type}
  (f: TM -> TL) (r0: TL -> X) (r0': TM -> X')
  (φ: X -> X) (ρ: X' -> X)
  (Φ: forall x, P x -> P (φ x))
  (Gr: forall y, P' y -> P (ρ y))
  (gA: forall a: TM, ρ (r0' a) = r0 (f a))
  (β: forall m: X, m = φ m)
  (Pi: forall (m: X) (y: P m), rew [fun x => P x] β m in y = Φ m y)
  (d1 d1': TM) (prv: d1 = d1')
  (z: TL) (a1: f d1 = z) (Q1: z = f d1')
  (c: P' (r0' d1)) (L1c: P' (r0' d1'))
  (u0: P (r0 (f d1))) (u1: P (r0 (f d1'))) (U1: P (r0 z))
  (b2: φ (r0 (f d1)) = r0 z)
  (σ: β (r0 (f d1)) • b2 = f_equal r0 a1)
  (N2: U1 = rew [fun x => P x] b2 in Φ (r0 (f d1)) u0)
  (w': X') (A1 A1x: r0' d1 = w') (HA: A1 = A1x)
  (B1: w' = r0' d1')
  (S1: A1 • B1 = f_equal r0' prv)
  (v': P' w')
  (pin: rew [fun x => P' x] A1 in c = v')
  (pinx: rew [fun x => P' x] A1x in c = v')
  (Hpin: rew [fun p => rew [fun x => P' x] p in c = v'] HA in pin = pinx)
  (nF: L1c = rew [fun x => P' x] B1 in v')
  (nG1: u0 = rew [fun x => P x] gA d1 in Gr (r0' d1) c)
  (nG2: u1 = rew [fun x => P x] gA d1' in Gr (r0' d1') L1c)
  (K: φ (ρ (r0' d1)) = ρ w')
  (σq: β (ρ (r0' d1)) • K = f_equal ρ A1x)
  (HC: rew [fun x => P x] K in Φ (ρ (r0' d1)) (Gr (r0' d1) c) = Gr w' v')
  (HH: f_equal φ (gA d1) • (b2 • f_equal r0 Q1)
       = K • (f_equal ρ B1 • gA d1'))
  (Htau: rew [fun r: ρ (r0' d1) = ρ w' =>
               rew [fun x => P x] r in Gr (r0' d1) c = Gr w' v'] σq in
           (Pi (ρ (r0' d1)) (Gr (r0' d1) c) ⊙[fun x => P x] HC)
         = sigT_map_eq (P := P') (Q := P) (f := ρ) Gr pinx).

Definition frameLeft :=
  eq_trans_map_distr r0 a1 Q1 •
    (whisker_r (eq_sym σ) (f_equal r0 Q1) •
      (eq_sym (eq_trans_assoc (β (r0 (f d1))) b2 (f_equal r0 Q1)) •
        whisker_l (β (r0 (f d1)))
          (eq_sym (eq_trans_refl_l (b2 • f_equal r0 Q1))))).

Definition frameRaw :=
  square_transfer_cells eq_refl (gA d1) eq_refl (f_equal φ (gA d1))
    (β (r0 (f d1))) (β (r0 (f d1))) (β (ρ (r0' d1)))
    K (f_equal ρ B1 • gA d1') (b2 • f_equal r0 Q1) (f_equal ρ A1)
    (homotopy_id_cell φ β (gA d1)) (eq_trans_refl_l (β (r0 (f d1))))
    HH (σq • f_equal (fun e => f_equal ρ e) (eq_sym HA)).

Definition frameRight :=
  eq_trans_refl_l
    (eq_sym (gA d1) • (f_equal ρ A1 • (f_equal ρ B1 • gA d1'))) •
    (whisker_l (eq_sym (gA d1))
      (eq_trans_assoc (f_equal ρ A1) (f_equal ρ B1) (gA d1') •
        (whisker_r (eq_sym (eq_trans_map_distr ρ A1 B1)) (gA d1') •
          (whisker_r (f_equal (fun e => f_equal ρ e) S1) (gA d1') •
            f_equal_naturality r0' f ρ r0 gA prv))) •
      eq_trans_sym_cancel_l (gA d1) (f_equal r0 (f_equal f prv))).

Definition sigmaFrameRecipe:
  f_equal r0 (a1 • Q1) = f_equal r0 (f_equal f prv) :=
  frameLeft • (frameRaw • frameRight).

Definition SigmaFrameCoherence (κ: a1 • Q1 = f_equal f prv): Type :=
  f_equal (fun e => f_equal r0 e) κ = sigmaFrameRecipe.

Let G0 := Gr (r0' d1) c.
Let Corr := rew [P] gA d1 in G0.
Let rawLayer := rew_cohLayer_hex P r0 Φ Gr Q1 (gA d1) B1 b2 (gA d1') K
  G0 v' HC HH.
Let endCorrection :=
  eq_sym (f_equal (fun y => rew [P] gA d1' in Gr (r0' d1') y) nF) • eq_sym nG2.
Let tail := f_equal (fun y => rew [fun t => P (r0 t)] Q1 in y) N2 •
  (f_equal (fun y => rew [fun t => P (r0 t)] Q1 in rew [P] b2 in Φ (r0 (f d1)) y) nG1 •
    (rawLayer • endCorrection)).
Let first := source_triangle_fill P r0 eq_refl a1 σ (Pi (r0 (f d1)) u0) (eq_sym N2).
Let source := source_triangle_fill P' r0' eq_refl prv S1 pin (eq_sym nF).
Let targetMap := fun a y => rew [P] gA a in Gr (r0' a) y.
Let mappedSource := sigT_map_eq (P := fun a => P' (r0' a))
  (Q := fun t => P (r0 t)) (f := f) targetMap source.
Let right := f_equal (fun y => rew [fun t => P (r0 t)] f_equal f prv in y) nG1 •
  (mappedSource • eq_sym nG2).
Let left := first ⊙[fun t => P (r0 t)] tail.
Let leftMap := sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0)
  (fun _ u => u) left.
Let rightMap := sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0)
  (fun _ u => u) right.
Let hPp := (eq_refl: rew [P] gA d1 in G0 = Corr).
Let hQp := sigT_map_eq (P := P) (Q := P) (f := φ) Φ hPp.
Let hQq := sigT_map_eq (P := P) (Q := P) (f := φ) Φ (p := eq_refl) nG1.
Let hS := sigT_map_eq (P := P') (Q := P) (f := ρ) Gr pin.
Let hR := sigT_map_eq (P := P') (Q := P) (f := ρ) Gr (eq_sym nF) ⊙[P] eq_sym nG2.
Let hDD := (eq_refl: rew [P] b2 in Φ (r0 (f d1)) Corr = _) ⊙[P]
  sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0) (fun _ u => u)
    (rawLayer • endCorrection).
Let rawLeft := Pi (r0 (f d1)) u0 ⊙[P] (hQq ⊙[P] hDD).
Let rawRight :=
  (nG1: rew [P] (eq_refl: r0 (f d1) = r0 (f d1)) in u0 = Corr)
    ⊙[P] (sigT_sym_eq hPp ⊙[P] (hS ⊙[P] hR)).

Lemma sigmaDD:
  rew [fun e => rew [P] e in Φ (ρ (r0' d1)) G0 = u1] HH in
    (hQp ⊙[P] hDD) = HC ⊙[P] hR.
Proof.
  unfold hQp, hDD, hR, hPp, Corr, rawLayer, endCorrection, G0.
  pose proof (rew_coh2Painting_restr0_edges Φ Gr Q1 (gA d1) B1 b2 (gA d1') K
    (Gr (r0' d1) c) v' HC HH
    (rew [P] gA d1 in Gr (r0' d1) c) eq_refl L1c nF
    (rew [P] b2 in Φ (r0 (f d1)) (rew [P] gA d1 in Gr (r0' d1) c)) eq_refl
    u1 nG2 _ eq_refl _ eq_refl _ eq_refl _ eq_refl) as D.
  cbn [f_equal] in D.
  rewrite 2 eq_trans_refl_l in D.
  rewrite (sigT_map_eq_id (P := P) r0).
  now exact D.
Defined.

Lemma sigmaRaw:
  rew [fun e => rew [P] e in u0 = u1] frameRaw in rawLeft = rawRight.
Proof.
  unfold frameRaw, rawLeft, rawRight.
  refine (square_transfer_cells_dep P
    (eq_refl: r0 (f d1) = r0 (f d1)) (gA d1)
    (eq_refl: φ (r0 (f d1)) = φ (r0 (f d1))) (f_equal φ (gA d1))
    (β (r0 (f d1))) (β (r0 (f d1))) (β (ρ (r0' d1)))
    K (f_equal ρ B1 • gA d1') (b2 • f_equal r0 Q1) (f_equal ρ A1)
    (homotopy_id_cell φ β (gA d1)) (eq_trans_refl_l (β (r0 (f d1))))
    HH (σq • f_equal (fun e => f_equal ρ e) (eq_sym HA))
    nG1 hPp hQq hQp (Pi _ _) (Pi _ _) (Pi _ _) HC hR hDD hS _ _ sigmaDD _).
  - now exact (homotopy_id_cell_dep P φ Φ β Pi (gA d1) hPp).
  - now exact (homotopy_id_cell_dep P φ Φ β Pi eq_refl nG1).
  - now exact (Htau ⊙[fun e => rew [P] e in G0 = Gr w' v']
      sigT_map_eq
        (P := fun e: r0' d1 = w' => rew [P'] e in c = v')
        (Q := fun e: ρ (r0' d1) = ρ w' => rew [P] e in G0 = Gr w' v')
        (f := fun e => f_equal ρ e)
        (fun e h => sigT_map_eq (P := P') (Q := P) (f := ρ) Gr h)
        (sigT_sym_eq Hpin)).
Defined.


Lemma sigmaLeft:
  rew [fun e => rew [P] e in u0 = u1] frameLeft in leftMap = rawLeft.
Proof.
  subst U1 u0.
  pose (D := fun e: r0 (f d1) = r0 (f d1') => rew [P] e in Corr = u1).
  pose (mapTail := sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0)
    (fun _ u => u) tail).
  pose proof (sigT_map_eq_comp (P := fun t => P (r0 t)) (Q := P) (f := r0)
    (fun _ u => u) first tail) as E1.
  pose proof (source_triangle_fill_boundary P r0 eq_refl a1 σ
    (Pi (r0 (f d1)) Corr) eq_refl) as Hfirst.
  pose proof (displayed_whisker_r P (eq_sym σ) (f_equal r0 Q1) mapTail
    (sigT_sym_eq Hfirst)) as E2.
  pose proof (sigT_trans_eq_assoc (Pi (r0 (f d1)) Corr)
    (eq_refl: rew [P] b2 in Φ (r0 (f d1)) Corr = _) mapTail) as E3.
  assert (TAIL: tail = rawLayer • endCorrection).
  { unfold tail. cbn [f_equal]. now rewrite 2 eq_trans_refl_l. }
  assert (DD: (eq_refl: rew [P] b2 in Φ (r0 (f d1)) Corr = _) ⊙[P] mapTail = hDD).
  { now exact (f_equal (fun h =>
      (eq_refl: rew [P] b2 in Φ (r0 (f d1)) Corr = _) ⊙[P]
        sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0)
          (fun _ u => u) h) TAIL). }
  pose (U := eq_sym (eq_trans_refl_l (b2 • f_equal r0 Q1))).
  pose (DDom := fun e: φ (r0 (f d1)) = r0 (f d1') =>
    rew [P] e in Φ (r0 (f d1)) Corr = u1).
  pose proof (f_equal (fun h => rew [DDom] U in h) DD •
    eq_sym (sigT_trans_eq_refl_l (b2 • f_equal r0 Q1) hDD)) as EUnit.
  pose proof (displayed_whisker_left P (β (r0 (f d1))) U
    (Pi (r0 (f d1)) Corr) EUnit) as E4.
  now exact (E1 ⊙[D] (E2 ⊙[D] (E3 ⊙[D] E4))).
Defined.

Lemma sigmaRight:
  rew [fun e => rew [P] e in u0 = u1] frameRight in rawRight = rightMap.
Proof.
  subst L1c u1 u0.
  pose (mapB := sigT_map_eq (P := P') (Q := P) (f := ρ) Gr
    (eq_refl: rew [P'] B1 in v' = _)).
  pose (pureEnd := (eq_refl: rew [P] gA d1' in
    Gr (r0' d1') (rew [P'] B1 in v') = _)).
  pose (finalMap := sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0)
    (fun _ u => u) mappedSource).
  pose (D := fun e: r0 (f d1) = r0 (f d1') =>
    rew [P] e in Corr = rew [P] gA d1' in Gr (r0' d1') (rew [P'] B1 in v')).
  pose (Inner := fun e: ρ (r0' d1) = r0 (f d1') =>
    rew [P] e in G0 = rew [P] gA d1' in Gr (r0' d1') (rew [P'] B1 in v')).
  pose proof (displayed_left_unit P
    (eq_sym (gA d1) • (f_equal ρ A1 • (f_equal ρ B1 • gA d1')))
    (sigT_sym_eq hPp ⊙[P] (hS ⊙[P] hR))) as EUnit.
  pose proof (displayed_assoc_forward P hS mapB pureEnd) as EAssoc.
  pose proof (displayed_whisker_r P (eq_sym (eq_trans_map_distr ρ A1 B1))
    (gA d1') pureEnd
    (sigT_sym_eq (sigT_map_eq_comp Gr pin (eq_refl: rew [P'] B1 in v' = _)))) as EMap.
  pose proof (source_triangle_fill_boundary P' r0' eq_refl prv S1 pin
    (eq_refl: rew [P'] B1 in v' = _)) as HS.
  pose proof (sigT_map_eq
    (P := fun e: r0' d1 = r0' d1' => rew [P'] e in c = rew [P'] B1 in v')
    (Q := fun e: ρ (r0' d1) = ρ (r0' d1') =>
      rew [P] e in G0 = Gr (r0' d1') (rew [P'] B1 in v'))
    (f := fun e => f_equal ρ e)
    (fun e h => sigT_map_eq (P := P') (Q := P) (f := ρ) Gr h) HS) as HMS.
  pose proof (displayed_whisker_r P (f_equal (fun e => f_equal ρ e) S1)
    (gA d1') pureEnd HMS) as ESource.
  pose proof (f_equal_naturality_dep
    (PA := fun a => P' (r0' a)) (PB := P') (PC := fun t => P (r0 t)) (PD := P)
    r0' f ρ r0 (fun _ u => u) targetMap Gr (fun _ u => u)
    gA (fun _ _ => eq_refl) prv source) as ENat.
  pose proof (EAssoc ⊙[Inner] (EMap ⊙[Inner] (ESource ⊙[Inner] ENat))) as EInner.
  pose proof (displayed_whisker_left P (eq_sym (gA d1)) _
    (sigT_sym_eq hPp) EInner) as EPrefix.
  pose proof (displayed_inverse_cancel P (gA d1) (f_equal r0 (f_equal f prv))
    hPp finalMap) as ECancel.
  assert (R: right = mappedSource).
  { unfold right. cbn [f_equal]. now rewrite eq_trans_refl_l. }
  refine ((EUnit ⊙[D] (EPrefix ⊙[D] ECancel)) • _).
  now exact (eq_sym (f_equal
    (fun h => sigT_map_eq (P := fun t => P (r0 t)) (Q := P) (f := r0)
      (fun _ u => u) h) R)).
Defined.

Lemma sigmaSelectedTransfer:
  rew [fun e => rew [P] e in u0 = u1] sigmaFrameRecipe in leftMap = rightMap.
Proof.
  now exact (sigmaLeft ⊙[fun e => rew [P] e in u0 = u1]
    (sigmaRaw ⊙[fun e => rew [P] e in u0 = u1] sigmaRight)).
Defined.

Lemma sigmaLayerKernelSelected
  (κ: a1 • Q1 = f_equal f prv) (frame3: SigmaFrameCoherence κ):
  rew [fun e => rew [fun t => P (r0 t)] e in u0 = u1] κ in left = right.
Proof.
  apply (dpath_to_P (P := P) (rf0 := r0) κ).
  pose proof sigmaSelectedTransfer as T.
  unfold leftMap, rightMap in T.
  rewrite 2 (sigT_map_eq_id (P := P) r0) in T.
  now exact (rew <- [fun C => rew [fun e => rew [P] e in u0 = u1] C in
    convP (P := P) (rf0 := r0) (a1 • Q1) left =
    convP (P := P) (rf0 := r0) (f_equal f prv) right] frame3 in T).
Defined.

End ScalarSigma.


(** Transparent transport cancellations. Their proofs reduce at
    [eq_refl], as do the inverse laws of [rewEquivD] built from them. *)

Lemma rewSymCancel {A: Type} {P: A -> Type} {x y: A} (e: x = y) (a: P x):
  rew [P] (eq_sym e) in rew [P] e in a = a.
Proof. now destruct e. Defined.

Lemma rewSymCancelR {A: Type} {P: A -> Type} {x y: A} (e: x = y) (b: P y):
  rew [P] e in rew [P] (eq_sym e) in b = b.
Proof. now destruct e. Defined.

Definition rewEquivD {A: Type} (P: A -> Type) {x y: A} (e: x = y):
  Equiv (P x) (P y) :=
  qinvEquiv (fun a => rew [P] e in a) (fun b => rew [P] (eq_sym e) in b)
    (fun a => rewSymCancel e a) (fun b => rewSymCancelR e b).

(** Move transport from a map's argument to its result. Transparent
    cancellation proofs allow the comparison to reduce when the ambient
    type identifications are identities. *)

Definition condFace {A: Type} {P: A -> Type} {C D C' D': A}
  (e: C = D) (e': C' = D')
  (FX: P C' -> P C) (FS: P D' -> P D)
  (G: forall t: P D', FX (rew [P] eq_sym e' in t) = rew [P] eq_sym e in FS t)
  (u: P C'): rew [P] e in FX u = FS (rew [P] e' in u) :=
  f_equal (fun z: P C => rew [P] e in z)
    (f_equal FX (eq_sym (rewSymCancel e' u)) • G (rew [P] e' in u))
  • rewSymCancelR e (FS (rew [P] e' in u)).

(** The unit and counit of transport satisfy the triangle used when
    a comparison is moved across the two inverse transports. *)
Lemma rewSymTriangle {A: Type} {P: A -> Type} {x y: A} (e: x = y) (v: P y):
  rewSymCancel e (rew [P] eq_sym e in v) =
  f_equal (fun v => rew [P] eq_sym e in v) (rewSymCancelR e v).
Proof.
  now destruct e.
Defined.

Lemma rew_path_inj {A: Type} (P: A -> Type) {x y: A} (e: x = y)
  {u v: P x} (p q: u = v):
  f_equal (fun u => rew [P] e in u) p = f_equal (fun u => rew [P] e in u) q ->
  p = q.
Proof.
  intro H.
  rewrite <- (fEqualRet (rewEquivD P e) p), <- (fEqualRet (rewEquivD P e) q).
  now rewrite H.
Defined.

(** Reading a transposed face through the inverse transport recovers
    its original comparison, preceded by the source unit. *)
Lemma condFace_back {A: Type} {P: A -> Type} {C D C' D': A}
  (e: C = D) (e': C' = D') (FX: P C' -> P C) (FS: P D' -> P D)
  (G: forall t: P D', FX (rew [P] eq_sym e' in t) = rew [P] eq_sym e in FS t)
  (u: P C'):
  f_equal (fun z => rew [P] eq_sym e in z) (condFace e e' FX FS G u) =
  rewSymCancel e (FX u) •
    (f_equal FX (eq_sym (rewSymCancel e' u)) • G (rew [P] e' in u)).
Proof.
  unfold condFace.
  rewrite eq_trans_map_distr.
  rewrite (f_equal_compose (fun z: P C => rew [P] e in z)
    (fun z: P D => rew [P] eq_sym e in z)).
  rewrite (path_change_natural (fun z => rew [P] eq_sym e in rew [P] e in z)
    (fun z => z) (rewSymCancel e)).
  unfold path_change.
  rewrite f_equal_id, rewSymTriangle, <- 2 eq_trans_assoc.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Defined.

(** Transposing a pasted pair of face comparisons pastes their transposes. *)
Lemma condFace_comp {A: Type} {P: A -> Type} {A0 A1 A2 B0 B1 B2: A}
  (e0: A0 = B0) (e1: A1 = B1) (e2: A2 = B2)
  (F0: P A1 -> P A0) (F1: P A2 -> P A1)
  (G0: P B1 -> P B0) (G1: P B2 -> P B1)
  (H0: forall t: P B1, F0 (rew [P] eq_sym e1 in t) = rew [P] eq_sym e0 in G0 t)
  (H1: forall t: P B2, F1 (rew [P] eq_sym e2 in t) = rew [P] eq_sym e1 in G1 t)
  (u: P A2):
  condFace e0 e2 (fun u => F0 (F1 u)) (fun v => G0 (G1 v))
    (fun v => f_equal F0 (H1 v) • H0 (G1 v)) u =
  condFace e0 e1 F0 G0 H0 (F1 u) • f_equal G0 (condFace e1 e2 F1 G1 H1 u).
Proof.
  apply (rew_path_inj P (eq_sym e0)).
  rewrite (eq_trans_map_distr (fun z: P B0 => rew [P] eq_sym e0 in z)
    (condFace e0 e1 F0 G0 H0 (F1 u))
    (f_equal G0 (condFace e1 e2 F1 G1 H1 u))).
  rewrite (condFace_back (P := P) e0 e2 (fun u => F0 (F1 u))
    (fun v => G0 (G1 v)) (fun v => f_equal F0 (H1 v) • H0 (G1 v)) u).
  rewrite (condFace_back (P := P) e0 e1 F0 G0 H0 (F1 u)).
  pose proof (f_equal_naturality (fun v => rew [P] eq_sym e1 in v)
    G0 F0 (fun v => rew [P] eq_sym e0 in v) H0
    (condFace e1 e2 F1 G1 H1 u)) as N.
  rewrite (condFace_back (P := P) e1 e2 F1 G1 H1 u) in N.
  rewrite <- 2 eq_trans_assoc.
  rewrite <- N.
  rewrite (eq_trans_assoc (f_equal F0 (eq_sym (rewSymCancel e1 (F1 u))))).
  rewrite <- eq_trans_map_distr, eq_trans_sym_cancel_l.
  rewrite eq_trans_map_distr, <- eq_trans_assoc, f_equal_compose.
  now reflexivity.
Defined.

(** A cell between two face comparisons is preserved by transposition. *)
Lemma condFace_cell {A: Type} {P: A -> Type} {C D C' D': A}
  (e: C = D) (e': C' = D') (F G: P C' -> P C) (F' G': P D' -> P D)
  (HF: forall v, F (rew [P] eq_sym e' in v) = rew [P] eq_sym e in F' v)
  (HG: forall v, G (rew [P] eq_sym e' in v) = rew [P] eq_sym e in G' v)
  (α: forall u, F u = G u) (β: forall v, F' v = G' v)
  (H: forall v, HF v • f_equal (fun w => rew [P] eq_sym e in w) (β v) =
    α (rew [P] eq_sym e' in v) • HG v) (u: P C'):
  f_equal (fun w => rew [P] e in w) (α u) • condFace e e' G G' HG u =
  condFace e e' F F' HF u • β (rew [P] e' in u).
Proof.
  apply (rew_path_inj P (eq_sym e)).
  rewrite (eq_trans_map_distr (fun z: P D => rew [P] eq_sym e in z)
    (f_equal (fun z: P C => rew [P] e in z) (α u)) (condFace e e' G G' HG u)),
    (eq_trans_map_distr (fun z: P D => rew [P] eq_sym e in z)
      (condFace e e' F F' HF u) (β (rew [P] e' in u))).
  rewrite (condFace_back (P := P) e e' G G' HG u),
    (condFace_back (P := P) e e' F F' HF u).
  rewrite (f_equal_compose (fun w: P C => rew [P] e in w)
    (fun w: P D => rew [P] eq_sym e in w)).
  rewrite (path_change_natural (fun w => rew [P] eq_sym e in rew [P] e in w)
    (fun w => w) (rewSymCancel e) (α u)).
  unfold path_change. rewrite f_equal_id.
  rewrite <- 4 eq_trans_assoc, eq_trans_sym_cancel_l.
  pose proof (eq_trans_natural F G α (eq_sym (rewSymCancel e' u))) as N.
  pose proof (square_stack N (H (rew [P] e' in u))) as E.
  rewrite <- eq_trans_assoc in E.
  now rewrite E.
Defined.

(** Transpose a commuting square by pasting its face comparisons and
    transporting the cell between the two composite faces. *)

Lemma condSq {A: Type} {P: A -> Type} {A0 A1 A2 B0 B1 B2: A}
  (e0: A0 = B0) (e1: A1 = B1) (e2: A2 = B2)
  (FXq FXr: P A1 -> P A0)
  (FXq' FXr': P A2 -> P A1)
  (FSq FSr: P B1 -> P B0)
  (FSq' FSr': P B2 -> P B1)
  (cohX: forall t: P A2, FXq (FXr' t) = FXr (FXq' t))
  (cohS: forall d: P B2, FSq (FSr' d) = FSr (FSq' d))
  (Gq: forall t: P B1,
     FXq (rew [P] eq_sym e1 in t) = rew [P] eq_sym e0 in FSq t)
  (Gr: forall t: P B1,
     FXr (rew [P] eq_sym e1 in t) = rew [P] eq_sym e0 in FSr t)
  (Gq': forall t: P B2,
     FXq' (rew [P] eq_sym e2 in t) = rew [P] eq_sym e1 in FSq' t)
  (Gr': forall t: P B2,
     FXr' (rew [P] eq_sym e2 in t) = rew [P] eq_sym e1 in FSr' t)
  (HCoh: forall t: P B2,
     (f_equal FXq (Gr' t) • Gq (FSr' t))
     • f_equal (fun w: P B0 => rew [P] eq_sym e0 in w) (cohS t)
     = cohX (rew [P] eq_sym e2 in t) • (f_equal FXr (Gq' t) • Gr (FSq' t)))
  (t: P A2):
  f_equal (fun z: P A0 => rew [P] e0 in z) (cohX t)
  • (condFace e0 e1 FXr FSr Gr (FXq' t)
     • f_equal FSr (condFace e1 e2 FXq' FSq' Gq' t))
  = condFace e0 e1 FXq FSq Gq (FXr' t)
    • (f_equal FSq (condFace e1 e2 FXr' FSr' Gr' t)
       • cohS (rew [P] e2 in t)).
Proof.
  rewrite <- (condFace_comp e0 e1 e2 FXr FXq' FSr FSq' Gr Gq' t).
  rewrite (eq_trans_assoc (condFace e0 e1 FXq FSq Gq (FXr' t))).
  rewrite <- (condFace_comp e0 e1 e2 FXq FXr' FSq FSr' Gq Gr' t).
  now exact (condFace_cell e0 e2
    (fun u => FXq (FXr' u)) (fun u => FXr (FXq' u))
    (fun v => FSq (FSr' v)) (fun v => FSr (FSq' v))
    (fun v => f_equal FXq (Gr' v) • Gq (FSr' v))
    (fun v => f_equal FXr (Gq' v) • Gr (FSq' v)) cohX cohS HCoh t).
Defined.

(** A pointwise change of the input comparison changes its transpose
    pointwise; no equality of functions is required. *)
Lemma condFace_congr {A: Type} {P: A -> Type} {C D C' D': A}
  (e: C = D) (e': C' = D') (FX: P C' -> P C) (FS: P D' -> P D)
  (G G': forall t, FX (rew [P] eq_sym e' in t) = rew [P] eq_sym e in FS t)
  (H: forall t, G t = G' t) (u: P C'):
  condFace e e' FX FS G u = condFace e e' FX FS G' u.
Proof.
  unfold condFace.
  now rewrite H.
Defined.

Lemma condFace_reindex_target {A: Type} {P: A -> Type} {C D C' D': A}
  {e f: C = D} (E: e = f) (e': C' = D')
  (FX: P C' -> P C) (FS: P D' -> P D)
  (G: forall t, FX (rew [P] eq_sym e' in t) = rew [P] eq_sym e in FS t)
  (G': forall t, FX (rew [P] eq_sym e' in t) = rew [P] eq_sym f in FS t)
  (H: forall t, G t = G' t •
    f_equal (fun q: C = D => rew [P] eq_sym q in FS t) (eq_sym E))
  (u: P C'):
  condFace e e' FX FS G u =
  f_equal (fun q: C = D => rew [P] q in FX u) E • condFace f e' FX FS G' u.
Proof.
  pose (Gt := rew [fun q: C = D => forall t: P D',
    FX (rew [P] eq_sym e' in t) = rew [P] eq_sym q in FS t] E in G).
  assert (Ht: forall t, Gt t = G' t).
  { intro t; unfold Gt.
    rewrite (homotopy_reindex_right (fun t => FX (rew [P] eq_sym e' in t))
      (fun q t => rew [P] eq_sym q in FS t) E G t).
    rewrite H, <- eq_trans_assoc,
      <- (eq_trans_map_distr (fun q: C = D => rew [P] eq_sym q in FS t)
        (eq_sym E) E), eq_trans_sym_inv_l.
    cbn [f_equal]. now rewrite eq_trans_refl_r. }
  pose proof (map_subst (fun (q: C = D)
    (H: forall t: P D', FX (rew [P] eq_sym e' in t) = rew [P] eq_sym q in FS t) =>
      condFace q e' FX FS H u) E G) as M.
  rewrite path_reindex_left in M.
  pose proof (path_prefix_solve M) as N.
  rewrite eq_sym_involutive in N.
  fold Gt in N.
  now rewrite (condFace_congr f e' FX FS Gt G' Ht u) in N.
Defined.

Lemma condFace_reindex_source {A: Type} {P: A -> Type} {C D C' D': A}
  (e: C = D) {e' f': C' = D'} (E: e' = f')
  (FX: P C' -> P C) (FS: P D' -> P D)
  (G: forall t, FX (rew [P] eq_sym e' in t) = rew [P] eq_sym e in FS t)
  (G': forall t, FX (rew [P] eq_sym f' in t) = rew [P] eq_sym e in FS t)
  (H: forall t, G t =
    f_equal (fun q: C' = D' => FX (rew [P] eq_sym q in t)) E • G' t)
  (u: P C'):
  condFace e e' FX FS G u = condFace e f' FX FS G' u •
    f_equal (fun q: C' = D' => FS (rew [P] q in u)) (eq_sym E).
Proof.
  pose (Gt := rew [fun q: C' = D' => forall t: P D',
    FX (rew [P] eq_sym q in t) = rew [P] eq_sym e in FS t] E in G).
  assert (Ht: forall t, Gt t = G' t).
  { intro t; unfold Gt.
    rewrite (homotopy_reindex_left (fun q t => FX (rew [P] eq_sym q in t))
      (fun t => rew [P] eq_sym e in FS t) E G t).
    now rewrite H, eq_trans_sym_cancel_l. }
  pose proof (map_subst (fun (q: C' = D')
    (H: forall t: P D', FX (rew [P] eq_sym q in t) = rew [P] eq_sym e in FS t) =>
      condFace e q FX FS H u) E G) as M.
  rewrite path_reindex_right in M.
  pose proof (path_suffix_solve M) as N.
  fold Gt in N.
  rewrite (condFace_congr e f' FX FS Gt G' Ht u) in N.
  now rewrite (eq_sym_map_distr (fun q: C' = D' => FS (rew [P] q in u)) E) in N.
Defined.

(** Moving a transposed identification along paths between the two ambient
    identifications: the correction terms enter at the two ends of the
    transposed path, and the hypothesis is the corresponding statement for
    the untransposed one. *)

Lemma condFaceCorr {A: Type} {P: A -> Type} {C D C' D': A}
  {e f: C = D} (E: e = f) {e' f': C' = D'} (E': e' = f')
  (FX: P C' -> P C) (FS: P D' -> P D)
  (G: forall t: P D', FX (rew [P] eq_sym e' in t) = rew [P] eq_sym e in FS t)
  (G': forall t: P D', FX (rew [P] eq_sym f' in t) = rew [P] eq_sym f in FS t)
  (HG: forall t: P D', G t
     = f_equal (fun z: C' = D' => FX (rew [P] eq_sym z in t)) E'
       • (G' t • f_equal (fun z: C = D => rew [P] eq_sym z in FS t) (eq_sym E)))
  (u: P C'):
  condFace e e' FX FS G u
  = f_equal (fun z: C = D => rew [P] z in FX u) E
    • (condFace f f' FX FS G' u
       • f_equal (fun z: C' = D' => FS (rew [P] z in u)) (eq_sym E')).
Proof.
  pose (Gmid := fun t: P D' =>
    f_equal (fun q: C' = D' => FX (rew [P] eq_sym q in t)) E' • G' t).
  refine (condFace_reindex_target E e' FX FS G Gmid _ u • _).
  - intro t; unfold Gmid.
    now rewrite <- eq_trans_assoc, <- HG.
  - apply f_equal.
    now apply (condFace_reindex_source f E' FX FS Gmid G' (fun _ => eq_refl) u).
Defined.

(** Normalize a mapped correction chain before adjoining its outer square. *)
Local Lemma map_corrected_chain {A B: Type} (f: A -> B)
  {x y z w u: A} {b: B} (K: b = f x) (eta: u = x)
  (er: f x = f u) (H: er • f_equal f eta = eq_refl)
  (p: x = y) (q: y = z) (r: z = w):
  (K • er) • f_equal f ((eta • (p • q)) • r) =
  K • f_equal f (p • (q • r)).
Proof.
  rewrite <- (eq_trans_assoc eta (p • q) r), <- (eq_trans_assoc p q r).
  rewrite eq_trans_map_distr.
  rewrite eq_trans_assoc, <- (eq_trans_assoc K er (f_equal f eta)), H.
  now rewrite eq_trans_refl_r.
Defined.

(** Assemble a square after reindexing its comparison paths.
    [Her] cancels one endpoint correction; [Hc] combines the other two,
    and naturality moves the composite through the square. *)

Lemma sqAssemble {Q1 Q2 T: Type} (FSr FSq: Q1 -> T) (Gq Gr: Q2 -> Q1)
  {X0 X1: T} (Phi: X0 = X1)
  {m1' m1: Q1} (eta: m1' = m1) {n1' n1: Q1} (eta': n1' = n1)
  (K0r: X1 = FSr m1) (K0q: X0 = FSq n1)
  (er: FSr m1 = FSr m1') (Her: er • f_equal FSr eta = eq_refl)
  (er': FSq n1 = FSq n1') (Her': er' • f_equal FSq eta' = eq_refl)
  {d2 d2': Q2} (theta: d2 = d2')
  (K1q: m1 = Gq d2) (K1r: n1 = Gr d2)
  {sq: Q1} (c1: Gq d2 = sq) (c2: sq = Gq d2') (Hc: c1 • c2 = f_equal Gq theta)
  {sr: Q1} (c1': Gr d2 = sr) (c2': sr = Gr d2')
  (Hc': c1' • c2' = f_equal Gr theta)
  (cohS: forall d: Q2, FSq (Gr d) = FSr (Gq d))
  (HSq: Phi • (K0r • f_equal FSr K1q) = K0q • (f_equal FSq K1r • cohS d2)):
  Phi • ((K0r • er) • f_equal FSr ((eta • (K1q • c1)) • c2))
  = (K0q • er') • (f_equal FSq ((eta' • (K1r • c1')) • c2') • cohS d2').
Proof.
  rewrite (eq_trans_assoc (K0q • er')
    (f_equal FSq ((eta' • (K1r • c1')) • c2')) (cohS d2')).
  rewrite (map_corrected_chain FSr K0r eta er Her K1q c1 c2),
    (map_corrected_chain FSq K0q eta' er' Her' K1r c1' c2').
  rewrite Hc, Hc'.
  rewrite (eq_trans_map_distr FSr K1q (f_equal Gq theta)),
    (eq_trans_map_distr FSq K1r (f_equal Gr theta)).
  rewrite <- 2 eq_trans_assoc.
  rewrite (f_equal_naturality Gr Gq FSq FSr cohS theta).
  pose proof (f_equal (fun p => p • f_equal FSr (f_equal Gq theta)) HSq) as H.
  cbn beta in H.
  rewrite <- 4 eq_trans_assoc in H.
  now exact H.
Defined.

(** The two facts about a correction that [sqAssemble] consumes: reading a
    map through a transport turns a path of the transported index into a
    [f_equal], so an inverse pair cancels and a composable pair fuses. *)

Lemma erCancel {T1 T2: HGpd} {C: Type} (FS: T2.(GDom) -> C)
  {z z': T1 = T2} (p: z = z') (u: T1.(GDom)):
  f_equal (fun e: T1 = T2 => FS (rew [GDom] e in u)) (eq_sym p)
  • f_equal FS (f_equal (fun e: T1 = T2 => rew [GDom] e in u) p)
  = eq_refl.
Proof.
  rewrite f_equal_compose.
  rewrite <- (eq_trans_map_distr (fun e => FS (rew [GDom] e in u))).
  now rewrite eq_trans_sym_inv_l.
Defined.

Lemma ccFuse {T1 T2: HGpd} {C: Type} (G: T2.(GDom) -> C)
  {z z' z'': T1 = T2} (p: z = z') (p': z' = z'') (u: T1.(GDom)):
  f_equal (fun e: T1 = T2 => G (rew [GDom] e in u)) p
  • f_equal (fun e: T1 = T2 => G (rew [GDom] e in u)) p'
  = f_equal G (f_equal (fun e: T1 = T2 => rew [GDom] e in u) (p • p')).
Proof.
  rewrite f_equal_compose.
  now rewrite <- (eq_trans_map_distr (fun e: T1 = T2 => G (rew [GDom] e in u)) p p').
Defined.

(** Transport in a map's fibre preserves the point and composes its
    equality witness with the path to the new base. *)

Lemma rewFibrePair {A C: Type} {pshF: C -> A} {c: C} {D0: A} (e: pshF c = D0):
  rew [fun D1: A => {cell: C &T D1 = pshF cell}] e in
    ((c; eq_refl): {cell: C &T pshF c = pshF cell})
  = (c; eq_sym e).
Proof. now destruct e. Defined.

(** Naturality, inversion, and exchange of comparison paths. *)

Lemma rewSwapSym {A: Type} (P: A -> Type) {x y: A} (c: y = x)
  {u: P x} {v: P y} (H: u = rew [P] c in v): rew [P] (eq_sym c) in u = v.
Proof.
  now exact (f_equal (fun u => rew [P] eq_sym c in u) H • rew_opp_l P c v).
Defined.

Lemma sectionPath {A B: Type} (gp: A -> B) (Cp: B -> A) (s: forall z, Cp (gp z) = z)
  {z1 z2: A} (Φ: z1 = z2):
  f_equal Cp (f_equal gp Φ) = s z1 • (Φ • eq_sym (s z2)).
Proof.
  rewrite f_equal_compose.
  pose proof (path_change_natural (fun z => Cp (gp z)) (fun z => z) s Φ) as H.
  unfold path_change in H.
  now rewrite f_equal_id in H.
Defined.

Lemma symExistTSwap {A: Type} {P: A -> Type} {x y: A} (a: x = y) {v: P x} {u: P y}
  (H: u = rew [P] a in v):
  eq_sym (=a; eq_sym H) = (=eq_sym a; rewSwapSym P a H).
Proof.
  destruct a.
  cbn in H.
  destruct H.
  now reflexivity.
Defined.

Lemma sectionPathSym {A B: Type} (gp: A -> B) (Cp: B -> A) (s: forall z, Cp (gp z) = z)
  {z1 z2: A} (Φ: z1 = z2):
  f_equal Cp (eq_sym (f_equal gp Φ)) = s z2 • (eq_sym Φ • eq_sym (s z1)).
Proof.
  rewrite eq_sym_map_distr.
  now exact (sectionPath gp Cp s (eq_sym Φ)).
Defined.

Lemma exchangeConjugate {Σ: Type} {P0 Q0 Q1 Q2 Q3 P1 Q4 P2 Q5 Q5b Q6 P3 Q7 Q8 PA PB: Σ}
  (s0: P0 = Q0) (A: Q0 = Q1) (sA: PA = Q1) (RCC: Q1 = Q2) (sB: PB = Q2)
  (B: Q3 = Q2) (s1: P1 = Q3) (piω: Q4 = Q3) (s2: P2 = Q4)
  (H1: Q4 = Q5) (H2a: Q5 = Q5b) (H2b: Q5b = Q2)
  (piε: Q6 = Q0) (s3: P3 = Q6) (Hε: Q6 = Q7) (K1: Q7 = Q8) (K2: Q8 = Q1)
  (Nω: piω • B = H1 • (H2a • H2b)) (Nε: A = eq_sym piε • (Hε • (K1 • K2))):
  ((s0 • (A • eq_sym sA)) • ((sA • (RCC • eq_sym sB)) • eq_sym (s1 • (B • eq_sym sB))))
  • ((s1 • (eq_sym piω • eq_sym s2)) • (s2 • (H1 • ((H2a • H2b) • eq_sym RCC))))
  = (s0 • (eq_sym piε • eq_sym s3)) • (s3 • (Hε • (eq_sym eq_refl • (K1 • K2)))).
Proof.
  rewrite (eq_trans_assoc H1 (H2a • H2b) (eq_sym RCC)), eq_trans_refl_l.
  change ((path_change s0 A sA •
    (path_change sA RCC sB • eq_sym (path_change s1 B sB))) •
    (path_change s1 (eq_sym piω) s2 • path_change s2 (H1 • (H2a • H2b)) RCC) =
    path_change s0 (eq_sym piε) s3 • (s3 • (Hε • (K1 • K2)))).
  rewrite path_change_sym, 4 path_change_comp.
  unfold path_change.
  rewrite <- Nω, (eq_trans_sym_cancel_l piω).
  rewrite <- 5 eq_trans_assoc.
  now rewrite (eq_trans_sym_cancel_l B), (eq_trans_sym_cancel_l s3),
    eq_trans_sym_inv_r, eq_trans_refl_r, <- Nε.
Defined.

Lemma mapThreePaths {A0 B0 C0: Type} (rho: A0 -> B0) (psi: B0 -> C0)
  {u v: A0} {x y z: B0}
  (pi: x = rho u) (delta: u = v) (a: x = y) (b: y = z) (c: z = rho v)
  (J: pi • f_equal rho delta = a • (b • c)):
  f_equal psi pi • f_equal (fun w => psi (rho w)) delta
  = f_equal psi a • (f_equal psi b • f_equal psi c).
Proof.
  rewrite <- (f_equal_compose rho psi delta).
  rewrite <- eq_trans_map_distr, J.
  now rewrite 2 eq_trans_map_distr.
Defined.

Lemma mapPathCancel {A0 B0 C0: Type} (rho: A0 -> B0) (psi: B0 -> C0)
  {u v: A0} {x y: B0} (pi: x = rho u) (delta: u = v)
  (a: x = y) (b: y = rho v)
  (J: pi • f_equal rho delta = a • b):
  f_equal (fun w => psi (rho w)) delta
  = eq_sym (f_equal psi pi) • (f_equal psi a • f_equal psi b).
Proof.
  rewrite <- (f_equal_compose rho psi delta).
  rewrite <- eq_trans_map_distr, <- J, eq_trans_map_distr.
  symmetry.
  now apply eq_trans_sym_cancel_l.
Defined.

Lemma totalPathComposeRight {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v v': P y} (p: x = y)
  (q: rew [P] p in u = v) (r: v = v'):
  (=p; q • r) = (=p; q) • (=eq_refl; r).
Proof.
  rewrite eq_trans_eq_existT_curried, sigT_trans_transport.
  cbn [rew_compose eq_sym].
  now rewrite f_equal_id, eq_trans_refl_l.
Defined.

(** Total-path forms of endpoint corrections and transported sections. *)

Lemma totalPathSectionMap {U A: Type} {P: A -> Type}
  (F: U -> A) (s: forall z, P (F z)) {x y: U} (e: x = y):
  (=f_equal F e;
    eq_sym (rew_map P F e (s x)) • f_equal_dep (fun z => P (F z)) s e) =
  f_equal (fun z => (F z; s z)) e.
Proof. destruct e. now reflexivity. Defined.

(** Mapping a total path, in the orientation used to expose the map. *)
Lemma totalPathMap {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  (=f_equal f p; sigT_map_eq g q) =
  f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) (=p; q).
Proof.
  now exact (eq_sym (f_equal_eq_existT_curried f g p q)).
Defined.

Lemma rewCorrR {A: Type} {a b0 b1: A} (h: b0 = b1) (Z: a = b1):
  rew <- [fun z: A => a = z] h in Z = Z • eq_sym h.
Proof.
  unfold eq_rect_r.
  rewrite (path_reindex_right (fun z => z) (eq_sym h) Z).
  now rewrite f_equal_id.
Qed.

Lemma sigT_trans_eq_trans_r {A: Type} {P: A -> Type} {x y z: A}
  {u: P x} {v: P y} {w w': P z} {p: x = y} (q: rew [P] p in u = v)
  {p': y = z} (r: rew [P] p' in v = w) (c: w = w'):
  q ⊙ (r • c) = (q ⊙ r) • c.
Proof.
  rewrite 2 sigT_trans_transport.
  now rewrite <- 2 eq_trans_assoc.
Qed.

Lemma corrCancelB2 {A: Type} {P: A -> Type} {xm x0 x1 x2: A} {Bt: Type}
  (pe: Bt -> P x1) {b0 b1: Bt} (hB: b0 = b1)
  {um: P xm} {beta: xm = x0} {u: P x0}
  (fp: rew [P] beta in um = u)
  {alpha: x0 = x1} (q: rew [P] alpha in u = pe b1)
  {w: P x2} {trR: x1 = x2} (Z: rew [P] trR in pe b1 = w):
  (fp ⊙ (q • eq_sym (f_equal pe hB)))
  ⊙ (rew <- [fun z: Bt => rew [P] trR in pe z = w] hB in Z)
  = (fp ⊙ q) ⊙ Z.
Proof.
  unfold eq_rect_r.
  rewrite sigT_trans_eq_trans_r.
  rewrite (path_reindex_left (fun z: Bt => rew [P] trR in pe z) (eq_sym hB) Z).
  rewrite (eq_sym_map_distr (fun z: Bt => rew [P] trR in pe z) (eq_sym hB)),
    eq_sym_involutive.
  rewrite <- (f_equal_compose pe (fun z => rew [P] trR in z) hB).
  now apply dpath_middle_cancel.
Qed.

Lemma corrCancelL {A: Type} {P: A -> Type} {x0 x1 x2: A}
  {u: P x0} {e1: x0 = x1} {pi: x1 = x2} {b0 b1: P x1} (h: b0 = b1)
  (Z: rew [P] e1 in u = b1) {w: P x2} (R: rew [P] pi in b1 = w):
  (rew <- [fun z: P x1 => rew [P] e1 in u = z] h in Z)
  ⊙ (f_equal (fun z: P x1 => rew [P] pi in z) h • R)
  = Z ⊙ R.
Proof.
  unfold eq_rect_r.
  rewrite (path_reindex_right (fun z: P x1 => z) (eq_sym h) Z), f_equal_id.
  now apply dpath_middle_cancel.
Qed.

Lemma corrCancelL2 {A: Type} {P: A -> Type} {x0 x1 x2: A} {u: P x0}
  {e1: x0 = x1} {pia: x1 = x2} {b1: P x1} (cA: b1 = rew [P] e1 in u)
  {w: P x2} (R: rew [P] pia in rew [P] e1 in u = w):
  eq_sym cA ⊙ (f_equal (fun z: P x1 => rew [P] pia in z) cA • R)
  = eq_sym (rew_compose P e1 pia u) • R.
Proof.
  pose proof (dpath_middle_cancel (P := P) (p := e1) (q := pia)
    (eq_refl: rew [P] e1 in u = rew [P] e1 in u) cA R) as H.
  rewrite eq_trans_refl_l, sigT_trans_eq_rew_l in H.
  now exact H.
Qed.

Lemma sigT_map_eq_htpy {A B: Type} {P: A -> Type} {Q: B -> Type} {f: A -> B}
  (h1 h2: forall a, P a -> Q (f a)) (Hh: forall a u, h1 a u = h2 a u)
  {x y: A} {u: P x} {v: P y} {pth: x = y} (q: rew [P] pth in u = v):
  sigT_map_eq h1 q
  = f_equal (fun z: Q (f x) => rew [Q] (f_equal f pth) in z) (Hh x u)
    • (sigT_map_eq h2 q • eq_sym (Hh y v)).
Proof.
  now exact (sigT_map_eq_homotopy h1 h2 Hh q).
Qed.

Lemma rewBaseTrans {A: Type} {P: A -> Type} {x y: A} {u: P x} {T T': P y}
  {pL pR: x = y} (HH: pL = pR) (Y: rew [P] pL in u = T) (c: T = T'):
  rew [fun r: x = y => rew [P] r in u = T'] HH in (Y • c)
  = (rew [fun r: x = y => rew [P] r in u = T] HH in Y) • c.
Proof.
  now exact (map_subst (fun π (h: rew [P] π in u = T) => h • c) HH Y).
Qed.

(** Reassociate a nested dependent pair, retaining the order of its
    three components. *)
Definition unassoc {A: Type} {L: A -> Type} {Cc: {d: A &T L d} -> Type}
  (w: {dl: {d: A &T L d} &T Cc dl}): {d: A &T {l: L d &T Cc (d; l)}} :=
  (w.1.1; (w.1.2; w.2)).

Lemma f_equal_unassoc_curried {A: Type} {L: A -> Type}
  {Cc: {d: A &T L d} -> Type} {x y: A} (a: x = y) {u: L x} {v: L y}
  (b: rew [L] a in u = v) {c: Cc (x; u)} {c': Cc (y; v)}
  (h: rew [Cc] (=a; b) in c = c'):
  f_equal (@unassoc A L Cc) (=(=a; b); h)
  = (=a; @eq_existT_curried_dep A x L Cc y a u c v c' b h).
Proof.
  destruct a. cbn in b. destruct b. cbn in h. destruct h. now reflexivity.
Defined.

Lemma pair_path_display_total {A: Type} {P: A -> Type}
  {R: {a: A &T P a} -> Type} {u v: {a: A &T P a}}
  (p: u = v) {cu: R u} {cv: R v} (hp: rew [R] p in cu = cv):
  (=projT1_eq p; pair_path_display p hp) = f_equal unassoc (=p; hp).
Proof. destruct p, hp, u as [a b]. now reflexivity. Defined.

Lemma totalPathAlignment {A: Type} {P: A -> Type}
  {x x' y: A} {e: x = y} {e': x' = y} (b: x = x')
  {v: P x} {v': P x'} {w: P y}
  (Hv: rew [P] b in v = v') (Hcoh: e = b • e')
  (h: rew [P] e' in v' = w):
  (=e; rew_align_dep b Hv Hcoh • h) = (=b; Hv) • (=e'; h).
Proof.
  rewrite eq_trans_eq_existT_curried.
  apply (eq_existT_curried_eq Hcoh).
  rewrite rewBaseAsTrans.
  unfold rew_align_dep.
  rewrite <- 2 eq_trans_assoc.
  rewrite <- (eq_sym_map_distr (fun p => rew [P] p in v) Hcoh).
  rewrite eq_trans_sym_cancel_l.
  now rewrite sigT_trans_transport.
Defined.

Lemma source_reindex_rebase {A: Type} {P: A -> Type}
  {x y: A} {e e0: x = y} (He: e = e0) {v: P x} {w z: P y}
  (c: rew [P] e0 in v = w) (h: w = z):
  rew <- [fun p => rew [P] p in v = z] He in
    path_reindex_source c h =
  path_reindex_source
    (rew <- [fun p => rew [P] p in v = w] He in c) h.
Proof. now destruct He. Defined.

Lemma totalPathAlignmentStrict {A: Type} {P: A -> Type}
  {x x' y: A} {e: x = y} {e': x' = y} (b: x = x')
  {v: P x} {v': P x'} {w: P y}
  (Hv: rew [P] b in v = v') (Hcoh: e = b • e')
  (h: rew [P] e' in v' = w):
  (=e; path_reindex_source (rew_align_dep b Hv Hcoh) h) =
    (=b; Hv) • (=e'; h).
Proof.
  now exact (f_equal (fun hh: rew [P] e in v = w => (=e; hh))
    (source_reindex_as_comp (rew_align_dep b Hv Hcoh) h)
    • totalPathAlignment b Hv Hcoh h).
Defined.

Definition section_pair_source_shift {I A: Type} {L: A -> Type}
  (f: I -> A) (l: forall i, L (f i))
  {x y: I} (E: x = y) (delta: y = x) (Hdelta: delta = eq_sym E)
  {z: A} {v: L z} (p: f x = z) (hu: rew [L] p in l x = v)
  (hm: rew [L] (f_equal f delta • p) in l y = v)
  (Hcomp: hm = f_equal_dep_sigT f l delta ⊙ hu):
  f_equal (fun i => (f i; l i)) E • (=f_equal f delta • p; hm) = (=p; hu).
Proof.
  subst delta.
  destruct E, hu, p.
  cbn in Hcomp.
  subst hm.
  now reflexivity.
Defined.

(** The successor painting is reindexed by the exact frame cancellation
    above. The combined layer and painting then have the selected source
    action followed by the ordinary successor path. *)
Lemma section_pair_source_shift_dep {I A: Type} {L: A -> Type}
  {C: {a: A &T L a} -> Type}
  (f: I -> A) (l: forall i, L (f i)) (c: forall i, C (f i; l i))
  {x y: I} (E: x = y) (delta: y = x) (Hdelta: delta = eq_sym E)
  {z: A} {v: L z} (p: f x = z) (hu: rew [L] p in l x = v)
  (hm: rew [L] (f_equal f delta • p) in l y = v)
  (Hcomp: hm = f_equal_dep_sigT f l delta ⊙ hu)
  {w: C (z; v)} (h: rew [C] (=f_equal f delta • p; hm) in c y = w):
  eq_existT_curried_dep (P := L) (Q := C) (Hu := hm) (Hv := h) =
  f_equal_dep_sigT (Q := fun a => {u: L a &T C (a; u)}) f
    (fun i => (l i; c i)) delta
  ⊙ eq_existT_curried_dep (P := L) (Q := C) (Hu := hu)
    (Hv := path_reindex_source
      (rew_align_dep (P := C)
        (f_equal (fun i => (f i; l i)) E)
        (eq_sym (rew_map C (fun i => (f i; l i)) E (c x))
          • f_equal_dep (fun i => C (f i; l i)) c E)
        (eq_sym (section_pair_source_shift f l E delta Hdelta p hu hm Hcomp))) h).
Proof.
  subst delta.
  destruct E, hu, p.
  cbn in Hcomp.
  subst hm.
  cbn [section_pair_source_shift f_equal_dep_sigT rew_align_dep
    rew_map f_equal_dep path_reindex_source f_equal eq_sym].
  now exact (eq_sym (sigT_trans_eq_refl_l
    (P := fun a => {u: L a &T C (a; u)}) eq_refl
    (eq_existT_curried_dep (P := L) (Q := C)
      (Hu := eq_refl) (Hv := h)))).
Defined.

Lemma conjShiftM {T: Type} {A B C D: T} (p1 q1: A = B) (p2 q2: B = C)
  (p3 q3: D = C): p1 = q1 -> p2 = q2 -> p3 = q3 ->
  p1 • (p2 • eq_sym p3) = q1 • (q2 • eq_sym q3).
Proof. intros H1 H2 H3. now rewrite H1, H2, H3. Defined.

(** Reindex an upper comparison along [dim]. Naturality of the
    comparison family [J] moves the resulting correction to its target. *)
Lemma canonicalUpperReindex
  {U Z W B: Type} (face: U -> Z) (read: Z -> B)
  (pair: U -> W) (restrict: W -> B)
  (J: forall u, read (face u) = restrict (pair u))
  {u v: U} (delta: u = v) {w: W}
  (K: pair u = w) (K': pair v = w)
  (K_REINDEX: K = f_equal pair delta • K')
  {z: Z} (h: z = face u) {b: B} (tail: restrict w = b):
  f_equal read (h • f_equal face delta)
    • (J v • (f_equal restrict K' • tail))
  = f_equal read h • (J u • (f_equal restrict K • tail)).
Proof.
  rewrite eq_trans_map_distr, <- eq_trans_assoc.
  rewrite (eq_trans_assoc (f_equal read (f_equal face delta)) (J v)).
  rewrite (f_equal_naturality face pair read restrict J delta).
  rewrite <- eq_trans_assoc.
  rewrite (eq_trans_assoc (f_equal restrict (f_equal pair delta))).
  now rewrite <- eq_trans_map_distr, <- K_REINDEX.
Defined.

Lemma sqAssembleGen {Xf Z Y W Σ Σ': Type} (dC: Xf -> Z) (C: Z -> Σ)
  (gω gε nuω nuε: Y -> Z) (gfB gf': Y -> W) (Ψω Ψε: W -> Σ)
  (Cw: Y -> Σ') (PsiR: Σ' -> Σ)
  (HR: forall y, PsiR (Cw y) = Ψε (gf' y))
  (gAsω: forall y, gω y = nuω y) (gAsε: forall y, gε y = nuε y)
  (cPω: forall y, C (nuω y) = Ψω (gfB y)) (cPε: forall y, C (nuε y) = Ψε (gfB y))
  (Hal: forall y, gfB y = gf' y)
  {t0 t1: Xf} (A: t0 = t1) {xε yε xω yω: Y} (Pε: xε = yε) (Pω: xω = yω)
  (B: dC t1 = gω xε) (Cc: dC t0 = gε xω) (G: gε yω = gω yε)
  (RAW: f_equal dC A • (B • f_equal gω Pε) = Cc • (f_equal gε Pω • G))
  {v: W} (Kε: gf' yε = v) {y2: Y} (gAs'': yω = y2) {w': Σ'} (cP'': Cw y2 = w')
  (XI: Ψω v = PsiR w')
  (EXCH: f_equal C G
           • (f_equal C (gAsω yε) • (cPω yε • (f_equal Ψω (Hal yε)
              • (f_equal Ψω Kε • XI))))
         = f_equal C (gAsε yω) • (cPε yω • (f_equal Ψε (Hal yω)
             • (eq_sym (HR yω) • (f_equal PsiR (f_equal Cw gAs'')
                • f_equal PsiR cP''))))):
  f_equal C (f_equal dC A)
  • (((f_equal C B • (f_equal C (gAsω xε) • cPω xε)) • f_equal Ψω (Hal xε))
     • (f_equal Ψω (f_equal gf' Pε • Kε) • XI))
  = ((f_equal C Cc • (f_equal C (gAsε xω) • cPε xω)) • f_equal Ψε (Hal xω))
    • (eq_sym (HR xω) • f_equal PsiR (f_equal Cw Pω • (f_equal Cw gAs'' • cP''))).
Proof.
  pose (Jω := fun y => f_equal C (gAsω y) • (cPω y • f_equal Ψω (Hal y))).
  pose (Jε := fun y =>
    (f_equal C (gAsε y) • (cPε y • f_equal Ψε (Hal y))) • eq_sym (HR y)).
  assert (EC: f_equal C G • (Jω yε • (f_equal Ψω Kε • XI)) =
    Jε yω • f_equal PsiR (f_equal Cw gAs'' • cP'')).
  { unfold Jω, Jε.
    rewrite eq_trans_map_distr, <- 5 eq_trans_assoc.
    now exact EXCH. }
  pose proof (square_compose
    (square_map C (RAW • eq_trans_assoc Cc (f_equal gε Pω) G))
    (EC • eq_sym (eq_trans_refl_l _))) as H.
  rewrite eq_trans_refl_r in H.
  pose proof (canonicalUpperReindex gω C gf' Ψω Jω Pε
    (f_equal gf' Pε • Kε) Kε eq_refl B XI) as Hω.
  pose proof (canonicalUpperReindex gε C Cw PsiR Jε Pω
    (f_equal Cw Pω • (f_equal Cw gAs'' • cP''))
    (f_equal Cw gAs'' • cP'') eq_refl Cc eq_refl) as Hε.
  rewrite 2 eq_trans_refl_r in Hε.
  rewrite Hω, Hε in H.
  unfold Jω, Jε in H.
  rewrite <- 5 eq_trans_assoc in H.
  rewrite <- 6 eq_trans_assoc.
  now exact H.
Defined.

(** [fEqualCompHomot] rewrites a map's action through a self-homotopy.
    [hexReindex] changes the six vertices of a hexagon along given paths. *)

Lemma fEqualCompHomot {A C: Type} (F: A -> C) (g: A -> A)
  (η: forall z, g z = z) {x y: A} (e: x = y):
  f_equal (fun z => F (g z)) e =
  f_equal F (η x) • (f_equal F e • eq_sym (f_equal F (η y))).
Proof.
  now exact (path_change_natural (fun z => F (g z)) F
    (fun z => f_equal F (η z)) e).
Defined.

Lemma hexReindex {T: Type} {v0 v1 v2 v3 v4 v5 w0 w1 w2 w3 w4 w5: T}
  (m0: v0 = w0) (m1: v1 = w1) (m2: v2 = w2) (m3: v3 = w3)
  (m4: v4 = w4) (m5: v5 = w5)
  (A: w0 = w1) (B: w1 = w2) (C: w2 = w3)
  (D: w0 = w4) (E: w4 = w5) (F: w5 = w3)
  (H: A • (B • C) = D • (E • F)):
  (m0 • (A • eq_sym m1)) • ((m1 • (B • eq_sym m2)) • (m2 • (C • eq_sym m3)))
  = (m0 • (D • eq_sym m4)) • ((m4 • (E • eq_sym m5)) • (m5 • (F • eq_sym m3))).
Proof.
  change (path_change m0 A m1 •
    (path_change m1 B m2 • path_change m2 C m3) =
    path_change m0 D m4 • (path_change m4 E m5 • path_change m5 F m3)).
  rewrite 4 path_change_comp.
  now rewrite H.
Defined.

(** Regroup the two paths at each end of a conjugated path. *)

Lemma legRegroup {T: Type} {t0 t1 t2 t3 t4 t5: T}
  (x: t0 = t1) (y: t1 = t2) (core: t2 = t3) (y': t4 = t3) (x': t5 = t4):
  x • ((y • (core • eq_sym y')) • eq_sym x')
  = (x • y) • (core • eq_sym (x' • y')).
Proof.
  now exact (path_change_nest x y core y' x').
Defined.

(** Rotation, mapping, and reindexing of path hexagons.
    [hexReindexR] leaves the right-hand composite left-associated. *)

Lemma hexRotate {T: Type} {w0 w1 w2 w3 w4 w5: T}
  (A: w0 = w1) (B: w1 = w2) (C: w2 = w3)
  (D: w0 = w4) (E: w4 = w5) (F: w5 = w3)
  (H: A • (B • C) = D • (E • F)):
  F • (eq_sym C • eq_sym B) = eq_sym E • (eq_sym D • A).
Proof.
  pose proof (square_rotate (H • eq_trans_assoc D E F)) as K.
  rewrite 2 eq_trans_sym_distr, <- eq_trans_assoc in K.
  now exact K.
Defined.

Lemma hexMap {A B: Type} (F: A -> B) {a0 a1 a2 a3 a4 a5: A}
  (A1: a0 = a1) (B1: a1 = a2) (C1: a2 = a3)
  (D1: a0 = a4) (E1: a4 = a5) (F1: a5 = a3)
  (H: A1 • (B1 • C1) = D1 • (E1 • F1)):
  f_equal F A1 • (f_equal F B1 • f_equal F C1)
  = f_equal F D1 • (f_equal F E1 • f_equal F F1).
Proof.
  rewrite <- 4 eq_trans_map_distr.
  now exact (f_equal (fun e: a0 = a3 => f_equal F e) H).
Defined.

(** Mapping a hexagon through a function and identifying its final edge. *)
Lemma hexMapProj {T U: Type} (π: T -> U) {v0 v1 v2 v3 v4 v5: T}
  (l1: v0 = v1) (l2: v1 = v2) (l3: v2 = v3)
  (l4: v0 = v4) (l5: v4 = v5) (l6: v5 = v3)
  {e: π v5 = π v3} (He: f_equal π l6 = e)
  (H: l1 • (l2 • l3) = (l4 • l5) • l6):
  f_equal π l1 • (f_equal π l2 • f_equal π l3)
  = (f_equal π l4 • f_equal π l5) • e.
Proof.
  rewrite <- He, <- 4 eq_trans_map_distr.
  now exact (f_equal (fun w => f_equal π w) H).
Defined.

Lemma legRegroupUp {T: Type} {t0 t1 t2 t3 t4 t5: T}
  (x: t0 = t1) (y: t1 = t2) (core: t2 = t3) (w: t5 = t4) (m: t4 = t3):
  x • ((y • (core • eq_sym (w • m))) • w) = (x • y) • (core • eq_sym m).
Proof.
  rewrite eq_trans_sym_distr, <- 4 eq_trans_assoc.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Defined.

Lemma legHomot2 {A B C: Type} (Φ: A -> B) (Ψ: B -> C) (G: A -> C)
  (η: forall x, Ψ (Φ x) = G x) {x y: A} (e: x = y):
  f_equal G e =
  eq_sym (η x) • (f_equal Ψ (f_equal Φ e) • eq_sym (eq_sym (η y))).
Proof.
  rewrite f_equal_compose.
  now exact (path_change_natural G (fun x => Ψ (Φ x)) (fun x => eq_sym (η x)) e).
Defined.

Lemma cancelXY {T: Type} {a b c d: T} (X: a = b) (Y: b = a) (W: a = c)
  (D: c = d) (H: X • Y = eq_refl):
  X • ((Y • W) • D) = W • D.
Proof.
  now rewrite <- eq_trans_assoc, (eq_trans_assoc X Y), H, eq_trans_refl_l.
Defined.

Lemma cancelMap {A B: Type} (π: A -> B) {a b: A} (u: a = b) (v: b = a)
  (Huv: u • v = eq_refl) {c d: B} (W: π a = c) (D: c = d):
  f_equal π u • ((f_equal π v • W) • D) = W • D.
Proof.
  refine (cancelXY _ _ _ _ _).
  now exact (eq_sym (eq_trans_map_distr π u v)
    • f_equal (fun w: a = a => f_equal π w) Huv).
Defined.

Lemma hexReindexR {T: Type} {v0 v1 v2 v3 v4 v5 w0 w1 w2 w3 w4 w5: T}
  (m0: v0 = w0) (m1: v1 = w1) (m2: v2 = w2) (m3: v3 = w3)
  (m4: v4 = w4) (m5: v5 = w5)
  (A: w0 = w1) (B: w1 = w2) (C: w2 = w3)
  (D: w0 = w4) (E: w4 = w5) (F: w5 = w3)
  (H: A • (B • C) = D • (E • F)):
  (m0 • (A • eq_sym m1)) • ((m1 • (B • eq_sym m2)) • (m2 • (C • eq_sym m3)))
  = ((m0 • (D • eq_sym m4)) • (m4 • (E • eq_sym m5)))
    • (m5 • (F • eq_sym m3)).
Proof.
  now exact (hexReindex m0 m1 m2 m3 m4 m5 A B C D E F H
    • eq_trans_assoc _ _ _).
Defined.

(** A hexagon follows from six edge presentations and a hexagon between
    the reindexed edges. *)
Lemma hexPaste6 {T: Type} {v0 v1 v2 v3 v4 v5 w0 w1 w2 w3 w4 w5: T}
  {m0: v0 = w0} {m1: v1 = w1} {m2: v2 = w2} {m3: v3 = w3}
  {m4: v4 = w4} {m5: v5 = w5}
  {A: w0 = w1} {B: w1 = w2} {C: w2 = w3}
  {D: w0 = w4} {E: w4 = w5} {F: w5 = w3}
  {l1: v0 = v1} {l2: v1 = v2} {l3: v2 = v3}
  {l4: v0 = v4} {l5: v4 = v5} {l6: v5 = v3}
  (H1: l1 = m0 • (A • eq_sym m1)) (H2: l2 = m1 • (B • eq_sym m2))
  (H3: l3 = m2 • (C • eq_sym m3)) (H4: l4 = m0 • (D • eq_sym m4))
  (H5: l5 = m4 • (E • eq_sym m5)) (H6: l6 = m5 • (F • eq_sym m3))
  (H: A • (B • C) = D • (E • F)):
  l1 • (l2 • l3) = (l4 • l5) • l6.
Proof.
  rewrite H1, H2, H3, H4, H5, H6.
  now exact (hexReindexR m0 m1 m2 m3 m4 m5 A B C D E F H).
Defined.

(** Pasting a hexagon with a square that reindexes three of its vertices:
    the composite of the two is the hexagon read at the new vertices. *)

Lemma hexDimGlue {T: Type} {v0 v1 v2 v3 v4 v5 w1 w2 u1 u2: T}
  (P: v0 = v1) (Q1: v1 = v2) (Q2: v2 = v3) (R1: v0 = v4) (R2: v4 = v5)
  (K: v5 = v3) (d1: v3 = w1) (d2: w1 = w2) (e1: v5 = u1) (e2: u1 = u2)
  (K': u2 = w2)
  (H1: P • (Q1 • Q2) = (R1 • R2) • K)
  (H2: K • (d1 • d2) = (e1 • e2) • K'):
  P • ((Q1 • (Q2 • d1)) • d2) = ((R1 • (R2 • e1)) • e2) • K'.
Proof.
  pose proof (square_compose H1 H2) as H.
  rewrite <- 4 eq_trans_assoc in H.
  rewrite <- 5 eq_trans_assoc.
  now exact H.
Defined.

(** Replace four hexagon edges along identifications of their source
    points, retaining the two other edges. *)
Polymorphic Lemma hex_replace_four
  {A T: Type} {F G: A -> T}
  {aq0 aq1 aq2 ar0 ar1: A} {v0 v1: T}
  {P: v0 = v1}
  {Dr Dr': v1 = F aq0} {Uq Uq': aq0 = aq1} {I: aq1 = aq2}
  {Dq Dq': v0 = G ar0} {Ur Ur': ar0 = ar1}
  {K: G ar1 = F aq2}
  (HDr: Dr = Dr') (HUq: Uq = Uq')
  (HDq: Dq = Dq') (HUr: Ur = Ur')
  (H: P • (Dr' • f_equal F (Uq' • I)) =
    (Dq' • f_equal G Ur') • K):
  P • (Dr • f_equal F (Uq • I)) =
  (Dq • f_equal G Ur) • K.
Proof.
  now rewrite HDr, HUq, HDq, HUr.
Qed.

(** Combine replacement of four hexagon edges with the endpoint
    corrections induced by a homotopy between their maps. *)
Polymorphic Lemma hex_transport_glue
  {A T: Type} {F G: A -> T}
  {aq0 aq1 aq2 aq3 ar0 ar1 ar2: A}
  {v0 v1 v2 v3 v4 v5: T}
  {P: v0 = v1} {Q1: v1 = v2} {Q2: v2 = v3}
  {R1: v0 = v4} {R2: v4 = v5} {K: v5 = v3}
  {Dr: v1 = F aq0} {uq: aq0 = aq1} {iq: aq1 = aq2}
  {Uq: aq0 = aq2} {iqs: aq2 = aq3} {iq': aq1 = aq3}
  {Dq: v0 = G ar0} {ur: ar0 = ar1} {ir: ar1 = ar2}
  {Ur: ar0 = ar2}
  {Dr': v2 = F aq1} {d1: v3 = F aq1}
  {Dq': v4 = G ar1} {e1: v5 = G ar1}
  {K': G ar2 = F aq3}
  (HUq: Uq = uq • iq) (HIq: iq • iqs = iq')
  (HUr: Ur = ur • ir)
  (HNatL: Dr • f_equal F uq = Q1 • Dr')
  (HAtL: Dr' = Q2 • d1)
  (HNatR: Dq • f_equal G ur = R1 • Dq')
  (HAtR: Dq' = R2 • e1)
  (Hhex: P • (Q1 • Q2) = (R1 • R2) • K)
  (Hdim: K • (d1 • f_equal F iq') =
    (e1 • f_equal G ir) • K'):
  P • (Dr • f_equal F (Uq • iqs)) =
  (Dq • f_equal G Ur) • K'.
Proof.
  rewrite HUq, <- eq_trans_assoc, HIq, eq_trans_map_distr.
  rewrite HUr, eq_trans_map_distr.
  rewrite (eq_trans_assoc Dr (f_equal F uq) (f_equal F iq')).
  rewrite (eq_trans_assoc Dq (f_equal G ur) (f_equal G ir)).
  rewrite HNatL, HNatR, HAtL, HAtR.
  now exact (hexDimGlue P Q1 Q2 R1 R2 K d1
    (f_equal F iq') e1 (f_equal G ir) K' Hhex Hdim).
Qed.

(** A [rew_cohLayer_hex] core evaluated at a section can instead use
    [unit] as its source fibre and the section as its fibre map. The
    section's action on [C2] becomes a leading endpoint correction. *)

Lemma rew_cohLayer_hex_sec {T1 T2 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfF: T2 -> X} {rfG: T3 -> X}
  (sec: forall mm, P (rfF mm))
  (G: forall n, S3 n -> P (rfG n))
  {d1 d2: T1} (E1: d1 = d2) {m1 m2: T2} (C2: m1 = m2)
  {n1 n2: T3} (D2: n1 = n2)
  (C1: rfF m2 = rf0 d1) (D1: rfG n2 = rf0 d2) (K: rfF m1 = rfG n1)
  {aR: S3 n1}
  (HC: rew [P] K in sec m1 = G n1 aR)
  (Hpath: f_equal rfF C2 • (C1 • f_equal rf0 E1) = K • (f_equal rfG D2 • D1)):
  rew_cohLayer_hex P rf0 (fun _ a => a) G E1 C2 D2 C1 D1 K
    (sec m1) aR HC Hpath
  = f_equal (fun x => rew [fun d => P (rf0 d)] E1 in rew [P] C1 in x)
      (f_equal_dep (fun mm => P (rfF mm)) sec C2)
    • rew_cohLayer_hex P rf0 (fun (z: T2) (_: unit) => sec z) G
        E1 C2 D2 C1 D1 K tt aR HC Hpath.
Proof.
  destruct C2.
  cbn [f_equal_dep f_equal].
  now rewrite eq_trans_refl_l.
Defined.

(** The groupoid step that turns the correction moved out by
    [rew_cohLayer_hex_sec] into a cancellation: a five-factor chain whose first
    factor has picked up [f_equal g (f_equal h (eq_sym D))] and whose core has
    picked up [f_equal (g ∘ h) D] is the chain without either. *)

Lemma cancel_fequal_sym {A B C: Type} (g: B -> C) (h: A -> B)
  {x y: A} (D: x = y)
  {W: C} (a: W = g (h y)) {Z: C} (v: g (h y) = Z) {U: C} (uu: Z = U):
  (a • f_equal g (f_equal h (eq_sym D)))
    • (eq_refl • ((f_equal (fun t => g (h t)) D • v) • uu))
  = a • (eq_refl • (v • uu)).
Proof.
  rewrite eq_trans_refl_l.
  rewrite f_equal_compose, <- (eq_sym_map_distr (fun t => g (h t)) D).
  rewrite <- 2 eq_trans_assoc, eq_trans_sym_cancel_l.
  now rewrite eq_trans_refl_l.
Defined.

(** The dual bookkeeping step: a chain whose first factor is the action of a
    map on a composite correction, followed by a unit, is the same chain with
    the two halves of that correction in consecutive slots. *)

Lemma split_fequal_assoc {A B C: Type} (g: B -> C) (h: A -> B)
  {N: B} {x y: A} (kc0: N = h x) (kbP: x = y)
  {Z: C} (Cc: g (h y) = Z) {U: C} (V: Z = U):
  f_equal g (kc0 • f_equal h kbP) • (eq_refl • (Cc • V))
  = f_equal g kc0 • (f_equal (fun t => g (h t)) kbP • (Cc • V)).
Proof.
  now rewrite eq_trans_map_distr, f_equal_compose, eq_trans_refl_l,
    <- eq_trans_assoc.
Defined.

(** Generic path algebra: a section reads a conjugated rebuilt square. *)
Lemma readRebuildSquare {U V: Type} (rebuild: U -> V) (read: V -> U)
  (sec: forall u, read (rebuild u) = u)
  {a b c d: U} (alpha: a = b) (core: b = c) (beta: d = c):
  f_equal read
    (f_equal rebuild alpha
      • (f_equal rebuild core • eq_sym (f_equal rebuild beta)))
    • (sec d • beta)
  = sec a • (alpha • core).
Proof.
  rewrite (eq_sym_map_distr rebuild beta), <- 2 eq_trans_map_distr.
  pose proof (eq_trans_natural (fun u => read (rebuild u)) (fun u => u)
    sec (alpha • (core • eq_sym beta))) as H.
  rewrite <- f_equal_compose, f_equal_id in H.
  rewrite eq_trans_assoc, H, <- 3 eq_trans_assoc.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Defined.

(** Paste a square of paths with a square of comparisons under [read].
    The two mapped side paths cancel, leaving the outer path conjugated
    by the endpoint comparisons and the inverse local square. *)
Lemma pasteReadSquares
  {Z B: Type} (read: Z -> B)
  {z0 z1 v0 v1: Z}
  (outer: z0 = z1) (left: z0 = v0) (right: z1 = v1)
  (core: v0 = v1)
  (PREFIX: outer • right = left • core)
  {b0 b1 d0 d1: B}
  (j0: read v0 = b0) (j1: read v1 = b1)
  (k0: b0 = d0) (k1: b1 = d1) (coh: d0 = d1)
  (LOCAL: f_equal read core • (j1 • k1)
    = j0 • (k0 • coh)):
  f_equal read outer
    • (f_equal read right • (j1 • (k1 • eq_sym coh)))
  = f_equal read left • (j0 • k0).
Proof.
  pose proof (square_compose (square_map read PREFIX) LOCAL) as H.
  rewrite <- eq_trans_assoc in H.
  apply (f_equal (fun p => p • eq_sym coh)) in H.
  rewrite <- 6 eq_trans_assoc in H.
  rewrite eq_trans_sym_inv_r, eq_trans_refl_r in H.
  now exact H.
Defined.

(** Assemble a comparison square from a descent square, a square
    under [read], and a local square. The two matching hypotheses
    identify the upper comparisons after applying [deep]. *)
Lemma canonicalSquareOfPrefix
  {Xf Z Y W B: Type}
  (desc: Xf -> Z) (read: Z -> B) (deep pair: Y -> W)
  (readDeep: forall y, pair y = deep y)
  (g_o g_e: Y -> Z) (n_o n_e: W -> Z) (r_o r_e: W -> B)
  (sec_o: forall w, read (n_o w) = r_o w)
  (sec_e: forall w, read (n_e w) = r_e w)
  (alpha_o: forall y, g_o y = n_o (deep y))
  (alpha_e: forall y, g_e y = n_e (deep y))
  {t0 t1: Xf} (h: t0 = t1)
  {x_e y_e x_o y_o: Y} (p_e: x_e = y_e) (p_o: x_o = y_o)
  (b_o: desc t1 = g_o x_e) (b_e: desc t0 = g_e x_o)
  (G: g_e y_o = g_o y_e)
  (RAW: f_equal desc h • (b_o • f_equal g_o p_e)
    = b_e • (f_equal g_e p_o • G))
  {z_e z_o: Y} (u_e: y_e = z_e) (u_o: y_o = z_o)
  (Glocal: n_e (deep z_o) = n_o (deep z_e))
  (PREFIX:
    G • (alpha_o y_e • f_equal (fun y => n_o (deep y)) u_e)
    = (alpha_e y_o • f_equal (fun y => n_e (deep y)) u_o) • Glocal)
  {w_e w_o: W} (d_e: deep z_e = w_e) (d_o: deep z_o = w_o)
  (coh: r_e w_o = r_o w_e)
  (LOCAL: f_equal read Glocal • (sec_o (deep z_e) • f_equal r_o d_e)
    = sec_e (deep z_o) • (f_equal r_e d_o • coh))
  (K_e: pair x_e = w_e) (K_o: pair x_o = w_o)
  (MATCH_e: eq_sym (readDeep x_e) • K_e
    = f_equal deep (p_e • u_e) • d_e)
  (MATCH_o: eq_sym (readDeep x_o) • K_o
    = f_equal deep (p_o • u_o) • d_o):
  f_equal read (f_equal desc h)
    • ((f_equal read b_o
        • (f_equal read (alpha_o x_e)
           • (sec_o (deep x_e) • f_equal r_o (eq_sym (readDeep x_e)))))
       • (f_equal r_o K_e • eq_sym coh))
  = (f_equal read b_e
      • (f_equal read (alpha_e x_o)
         • (sec_e (deep x_o) • f_equal r_e (eq_sym (readDeep x_o)))))
    • f_equal r_e K_o.
Proof.
  pose proof (square_compose
    (RAW • eq_trans_assoc b_e (f_equal g_e p_o) G) PREFIX) as HP.
  rewrite <- (f_equal_compose deep n_o u_e),
    <- (f_equal_compose deep n_e u_o) in HP.
  rewrite <- (f_equal_naturality (fun y => y) deep g_o n_o alpha_o u_e),
    <- (f_equal_naturality (fun y => y) deep g_e n_e alpha_e u_o) in HP.
  rewrite 2 f_equal_id in HP.
  rewrite <- 4 eq_trans_assoc in HP.
  rewrite (eq_trans_assoc (f_equal g_o p_e) (f_equal g_o u_e)),
    (eq_trans_assoc (f_equal g_e p_o) (f_equal g_e u_o)) in HP.
  rewrite <- 2 eq_trans_map_distr in HP.
  rewrite (eq_trans_assoc (f_equal g_e (p_o • u_o)) (alpha_e z_o)),
    (eq_trans_assoc b_e (f_equal g_e (p_o • u_o) • alpha_e z_o)) in HP.
  pose proof (pasteReadSquares read (f_equal desc h)
    (b_e • (f_equal g_e (p_o • u_o) • alpha_e z_o))
    (b_o • (f_equal g_o (p_e • u_e) • alpha_o z_e))
    Glocal HP (sec_e (deep z_o)) (sec_o (deep z_e))
    (f_equal r_e d_o) (f_equal r_o d_e) coh LOCAL) as H.
  rewrite (eq_trans_map_distr read b_o),
    (eq_trans_map_distr read (f_equal g_o (p_e • u_e))),
    (eq_trans_map_distr read b_e),
    (eq_trans_map_distr read (f_equal g_e (p_o • u_o))) in H.
  rewrite <- 4 eq_trans_assoc in H.
  pose (J_o := fun y => f_equal read (alpha_o y) • sec_o (deep y)).
  pose (J_e := fun y => f_equal read (alpha_e y) • sec_e (deep y)).
  pose proof (canonicalUpperReindex g_o read deep r_o J_o
    (p_e • u_e) (f_equal deep (p_e • u_e) • d_e) d_e eq_refl
    b_o (eq_sym coh)) as Ho.
  pose proof (canonicalUpperReindex g_e read deep r_e J_e
    (p_o • u_o) (f_equal deep (p_o • u_o) • d_o) d_o eq_refl
    b_e eq_refl) as He.
  unfold J_o in Ho; unfold J_e in He.
  rewrite eq_trans_map_distr, <- 3 eq_trans_assoc in Ho.
  rewrite eq_trans_map_distr, <- 3 eq_trans_assoc in He.
  rewrite 2 eq_trans_refl_r in He.
  rewrite Ho, He in H.
  rewrite <- MATCH_e, <- MATCH_o in H.
  rewrite 2 eq_trans_map_distr, <- eq_trans_assoc in H.
  rewrite <- 6 eq_trans_assoc.
  now exact H.
Defined.











(** Selected comparison cells and their dependent witnesses. *)

Definition restriction_index_cell {U V W: Type}
  (d: U -> V) (tr: V -> W) {u0 u1: U} (e: u0 = u1) {z: V}
  (c0: d u0 = z) (c1: d u1 = z)
  (C: c0 = f_equal d e • c1):
  f_equal tr c0 = f_equal tr (f_equal d e) • f_equal tr c1 :=
  f_equal (fun c => f_equal tr c) C • eq_trans_map_distr tr (f_equal d e) c1.

Definition restriction_naturality_cell {U V W: Type}
  (f: U -> W) (d: U -> V) (tr: V -> W)
  (alpha: forall u, f u = tr (d u)) {u0 u1: U} (e: u0 = u1):
  alpha u0 • f_equal tr (f_equal d e) = f_equal f e • alpha u1 :=
  eq_sym (f_equal_naturality f d (fun w => w) tr alpha e)
    • f_equal (fun q => q • alpha u1) (f_equal_id (f_equal f e)).

(** This choice pastes the index comparison, the naturality square, and
    the previous restriction square in the order used by its dependent lift. *)
Definition restriction_step_cell {U V W: Type}
  (f: U -> W) (d: U -> V) (tr: V -> W)
  (alpha: forall u, f u = tr (d u))
  {u0 u1: U} (e: u0 = u1) {z: V}
  (c0: d u0 = z) (c1: d u1 = z)
  (C: c0 = f_equal d e • c1)
  {a b: W} (a0: tr z = b) (b0: f u1 = a) (r: a = b)
  (Qprev: (alpha u1 • f_equal tr c1) • a0 = b0 • r):
  (alpha u0 • f_equal tr c0) • a0 = (f_equal f e • b0) • r :=
  let m := f_equal tr (f_equal d e) in
  let n := f_equal tr c1 in
  f_equal (fun q => (alpha u0 • q) • a0) (restriction_index_cell d tr e c0 c1 C)
  • (eq_sym (eq_trans_assoc (alpha u0) (m • n) a0)
  • (f_equal (eq_trans (alpha u0)) (eq_sym (eq_trans_assoc m n a0))
  • square_compose (restriction_naturality_cell f d tr alpha e)
      (eq_trans_assoc (alpha u1) n a0 • Qprev))).

Definition DPathBaseCell {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} {p q: x = y}
  (_: rew [P] p in u = v) (_: rew [P] q in u = v): Type := p = q.

Definition DPathCellOver {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y} {p q: x = y}
  (h: rew [P] p in u = v) (k: rew [P] q in u = v)
  (K: DPathBaseCell h k): Type :=
  rew [fun e => rew [P] e in u = v] K in h = k.

Definition DPathTotal {A: Type} {P: A -> Type} {x y: A}
  {u: P x} {v: P y} {p: x = y} (h: rew [P] p in u = v):
  (x; u) = (y; v) := (=p; h).

(** Map a path of dependent pairs through its chosen component encoding. *)
Definition sigT_total_map_cell {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  {u v: {a: A &T P a}} (p: u = v):
  f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) p =
  (=f_equal f (projT1_eq p); sigT_map_eq (P := P) (Q := Q) (f := f) g (projT2_eq p)) :=
  f_equal (fun q => f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) q)
    (eq_sym (totalPathReencode p))
  • f_equal_eq_existT_curried (P := P) (Q := Q) f g (projT1_eq p) (projT2_eq p).

(** The selected total cell names its two route encodings and its base and
    displayed comparison. *)
Definition sigT_route_cell {A: Type} {P: A -> Type} {x y: A}
  {u: P x} {v: P y} {l r: ((x; u): {a: A &T P a}) = (y; v)}
  {p q: x = y} {hl: rew [P] p in u = v} {hr: rew [P] q in u = v}
  (EL: l = (=p; hl)) (ER: r = (=q; hr))
  (K: p = q) (HK: rew [fun e => rew [P] e in u = v] K in hl = hr): l = r :=
  EL • (eq_existT_curried_eq (P := P) K HK • eq_sym ER).

(** The next component is assembled over [sigT_route_cell] itself. *)
Definition sigT_route_lift_result {A: Type} {P: A -> Type}
  (R: {a: A &T P a} -> Type) {x y: A} {u: P x} {v: P y}
  {l r: ((x; u): {a: A &T P a}) = (y; v)}
  {p q: x = y} {hl: rew [P] p in u = v} {hr: rew [P] q in u = v}
  (EL: l = (=p; hl)) (ER: r = (=q; hr))
  (K: p = q) (HK: rew [fun e => rew [P] e in u = v] K in hl = hr)
  {a: R (x; u)} {b: R (y; v)}
  (vl: rew [R] l in a = b) (vr: rew [R] r in a = b): Type :=
  rew [fun e: x = y => rew [fun x => {u: P x &T R (x; u)}] e in
      (u; a) = (v; b)] K in
    @eq_existT_curried_dep A x P R y p u a v b hl
      (rew [fun e => rew [R] e in a = b] EL in vl) =
  @eq_existT_curried_dep A x P R y q u a v b hr
      (rew [fun e => rew [R] e in a = b] ER in vr).

Lemma sigT_route_cell_dep {A: Type} {P: A -> Type}
  (R: {a: A &T P a} -> Type) {x y: A} {u: P x} {v: P y}
  {l r: ((x; u): {a: A &T P a}) = (y; v)}
  {p q: x = y} {hl: rew [P] p in u = v} {hr: rew [P] q in u = v}
  (EL: l = (=p; hl)) (ER: r = (=q; hr))
  (K: p = q) (HK: rew [fun e => rew [P] e in u = v] K in hl = hr)
  {a: R (x; u)} {b: R (y; v)}
  (vl: rew [R] l in a = b) (vr: rew [R] r in a = b)
  (HH: rew [fun e => rew [R] e in a = b] sigT_route_cell EL ER K HK in vl = vr):
  rew [fun e: x = y => rew [fun x => {u: P x &T R (x; u)}] e in
      (u; a) = (v; b)] K in
    @eq_existT_curried_dep A x P R y p u a v b hl
      (rew [fun e => rew [R] e in a = b] EL in vl) =
  @eq_existT_curried_dep A x P R y q u a v b hr
      (rew [fun e => rew [R] e in a = b] ER in vr).
Proof.
  apply (eq_existT_curried_dep_eq (P := P) (Q := R) K HK).
  now exact (rew_conjugate (fun e => rew [R] e in a = b)
    EL (eq_existT_curried_eq (P := P) K HK) ER vl vr HH).
Defined.

(** Reindex a displayed path along a mapped base path. The identity
    case returns the supplied displayed path directly. *)
Definition sigT_unmap_eq {X Y: Type} (P: Y -> Type) (f: X -> Y)
  {x y: X} (p: x = y) {u: P (f x)} {v: P (f y)}
  (h: rew [P] f_equal f p in u = v):
  rew [fun x => P (f x)] p in u = v.
Proof. destruct p. now exact h. Defined.

Lemma sigT_unmap_eq_map {X Y: Type} (P: Y -> Type) (f: X -> Y)
  {x y: X} (p: x = y) {u: P (f x)} {v: P (f y)}
  (h: rew [P] f_equal f p in u = v):
  sigT_map_eq (Q := P) (fun _ u => u) (sigT_unmap_eq P f p h) = h.
Proof.
  destruct p. cbn [sigT_unmap_eq].
  now rewrite sigT_map_eq_refl, f_equal_id.
Defined.

Definition residueFill {Y T1 D: Type} (P: T1 -> Type) {Dp: D -> Type}
  (r: Y -> T1) (phi: D -> T1) (pe: forall d, Dp d -> P (phi d))
  {y1 y2: Y} (E: y1 = y2)
  {a: T1} (w: P a) (e1: a = r y1)
  {c1: D} (a2: a = phi c1) {v1: Dp c1}
  {c2: D} {n: Dp c2} (hp: ((c1; v1): {d: D &T Dp d}) = (c2; n))
  (trR: phi c2 = r y2)
  (hr: (a2 • f_equal phi (projT1_eq hp)) • trR = e1 • f_equal r E)
  (fp: rew [P] a2 in w = pe c1 v1):
  rew [fun y => P (r y)] E in rew [P] e1 in w = rew [P] trR in pe c2 n :=
  sigT_unmap_eq P r E
    (sigT_square_fill (eq_sym hr) eq_refl
      (fp ⊙ sigT_map_eq pe (projT2_eq hp)) eq_refl).

Lemma residueFill_boundary {Y T1 D: Type} (P: T1 -> Type) {Dp: D -> Type}
  (r: Y -> T1) (phi: D -> T1) (pe: forall d, Dp d -> P (phi d))
  {y1 y2: Y} (E: y1 = y2)
  {a: T1} (w: P a) (e1: a = r y1)
  {c1: D} (a2: a = phi c1) {v1: Dp c1}
  {c2: D} {n: Dp c2} (hp: ((c1; v1): {d: D &T Dp d}) = (c2; n))
  (trR: phi c2 = r y2)
  (hr: (a2 • f_equal phi (projT1_eq hp)) • trR = e1 • f_equal r E)
  (fp: rew [P] a2 in w = pe c1 v1):
  rew [fun edge => rew [P] edge in w = rew [P] trR in pe c2 n] hr in
    ((fp ⊙ sigT_map_eq pe (projT2_eq hp)) ⊙ eq_refl) =
  eq_refl ⊙ sigT_map_eq (Q := P) (fun _ u => u)
    (residueFill P r phi pe E w e1 a2 hp trR hr fp).
Proof.
  unfold residueFill. rewrite sigT_unmap_eq_map.
  pose proof (sigT_square_fill_boundary (eq_sym hr) eq_refl
    (fp ⊙ sigT_map_eq pe (projT2_eq hp)) eq_refl) as H.
  rewrite <- H.
  now exact (rew_opp_r _ hr _).
Defined.

(** Convert an endpoint-corrected displayed path through a reindexed family.
    This keeps its central displayed edge opaque. *)
Lemma convP_change {X Y: Type} (P: Y -> Type) (r: X -> Y)
  {x y: X} (E: x = y) {u u': P (r x)} {v v': P (r y)}
  (cA: u' = u) (h: rew [fun x => P (r x)] E in u = v) (cB: v = v'):
  eq_sym (rew_map P r E u')
    • (f_equal (fun u => rew [fun x => P (r x)] E in u) cA • (h • cB)) =
  f_equal (fun u => rew [P] f_equal r E in u) cA •
    (sigT_map_eq (Q := P) (fun _ u => u) h • cB).
Proof.
  refine (eq_sym (sigT_map_eq_id (P := P) r
    (f_equal (fun u => rew [fun x => P (r x)] E in u) cA • (h • cB))) • _).
  pose proof (dpath_change_map (Q := P) (f := r) (fun _ u => u)
    cA (eq_sym cB) h) as H.
  unfold dpath_change in H.
  rewrite 2 f_equal_id, eq_sym_involutive in H.
  now exact H.
Defined.

(** Separate the terminal fibre path from the preceding base transport. *)
Lemma sigT_trans_eq_finish {A: Type} {P: A -> Type}
  {x y z: A} {p: x = y} {u: P x} {v: P y}
  (h: rew [P] p in u = v) (q: y = z) {w: P z}
  (c: rew [P] q in v = w):
  h ⊙ c = (h ⊙ (eq_refl: rew [P] q in v = rew [P] q in v)) • c.
Proof.
  rewrite <- (sigT_trans_eq_trans_r h
    (eq_refl: rew [P] q in v = rew [P] q in v) c).
  now rewrite eq_trans_refl_l.
Defined.
