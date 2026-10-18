From Bonak Require Import Notation.

Set Primitive Projections.
Set Printing Projections.

Record sigT {A: Type} (P: A -> Type): Type :=
  existT { projT1: A; projT2: P projT1 }.

Arguments sigT {A} P.
Arguments projT1 {A P} _.
Arguments projT2 {A P} _.
Arguments existT {A} P _ _.

Set Warnings "-notation-overridden".

Notation "{ x &T P }" := (sigT (fun x => P%type))
  (x at level 99, format "{ '[ ' x  &T  '/' P ']' }"): type_scope.
Notation "{ x : A &T P }" := (sigT (A := A) (fun x => P%type))
  (x at level 99, format "{ '[ ' '[' x  :  A ']'  &T  '/' P ']' }"): type_scope.
Notation "( x 'as' z 'in' T ; y 'in' P )" := (existT (fun z: T => P%type) x y)
  (at level 0, only parsing).
Notation "( x ; y )" := (existT _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

Import Logic.EqNotations.

Definition eq_existT_uncurried {A: Type} {P: A -> Type} {u1 v1: A}
  {u2: P u1} {v2: P v1} (pq: { p: u1 = v1 &T rew p in u2 = v2 }):
  (u1; u2) = (v1; v2).
Proof.
  now destruct pq as [p q], q, p.
Defined.

Definition eq_sigT_uncurried {A: Type} {P: A -> Type} (u v: { a: A &T P a })
  (pq: { p: u.1 = v.1 &T rew p in u.2 = v.2 }): u = v.
Proof.
  destruct u, v; now apply eq_existT_uncurried.
Defined.

Lemma eq_existT_curried {A: Type} {P: A -> Type} {u1 v1: A} {u2: P u1}
  {v2: P v1} (p: u1 = v1) (q: rew p in u2 = v2): (u1; u2) = (v1; v2).
Proof.
  apply eq_sigT_uncurried; now exists p.
Defined.

Definition projT1_eq {A} {P: A -> Type} {u v: { a: A &T P a }} (p: u = v):
  u.1 = v.1 := f_equal (fun x => x.1) p.

Definition projT2_eq {A} {P: A -> Type} {u v: { a: A &T P a }} (p: u = v):
  rew projT1_eq p in u.2 = v.2 := rew dependent p in eq_refl.

Notation "(= u ; v )" := (eq_existT_curried u v)
  (at level 0, format "(= u ;  '/  ' v )").

Lemma eq_existT_curried_dep {A x} {P: A -> Type} {Q: {a &T P a} -> Type}
   {y} {H: x = y}
   {u: P x} {v: Q (x; u)}
   {u': P y} {v': Q (y; u')}
   {Hu: rew H in u = u'} {Hv: rew (=H; Hu) in v = v'}:
   rew [fun x => {a: P x &T Q (x; a)}] H in (u; v) = (u'; v').
Proof.
   now destruct Hu, Hv, H.
Defined.

Lemma eq_existT_curried_eq {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {p p': x = y}
  {q: rew [P] p in u = v} {q': rew [P] p' in u = v}
  (Hp: p = p')
  (Hq: rew [fun r => rew [P] r in u = v] Hp in q = q'):
  (= p; q) = (= p'; q').
Proof.
  destruct Hp; simpl in Hq. now destruct Hq.
Defined.

Lemma eq_existT_curried_dep_eq {A x y} {P: A -> Type}
  {Q: {a &T P a} -> Type}
  {H H': x = y}
  {u: P x} {v: Q (x; u)}
  {u': P y} {v': Q (y; u')}
  {Hu: rew [P] H in u = u'} {Hu': rew [P] H' in u = u'}
  {Hv: rew [Q] (=H; Hu) in v = v'}
  {Hv': rew [Q] (=H'; Hu') in v = v'}
  (HH: H = H')
  (HHu: rew [fun H => rew [P] H in u = u'] HH in Hu = Hu')
  (HHv: rew [fun p => rew [Q] p in v = v']
    eq_existT_curried_eq HH HHu in Hv = Hv'):
  rew [fun H => rew [fun x => {a: P x &T Q (x; a)}] H in
    (u; v) = (u'; v')] HH in
  @eq_existT_curried_dep A x P Q y H u v u' v' Hu Hv =
  @eq_existT_curried_dep A x P Q y H' u v u' v' Hu' Hv'.
Proof.
  destruct HH; cbn in HHu. destruct HHu; cbn in HHv.
  now destruct HHv.
Defined.

Definition sigT_map_eq {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v):
  rew [Q] f_equal f p in g x u = g y v.
Proof.
  now destruct q, p.
Defined.

(** Transport a lifted path before or after applying its dependent map. *)
Lemma sigT_map_eq_transport {X Y: Type} {P: X->Type} {Q: Y->Type}
  {f: X->Y} (F: forall x, P x -> Q (f x))
  {x y: X} {p q: x=y} (H: p=q) {u: P x} {v: P y}
  (h: rew [P] p in u=v):
  rew [fun e=>rew [Q] e in F x u=F y v]
    f_equal (fun e=>f_equal f e) H in sigT_map_eq F h =
  sigT_map_eq F (rew [fun e=>rew [P] e in u=v] H in h).
Proof.
  now destruct H.
Defined.

Lemma sigT_map_eq_refl {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x: A} {u v: P x} (q: u = v):
  sigT_map_eq g (p := eq_refl) q = f_equal (g x) q.
Proof.
  now destruct q.
Defined.

(** Mapping the first component of a dependent pair path forgets its second component. *)
Lemma sigT_map_eq_fst {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {R: forall x, P x -> Type} {f: X -> Y} (g: forall x, P x -> Q (f x))
  {x y: X} {p: x = y} {a: P x} {b: P y}
  {h: rew [P] p in a = b} {v: R x a} {w: R y b}
  (k: rew [fun z: {x: X &T P x} => R z.1 z.2] (= p; h) in
    (v: (fun z: {x: X &T P x} => R z.1 z.2) (x; a)) = w):
  sigT_map_eq (P := fun x => {a: P x &T R x a}) (fun x z => g x z.1)
    (eq_existT_curried_dep (Q := fun z => R z.1 z.2) (H := p) (Hu := h) (Hv := k)) =
  sigT_map_eq g h.
Proof.
  now destruct p, h, k.
Defined.

Lemma f_equal_eq_existT_curried {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y}
  (p: x = y) (q: rew [P] p in u = v):
  f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) (= p; q) =
  (= f_equal f p; sigT_map_eq g q).
Proof.
  now destruct q, p.
Defined.

Lemma sigT_map_eq_existT_curried_dep_curried {A B: Type} {P: A -> Type}
  {R: forall a, P a -> Type} {P': B -> Type}
  {R': forall b, P' b -> Type}
  (f: A -> B) (g: forall a, P a -> P' (f a))
  (h: forall a u, R a u -> R' (f a) (g a u))
  {x y: A} {u: P x} {v: R x u}
  {u': P y} {v': R y u'}
  (H: x = y) (Hu: rew [P] H in u = u')
  (Hv: rew [fun z => R z.1 z.2] (=H; Hu) in
    (v: (fun z => R z.1 z.2) (x; u)) = v'):
  sigT_map_eq
    (P := fun a => {u: P a &T R a u})
    (Q := fun b => {u: P' b &T R' b u})
    (fun a uv => (g a uv.1; h a uv.1 uv.2))
    (eq_existT_curried_dep (Q := fun z => R z.1 z.2)
      (H := H) (Hu := Hu) (Hv := Hv)) =
  eq_existT_curried_dep
    (Q := fun z => R' z.1 z.2)
    (H := f_equal f H)
    (Hu := sigT_map_eq g Hu)
    (Hv := rew [fun p => rew [fun z => R' z.1 z.2] p in
        (h x u v: (fun z => R' z.1 z.2) (f x; g x u)) =
        (h y u' v': (fun z => R' z.1 z.2) (f y; g y u'))]
      f_equal_eq_existT_curried f g H Hu in
      @sigT_map_eq _ _ (fun z => R z.1 z.2) (fun z => R' z.1 z.2)
        (fun z => (f z.1; g z.1 z.2))
        (fun z => h z.1 z.2) (x; u) (y; u') v v' (=H; Hu) Hv).
Proof.
  now destruct Hv, Hu, H.
Defined.

Definition sigT_trans_eq {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} (q: rew [P] p in u = v)
  {p': y = z} (q': rew [P] p' in v = w):
  rew [P] eq_trans p p' in u = w.
Proof.
  now destruct q', p', q, p.
Defined.

Infix "⊙" := sigT_trans_eq (at level 65, left associativity).

Notation "q ⊙[ P ] q'" := (@sigT_trans_eq _ P _ _ _ _ _ _ _ q _ q')
  (at level 65, left associativity, only parsing).

Lemma sigT_trans_eq_refl {A: Type} {P: A -> Type} {x: A} {u v w: P x}
  (q: u = v) (q': v = w):
  sigT_trans_eq (p := eq_refl) q (p' := eq_refl) q' = eq_trans q q'.
Proof.
  now destruct q', q.
Defined.

(** Prefixing a dependent path by a pure transport combines the base paths. *)
Lemma sigT_trans_eq_rew_l {A: Type} {P: A -> Type}
  {x y z: A} (p: x = y) (r: y = z) (u: P x) {w: P z}
  (h: rew [P] r in rew [P] p in u = w):
  eq_refl ⊙ h = eq_sym (rew_compose P p r u) • h.
Proof.
  now destruct p, r, h.
Defined.

(** Solve for the second dependent path in a composite with a fixed first path. *)
Definition sigT_trans_eq_inv_l {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {r: y = z}
  (q: rew [P] p in u = v) (h: rew [P] (p • r) in u = w):
  rew [P] r in v = w :=
  eq_sym (f_equal (fun v => rew [P] r in v) q)
  • (rew_compose P p r u • h).

(** Composing the recovered second path with the first recovers the given composite. *)
Lemma sigT_trans_eq_inv_l_cancel {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {r: y = z}
  (q: rew [P] p in u = v) (h: rew [P] (p • r) in u = w):
  q ⊙ sigT_trans_eq_inv_l q h = h.
Proof.
  now destruct q, p, r, h.
Defined.

(** Fill the remaining dependent edge of a commuting square. *)
Definition sigT_square_fill {X: Type} {P: X -> Type}
  {x0 x1 y0 y1: X}
  {a: x0 = x1} {c: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • c = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (hp: rew [P] p in u0 = v0) (ha: rew [P] a in u0 = u1)
  (hq: rew [P] q in u1 = v1):
  rew [P] c in v0 = v1 :=
  sigT_trans_eq_inv_l hp
    (rew [fun e => rew [P] e in u0 = v1] (eq_sym H) in (ha ⊙ hq)).

(** The filled edge satisfies the square's dependent boundary equation. *)
Lemma sigT_square_fill_boundary {X: Type} {P: X -> Type}
  {x0 x1 y0 y1: X}
  {a: x0 = x1} {c: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • c = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (hp: rew [P] p in u0 = v0) (ha: rew [P] a in u0 = u1)
  (hq: rew [P] q in u1 = v1):
  rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_square_fill H hp ha hq) = ha ⊙ hq.
Proof.
  unfold sigT_square_fill.
  rewrite sigT_trans_eq_inv_l_cancel.
  now exact (rew_opp_r _ H _).
Defined.

(** Cancel a fixed final dependent path. *)
Definition sigT_trans_eq_inv_r {X: Type} {P: X -> Type}
  {x y z: X} {p: x = y} {q: y = z}
  {u: P x} {v: P y} {w: P z}
  (hq: rew [P] q in v = w)
  (h: rew [P] (p • q) in u = w): rew [P] p in u = v.
Proof. now destruct hq, q. Defined.

Lemma sigT_trans_eq_inv_r_comp {X: Type} {P: X -> Type}
  {x y z: X} {p: x = y} {q: y = z}
  {u: P x} {v: P y} {w: P z}
  (hq: rew [P] q in v = w) (h: rew [P] p in u = v):
  sigT_trans_eq_inv_r hq (h ⊙ hq) = h.
Proof.
  destruct q, hq, p.
  change (sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl = h).
  rewrite sigT_trans_eq_refl. now exact (eq_trans_refl_r h).
Defined.

Lemma sigT_trans_eq_inv_r_cancel {X: Type} {P: X -> Type}
  {x y z: X} {p: x = y} {q: y = z}
  {u: P x} {v: P y} {w: P z}
  (hq: rew [P] q in v = w) (h: rew [P] p • q in u = w):
  sigT_trans_eq_inv_r hq h ⊙ hq = h.
Proof.
  destruct q, hq, p.
  change (sigT_trans_eq (P := P) (p := eq_refl) h (p' := eq_refl) eq_refl = h).
  rewrite sigT_trans_eq_refl. now exact (eq_trans_refl_r h).
Defined.

(** Fill the opposite dependent edge by removing the supplied suffix. *)
Definition sigT_square_fill_upper {X: Type} {P: X -> Type}
  {x0 x1 y0 y1: X}
  {a: x0 = x1} {c: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • c = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (hp: rew [P] p in u0 = v0) (hc: rew [P] c in v0 = v1)
  (hq: rew [P] q in u1 = v1):
  rew [P] a in u0 = u1 :=
  sigT_trans_eq_inv_r hq
    (rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc)).

Lemma sigT_square_fill_upper_boundary {X: Type} {P: X -> Type}
  {x0 x1 y0 y1: X}
  {a: x0 = x1} {c: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • c = a • q)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (hp: rew [P] p in u0 = v0) (hc: rew [P] c in v0 = v1)
  (hq: rew [P] q in u1 = v1):
  rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) =
    sigT_square_fill_upper H hp hc hq ⊙ hq.
Proof. now exact (eq_sym (sigT_trans_eq_inv_r_cancel hq _)). Defined.

(** Naturality of dependent path composition in each argument. *)
Lemma rew_sigT_trans_eq_l {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p p': x = y} (e: p = p') {r: y = z}
  (q: rew [P] p in u = v) (s: rew [P] r in v = w):
  rew [fun p => rew [P] (p • r) in u = w] e in (q ⊙ s) =
  (rew [fun p => rew [P] p in u = v] e in q) ⊙ s.
Proof.
  now exact (map_subst (fun p (q: rew [P] p in u = v) => q ⊙ s) e q).
Defined.

Lemma rew_sigT_trans_eq_r {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {r r': y = z} (e: r = r')
  (q: rew [P] p in u = v) (s: rew [P] r in v = w):
  rew [fun r => rew [P] (p • r) in u = w] e in (q ⊙ s) =
  q ⊙ (rew [fun r => rew [P] r in v = w] e in s).
Proof.
  now exact (map_subst (fun r (s: rew [P] r in v = w) => q ⊙ s) e s).
Defined.

Lemma eq_trans_eq_existT_curried {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  (p: x = y) (q: rew [P] p in u = v)
  (p': y = z) (q': rew [P] p' in v = w):
  eq_trans (= p; q) (= p'; q') =
  (= eq_trans p p'; sigT_trans_eq q q').
Proof.
  now destruct q', p', q, p.
Defined.

Lemma sigT_trans_eq_existT_curried_dep {A: Type} {P: A -> Type}
  {Q: {a: A &T P a} -> Type}
  {x y z: A}
  {u: P x} {v: Q (x; u)}
  {u': P y} {v': Q (y; u')}
  {u'': P z} {v'': Q (z; u'')}
  (H: x = y) (Hu: rew [P] H in u = u')
  (Hv: rew [Q] (=H; Hu) in v = v')
  (H': y = z) (Hu': rew [P] H' in u' = u'')
  (Hv': rew [Q] (=H'; Hu') in v' = v''):
  eq_existT_curried_dep (H := H) (Hu := Hu) (Hv := Hv)
    ⊙ eq_existT_curried_dep (H := H') (Hu := Hu') (Hv := Hv') =
  eq_existT_curried_dep
    (H := eq_trans H H')
    (Hu := Hu ⊙ Hu')
    (Hv := rew [fun p => rew [Q] p in v = v'']
      eq_trans_eq_existT_curried H Hu H' Hu' in (Hv ⊙ Hv')).
Proof.
  now destruct Hv', Hu', H', Hv, Hu, H.
Defined.

Lemma rew_sigT_fst_const {A B: Type} {Q: A -> B -> Type} {x y: A}
  (E: x = y) (b: B) (q: Q x b):
  rew [fun a => {b0: B &T Q a b0}] E in (b; q) =
  (b; rew [fun a => Q a b] E in q).
Proof.
  now destruct E.
Defined.

Lemma sigT_map_eq_comp {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (g: forall x, P x -> Q (f x))
  {x y z: X} {p: x = y} {q: y = z} {u: P x} {v: P y} {w: P z}
  (h: rew [P] p in u = v) (k: rew [P] q in v = w):
  rew [fun e => rew [Q] e in g x u = g z w] (eq_trans_map_distr f p q) in
    sigT_map_eq g (h ⊙ k) = sigT_map_eq g h ⊙ sigT_map_eq g k.
Proof.
  now destruct p, q, h, k.
Defined.

Lemma sigT_trans_eq_assoc {X: Type} {P: X -> Type}
  {x y z t: X} {p: x = y} {q: y = z} {r: z = t}
  {a: P x} {b: P y} {c: P z} {d: P t}
  (h: rew [P] p in a = b) (j: rew [P] q in b = c) (k: rew [P] r in c = d):
  rew [fun e => rew [P] e in a = d] (eq_sym (eq_trans_assoc p q r)) in
    ((h ⊙ j) ⊙ k) = h ⊙ (j ⊙ k).
Proof.
  now destruct p, q, r, h, j, k.
Defined.

Lemma sigT_map_eq_id {X Y: Type} {P: X -> Type} (f: Y -> X)
  {x y: Y} {p: x = y} {u: P (f x)} {v: P (f y)}
  (h: rew [fun y => P (f y)] p in u = v):
  sigT_map_eq (Q := P) (fun _ u => u) h = eq_sym (rew_map P f p u) • h.
Proof.
  now destruct p, h.
Defined.

Lemma sigT_map_eq_id_inj {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x y: Y} {p: x = y} {u: P (f x)} {v: P (f y)}
  (h k: rew [fun y => P (f y)] p in u = v):
  sigT_map_eq (Q := P) (fun _ u => u) h =
  sigT_map_eq (Q := P) (fun _ u => u) k -> h = k.
Proof.
  destruct p. rewrite 2 sigT_map_eq_id.
  cbn [rew_map eq_sym]. now rewrite 2 eq_trans_refl_l.
Defined.

Definition sigT_sym_eq {X: Type} {P: X -> Type} {x y: X}
  {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  rew [P] eq_sym p in v = u.
Proof. now destruct p, h. Defined.

(** Inverting a dependent path agrees with reversing its transport and
    substituting the supplied fiber equality. *)
Lemma sigT_sym_eq_rew {A: Type} (P: A -> Type) {x y: A} (p: x = y)
  {u: P x} {v: P y} (H: rew [P] p in u = v):
  sigT_sym_eq H = eq_ind (rew [P] p in u)
    (fun v => rew [P] eq_sym p in v = u) (rew_opp_l P p u) v H.
Proof. now destruct p, H. Defined.

Lemma sigT_map_eq_sym {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (F: forall x, P x -> Q (f x))
  {x y: X} {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  rew [fun e => rew [Q] e in F y v = F x u]
    eq_sym (eq_sym_map_distr f p) in sigT_map_eq F (sigT_sym_eq h) =
  sigT_sym_eq (sigT_map_eq F h).
Proof. now destruct p, h. Defined.

Lemma sigT_sym_eq_map {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (F: forall x, P x -> Q (f x))
  {x y: X} {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  rew [fun e => rew [Q] e in F y v = F x u]
    eq_sym_map_distr f p in sigT_sym_eq (sigT_map_eq F h) =
  sigT_map_eq F (sigT_sym_eq h).
Proof. now destruct p, h. Defined.

Lemma sigT_trans_eq_units {X: Type} {P: X -> Type} {x y: X}
  {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  rew [fun e => rew [P] e in u = v] eq_sym (eq_trans_refl_l p) in
    sigT_trans_eq h (p' := eq_refl) eq_refl =
  sigT_trans_eq (p := eq_refl) eq_refl h.
Proof. now destruct p, h. Defined.

Lemma sigT_trans_eq_assoc_l {X: Type} {P: X -> Type}
  {x y z t: X} {p: x = y} {q: y = z} {r: z = t}
  {a: P x} {b: P y} {c: P z} {d: P t}
  (h: rew [P] p in a = b) (j: rew [P] q in b = c) (k: rew [P] r in c = d):
  rew [fun e => rew [P] e in a = d] eq_trans_assoc p q r in
    (h ⊙ (j ⊙ k)) = (h ⊙ j) ⊙ k.
Proof. now destruct p, q, r, h, j, k. Defined.

Definition sigT_map_eq_retract {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (F: forall x, P x -> Q (f x))
  (G: forall x, Q (f x) -> P x) (R: forall x a, G x (F x a) = a)
  {x y: X} (p: x = y) {a: P x} {b: P y}
  (H: rew [Q] f_equal f p in F x a = F y b): rew [P] p in a = b.
Proof.
  destruct p. now exact (eq_sym (R x a) • (f_equal (G x) H • R x b)).
Defined.

Lemma sigT_map_eq_retract_section {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (F: forall x, P x -> Q (f x))
  (G: forall x, Q (f x) -> P x) (R: forall x a, G x (F x a) = a)
  {x y: X} {p: x = y} {a: P x} {b: P y} (H: rew [P] p in a = b):
  sigT_map_eq_retract F G R p (sigT_map_eq F H) = H.
Proof.
  destruct p, H. cbn [sigT_map_eq_retract sigT_map_eq f_equal].
  rewrite eq_trans_refl_l. now exact (eq_trans_sym_inv_l (R x a)).
Defined.

Lemma sigT_trans_eq_inv_l_comp {X: Type} {P: X -> Type} {x y z: X}
  {p: x = y} {q: y = z} {a: P x} {b: P y} {c: P z}
  (h: rew [P] p in a = b) (k: rew [P] q in b = c):
  sigT_trans_eq_inv_l h (h ⊙ k) = k.
Proof. now destruct p, q, h, k. Defined.

Lemma sigT_trans_eq_unit_r {X: Type} {P: X -> Type} {x y: X}
  {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  sigT_trans_eq h (p' := eq_refl) eq_refl = h.
Proof. now destruct p, h. Defined.

Lemma sigT_trans_eq_unit_l {X: Type} {P: X -> Type} {x y: X}
  {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  rew [fun e => rew [P] e in u = v] eq_trans_refl_l p in
    sigT_trans_eq (p := eq_refl) eq_refl h = h.
Proof. now destruct p, h. Defined.

Lemma sigT_trans_eq_assoc_inverse {X: Type} {P: X -> Type}
  {x y z t: X} {p: x = y} {q: y = z} {r: z = t}
  {a: P x} {b: P y} {c: P z} {d: P t}
  (h: rew [P] p in a = b) (j: rew [P] q in b = c) (k: rew [P] r in c = d):
  sigT_sym_eq (sigT_trans_eq_assoc_l h j k) = sigT_trans_eq_assoc h j k.
Proof. now destruct p, q, r, h, j, k. Defined.

Lemma sigT_trans_eq_ind {A: Type} {P: A -> Type} {x y z: A}
  {p: x = y} {q: y = z} {u: P x} {v: P y} {w: P z}
  (h: rew [P] p in u = v) (k: rew [P] q in v = w):
  h ⊙ k = eq_ind (rew [P] q in rew [P] p in u) (fun z => z = w)
    (eq_ind_r (fun v => rew [P] q in v = w) k h)
    (rew [P] (p • q) in u) (rew_compose P p q u).
Proof. now destruct q, k, p, h. Defined.

(** A dependent map preserves endpoint changes of a lifted path. *)

Lemma sigT_map_eq_conjugate {X Y:Type}{P:X->Type}{Q:Y->Type}
  {f:X->Y}(F:forall x,P x->Q(f x))
  {x y:X}(H:x=y){a a':P x}{b b':P y}
  (L:a=a')(R:b=b')(M:rew[P]H in a'=b'):
  sigT_map_eq F
    (f_equal(fun z=>rew[P]H in z)L •(M •eq_sym R)) =
  f_equal(fun z=>rew[Q]f_equal f H in z)(f_equal(F x)L) •
    (sigT_map_eq F M •eq_sym(f_equal(F y)R)).
Proof.
  destruct L,R. cbn [f_equal eq_sym].
  now rewrite 2 eq_trans_refl_l.
Defined.

(** A fiberwise left inverse of a dependent map. Its section law recovers
    each source witness after mapping. *)
Record fiber_retraction {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} (F: forall x, P x -> Q (f x)) := {
  fiber_back: forall x, Q (f x) -> P x;
  fiber_section: forall x a, fiber_back x (F x a) = a
}.
Arguments fiber_back {X Y P Q f F} _ _ _.
Arguments fiber_section {X Y P Q f F} _ _ _.

(** Compose fiber retractions in the order of their forward maps. *)
Definition compose_retraction {X Y Z: Type}
  {P: X -> Type} {Q: Y -> Type} {R: Z -> Type}
  {f: X -> Y} {g: Y -> Z}
  {F: forall x, P x -> Q (f x)} {H: forall y, Q y -> R (g y)}
  (r: fiber_retraction F) (s: fiber_retraction H):
  fiber_retraction (fun x a => H (f x) (F x a)).
Proof.
  refine {| fiber_back := fun x a => fiber_back r x (fiber_back s (f x) a) |}.
  intros x a.
  now exact (f_equal (fiber_back r x) (fiber_section s (f x) (F x a)) •
    fiber_section r x a).
Defined.

(** Lift a fiber retraction to dependent paths. *)
Definition path_retraction {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} {F: forall x, P x -> Q (f x)}
  (r: fiber_retraction F) {x y: X} (a: P x) (b: P y):
  fiber_retraction (f := fun p: x = y => f_equal f p)
    (P := fun p => rew [P] p in a = b)
    (Q := fun p => rew [Q] p in F x a = F y b)
    (fun (p: x = y) (h: rew [P] p in a = b) => sigT_map_eq (f := f) (Q := Q) F h).
Proof.
  refine {| fiber_back := fun p h =>
    sigT_map_eq_retract F (fiber_back r) (fiber_section r) p h |}.
  intros p h.
  now exact (sigT_map_eq_retract_section F (fiber_back r) (fiber_section r) h).
Defined.

Definition prefix_retraction {X: Type} (P: X -> Type)
  {x0 x1 x2: X} (p: x0 = x1) {a: P x0} {b: P x1} (hp: rew [P] p in a = b)
  (c: P x2):
  fiber_retraction (f := fun e: x1 = x2 => p • e)
    (P := fun e => rew [P] e in b = c) (Q := fun e => rew [P] e in a = c)
    (fun (e: x1 = x2) (h: rew [P] e in b = c) => hp ⊙ h) :=
  {| fiber_back := fun _ h => sigT_trans_eq_inv_l hp h;
     fiber_section := fun _ h => sigT_trans_eq_inv_l_comp hp h |}.

Definition suffix_retraction {X: Type} (P: X -> Type)
  {x0 x1 x2: X} (q: x1 = x2) {b: P x1} {c: P x2}
  (hq: rew [P] q in b = c) (a: P x0):
  fiber_retraction (f := fun e: x0 = x1 => e • q)
    (P := fun e => rew [P] e in a = b) (Q := fun e => rew [P] e in a = c)
    (fun (e: x0 = x1) (h: rew [P] e in a = b) => h ⊙ hq) :=
  {| fiber_back := fun _ h => sigT_trans_eq_inv_r hq h;
     fiber_section := fun _ h => sigT_trans_eq_inv_r_comp hq h |}.

(** Retract the pullback path map using transport composition. *)
Definition pullback_path_retraction {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x y: Y} (a: P (f x)) (b: P (f y)):
  fiber_retraction (f := fun e: x = y => f_equal f e)
    (P := fun e => rew [fun y => P (f y)] e in a = b)
    (Q := fun e => rew [P] e in a = b)
    (fun (e: x = y) (h: rew [fun y => P (f y)] e in a = b) =>
      sigT_map_eq (f := f) (Q := P) (fun _ u => u) h).
Proof.
  refine {| fiber_back := fun e h => rew_map P f e a • h |}.
  intros e h. rewrite sigT_map_eq_id.
  rewrite eq_trans_assoc, eq_trans_sym_inv_r.
  now apply eq_trans_refl_l.
Defined.

Definition fiber_recovery {X Y: Type} {P: X -> Type} {Q: Y -> Type}
  {f: X -> Y} {F: forall x, P x -> Q (f x)} (r: fiber_retraction F) :=
  forall x b, F x (fiber_back r x b) = b.
