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

Definition sigT_const_path {A B: Type} {x y: { _ : A &T B }}
  (p1: x.1 = y.1) (p2: x.2 = y.2): x = y.
Proof.
  destruct x as [x1 x2], y as [y1 y2].
  simpl in p1, p2. destruct p1, p2. reflexivity.
Defined.

Lemma sigT_const_path_eta {A B: Type} {x y: { _ : A &T B }}
  (p: x = y):
  sigT_const_path (f_equal (fun z => z.1) p)
    (f_equal (fun z => @projT2 A (fun _ : A => B) z) p) = p.
Proof.
  destruct p. destruct x. reflexivity.
Defined.

Lemma sigT_const_path_ext {A B: Type} {x y: { _ : A &T B }}
  (p q: x = y):
  f_equal (fun z => z.1) p = f_equal (fun z => z.1) q ->
  f_equal (fun z => @projT2 A (fun _ : A => B) z) p =
    f_equal (fun z => @projT2 A (fun _ : A => B) z) q ->
  p = q.
Proof.
  intros H1 H2.
  rewrite <- (sigT_const_path_eta p).
  rewrite <- (sigT_const_path_eta q).
  now rewrite H1, H2.
Defined.

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
Qed.

Definition sigT_map_eq {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v):
  rew [Q] f_equal f p in g x u = g y v.
Proof.
  now destruct q, p.
Defined.

Lemma sigT_map_eq_refl {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x: A} {u: P x}:
  @sigT_map_eq A B P Q f g x x u u eq_refl eq_refl = eq_refl.
Proof.
  reflexivity.
Defined.

Lemma sigT_map_eq_transport_refl {A B: Type}
  {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} (p: x = y):
  @sigT_map_eq A B P Q f g x y u (rew [P] p in u) p eq_refl =
  eq_trans
    (eq_sym (rew_map Q f p (g x u)))
    (@map_subst A P (fun a => Q (f a)) g x y p u).
Proof.
  now destruct p.
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

Lemma sigT_map_eq_existT_curried_dep {A B: Type} {P: A -> Type}
  {P': B -> Type} {Q: {a: A &T P a} -> Type}
  {Q': {b: B &T P' b} -> Type}
  (f: A -> B) (g: forall a, P a -> P' (f a))
  (h: forall z: {a: A &T P a}, Q z ->
    Q' (f z.1; g z.1 z.2))
  {x y: A} {u: P x} {v: Q (x; u)}
  {u': P y} {v': Q (y; u')}
  (H: x = y) (Hu: rew [P] H in u = u')
  (Hv: rew [Q] (=H; Hu) in v = v'):
  sigT_map_eq
    (fun a uv => (g a uv.1; h (a; uv.1) uv.2))
    (eq_existT_curried_dep (H := H) (Hu := Hu) (Hv := Hv)) =
  eq_existT_curried_dep
    (H := f_equal f H)
    (Hu := sigT_map_eq g Hu)
    (Hv := rew [fun p => rew [Q'] p in h (x; u) v = h (y; u') v']
      f_equal_eq_existT_curried f g H Hu in sigT_map_eq h Hv).
Proof.
  now destruct Hv, Hu, H.
Qed.

Lemma sigT_map_eq_existT_curried_dep_fst {A B: Type} {P: A -> Type}
  {P': B -> Type} {Q: {a: A &T P a} -> Type}
  (f: A -> B) (g: forall a, P a -> P' (f a))
  {x y: A} {u: P x} {v: Q (x; u)}
  {u': P y} {v': Q (y; u')}
  (H: x = y) (Hu: rew [P] H in u = u')
  (Hv: rew [Q] (=H; Hu) in v = v'):
  sigT_map_eq
    (P := fun a => {u: P a &T Q (a; u)})
    (Q := P')
    (fun a uv => g a uv.1)
    (eq_existT_curried_dep (H := H) (Hu := Hu) (Hv := Hv)) =
  sigT_map_eq g Hu.
Proof.
  now destruct Hv, Hu, H.
Qed.

Lemma sigT_map_eq_existT_curried_dep_eta {A B: Type} {P: A -> Type}
  {P': B -> Type} {Q: {a: A &T P a} -> Type}
  {Q': {b: B &T P' b} -> Type}
  (f: A -> B) (g: forall a, P a -> P' (f a))
  (h: forall a u, Q (a; u) -> Q' (f a; g a u))
  {x y: A} {u: P x} {v: Q (x; u)}
  {u': P y} {v': Q (y; u')}
  (H: x = y) (Hu: rew [P] H in u = u')
  (Hv: rew [Q] (=H; Hu) in v = v'):
  sigT_map_eq
    (fun a uv => (g a uv.1; h a uv.1 uv.2))
    (eq_existT_curried_dep (H := H) (Hu := Hu) (Hv := Hv)) =
  eq_existT_curried_dep
    (H := f_equal f H)
    (Hu := sigT_map_eq g Hu)
    (Hv := rew [fun p => rew [Q'] p in h x u v = h y u' v']
      f_equal_eq_existT_curried f g H Hu in
      @sigT_map_eq _ _ Q Q' (fun z => (f z.1; g z.1 z.2))
        (fun z => h z.1 z.2) (x; u) (y; u') v v' (=H; Hu) Hv).
Proof.
  now destruct Hv, Hu, H.
Qed.

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
Qed.

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

Lemma sigT_trans_eq_refl_l {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v):
  rew [fun p => rew [P] p in u = v] (eq_trans_refl_l p) in
    @sigT_trans_eq A P x x y u u v eq_refl eq_refl p q = q.
Proof.
  now destruct q, p.
Defined.

Lemma sigT_trans_eq_refl_r {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v):
  rew [fun p => rew [P] p in u = v] (eq_trans_refl_r p) in
    @sigT_trans_eq A P x y y u v v p q eq_refl eq_refl = q.
Proof.
  now destruct q, p.
Defined.

Definition eq_trans_refl_l_transport {A: Type} {x y: A}
  {p0: x = x} (Hp0: eq_refl = p0) (p: x = y):
  eq_trans p0 p = p.
Proof.
  destruct Hp0. now apply eq_trans_refl_l.
Defined.

Definition eq_trans_refl_r_transport {A: Type} {x y: A}
  (p: x = y) {p0: y = y} (Hp0: eq_refl = p0):
  eq_trans p p0 = p.
Proof.
  destruct Hp0. now apply eq_trans_refl_r.
Defined.

Lemma sigT_trans_eq_refl_l_transport {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {p0: x = x} (q0: rew [P] p0 in u = u)
  {p: x = y} (q: rew [P] p in u = v)
  (Hp0: eq_refl = p0)
  (Hq0: rew [fun p0 => rew [P] p0 in u = u] Hp0 in
    (eq_refl: rew [P] eq_refl in u = u) = q0):
  rew [fun p => rew [P] p in u = v]
    (eq_trans_refl_l_transport Hp0 p) in
    @sigT_trans_eq A P x x y u u v p0 q0 p q = q.
Proof.
  destruct Hp0; cbn in Hq0 |- *.
  destruct Hq0; cbn.
  now apply sigT_trans_eq_refl_l.
Defined.

Lemma sigT_trans_eq_refl_r_transport {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v)
  {p0: y = y} (q0: rew [P] p0 in v = v)
  (Hp0: eq_refl = p0)
  (Hq0: rew [fun p0 => rew [P] p0 in v = v] Hp0 in
    (eq_refl: rew [P] eq_refl in v = v) = q0):
  rew [fun p => rew [P] p in u = v]
    (eq_trans_refl_r_transport p Hp0) in
    @sigT_trans_eq A P x y y u v v p q p0 q0 = q.
Proof.
  destruct Hp0; cbn in Hq0 |- *.
  destruct Hq0; cbn.
  now apply sigT_trans_eq_refl_r.
Defined.

Lemma sigT_trans_eq_eq_refl_l {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {w: P z}
  {p: x = y} {p': y = z}
  (q': rew [P] p' in rew [P] p in u = w):
  @sigT_trans_eq A P x y z u (rew [P] p in u) w p eq_refl p' q' =
  eq_trans (eq_sym (@rew_compose A P x y z p p' u)) q'.
Proof.
  now destruct q', p', p.
Defined.

Lemma sigT_trans_eq_eq_refl_r {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v)
  {p': y = z}:
  @sigT_trans_eq A P x y z u v (rew [P] p' in v) p q p' eq_refl =
  eq_trans (eq_sym (@rew_compose A P x y z p p' u))
    (f_equal (fun v => rew [P] p' in v) q).
Proof.
  now destruct q, p', p.
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
Qed.
