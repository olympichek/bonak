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
Qed.

Lemma eq_existT_curried_eq {A: Type} {P: A -> Type}
  {x y: A} {u: P x} {v: P y}
  {p p': x = y}
  {q: rew [P] p in u = v} {q': rew [P] p' in u = v}
  (Hp: p = p')
  (Hq: rew [fun r => rew [P] r in u = v] Hp in q = q'):
  (= p; q) = (= p'; q').
Proof.
  destruct Hp; simpl in Hq. now destruct Hq.
Qed.

Definition sigT_map_eq {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y}
  {p: x = y} (q: rew [P] p in u = v):
  rew [Q] f_equal f p in g x u = g y v.
Proof.
  now destruct q, p.
Defined.

Lemma f_equal_eq_existT_curried {A B: Type} {P: A -> Type} {Q: B -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v: P y}
  (p: x = y) (q: rew [P] p in u = v):
  f_equal (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) (= p; q) =
  (= f_equal f p; sigT_map_eq g q).
Proof.
  now destruct q, p.
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

Lemma eq_trans_eq_existT_curried {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  (p: x = y) (q: rew [P] p in u = v)
  (p': y = z) (q': rew [P] p' in v = w):
  eq_trans (= p; q) (= p'; q') =
  (= eq_trans p p'; sigT_trans_eq q q').
Proof.
  now destruct q', p', q, p.
Qed.
