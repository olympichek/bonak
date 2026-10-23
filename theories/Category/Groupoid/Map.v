(** Maps of displayed groupoids, preserving the specified base functor. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export Family.
From Bonak.Category Require Export FunctorPointwise.
From Bonak.Lib Require Import HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record Map {G H: HSetGroupoid} {E: Family G} {P: Family H} {F: Functor G H} := {
  mobj: forall x, E.(dobj) x -> P.(dobj) (F.(fobj) x);
  mhom: forall {x y} {a: E.(dobj) x} {b: E.(dobj) y},
    E.(dhom) a b -> P.(dhom) (mobj x a) (mobj y b);
  mid: forall {x} (a: E.(dobj) x), mhom (E.(did) a) = P.(did) (mobj x a);
  mcomp: forall {x y z} {a: E.(dobj) x} {b: E.(dobj) y} {c: E.(dobj) z}
    (f: E.(dhom) a b) (g: E.(dhom) b c),
    mhom (E.(dcomp) f g) = P.(dcomp) (mhom f) (mhom g);
  mbase: forall {x y} {a: E.(dobj) x} {b: E.(dobj) y} (f: E.(dhom) a b),
    P.(dbase) (mhom f) = F.(fhom) (E.(dbase) f);
}.
Arguments Map {G H} E P F.

Definition totalMap {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F: Functor G H} (m: Map E P F): Functor (total E) (total P) :=
  Build_Functor (total E) (total P) (fun a => (F.(fobj) a.1; m.(mobj) a.1 a.2))
    (fun a b => m.(mhom)) (fun a => m.(mid) a.2) (fun a b c => m.(mcomp)).

(** Equality of displayed maps over a specified equality of base functors. *)
Record MapEq {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F L: Functor G H} {e: F ≐ L} {m: Map E P F} {n: Map E P L}: Prop := {
  mapObjEq: forall x (a: E.(dobj) x),
    rew [fun y => P.(dobj) y] e.(objEq) x in m.(mobj) x a = n.(mobj) x a;
  mapHomEq: forall x y (a: E.(dobj) x) (b: E.(dobj) y) (f: E.(dhom) a b),
    castArrow (G := total P)
      (= e.(objEq) x; mapObjEq x a) (= e.(objEq) y; mapObjEq y b)
      (m.(mhom) f) = n.(mhom) f;
}.
Arguments MapEq {G H E P F L} e m n.

Definition totalMapEq {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F L: Functor G H} (e: F ≐ L) {m: Map E P F} {n: Map E P L}
  (h: MapEq e m n): totalMap m ≐ totalMap n :=
  @Build_FunctorEq (total E) (total P) (totalMap m) (totalMap n)
    (fun a => (= e.(objEq) a.1; h.(mapObjEq) a.1 a.2))
    (fun a b f => h.(mapHomEq) a.1 b.1 a.2 b.2 f).

Definition mapEqOfTotal {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F L: Functor G H} (e: F ≐ L) {m: Map E P F} {n: Map E P L}
  (h: totalMap m ≐ totalMap n): MapEq e m n.
Proof.
  unshelve econstructor.
  - intros x a. pose proof (projT2_eq (h.(objEq) (x; a))) as p.
    rewrite (@UIP H _ _ (projT1_eq (h.(objEq) (x; a))) (e.(objEq) x)) in p.
    now exact p.
  - intros x y a b f.
    rewrite (@UIP (total P) _ _ _ (h.(objEq) (x; a))).
    rewrite (@UIP (total P) _ _ _ (h.(objEq) (y; b))).
    now exact (h.(homEq) (x; a) (y; b) f).
Defined.

(** These law proofs match [compFunctor], so [totalMap] preserves composition
    definitionally, including the functor laws. *)
Definition compMap {G H K: HSetGroupoid} {E: Family G} {P: Family H} {Q: Family K}
  {F: Functor G H} {L: Functor H K} (m: Map E P F) (n: Map P Q L):
  Map E Q (F ⨟ᶠ L).
Proof.
  refine (@Build_Map G K E Q (F ⨟ᶠ L)
    (fun x a => n.(mobj) (F.(fobj) x) (m.(mobj) x a))
    (fun x y a b f => n.(mhom) (m.(mhom) f)) _ _ _).
  - intros x a. now exact (f_equal n.(mhom) (m.(mid) a) • n.(mid) (m.(mobj) x a)).
  - intros x y z a b c f g.
    now exact (f_equal n.(mhom) (m.(mcomp) f g) • n.(mcomp) (m.(mhom) f) (m.(mhom) g)).
  - intros. cbn. now rewrite n.(mbase), m.(mbase).
Defined.

Definition idMap {G: HSetGroupoid} (E: Family G): Map E E (idFunctor G) :=
  @Build_Map G G E E (idFunctor G) (fun _ a => a) (fun _ _ _ _ f => f)
    (fun _ _ => eq_refl) (fun _ _ _ _ _ _ _ _ => eq_refl) (fun _ _ _ _ _ => eq_refl).

Definition precomposeMapId {G H: HSetGroupoid} {E P: Family G} {Q: Family H}
  {F: Functor G H} (m: Map E P (idFunctor G)) (n: Map P Q F): Map E Q F.
Proof.
  refine (@Build_Map G H E Q F (fun x a => n.(mobj) x (m.(mobj) x a))
    (fun x y a b f => n.(mhom) (m.(mhom) f)) _ _ _).
  - intros. now rewrite m.(mid), n.(mid).
  - intros. now rewrite m.(mcomp), n.(mcomp).
  - intros x y a b f.
    now exact (n.(mbase) (m.(mhom) f) • f_equal F.(fhom) (m.(mbase) f)).
Defined.

Lemma precomposeMapIdTotal {G H: HSetGroupoid} {E P: Family G} {Q: Family H}
  {F: Functor G H} (m: Map E P (idFunctor G)) (n: Map P Q F):
  totalMap (precomposeMapId m n) ≐ totalMap m ⨟ᶠ totalMap n.
Proof. unshelve econstructor; now intros. Defined.

Definition castHom {G: HSetGroupoid} (E: Family G) {x x' y y': G}
  (hx: x = x') (hy: y = y') {a: E.(dobj) x} {b: E.(dobj) y} (f: E.(dhom) a b):
  E.(dhom) (rew [fun x => E.(dobj) x] hx in a) (rew [fun y => E.(dobj) y] hy in b).
Proof. now destruct hx, hy. Defined.

Lemma castHomId {G: HSetGroupoid} (E: Family G) {x y: G}
  (p: x = y) (a: E.(dobj) x):
  castHom E p p (E.(did) a) = E.(did) (rew [fun x => E.(dobj) x] p in a).
Proof. now destruct p. Defined.

Lemma castHomComp {G: HSetGroupoid} (E: Family G) {x x' y y' z z': G}
  (p: x = x') (q: y = y') (r: z = z')
  {a: E.(dobj) x} {b: E.(dobj) y} {c: E.(dobj) z}
  (f: E.(dhom) a b) (g: E.(dhom) b c):
  castHom E p r (E.(dcomp) f g) = E.(dcomp) (castHom E p q f) (castHom E q r g).
Proof. now destruct p, q, r. Defined.

Lemma castHomBase {G: HSetGroupoid} (E: Family G) {x x' y y': G}
  (p: x = x') (q: y = y') {a: E.(dobj) x} {b: E.(dobj) y} (f: E.(dhom) a b):
  E.(dbase) (castHom E p q f) = castArrow p q (E.(dbase) f).
Proof. now destruct p, q. Defined.

Definition castBase {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F L: Functor G H} (e: F ≐ L) (m: Map E P F): Map E P L.
Proof.
  refine (@Build_Map G H E P L
    (fun x a => rew [fun y => P.(dobj) y] e.(objEq) x in m.(mobj) x a)
    (fun x y a b f => castHom P (e.(objEq) x) (e.(objEq) y) (m.(mhom) f)) _ _ _).
  - intros x a. cbn beta. rewrite m.(mid). now apply castHomId.
  - intros x y z a b c f g. cbn beta. rewrite m.(mcomp). now apply castHomComp.
  - intros x y a b f. cbn beta. rewrite castHomBase, m.(mbase). now apply e.(homEq).
Defined.

Lemma castTotalHom {G: HSetGroupoid} (E: Family G) {x x' y y': G}
  (p: x = x') (q: y = y') {a: E.(dobj) x} {b: E.(dobj) y} (f: E.(dhom) a b):
  castArrow (G := total E)
    (eq_existT_rew p a) (eq_existT_rew q b) (castHom E p q f) = f.
Proof. now destruct p, q. Defined.

Definition castBaseTotal {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F L: Functor G H} (e: F ≐ L) (m: Map E P F): totalMap (castBase e m) ≐ totalMap m.
Proof.
  refine (@Build_FunctorEq (total E) (total P) (totalMap (castBase e m)) (totalMap m)
    (fun a => eq_existT_rew (e.(objEq) a.1) (m.(mobj) a.1 a.2)) _).
  intros a b f. now apply (castTotalHom P).
Defined.

Definition pull {G H K: HSetGroupoid} {E: Family H} {P: Family K}
  {R: Functor H K} (m: Map E P R) (F: Functor G H):
  Map (reindex E F) P (F ⨟ᶠ R).
Proof.
  refine (@Build_Map G K (reindex E F) P (F ⨟ᶠ R)
    (fun x a => m.(mobj) (F.(fobj) x) a) (fun x y a b f => m.(mhom) f.2.1)
    (fun x a => m.(mid) a) (fun x y z a b c f g => m.(mcomp) f.2.1 g.2.1) _).
  intros. cbn. now rewrite m.(mbase), f.2.2.
Defined.

Definition intoPull {G H K: HSetGroupoid} {E: Family G} {P: Family K}
  (F: Functor G H) (R: Functor H K) (m: Map E P (F ⨟ᶠ R)):
  Map E (reindex P R) F.
Proof.
  refine (@Build_Map G H E (reindex P R) F m.(mobj)
    (fun x y a b f => (F.(fhom) (E.(dbase) f); (m.(mhom) f; m.(mbase) f))) _ _ _).
  - intros. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now rewrite E.(dbaseId), F.(fid).
    + now apply m.(mid).
  - intros. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now rewrite E.(dbaseComp), F.(fcomp).
    + now apply m.(mcomp).
  - now intros.
Defined.

Definition sigmaFst {G: HSetGroupoid} (E: Family G) (P: Family (total E)):
  Map (sigma E P) E (idFunctor G) :=
  @Build_Map G G (sigma E P) E (idFunctor G)
    (fun x a => a.1) (fun x y a b => P.(dbase))
    (fun x a => P.(dbaseId) a.2) (fun x y z a b c => P.(dbaseComp))
    (fun x y a b f => eq_refl).

Definition forgetPull {G H: HSetGroupoid} (E: Family H) (F: Functor G H):
  Map (reindex E F) E F :=
  @Build_Map G H (reindex E F) E F (fun x a => a)
    (fun x y a b f => f.2.1) (fun x a => eq_refl)
    (fun x y z a b c f g => eq_refl) (fun x y a b f => f.2.2).

Definition reindexTotal {G H: HSetGroupoid} (E: Family H) (F: Functor G H):
  Functor (total (reindex E F)) (total E) := totalMap (forgetPull E F).

Definition sigmaMap {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F: Functor G H} (m: Map E P F) {Q: Family (total E)} {R: Family (total P)}
  (n: Map Q R (totalMap m)): Map (sigma E Q) (sigma P R) F.
Proof.
  refine (@Build_Map G H (sigma E Q) (sigma P R) F
    (fun x a => (m.(mobj) x a.1; n.(mobj) (x; a.1) a.2))
    (fun x y a b => n.(mhom))
    (fun x a => n.(mid) a.2) (fun x y z a b c => n.(mcomp)) _).
  intros x y a b f. change (P.(dbase) (R.(dbase) (n.(mhom) f)) = F.(fhom) (E.(dbase) (Q.(dbase) f))).
  rewrite n.(mbase). now apply m.(mbase).
Defined.

(** A dependent-sum equality pairs the displayed equality of its first
    component with the equality of the second component over that pair path. *)
Definition sigmaMapEq {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F L: Functor G H} (e: F ≐ L) {m: Map E P F} {m': Map E P L}
  (h: MapEq e m m') {Q: Family (total E)} {R: Family (total P)}
  {n: Map Q R (totalMap m)} {n': Map Q R (totalMap m')}
  (k: MapEq (totalMapEq e h) n n'):
  MapEq e (sigmaMap m n) (sigmaMap m' n').
Proof.
  refine (@Build_MapEq G H (sigma E Q) (sigma P R) F L e
    (sigmaMap m n) (sigmaMap m' n')
    (fun x a => eq_existT_curried_dep
      (H := e.(objEq) x) (Hu := h.(mapObjEq) x a.1)
      (Hv := k.(mapObjEq) (x; a.1) a.2)) _).
  intros x y a b f.
  pose (p := (= e.(objEq) x; eq_existT_curried_dep
    (H := e.(objEq) x) (Hu := h.(mapObjEq) x a.1)
    (Hv := k.(mapObjEq) (x; a.1) a.2))).
  pose (q := (= e.(objEq) y; eq_existT_curried_dep
    (H := e.(objEq) y) (Hu := h.(mapObjEq) y b.1)
    (Hv := k.(mapObjEq) (y; b.1) b.2))).
  change ((totalAssoc P R).(fhom)
    (castArrow (G := total (sigma P R)) p q (n.(mhom) f)) = n'.(mhom) f).
  rewrite (mapCastArrow (totalAssoc P R)).
  rewrite (@UIP (total R) _ _ _
    (= (totalMapEq e h).(objEq) (x; a.1); k.(mapObjEq) (x; a.1) a.2)).
  rewrite (@UIP (total R) _ _ _
    (= (totalMapEq e h).(objEq) (y; b.1); k.(mapObjEq) (y; b.1) b.2)).
  now exact (k.(mapHomEq) (x; a.1) (y; b.1) a.2 b.2 f).
Defined.

Lemma sigmaCompositeMapEq {G H K: HSetGroupoid}
  {E: Family G} {P: Family H} {Q: Family K}
  {F F': Functor G H} {L L': Functor H K}
  {m: Map E P F} {m': Map E P F'} {n: Map P Q L} {n': Map P Q L'}
  (e: F ⨟ᶠ L ≐ F' ⨟ᶠ L') (h: MapEq e (compMap m n) (compMap m' n'))
  {U: Family (total E)} {V: Family (total P)} {W: Family (total Q)}
  {a: Map U V (totalMap m)} {a': Map U V (totalMap m')}
  {b: Map V W (totalMap n)} {b': Map V W (totalMap n')}
  (k: MapEq (totalMapEq e h) (compMap a b) (compMap a' b')):
  MapEq e (compMap (sigmaMap m a) (sigmaMap n b))
    (compMap (sigmaMap m' a') (sigmaMap n' b')).
Proof.
  now exact (@Build_MapEq G K (sigma E U) (sigma Q W) (F ⨟ᶠ L) (F' ⨟ᶠ L') e
    (compMap (sigmaMap m a) (sigmaMap n b))
    (compMap (sigmaMap m' a') (sigmaMap n' b'))
    (sigmaMapEq e h k).(mapObjEq) (sigmaMapEq e h k).(mapHomEq)).
Defined.

(** Reindex a displayed map along a commuting square. *)
Definition reindexMap {X Y G H: HSetGroupoid} {E: Family G} {P: Family H}
  {R: Functor G H} (m: Map E P R) (S: Functor X G) (T: Functor Y H)
  (F: Functor X Y) (c: S ⨟ᶠ R ≐ F ⨟ᶠ T): Map (reindex E S) (reindex P T) F :=
  intoPull F T (castBase c (pull m S)).

Lemma totalProj {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F: Functor G H} (m: Map E P F): totalMap m ⨟ᶠ proj P ≐ proj E ⨟ᶠ F.
Proof.
  unshelve econstructor; [now intros|]. intros x y f. now apply m.(mbase).
Defined.

Lemma reindexMapTotal {X Y G H: HSetGroupoid} {E: Family G} {P: Family H}
  {R: Functor G H} (m: Map E P R) (S: Functor X G) (T: Functor Y H)
  (F: Functor X Y) (c: S ⨟ᶠ R ≐ F ⨟ᶠ T):
  totalMap (reindexMap m S T F c) ⨟ᶠ reindexTotal P T ≐ reindexTotal E S ⨟ᶠ totalMap m.
Proof.
  unfold reindexMap.
  refine ((_ : _ ≐ totalMap (castBase c (pull m S))) •ᶠ _).
  - unshelve econstructor; now intros.
  - refine (castBaseTotal c (pull m S) •ᶠ _).
    unshelve econstructor; now intros.
Defined.

(** Projection of a dependent-sum map. *)
Lemma sigmaFstTotal {G H: HSetGroupoid} {E: Family G} {P: Family H}
  {F: Functor G H} (m: Map E P F) {Q: Family (total E)} {R: Family (total P)}
  (n: Map Q R (totalMap m)):
  totalMap (sigmaMap m n) ⨟ᶠ totalMap (sigmaFst P R) ≐
  totalMap (sigmaFst E Q) ⨟ᶠ totalMap m.
Proof.
  unshelve econstructor; [now intros|]. intros x y f.
  now exact (@mbase _ _ _ _ _ n (x.1; x.2.1) (y.1; y.2.1) x.2.2 y.2.2 f).
Defined.
