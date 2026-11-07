(** Strict fiber and total-groupoid roundtrips, on objects and arrows. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export GraphFiber.
From Bonak.Category.Groupoid Require Import FamilyIdentity.
From Bonak.Lib Require Import Equiv HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Definition graphUnitIso {C B: StrictGroupoid} (p: Functor C B):
  StrictGroupoidIso C (total (graphFiber p)).
Proof.
  now refine (@Build_StrictGroupoidIso C (total (graphFiber p))
    (qinvEquiv (graphUnit p).(fobj) (graphTotal p).(fobj)
      (fun _ => eq_refl) (graphObjectEta p))
    (fun x y => idEquiv) (fun x => eq_refl) (fun x y z f g => eq_refl)).
Defined.

Definition graphFamilyObj {G: StrictGroupoid} (E: Family G) {x: G}
  (a: (graphFiber (proj E)).(dobj) x): E.(dobj) x :=
  rew [fun y => E.(dobj) y] (eq_sym a.2) in a.1.2.

Definition graphFamilyPoint {G: StrictGroupoid} (E: Family G) {x: G}
  (a: E.(dobj) x): (graphFiber (proj E)).(dobj) x :=
  graphPoint (proj E) (x; a).

Definition graphFamilyObjEquiv {G: StrictGroupoid} (E: Family G) (x: G):
  Equiv ((graphFiber (proj E)).(dobj) x) (E.(dobj) x).
Proof.
  refine (qinvEquiv (graphFamilyObj E) (graphFamilyPoint E) _ _).
  - intros [[y a] e]. cbn in e. now destruct e.
  - now intros.
Defined.

Definition graphFamilyHom {G: StrictGroupoid} (E: Family G) {x y: G}
  (a: (graphFiber (proj E)).(dobj) x) (b: (graphFiber (proj E)).(dobj) y):
  Equiv ((graphFiber (proj E)).(dhom) a b)
    (E.(dhom) (graphFamilyObj E a) (graphFamilyObj E b)).
Proof.
  destruct a as [[x' a] p], b as [[y' b] q]. cbn in p, q.
  destruct p, q. now exact idEquiv.
Defined.

Definition graphFamilyMap {G: StrictGroupoid} (E: Family G):
  Map (graphFiber (proj E)) E (idFunctor G).
Proof.
  refine (Build_Map (fun x a => graphFamilyObj E a)
    (fun x y a b => graphFamilyHom E a b) _ _ _).
  - intros x [[y a] p]. cbn in p. now destruct p.
  - intros x y z [[x' a] p] [[y' b] q] [[z' c] r] f g.
    cbn in p, q, r. now destruct p, q, r.
  - intros x y [[x' a] p] [[y' b] q] f.
    cbn in p, q. now destruct p, q.
Defined.

Definition graphFamilyIso {G: StrictGroupoid} (E: Family G):
  FamilyIso (graphFiber (proj E)) E := {|
  fisoObj := graphFamilyObjEquiv E;
  fisoHom x y a b := graphFamilyHom E a b;
  fisoBase x y a b := (graphFamilyMap E).(mbase);
  fisoId x a := (graphFamilyMap E).(mid) a;
  fisoComp x y z a b c := (graphFamilyMap E).(mcomp);
|}.

Definition graphFiberIsoOf {B A C: StrictGroupoid} (eB: B = A)
  {E: Family B} (eC: C = total E) (p: Functor C A)
  (hp: transportGroupoidFunctor eC ⨟ᶠ proj E ⨟ᶠ transportGroupoidFunctor eB = p):
  FamilyIso (rew [Family] (eq_sym eB) in graphFiber p) E.
Proof.
  destruct eB. revert p hp.
  refine (eqIndL (fun (C: StrictGroupoid) eC => forall p: Functor C B,
    transportGroupoidFunctor eC ⨟ᶠ proj E ⨟ᶠ transportGroupoidFunctor eq_refl = p ->
    FamilyIso (graphFiber p) E) _ eC).
  intros p hp.
  assert (h: p = proj E).
  { rewrite <- hp. apply (functorEqPath B.(groupoidStrictness)).
    unshelve econstructor; now intros. }
  clear hp. subst p. now apply graphFamilyIso.
Defined.

Local Lemma graphFiberIsoOfId {B: StrictGroupoid} (E: Family B)
  (hp: transportGroupoidFunctor eq_refl ⨟ᶠ proj E ⨟ᶠ
       transportGroupoidFunctor eq_refl = proj E):
  graphFiberIsoOf eq_refl eq_refl (proj E) hp = graphFamilyIso E.
Proof.
  cbn [graphFiberIsoOf eqIndL].
  match goal with |- context [eq_rect_r _ _ ?h] =>
    rewrite (@UIP (strictGroupoidFunctorSet (total E) B) _ _ h eq_refl)
  end.
  now reflexivity.
Defined.

Lemma graphFiberIsoOfWhole {B C: StrictGroupoid} {E: Family B}
  (eC: C = total E) (p: Functor C B)
  (hp: transportGroupoidFunctor eC ⨟ᶠ proj E ⨟ᶠ
       transportGroupoidFunctor eq_refl = p):
  graphUnit p ⨟ᶠ familyPathTotal (familyEq (graphFiberIsoOf eq_refl eC p hp)) =
    transportGroupoidFunctor eC.
Proof.
  subst C.
  assert (h: p = proj E).
  { rewrite <- hp. apply (functorEqPath B.(groupoidStrictness)).
    unshelve econstructor; now intros. }
  revert hp. subst p. intro hp.
  rewrite graphFiberIsoOfId, familyEqTotalFunctor.
  apply (functorEqPath (total E).(groupoidStrictness)).
  unshelve econstructor; now intros.
Defined.

(** Displayed groupoids classify functors with a fixed codomain. *)

Local Definition groupoidFunctorPairEq {B C D: StrictGroupoid}
  (e: StrictGroupoidIso C D) (p: Functor C B) (q: Functor D B)
  (h: strictGroupoidIsoFunctor e ⨟ᶠ q = p):
  ((C; p): {G: StrictGroupoid &T Functor G B}) = (D; q).
Proof.
  revert p q h.
  refine (strictGroupoidIsoInd C (fun D e => forall p q,
    strictGroupoidIsoFunctor e ⨟ᶠ q = p ->
    ((C; p): {G: StrictGroupoid &T Functor G B}) = (D; q)) _ D e).
  intros p q h. change (idFunctor C ⨟ᶠ q = p) in h.
  rewrite functorIdL in h. now destruct h.
Defined.

Definition graphFiberTotal {B C: StrictGroupoid} (p: Functor C B):
  ((total (graphFiber p); proj (graphFiber p)):
    {G: StrictGroupoid &T Functor G B}) = (C; p).
Proof.
  symmetry. apply (groupoidFunctorPairEq (graphUnitIso p)).
  apply (functorEqPath B.(groupoidStrictness)). now apply graphUnitProj.
Defined.

Definition graphFiberProj {B: StrictGroupoid} (E: Family B):
  graphFiber (proj E) = E := familyEq (graphFamilyIso E).

Definition familyEquivFunctor (B: StrictGroupoid):
  Equiv (Family B) {G: StrictGroupoid &T Functor G B}.
Proof.
  refine (qinvEquiv (fun E => (total E; proj E))
    (fun p => graphFiber p.2) graphFiberProj _).
  intros [C p]. now apply graphFiberTotal.
Defined.
