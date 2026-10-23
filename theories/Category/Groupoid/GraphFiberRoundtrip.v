(** Strict fiber and total-groupoid roundtrips, on objects and arrows. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export GraphFiber.
From Bonak.Category.Groupoid Require Import FamilyIdentity.
From Bonak.Lib Require Import Equiv HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Definition graphUnitIso {C B: HSetGroupoid} (p: Functor C B):
  HSetGroupoidIso C (total (graphFiber p)).
Proof.
  now refine (@Build_HSetGroupoidIso C (total (graphFiber p))
    (qinvEquiv (graphUnit p).(fobj) (graphTotal p).(fobj)
      (fun _ => eq_refl) (graphObjectEta p))
    (fun x y => idEquiv) (fun x => eq_refl) (fun x y z f g => eq_refl)).
Defined.

Definition graphFamilyObj {G: HSetGroupoid} (E: Family G) {x: G}
  (a: (graphFiber (proj E)).(dobj) x): E.(dobj) x :=
  rew [fun y => E.(dobj) y] (eq_sym a.2) in a.1.2.

Definition graphFamilyPoint {G: HSetGroupoid} (E: Family G) {x: G}
  (a: E.(dobj) x): (graphFiber (proj E)).(dobj) x :=
  graphPoint (proj E) (x; a).

Definition graphFamilyObjEquiv {G: HSetGroupoid} (E: Family G) (x: G):
  Equiv ((graphFiber (proj E)).(dobj) x) (E.(dobj) x).
Proof.
  refine (qinvEquiv (graphFamilyObj E) (graphFamilyPoint E) _ _).
  - intros [[y a] e]. cbn in e. now destruct e.
  - now intros.
Defined.

Definition graphFamilyHom {G: HSetGroupoid} (E: Family G) {x y: G}
  (a: (graphFiber (proj E)).(dobj) x) (b: (graphFiber (proj E)).(dobj) y):
  Equiv ((graphFiber (proj E)).(dhom) a b)
    (E.(dhom) (graphFamilyObj E a) (graphFamilyObj E b)).
Proof.
  destruct a as [[x' a] p], b as [[y' b] q]. cbn in p, q.
  destruct p, q. now exact idEquiv.
Defined.

Definition graphFamilyMap {G: HSetGroupoid} (E: Family G):
  Map (graphFiber (proj E)) E (idFunctor G).
Proof.
  refine (@Build_Map G G (graphFiber (proj E)) E (idFunctor G)
    (fun x a => graphFamilyObj E a)
    (fun x y a b => graphFamilyHom E a b) _ _ _).
  - intros x [[y a] p]. cbn in p. now destruct p.
  - intros x y z [[x' a] p] [[y' b] q] [[z' c] r] f g.
    cbn in p, q, r. now destruct p, q, r.
  - intros x y [[x' a] p] [[y' b] q] f.
    cbn in p, q. now destruct p, q.
Defined.

Definition graphFamilyIso {G: HSetGroupoid} (E: Family G):
  FamilyIso (graphFiber (proj E)) E := {|
  fisoObj := graphFamilyObjEquiv E;
  fisoHom x y a b := graphFamilyHom E a b;
  fisoBase x y a b := (graphFamilyMap E).(mbase);
  fisoId x a := (graphFamilyMap E).(mid) a;
  fisoComp x y z a b c := (graphFamilyMap E).(mcomp);
|}.

Definition graphFiberIsoOf {B A C: HSetGroupoid} (eB: B = A)
  {E: Family B} (eC: C = total E) (p: Functor C A)
  (hp: transportGroupoidFunctor eC ⨟ᶠ proj E ⨟ᶠ transportGroupoidFunctor eB = p):
  FamilyIso (rew [Family] (eq_sym eB) in graphFiber p) E.
Proof.
  destruct eB. revert p hp.
  refine (eqIndL (fun (C: HSetGroupoid) eC => forall p: Functor C B,
    transportGroupoidFunctor eC ⨟ᶠ proj E ⨟ᶠ transportGroupoidFunctor eq_refl = p ->
    FamilyIso (graphFiber p) E) _ eC).
  intros p hp.
  assert (h: p = proj E).
  { rewrite <- hp. apply (functorEqPath B.(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  clear hp. subst p. now apply graphFamilyIso.
Defined.

Local Lemma graphFiberIsoOfId {B: HSetGroupoid} (E: Family B)
  (hp: transportGroupoidFunctor eq_refl ⨟ᶠ proj E ⨟ᶠ
       transportGroupoidFunctor eq_refl = proj E):
  graphFiberIsoOf eq_refl eq_refl (proj E) hp = graphFamilyIso E.
Proof.
  cbn [graphFiberIsoOf eqIndL].
  match goal with |- context [eq_rect_r _ _ ?h] =>
    rewrite (@UIP (hsetFunctorSet (total E) B) _ _ h eq_refl)
  end.
  now reflexivity.
Defined.

Lemma graphFiberIsoOfWhole {B C: HSetGroupoid} {E: Family B}
  (eC: C = total E) (p: Functor C B)
  (hp: transportGroupoidFunctor eC ⨟ᶠ proj E ⨟ᶠ
       transportGroupoidFunctor eq_refl = p):
  graphUnit p ⨟ᶠ familyPathTotal (familyEq (graphFiberIsoOf eq_refl eC p hp)) =
    transportGroupoidFunctor eC.
Proof.
  subst C.
  assert (h: p = proj E).
  { rewrite <- hp. apply (functorEqPath B.(hsetGroupoidUIP)).
    unshelve econstructor; now intros. }
  revert hp. subst p. intro hp.
  rewrite graphFiberIsoOfId, familyEqTotalFunctor.
  apply (functorEqPath (total E).(hsetGroupoidUIP)).
  unshelve econstructor; now intros.
Defined.
