Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Contractible Truncation.
From Bonak.Category Require Import Category Groupoid.
From Bonak.Category.Groupoid Require Import WeakEquivalence.
From Stdlib.Logic Require Import FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Descent along fully faithful, essentially surjective functors of groupoids.
    A compatible cone of images of representatives is contractible in a
    univalent target. Its center supplies the descended object without choosing
    a representative from a propositional truncation. *)
Local Definition arrowTotal (G: UnivalentGroupoid) (a: G.(CObj)):
  Contr {b: G.(CObj) &T G.(CHom) a b}.
Proof.
  exists (a; cid a). intros [b f].
  pose (p := homToId f).
  assert (h: idToHom p = f) by now apply idToHomToId.
  refine (eq_existT_curried p _). now exact h.
Defined.

Module GroupoidDescent (T: PropositionalTruncation).
  Import T.
  Module W := WeakEquivalences T.
  Import W W.TF.
  Set Universe Polymorphism.

  Section Descent.
  Context {G H: Groupoid} (F: Functor G H) (w: IsWeakEquivalence F).
  Context (U: UnivalentGroupoid) (E: Functor G U).

  Definition Representative (y: H.(CObj)): Type :=
    {a: G.(CObj) &T H.(CHom) (F.(fobj) a) y}.

  Definition liftArrow {a b: G.(CObj)}
    (f: H.(CHom) (F.(fobj) a) (F.(fobj) b)): G.(CHom) a b :=
    invEq (ffEquiv F (weakFullyFaithful _ w) a b) f.

  Lemma liftArrowBeta {a b: G.(CObj)}
    (f: H.(CHom) (F.(fobj) a) (F.(fobj) b)): F.(fhom) (liftArrow f) = f.
  Proof. now apply (secEq (ffEquiv F (weakFullyFaithful _ w) a b)). Qed.

  Definition representativeArrow {y: H.(CObj)} (r s: Representative y):
    G.(CHom) r.1 s.1 := liftArrow (r.2 ⨟ ginv s.2).

  Lemma representativeComm {y: H.(CObj)} (r s: Representative y):
    F.(fhom) (representativeArrow r s) ⨟ s.2 = r.2.
  Proof.
    unfold representativeArrow. rewrite liftArrowBeta, cassoc, ginvL.
    now apply cidr.
  Qed.

  Lemma representativeUnique {y: H.(CObj)} (r s: Representative y)
    (f: G.(CHom) r.1 s.1) (e: F.(fhom) f ⨟ s.2 = r.2):
    f = representativeArrow r s.
  Proof.
    apply (eqvInj (ffEquiv F (weakFullyFaithful _ w) r.1 s.1)).
    apply (groupoidCancelR s.2). now exact (e • eq_sym (representativeComm r s)).
  Qed.

  Lemma representativeComp {y: H.(CObj)} (r s t: Representative y):
    representativeArrow r s ⨟ representativeArrow s t = representativeArrow r t.
  Proof.
    apply representativeUnique. now rewrite F.(fcomp), cassoc, 2 representativeComm.
  Qed.

  Definition moveRepresentative {y z: H.(CObj)} (k: H.(CHom) y z)
    (r: Representative y): Representative z := (r.1; r.2 ⨟ k).

  Lemma representativeMove {y z: H.(CObj)} (k: H.(CHom) y z)
    (r s: Representative y):
    representativeArrow (moveRepresentative k r) (moveRepresentative k s)
    = representativeArrow r s.
  Proof.
    apply eq_sym, representativeUnique. cbn.
    now rewrite <- cassoc, representativeComm.
  Qed.

  Definition Cone (y: H.(CObj)): Type :=
    {b: U.(CObj) &T
      {α: forall r: Representative y, U.(CHom) (E.(fobj) r.1) b &T
       forall r s, E.(fhom) (representativeArrow r s) ⨟ α s = α r}}.

  Definition coneFrom (y: H.(CObj)) (r: Representative y)
    (z: {b: U.(CObj) &T U.(CHom) (E.(fobj) r.1) b}): Cone y.
  Proof.
    refine (z.1; ((fun s => E.(fhom) (representativeArrow s r) ⨟ z.2); _)).
    intros s t. now rewrite <- cassoc, <- E.(fcomp), representativeComp.
  Defined.

  Definition coneEvaluate (y: H.(CObj)) (r: Representative y) (c: Cone y):
    {b: U.(CObj) &T U.(CHom) (E.(fobj) r.1) b} := (c.1; c.2.1 r).

  Lemma coneFromEvaluate (y: H.(CObj)) (r: Representative y) (c: Cone y):
    coneFrom y r (coneEvaluate y r c) = c.
  Proof.
    destruct c as [b [α h]]. refine (eq_existT_curried eq_refl _).
    assert (e: (fun s => E.(fhom) (representativeArrow s r) ⨟ α r) = α).
    { apply functional_extensionality_dep; intro s. now apply h. }
    refine (eq_existT_curried e _).
    repeat (apply functional_extensionality_dep; intro). now apply UIP.
  Qed.

  Definition coneContrFrom (y: H.(CObj)) (r: Representative y): Contr (Cone y) :=
    retractContr (coneEvaluate y r) (coneFrom y r) (coneFromEvaluate y r)
      (arrowTotal U (E.(fobj) r.1)).

  Definition coneContr (y: H.(CObj)): Contr (Cone y) :=
    trRec contrProp (coneContrFrom y) (weakEssentiallySurjective _ w y).

  Definition descentCone (y: H.(CObj)): Cone y := (coneContr y).1.
  Definition descentObject (y: H.(CObj)): U.(CObj) := (descentCone y).1.
  Definition descentLeg {y: H.(CObj)} (r: Representative y):
    U.(CHom) (E.(fobj) r.1) (descentObject y) := (descentCone y).2.1 r.

  Lemma descentLegComm {y: H.(CObj)} (r s: Representative y):
    E.(fhom) (representativeArrow r s) ⨟ descentLeg s = descentLeg r.
  Proof. now exact ((descentCone y).2.2 r s). Qed.

  Definition DescentArrow {y z: H.(CObj)} (k: H.(CHom) y z): Type :=
    {f: U.(CHom) (descentObject y) (descentObject z) &T
      forall r: Representative y, descentLeg r ⨟ f = descentLeg (moveRepresentative k r)}.

  Lemma descentArrowProp {y z: H.(CObj)} (k: H.(CHom) y z): IsHProp (DescentArrow k).
  Proof.
    intros [f hf] [g hg].
    assert (e: f = g).
    { refine (trRec (@UIP (U.(CHom) (descentObject y) (descentObject z)) f g)
        _ (weakEssentiallySurjective _ w y)).
      intro r. apply (groupoidCancelL (descentLeg r)). now rewrite hf, hg. }
    refine (eq_existT_curried e _).
    apply functional_extensionality_dep; intro r. now apply UIP.
  Qed.

  Definition descentArrowFrom {y z: H.(CObj)} (k: H.(CHom) y z)
    (r: Representative y): DescentArrow k.
  Proof.
    refine (ginv (descentLeg r) ⨟ descentLeg (moveRepresentative k r); _).
    intro s. rewrite <- (descentLegComm s r).
    rewrite (U.(cassoc) (E.(fhom) (representativeArrow s r)) (descentLeg r)).
    rewrite <- (U.(cassoc) (descentLeg r) (ginv (descentLeg r))), ginvR, cidl.
    rewrite <- (representativeMove k s r).
    now exact (descentLegComm (moveRepresentative k s) (moveRepresentative k r)).
  Defined.

  Definition descentArrow {y z: H.(CObj)} (k: H.(CHom) y z):
    U.(CHom) (descentObject y) (descentObject z) :=
    (trRec (descentArrowProp k) (descentArrowFrom k)
      (weakEssentiallySurjective _ w y)).1.

  Lemma descentArrowLeg {y z: H.(CObj)} (k: H.(CHom) y z) (r: Representative y):
    descentLeg r ⨟ descentArrow k = descentLeg (moveRepresentative k r).
  Proof.
    now exact ((trRec (descentArrowProp k) (descentArrowFrom k)
      (weakEssentiallySurjective _ w y)).2 r).
  Qed.

  Lemma descentArrowId (y: H.(CObj)): descentArrow (cid y) = cid (descentObject y).
  Proof.
    refine (trRec (@UIP (U.(CHom) (descentObject y) (descentObject y)) _ _)
      _ (weakEssentiallySurjective _ w y)).
    intro r. apply (groupoidCancelL (descentLeg r)).
    rewrite descentArrowLeg, cidr. unfold moveRepresentative. now rewrite cidr.
  Qed.

  Lemma descentArrowComp {x y z: H.(CObj)} (f: H.(CHom) x y) (g: H.(CHom) y z):
    descentArrow (f ⨟ g) = descentArrow f ⨟ descentArrow g.
  Proof.
    refine (trRec (@UIP (U.(CHom) (descentObject x) (descentObject z)) _ _)
      _ (weakEssentiallySurjective _ w x)).
    intro r. apply (groupoidCancelL (descentLeg r)).
    change (descentLeg r ⨟ descentArrow (f ⨟ g)
      = descentLeg r ⨟ (descentArrow f ⨟ descentArrow g)).
    rewrite <- cassoc.
    rewrite (descentArrowLeg (f ⨟ g) r), (descentArrowLeg f r).
    refine (_ • eq_sym (descentArrowLeg g (moveRepresentative f r))).
    now exact (@f_equal (H.(CHom) (F.(fobj) r.1) z)
      (U.(CHom) (E.(fobj) r.1) (descentObject z))
      (fun t => @descentLeg z (r.1; t)) _ _ (eq_sym (H.(cassoc) r.2 f g))).
  Qed.

  Definition descend: Functor H U := {|
    fobj := descentObject;
    fhom y z k := descentArrow k;
    fid := descentArrowId;
    fcomp x y z f g := descentArrowComp f g;
  |}.

  Definition canonicalRepresentative (a: G.(CObj)): Representative (F.(fobj) a) :=
    (a; cid (F.(fobj) a)).

  Lemma representativeCanonical {a b: G.(CObj)} (f: G.(CHom) a b):
    representativeArrow (moveRepresentative (F.(fhom) f) (canonicalRepresentative a))
      (canonicalRepresentative b) = f.
  Proof.
    apply eq_sym, representativeUnique. cbn. now rewrite cidl, cidr.
  Qed.

  Definition descentUnit: NatTrans E (compFunctor F descend).
  Proof.
    refine {| ncomp a := descentLeg (canonicalRepresentative a); nnat := _ |}.
    intros a b f.
    change (E.(fhom) f ⨟ descentLeg (canonicalRepresentative b)
      = descentLeg (canonicalRepresentative a) ⨟ descentArrow (F.(fhom) f)).
    rewrite descentArrowLeg.
    refine (_ • descentLegComm
      (moveRepresentative (F.(fhom) f) (canonicalRepresentative a))
      (canonicalRepresentative b)).
    now rewrite representativeCanonical.
  Defined.
  End Descent.
End GroupoidDescent.
