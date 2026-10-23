Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Category Groupoid UnivalenceFacts FunctorUnivalence.
From Bonak.Category.Groupoid Require Import WeakEquivalence Descent.
From Stdlib.Logic Require Import FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Natural transformations extend uniquely along a weak equivalence of
    groupoids. With a univalent target, descent also makes precomposition an
    equivalence on functors. *)
Module GroupoidPrecomposition (T: PropositionalTruncation).
  Import T.
  Module D := GroupoidDescent T.
  Import D D.W D.W.TF.
  Set Universe Polymorphism.

  Section Precomposition.
  Context {G H: Groupoid} (F: Functor G H) (w: IsWeakEquivalence F).
  Context (U: Groupoid).

  Section Transformations.
  Context (K L: Functor H U) (α: NatTrans (compFunctor F K) (compFunctor F L)).

  Definition Component (y: H.(CObj)): Type :=
    {v: U.(CHom) (K.(fobj) y) (L.(fobj) y) &T
     forall r: Representative F y,
       K.(fhom) r.2 ⨟ v = α.(ncomp) r.1 ⨟ L.(fhom) r.2}.

  Lemma componentProp (y: H.(CObj)): IsHProp (Component y).
  Proof.
    intros [v hv] [v' hv'].
    assert (e: v = v').
    { refine (trRec (@UIP (U.(CHom) (K.(fobj) y) (L.(fobj) y)) v v')
        _ (weakEssentiallySurjective _ w y)).
      intro r. apply (groupoidCancelL (K.(fhom) r.2)). now rewrite hv, hv'. }
    refine (eq_existT_curried e _).
    apply functional_extensionality_dep; intro r. now apply UIP.
  Qed.

  Definition componentFrom (y: H.(CObj)) (r: Representative F y): Component y.
  Proof.
    refine (ginv (K.(fhom) r.2) ⨟ (α.(ncomp) r.1 ⨟ L.(fhom) r.2); _).
    intro s.
    pose (h := representativeArrow F w s r).
    assert (e: F.(fhom) h ⨟ r.2 = s.2) by now apply representativeComm.
    rewrite <- e, K.(fcomp).
    rewrite (U.(cassoc) (K.(fhom) (F.(fhom) h)) (K.(fhom) r.2)).
    rewrite <- (U.(cassoc) (K.(fhom) r.2) (ginv (K.(fhom) r.2))), ginvR, cidl.
    pose proof (α.(nnat) h) as n.
    change (K.(fhom) (F.(fhom) h) ⨟ α.(ncomp) r.1
      = α.(ncomp) s.1 ⨟ L.(fhom) (F.(fhom) h)) in n.
    rewrite <- cassoc.
    refine (f_equal (fun v => v ⨟ L.(fhom) r.2) n • _).
    now exact (U.(cassoc) (α.(ncomp) s.1) (L.(fhom) (F.(fhom) h)) (L.(fhom) r.2)
      • f_equal (fun v => α.(ncomp) s.1 ⨟ v) (eq_sym (L.(fcomp) (F.(fhom) h) r.2))).
  Defined.

  Definition extendComponent (y: H.(CObj)): Component y :=
    trRec (componentProp y) (componentFrom y) (weakEssentiallySurjective _ w y).

  Definition extendNat: NatTrans K L.
  Proof.
    refine (@Build_NatTrans H U K L (fun y => (extendComponent y).1) _).
    intros y z k.
    refine (trRec (@UIP (U.(CHom) (K.(fobj) y) (L.(fobj) z)) _ _)
      _ (weakEssentiallySurjective _ w y)).
    intro r. apply (groupoidCancelL (K.(fhom) r.2)).
    rewrite <- cassoc, <- K.(fcomp).
    refine ((extendComponent z).2 (moveRepresentative F k r) • _).
    change (α.(ncomp) r.1 ⨟ L.(fhom) (r.2 ⨟ k)
      = K.(fhom) r.2 ⨟ ((extendComponent y).1 ⨟ L.(fhom) k)).
    now exact (f_equal (fun v => α.(ncomp) r.1 ⨟ v) (L.(fcomp) r.2 k)
      • eq_sym (U.(cassoc) (α.(ncomp) r.1) (L.(fhom) r.2) (L.(fhom) k))
      • f_equal (fun v => v ⨟ L.(fhom) k) (eq_sym ((extendComponent y).2 r))
      • U.(cassoc) (K.(fhom) r.2) (extendComponent y).1 (L.(fhom) k)).
  Defined.

  Lemma restrictExtend: whiskerLNat F extendNat = α.
  Proof.
    apply natTransEq; intro a.
    pose proof ((extendComponent (F.(fobj) a)).2 (canonicalRepresentative F a)) as e.
    change (K.(fhom) (cid (F.(fobj) a)) ⨟ (extendComponent (F.(fobj) a)).1
      = α.(ncomp) a ⨟ L.(fhom) (cid (F.(fobj) a))) in e.
    rewrite K.(fid), L.(fid), cidl, cidr in e. now exact e.
  Qed.
  End Transformations.

  Lemma precomposeFaithful {K L: Functor H U} (α β: NatTrans K L)
    (e: whiskerLNat F α = whiskerLNat F β): α = β.
  Proof.
    apply natTransEq; intro y.
    refine (trRec (@UIP (U.(CHom) (K.(fobj) y) (L.(fobj) y)) _ _)
      _ (weakEssentiallySurjective _ w y)).
    intros [a u]. apply (groupoidCancelL (K.(fhom) u)).
    rewrite α.(nnat), β.(nnat).
    now exact (f_equal (fun n: NatTrans (compFunctor F K) (compFunctor F L) =>
      n.(ncomp) a ⨟ L.(fhom) u) e).
  Qed.

  End Precomposition.

  Section UnivalentPrecomposition.
  Context {G H: Groupoid} (F: Functor G H) (w: IsWeakEquivalence F).
  Context (U: UnivalentGroupoid).

  Definition precomposeFunctorEquiv: Equiv (Functor H U) (Functor G U).
  Proof.
    refine (qinvEquiv (compFunctor F) (descend F w U) _ _).
    - intro E. apply (categoryIsoPath (functorCategoryUnivalence U.(groupoidUnivalence))).
      pose (α := extendNat F w U (descend F w U (compFunctor F E)) E
        (natInv (descentUnit F w U (compFunctor F E)))).
      now exact (@Build_Iso (functorCategory H U) _ _ α (natInvertible α)).
    - intro E. apply (categoryIsoPath (functorCategoryUnivalence U.(groupoidUnivalence))).
      pose (α := natInv (descentUnit F w U E)).
      now exact (@Build_Iso (functorCategory G U) _ _ α (natInvertible α)).
  Defined.

  End UnivalentPrecomposition.
End GroupoidPrecomposition.
