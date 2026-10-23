(** Coherent evaluations descend along componentwise weak equivalences.
    The comparison transformations are determined on represented objects. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Funext RewLemmas Truncation.
From Bonak.νGpd Require Import HGpd.
From Bonak.Strictification Require Import DiagramEvaluation.
From Bonak.Category.Groupoid Require Import CompletionUniqueness Precomposition SetBased WeakEquivalence.
From Bonak.Category.Bicategory Require Import PathDiagram PathGroupoid Pseudonatural
  LocallyDiscretePseudofunctor HGpdDiagramEq.
Set Primitive Projections.
Set Keyed Unification.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Lemma pathInverse {Z: HGpd} {x y: Z} (p: x = y):
  @ginv (pathGpd Z) x y p = eq_sym p.
Proof.
  destruct p. pose proof (@ginvR (pathGpd Z) x x eq_refl) as h.
  change (eq_refl • @ginv (pathGpd Z) x x eq_refl = eq_refl) in h.
  now rewrite eq_trans_refl_l in h.
Qed.

Module DiagramDescent (Tr: PropositionalTruncation).
  Module U := CompletionUniqueness Tr.
  Import U.P U.P.D U.P.D.W.
  Set Universe Polymorphism.

  Section Comparison.
  Context {C: Category} {D: Functor C HSetGroupoidCat}
    {Y X: PathDiagramFamily C}
    (E: DiagramEvaluation D Y) (Q: DiagramEvaluation D X)
    (wE: forall a, IsWeakEquivalence (E.(evalFunctor) a)).
  Local Abbreviation Yd := (pathData C Y.(pfObj) Y.(pfStr)).
  Local Abbreviation Xd := (pathData C X.(pfObj) X.(pfStr)).
  Local Abbreviation Ei a := (E.(evalFunctor) a).
  Local Abbreviation Qi a := (Q.(evalFunctor) a).

  Definition comparisonFunctor a: Functor (pathGpd (Y.(pfObj) a)) (pathGpd (X.(pfObj) a)) :=
    descend (Ei a) (wE a) (pathGpd (X.(pfObj) a)) (Qi a).

  Definition comparisonUnit a:
    NatTrans (Qi a) (Ei a ⨟ᶠ comparisonFunctor a) :=
    descentUnit (Ei a) (wE a) (pathGpd (X.(pfObj) a)) (Qi a).

  Definition comparisonSource {a b} (f: C.(CHom) a b):
    NatTrans (Ei a ⨟ᶠ (pathFunctor (Yd.(phom) f) ⨟ᶠ comparisonFunctor b))
      (Ei a ⨟ᶠ (comparisonFunctor a ⨟ᶠ pathFunctor (Xd.(phom) f))).
  Proof.
    pose (r := natInv (whiskerRNat (E.(evalNaturality) f) (comparisonFunctor b))).
    pose (s := whiskerLNat (D.(fhom) f) (natInv (comparisonUnit b))).
    pose (t := whiskerRNat (comparisonUnit a) (pathFunctor (Xd.(phom) f))).
    pose (r' := @Build_NatTrans (D.(fobj) a) (pathGpd (X.(pfObj) b))
      (Ei a ⨟ᶠ (pathFunctor (Yd.(phom) f) ⨟ᶠ comparisonFunctor b))
      (D.(fhom) f ⨟ᶠ (Ei b ⨟ᶠ comparisonFunctor b)) r.(ncomp)
      (fun x y h => r.(nnat) h)).
    pose (t' := @Build_NatTrans (D.(fobj) a) (pathGpd (X.(pfObj) b))
      (Qi a ⨟ᶠ pathFunctor (Xd.(phom) f))
      (Ei a ⨟ᶠ (comparisonFunctor a ⨟ᶠ pathFunctor (Xd.(phom) f))) t.(ncomp)
      (fun x y h => t.(nnat) h)).
    now exact (compNatTrans r' (compNatTrans s (compNatTrans (Q.(evalNaturality) f) t'))).
  Defined.

  Definition comparisonNaturality {a b} (f: C.(CHom) a b):
    NatTrans (pathFunctor (Yd.(phom) f) ⨟ᶠ comparisonFunctor b)
      (comparisonFunctor a ⨟ᶠ pathFunctor (Xd.(phom) f)) :=
    extendNat (Ei a) (wE a) (pathGpd (X.(pfObj) b)) _ _ (comparisonSource f).

  Lemma comparisonSquare {a b} (f: C.(CHom) a b) (x: D.(fobj) a):
    (comparisonUnit b).(ncomp) ((D.(fhom) f).(fobj) x)
      • (f_equal (comparisonFunctor b).(fobj) ((E.(evalNaturality) f).(ncomp) x)
      • (comparisonNaturality f).(ncomp) ((Ei a).(fobj) x))
    = (Q.(evalNaturality) f).(ncomp) x
      • f_equal (Xd.(phom) f) ((comparisonUnit a).(ncomp) x).
  Proof.
    pose proof (f_equal (fun n => n.(ncomp) x)
      (restrictExtend (Ei a) (wE a) (pathGpd (X.(pfObj) b)) _ _ (comparisonSource f))) as h.
    change ((comparisonNaturality f).(ncomp) ((Ei a).(fobj) x)
      = ginv ((comparisonFunctor b).(fhom) ((E.(evalNaturality) f).(ncomp) x))
        • (ginv ((comparisonUnit b).(ncomp) ((D.(fhom) f).(fobj) x))
        • ((Q.(evalNaturality) f).(ncomp) x
        • f_equal (Xd.(phom) f) ((comparisonUnit a).(ncomp) x)))) in h.
    rewrite 2 pathInverse, pathFunctorFhom in h. rewrite h, 2 transSymCancelL.
    now reflexivity.
  Qed.

  Lemma comparisonInduction a (R: Y.(pfObj) a -> Type)
    (hR: forall y, IsHProp (R y)) (h: forall x, R ((Ei a).(fobj) x)):
    forall y, R y.
  Proof.
    intro y. refine (Tr.trRec (hR y) _ (weakEssentiallySurjective _ (wE a) y)).
    intros [x p]. now exact (rew [R] p in h x).
  Defined.

  Local Abbreviation Ki a := (comparisonFunctor a).(fobj).
  Local Abbreviation β a := (comparisonUnit a).(ncomp).
  Local Abbreviation δ a b f := (@comparisonNaturality a b f).(ncomp).
  Local Abbreviation ε a b f := (@evalNaturality _ _ _ E a b f).(ncomp).
  Local Abbreviation γ a b f := (@evalNaturality _ _ _ Q a b f).(ncomp).

  Lemma comparisonUnitLaw a (z: Y.(pfObj) a):
    f_equal (Ki a) (happly (Yd.(pid) a) z) =
    δ a a (C.(cid) a) z • happly (Xd.(pid) a) (Ki a z).
  Proof.
    revert z. apply (comparisonInduction a).
    - intros z p q. now apply GUIP.
    - intro x.
      pose (h := f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) a) =>
        F.(fobj) x) (D.(fid) a)).
      pose proof (comparisonSquare (C.(cid) a) x) as s.
      pose proof (E.(evalUnit) a x) as eu.
      pose proof (Q.(evalUnit) a x) as qu.
      pose proof (homotopyNat (Q.(evalFunctor) a).(fobj)
        (fun x => Ki a ((E.(evalFunctor) a).(fobj) x)) (β a) h) as un.
      pose proof (homotopyNat (Xd.(phom) (C.(cid) a)) (fun x => x)
        (happly (Xd.(pid) a)) (β a x)) as xu.
      rewrite f_equal_id in xu.
      apply (transCancelL (f_equal (Ki a) ((E.(evalNaturality) (C.(cid) a)).(ncomp) x))).
      apply (transCancelL (β a ((D.(fhom) (C.(cid) a)).(fobj) x))).
      rewrite <- eq_trans_map_distr, eu.
      rewrite (f_equal_compose (E.(evalFunctor) a).(fobj) (Ki a)).
      fold h. rewrite <- un.
      rewrite <- (eqTransAssoc
        (f_equal (Ki a) ((E.(evalNaturality) (C.(cid) a)).(ncomp) x))).
      rewrite <- eqTransAssoc, s, eqTransAssoc, xu, <- eqTransAssoc, qu.
      now reflexivity.
  Qed.

  Lemma comparisonCompLaw {a b c} (f: C.(CHom) a b) (g: C.(CHom) b c)
    (z: Y.(pfObj) a):
    f_equal (Ki c) (Yd.(pcomp) f g z) • δ a c (f ⨟ g) z
    = δ b c g (Yd.(phom) f z)
      • (f_equal (Xd.(phom) g) (δ a b f z) • Xd.(pcomp) f g (Ki a z)).
  Proof.
    revert z. apply (comparisonInduction a).
    - intros z p q. now apply GUIP.
    - intro x.
      pose (d := f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) c) => F.(fobj) x)
        (D.(fcomp) f g)).
      pose (p := β c ((D.(fhom) (f ⨟ g)).(fobj) x)
        • (f_equal (Ki c) (f_equal (Ei c).(fobj) d)
        • (f_equal (Ki c) (ε b c g ((D.(fhom) f).(fobj) x))
        • f_equal (Ki c) (f_equal (Yd.(phom) g) (ε a b f x))))).
      apply (transCancelL p).
      transitivity (γ a c (f ⨟ g) x • f_equal (Xd.(phom) (f ⨟ g)) (β a x)).
      + pose proof (comparisonSquare (f ⨟ g) x) as h.
        rewrite <- (E.(evalComp) f g x) in h.
        rewrite 3 eq_trans_map_distr, 3 eqTransAssoc in h.
        unfold p. rewrite 3 eqTransAssoc.
        now exact h.
      + apply eq_sym. unfold p.
        rewrite <- 4 eqTransAssoc.
        rewrite f_equal_compose.
        pose proof (homotopyNat (Qi c).(fobj)
          (fun t => Ki c ((Ei c).(fobj) t)) (β c) d) as hd.
        rewrite <- hd.
        pose proof (homotopyNat (fun t => Ki c (Yd.(phom) g t))
          (fun t => Xd.(phom) g (Ki b t)) (δ b c g) (ε a b f x)) as hn.
        rewrite <- f_equal_compose in hn.
        rewrite <- (f_equal_compose (Ki b) (Xd.(phom) g)) in hn.
        rewrite 5 eqTransAssoc.
        rewrite <- (eqTransAssoc
          (f_equal (Ki c) (f_equal (Yd.(phom) g) (ε a b f x)))
          (δ b c g (Yd.(phom) f ((Ei a).(fobj) x)))).
        rewrite hn.
        rewrite eqTransAssoc.
        rewrite <- (eqTransAssoc (f_equal (Ki c) (ε b c g ((D.(fhom) f).(fobj) x)))
          (δ b c g ((Ei b).(fobj) ((D.(fhom) f).(fobj) x)))).
        rewrite <- (eqTransAssoc (β c ((D.(fhom) g).(fobj) ((D.(fhom) f).(fobj) x)))).
        rewrite comparisonSquare.
        rewrite eqTransAssoc.
        rewrite <- (eqTransAssoc
          (f_equal (Xd.(phom) g) (f_equal (Ki b) (ε a b f x)))
          (f_equal (Xd.(phom) g) (δ a b f ((Ei a).(fobj) x)))).
        rewrite <- eq_trans_map_distr.
        rewrite <- (eqTransAssoc (f_equal (Xd.(phom) g) (β b ((D.(fhom) f).(fobj) x)))).
        rewrite <- eq_trans_map_distr.
        rewrite comparisonSquare.
        rewrite eq_trans_map_distr, eqTransAssoc.
        pose proof (homotopyNat
          (fun t => Xd.(phom) g (Xd.(phom) f t)) (Xd.(phom) (f ⨟ g))
          (Xd.(pcomp) f g) (β a x)) as hc.
        rewrite <- f_equal_compose in hc.
        rewrite <- eqTransAssoc, hc, <- 2 eqTransAssoc.
        apply (f_equal (fun p => p • f_equal (Xd.(phom) (f ⨟ g)) (β a x))).
        rewrite 2 eqTransAssoc. now apply Q.(evalComp).
  Qed.
  End Comparison.
End DiagramDescent.

(** Two evaluations of one strict diagram that are componentwise weak
    equivalences identify the target diagrams, including their unit and
    composition comparisons. *)
Unset Keyed Unification.

Module DiagramComparisons (Tr: PropositionalTruncation).
  Module K := DiagramDescent Tr.
  Module W := WeakEquivalences Tr.
  Import K W.

  Definition evaluationComparison {I: Category} {D: Functor I HSetGroupoidCat}
    {Y X: PathDiagramFamily I} (E: DiagramEvaluation D Y) (Q: DiagramEvaluation D X)
    (wE: forall i, IsWeakEquivalence (E.(evalFunctor) i)):
    Pseudonatural (expandPseudofunctor Y) (expandPseudofunctor X) :=
    pathDiagramTransformation Y X
      (fun i => (comparisonFunctor E Q wE i).(fobj))
      (fun i j f => (comparisonNaturality E Q wE f).(ncomp))
      (fun i x => K.comparisonUnitLaw E Q wE i x)
      (fun i j k f g x => K.comparisonCompLaw E Q wE f g x).

  Definition evaluationComparisonEq {I: Category} {D: Functor I HSetGroupoidCat}
    {Y X: PathDiagramFamily I} (E: DiagramEvaluation D Y) (Q: DiagramEvaluation D X)
    (wE: forall i, IsWeakEquivalence (E.(evalFunctor) i))
    (wQ: forall i, IsWeakEquivalence (Q.(evalFunctor) i)):
    expandPseudofunctor Y = expandPseudofunctor X :=
    hgpdPseudofunctorEq (evaluationComparison E Q wE)
      (fun i => (K.U.comparisonObjectEquiv
        (E.(evalFunctor) i) (wE i) (Q.(evalFunctor) i) (wQ i)).(eqvIsEquiv)).
End DiagramComparisons.
