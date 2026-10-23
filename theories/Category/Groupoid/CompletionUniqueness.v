Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Category Groupoid FunctorAlgebra.
From Bonak.Category.Groupoid Require Import Precomposition WeakEquivalence.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Two weak presentations by the same groupoid have equivalent univalent
    targets. The comparison functors and their inverse laws follow from descent. *)
Module CompletionUniqueness (T: PropositionalTruncation).
  Module P := GroupoidPrecomposition T.
  Import P P.D P.D.W.
  Set Universe Polymorphism.

  Section Compare.
  Context {G: Groupoid} {U V: UnivalentGroupoid}
    (i: Functor G U) (wi: IsWeakEquivalence i)
    (j: Functor G V) (wj: IsWeakEquivalence j).

  Definition compareCompletions: Functor U V := descend i wi V j.
  Definition compareCompletionsBack: Functor V U := descend j wj U i.

  Lemma compareUnit: compFunctor i compareCompletions = j.
  Proof. now exact (secEq (precomposeFunctorEquiv i wi V) j). Qed.

  Lemma compareBackUnit: compFunctor j compareCompletionsBack = i.
  Proof. now exact (secEq (precomposeFunctorEquiv j wj U) i). Qed.

  Lemma compareRet:
    compFunctor compareCompletions compareCompletionsBack = idFunctor U.
  Proof.
    apply (eqvInj (precomposeFunctorEquiv i wi U)).
    change (compFunctor i (compFunctor compareCompletions compareCompletionsBack)
      = compFunctor i (idFunctor U)).
    now rewrite <- functorAssocEq, compareUnit, compareBackUnit, functorIdR.
  Qed.

  Lemma compareSec:
    compFunctor compareCompletionsBack compareCompletions = idFunctor V.
  Proof.
    apply (eqvInj (precomposeFunctorEquiv j wj V)).
    change (compFunctor j (compFunctor compareCompletionsBack compareCompletions)
      = compFunctor j (idFunctor V)).
    now rewrite <- functorAssocEq, compareBackUnit, compareUnit, functorIdR.
  Qed.

  Definition comparisonObjectEquiv: Equiv U.(CObj) V.(CObj) :=
    qinvEquiv compareCompletions.(fobj) compareCompletionsBack.(fobj)
      (fun a => f_equal (fun F => F.(fobj) a) compareRet)
      (fun b => f_equal (fun F => F.(fobj) b) compareSec).

  End Compare.
End CompletionUniqueness.
