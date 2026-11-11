(** Strictification of groupoid diagrams on the semi-shape category. A set
    cover of all levels gives a strict diagram whose completion is the given
    weak diagram. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Notation NatLemmas Truncation.
From Bonak.Lib Require Import HGpd.
From Bonak.Category Require Import Category.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presheaf.Strictification Require Import ChartDiagram
  DiagramCompletion DiagramCompletionUnit.
From Bonak.Category.Groupoid Require Import Strict WeakEquivalence.
From Bonak.Category.Bicategory Require Import HGpdBicat LocallyDiscrete Pseudofunctor
  LocallyDiscretePseudofunctor.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Pseudofunctor.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module GpdPseudofunctor := Gpd.Pseudofunctor.

Module PresheafStrictification (Tr: PropositionalTruncation)
  (Complete: CompletionDiagramsSig Tr).
  Import Tr.
  Module Covers := GroupoidSetCovers Tr.
  Module TF := Covers.W.TF.
  Module Coverage := ChartDiagram.ChartCoverage Tr.
  Module Comparison := CompletionComparisonsOn Tr Complete.

  Definition totalDiagramCells {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat): HGpd :=
    gsigT (A := hgpdOfHSet {| Dom := nat; UIP := @natUIP |})
      (fun n => Q.(psObj) n).

  Definition strictDiagramOfCover {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat)
    (cover: Covers.SetCover (totalDiagramCells Q)):
    Functor (Op (νSemiShape arity)) StrictGroupoidCat :=
    chartDiagram (contractPseudofunctor Q)
      cover.1 (fun s => (cover.2.1 s).1) (fun s => (cover.2.1 s).2).

  Definition strictDiagramOfCoverEq {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat)
    (cover: Covers.SetCover (totalDiagramCells Q)):
    Complete.completeDiagram (strictDiagramOfCover Q cover) = Q :=
    Comparison.completeDiagramEq (strictDiagramOfCover Q cover)
      (contractPseudofunctor Q)
      (chartDiagramEvaluation (contractPseudofunctor Q)
        cover.1 (fun s => (cover.2.1 s).1) (fun s => (cover.2.1 s).2))
      (Coverage.chartEvaluationWeak (contractPseudofunctor Q)
        cover.1 (fun s => (cover.2.1 s).1) (fun s => (cover.2.1 s).2) cover.2.2)
    • secEq (locallyDiscretePseudofunctorEquiv (Op (νSemiShape arity))) Q.

  Definition completeDiagramSurjective (covers: Covers.SetsCover1Types)
    {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat):
    merely {F: Functor (Op (νSemiShape arity)) StrictGroupoidCat &T Complete.completeDiagram F = Q} :=
    TF.trMap
      (fun cover => (strictDiagramOfCover Q cover; strictDiagramOfCoverEq Q cover))
      (covers (totalDiagramCells Q)).

  (** The objects of a strict level and its completion unit cover the
      corresponding completed level. *)
  Definition completedDiagramLevelCover {arity: HSet}
    (F: Functor (Op (νSemiShape arity)) StrictGroupoidCat) n:
    Covers.SetCover ((Complete.completeDiagram F).(psObj) n).
  Proof.
    rewrite Complete.completeDiagramObj.
    now exact (Covers.weakEquivalenceCover
      (Complete.P.completedPaths (F.(fobj) n))
      (Complete.P.pathCompletionUnit (F.(fobj) n))
      (Complete.P.pathCompletionUnitWeak (F.(fobj) n))).
  Defined.

  Local Definition constantPresentation (arity: HSet) (X: HGpd): νGpdPresentation arity.
  Proof.
    refine {| G0 := fun _ => X;
      GFace := fun _ _ _ _ x => x;
      GFaceCoh := fun _ _ _ _ _ _ _ _ => eq_refl |}.
    now intros.
  Defined.

  (** Strictification of constant presheaves already implies the covering
      principle for all 1-types. Any fixed arity suffices. *)
  Definition completeDiagramSurjectiveCovers {arity: HSet}
    (surjective: forall Q: Pseudofunctor
      (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat,
      merely {F: Functor (Op (νSemiShape arity)) StrictGroupoidCat &T Complete.completeDiagram F = Q}):
    Covers.SetsCover1Types.
  Proof.
    intro X. refine (TF.trMap _
      (surjective (GpdPseudofunctor.toPseudofunctor arity (constantPresentation arity X)))).
    intros [F e].
    now exact (rew [fun Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat =>
      Covers.SetCover (Q.(psObj) 0)] e in
      completedDiagramLevelCover F 0).
  Defined.

  Definition completeDiagramSurjectiveCoverEquiv (arity: HSet):
    Equiv (forall Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpdBicat,
      merely {F: Functor (Op (νSemiShape arity)) StrictGroupoidCat &T Complete.completeDiagram F = Q})
      Covers.SetsCover1Types :=
    qinvEquiv completeDiagramSurjectiveCovers
      (fun covers => completeDiagramSurjective covers)
      (fun _ => piHProp (fun Q => merelyProp _) _ _)
      (fun _ => piHProp (fun X => merelyProp _) _ _).
End PresheafStrictification.
