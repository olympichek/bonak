(** Strictification of groupoid diagrams, face presentations, and indexed
    groupoids. A set cover of all levels gives a strict diagram whose
    completion is the given weak diagram; the presentation and indexed
    correspondences transfer this result. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Notation NatLemmas Truncation.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category Require Import Category.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Strictification Require Import ChartDiagram Completion DiagramCompletionUnit.
From Bonak.Category.Groupoid Require Import WeakEquivalence.
From Bonak.Category.Bicategory Require Import HGpd2Cat LocallyDiscrete Pseudofunctor
  LocallyDiscretePseudofunctor.
From Bonak.Presheaf.StrictGpd Require Import Presentation Roundtrip.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor Roundtrip.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Equiv.StrictGpd Require Correspondence.
From Bonak.Equiv.Gpd Require Correspondence.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module StrictRoundtrip := StrictGpd.Roundtrip.
Module GpdPseudofunctor := Gpd.Pseudofunctor.

Module PresentationStrictification (Tr: PropositionalTruncation)
  (Complete: StrictGpdCompletionSig Tr).
  Import Tr.
  Module Covers := GroupoidSetCovers Tr.
  Module TF := Covers.W.TF.
  Module Coverage := ChartDiagram.ChartCoverage Tr.
  Module Comparison := CompletionComparisonsOn Tr Complete.

  Definition totalDiagramCells {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat): HGpd :=
    gsigT (A := hgpdOfHSet {| Dom := nat; UIP := @natUIP |})
      (fun n => Q.(psObj) n).

  Definition strictDiagramOfCover {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat)
    (cover: Covers.SetCover (totalDiagramCells Q)):
    Functor (Op (νSemiShape arity)) HSetGroupoidCat :=
    chartDiagram (contractPseudofunctor Q)
      cover.1 (fun s => (cover.2.1 s).1) (fun s => (cover.2.1 s).2).

  Definition strictDiagramOfCoverEq {arity: HSet}
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat)
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
    (Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat):
    merely {F: Functor (Op (νSemiShape arity)) HSetGroupoidCat &T Complete.completeDiagram F = Q} :=
    TF.trMap
      (fun cover => (strictDiagramOfCover Q cover; strictDiagramOfCoverEq Q cover))
      (covers (totalDiagramCells Q)).

  (** The objects of a strict level and its completion unit cover the
      corresponding completed level. *)
  Definition completedDiagramLevelCover {arity: HSet}
    (F: Functor (Op (νSemiShape arity)) HSetGroupoidCat) n:
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
      (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat,
      merely {F: Functor (Op (νSemiShape arity)) HSetGroupoidCat &T Complete.completeDiagram F = Q}):
    Covers.SetsCover1Types.
  Proof.
    intro X. refine (TF.trMap _
      (surjective (GpdPseudofunctor.toPseudofunctor arity (constantPresentation arity X)))).
    intros [F e].
    now exact (rew [fun Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat =>
      Covers.SetCover (Q.(psObj) 0)] e in
      completedDiagramLevelCover F 0).
  Defined.

  Definition completeDiagramSurjectiveCoverEquiv (arity: HSet):
    Equiv (forall Q: Pseudofunctor (locallyDiscrete (Op (νSemiShape arity))) HGpd2Cat,
      merely {F: Functor (Op (νSemiShape arity)) HSetGroupoidCat &T Complete.completeDiagram F = Q})
      Covers.SetsCover1Types :=
    qinvEquiv completeDiagramSurjectiveCovers
      (fun covers => completeDiagramSurjective covers)
      (fun _ => piHProp (fun Q => merelyProp _) _ _)
      (fun _ => piHProp (fun X => merelyProp _) _ _).

  Definition totalCells {arity: HSet} (Q: νGpdPresentation arity): HGpd :=
    totalDiagramCells (GpdPseudofunctor.toPseudofunctor arity Q).

  Definition strictPresentationOfCover {arity: HSet} (Q: νGpdPresentation arity)
    (cover: Covers.SetCover (totalCells Q)): νStrictGpdPresentation arity :=
    StrictFunctor.ofFunctor
      (strictDiagramOfCover (GpdPseudofunctor.toPseudofunctor arity Q) cover).

  Local Definition diagramStrictificationPresentation {arity: HSet}
    (Q: νGpdPresentation arity) (F: Functor (Op (νSemiShape arity)) HSetGroupoidCat)
    (e: Complete.completeDiagram F = GpdPseudofunctor.toPseudofunctor arity Q):
    Complete.completePresentation (StrictFunctor.ofFunctor F) = Q :=
    f_equal (GpdPseudofunctor.ofPseudofunctor arity)
      (f_equal (@Complete.completeDiagram (Op (νSemiShape arity)))
        (StrictRoundtrip.toOfFunctor F) • e)
    • WeakRoundtrip.ofToPseudofunctor arity Q.

  Definition strictPresentationOfCoverEq {arity: HSet} (Q: νGpdPresentation arity)
    (cover: Covers.SetCover (totalCells Q)):
    Complete.completePresentation (strictPresentationOfCover Q cover) = Q :=
    diagramStrictificationPresentation Q _
      (strictDiagramOfCoverEq (GpdPseudofunctor.toPseudofunctor arity Q) cover).

  Definition completePresentationSurjective (covers: Covers.SetsCover1Types)
    {arity: HSet} (Q: νGpdPresentation arity):
    merely {P: νStrictGpdPresentation arity &T Complete.completePresentation P = Q} :=
    TF.trMap
      (fun z => (StrictFunctor.ofFunctor z.1; diagramStrictificationPresentation Q z.1 z.2))
      (completeDiagramSurjective covers (GpdPseudofunctor.toPseudofunctor arity Q)).

  Definition completedLevelCover {arity: HSet} (P: νStrictGpdPresentation arity) n:
    Covers.SetCover ((Complete.completePresentation P).(G0) n) :=
    completedDiagramLevelCover (StrictFunctor.toFunctor P) n.

  Definition completedPresentationCover {arity: HSet} (P: νStrictGpdPresentation arity):
    Covers.SetCover (totalCells (Complete.completePresentation P)).
  Proof.
    refine (hsigT (A := {| Dom := nat; UIP := @natUIP |})
      (fun n => (completedLevelCover P n).1);
      ((fun s => (s.1; (completedLevelCover P s.1).2.1 s.2)); _)).
    intros [n x]. refine (TF.trMap _ ((completedLevelCover P n).2.2 x)).
    intros [s e]. now exact ((n; s); f_equal (fun y => (n; y)) e).
  Defined.

  Definition presentationCover {arity: HSet} (Q: νGpdPresentation arity)
    (p: {P: νStrictGpdPresentation arity &T Complete.completePresentation P = Q}):
    Covers.SetCover (totalCells Q).
  Proof.
    destruct p as [P e]. destruct e.
    now exact (completedPresentationCover P).
  Defined.

  Definition presentationCoverEquiv {arity: HSet} (Q: νGpdPresentation arity):
    Equiv (merely {P: νStrictGpdPresentation arity &T Complete.completePresentation P = Q})
      (merely (Covers.SetCover (totalCells Q))) :=
    qinvEquiv (TF.trMap (presentationCover Q))
      (TF.trMap
        (fun cover => (strictPresentationOfCover Q cover; strictPresentationOfCoverEq Q cover)))
      (fun _ => merelyProp _ _ _) (fun _ => merelyProp _ _ _).

  Definition completePresentationSurjectiveCovers {arity: HSet}
    (surjective: forall Q: νGpdPresentation arity,
      merely {P: νStrictGpdPresentation arity &T Complete.completePresentation P = Q}):
    Covers.SetsCover1Types :=
    completeDiagramSurjectiveCovers
      (fun Q => TF.trMap
        (fun z => (StrictFunctor.toFunctor z.1;
          eq_sym (Complete.completePresentationDiagram z.1)
          • (f_equal (GpdPseudofunctor.toPseudofunctor arity) z.2
              • WeakRoundtrip.toOfPseudofunctor arity Q)))
        (surjective (GpdPseudofunctor.ofPseudofunctor arity Q))).

  Definition completePresentationSurjectiveCoverEquiv (arity: HSet):
    Equiv (forall Q: νGpdPresentation arity,
      merely {P: νStrictGpdPresentation arity &T Complete.completePresentation P = Q})
      Covers.SetsCover1Types :=
    qinvEquiv completePresentationSurjectiveCovers
      (fun covers => completePresentationSurjective covers)
      (fun _ => piHProp (fun Q => merelyProp _) _ _)
      (fun _ => piHProp (fun X => merelyProp _) _ _).
End PresentationStrictification.

(** Indexed strictification through the presentation correspondences. *)
Module IndexedStrictification (Tr: PropositionalTruncation)
  (Complete: StrictGpdCompletionSig Tr).
  Import Tr.
  Module Forward := IndexedCompletionOn Tr Complete.
  Module Presentations := PresentationStrictification Tr Complete.
  Module TF := TruncationFacts Tr.

  Module On (A: LayerSig) (B: LayerGpdSig with Definition arity := A.arity.(Dom))
    (S: νStrictGpdSig A) (W: νGpdSig B)
    (StrictMaps: StrictGpd.Constructions.ConstructionsSig A S)
    (WeakMaps: Gpd.Constructions.ConstructionsSig B W)
    (Strict: StrictGpd.Correspondence.CorrespondenceSig A S StrictMaps)
    (Weak: Gpd.Correspondence.CorrespondenceSig B W WeakMaps).
    Module Export Completion := Forward.On A B S W StrictMaps WeakMaps.

    Definition completeνStrictGpdsPresentation (P: νStrictGpdPresentation A.arity):
      completeνStrictGpds (StrictMaps.Reconstruction.f P) =
        WeakMaps.Reconstruction.f (Complete.completePresentation P) :=
      f_equal (fun Q => WeakMaps.Reconstruction.f (Complete.completePresentation Q))
        (Strict.presentationRoundtrip P).

    Definition completeνStrictGpdsSurjective (covers: Presentations.Covers.SetsCover1Types)
      (Y: W.νGpds): merely {X: S.νStrictGpds &T completeνStrictGpds X = Y} :=
      TF.trMap
        (fun z => (StrictMaps.Reconstruction.f z.1;
          completeνStrictGpdsPresentation z.1 •
            (f_equal WeakMaps.Reconstruction.f z.2 • Weak.indexedRoundtrip Y)))
        (Presentations.completePresentationSurjective covers (WeakMaps.Extraction.g Y)).

    Definition completeνStrictGpdsSurjectiveCovers
      (surjective: forall Y: W.νGpds, merely {X: S.νStrictGpds &T completeνStrictGpds X = Y}):
      Presentations.Covers.SetsCover1Types :=
      Presentations.completePresentationSurjectiveCovers
        (fun Q => TF.trMap
          (fun z => (StrictMaps.Extraction.g z.1; eqvInj Weak.presheafνGpdsEquiv z.2))
          (surjective (WeakMaps.Reconstruction.f Q))).

    Definition completeνStrictGpdsSurjectiveCoverEquiv:
      Equiv (forall Y: W.νGpds, merely {X: S.νStrictGpds &T completeνStrictGpds X = Y})
        Presentations.Covers.SetsCover1Types :=
      qinvEquiv completeνStrictGpdsSurjectiveCovers completeνStrictGpdsSurjective
        (fun _ => piHProp (fun Y => merelyProp _) _ _)
        (fun _ => piHProp (fun X => merelyProp _) _ _).
  End On.

  Module Simplicial := On SimplicialLayer SimplicialGpdLayer
    νStrictGpdSimplicial νGpdSimplicial
    StrictGpd.Constructions.ConstructionsSimplicial
    Gpd.Constructions.ConstructionsSimplicial
    StrictGpd.Correspondence.CorrespondenceSimplicial
    Gpd.Correspondence.CorrespondenceSimplicial.

  Module Cubical := On CubicalLayer CubicalGpdLayer νStrictGpdCubical νGpdCubical
    StrictGpd.Constructions.ConstructionsCubical Gpd.Constructions.ConstructionsCubical
    StrictGpd.Correspondence.CorrespondenceCubical Gpd.Correspondence.CorrespondenceCubical.
End IndexedStrictification.
