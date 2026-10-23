(** Completion of strict face presentations and indexed groupoids through
    their diagrams. The diagram comparison supplies the weak exchange
    paths and their coherence. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp Truncation.
From Bonak.νGpd Require Import HGpd.
From Bonak.Presheaf Require Import νSemiShape CategoryAction.
From Bonak.Presheaf.StrictGpd Require Import Presentation Functor.
From Bonak.Strictification Require Export DiagramCompletion.
From Bonak.Presheaf.Gpd Require Import Presentation Pseudofunctor Roundtrip.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Equiv.StrictGpd Require Constructions.
From Bonak.Equiv.Gpd Require Constructions.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module StrictPresentation := StrictGpd.Presentation.
Module StrictFunctor := StrictGpd.Functor.
Module WeakPresentation := Gpd.Presentation.
Module GpdPseudofunctor := Gpd.Pseudofunctor.
Module WeakRoundtrip := Gpd.Roundtrip.

Module StrictGpdCompletion (Tr: PropositionalTruncation).
  Include CompletionDiagrams Tr.

  Definition completePresentation {arity: HSet} (X: νStrictGpdPresentation arity):
    νGpdPresentation arity :=
    GpdPseudofunctor.ofPseudofunctor arity (completeDiagram (StrictFunctor.toFunctor X)).

  Definition completePresentationDiagram {arity: HSet} (X: νStrictGpdPresentation arity):
    GpdPseudofunctor.toPseudofunctor arity (completePresentation X) =
      completeDiagram (StrictFunctor.toFunctor X) :=
    WeakRoundtrip.toOfPseudofunctor arity (completeDiagram (StrictFunctor.toFunctor X)).

  Lemma completePresentationObj {arity: HSet} (X: νStrictGpdPresentation arity) n:
    (completePresentation X).(WeakPresentation.G0) n =
      P.classifying (X.(StrictPresentation.G0) n).
  Proof. now exact (completeDiagramObj (StrictFunctor.toFunctor X) n). Defined.

  Lemma completePresentationFace {arity: HSet} (X: νStrictGpdPresentation arity)
    n q (Hq: q <= n) (ε: arity)
    (x: P.classifying (X.(StrictPresentation.G0) n.+1)):
    (completePresentation X).(WeakPresentation.GFace) n q Hq ε x =
      (A.liftFunctor (X.(StrictPresentation.GFace) n q Hq ε)).(fobj) x.
  Proof.
    refine (completeDiagramHom (StrictFunctor.toFunctor X) (wgen n q ε) x • _).
    now exact (f_equal (fun F => (A.liftFunctor F).(fobj) x)
      (categoryApplyWGen (StrictFunctor.pshStr X) n q Hq ε)).
  Defined.
End StrictGpdCompletion.

Module Type StrictGpdCompletionSig (Tr: PropositionalTruncation).
  Include StrictGpdCompletion Tr.
End StrictGpdCompletionSig.

(** Indexed completion through the presentation map. *)
Module IndexedCompletionOn (Tr: PropositionalTruncation)
  (Complete: StrictGpdCompletionSig Tr).

  (** The two layer formers share an arity; their representations of layers
      and their indexed cores may differ. *)
  Module On (A: LayerSig) (B: LayerGpdSig with Definition arity := A.arity.(Dom))
    (S: νStrictGpdSig A) (W: νGpdSig B)
    (Strict: StrictGpd.Constructions.ConstructionsSig A S)
    (Weak: Gpd.Constructions.ConstructionsSig B W).

    Definition completeνStrictGpds (X: S.νStrictGpds): W.νGpds :=
      Weak.Reconstruction.f (Complete.completePresentation (Strict.Extraction.g X)).
  End On.

  Module Simplicial := On SimplicialLayer SimplicialGpdLayer
    νStrictGpdSimplicial νGpdSimplicial
    StrictGpd.Constructions.ConstructionsSimplicial
    Gpd.Constructions.ConstructionsSimplicial.

  Module Cubical := On CubicalLayer CubicalGpdLayer νStrictGpdCubical νGpdCubical
    StrictGpd.Constructions.ConstructionsCubical Gpd.Constructions.ConstructionsCubical.
End IndexedCompletionOn.

Module IndexedCompletion (Tr: PropositionalTruncation).
  Module Complete := StrictGpdCompletion Tr.
  Include IndexedCompletionOn Tr Complete.
End IndexedCompletion.
