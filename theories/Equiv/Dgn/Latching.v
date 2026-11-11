(** Generating degeneracies: their mixed laws with faces, and the
    latching lifts they determine. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Notation LeSProp Equiv Funext
  FinitePrefix.
From Bonak.Presheaf Require Import GeneratingFaces.
From Bonak.Presheaf.Dgn Require Import Generators.
From Bonak.Reedy Require Import GeneratorBoundary.
From Bonak.Reedy.Dgn Require Import Reedy Latching.
From Bonak.Reedy Require Reedy.

Set Primitive Projections.
Set Printing Projections.

(** Mixed face and coordinate-deletion laws indexed by depth from the top. *)

Section Generators.
Context {A: HSet}.

Local Lemma faceFirst n a:
  shapeFace (depthFaceWord A n (firstDepth n) a) = shapeConst a (shapeId n).
Proof. rewrite depthFaceFirst. now reflexivity. Qed.

Local Lemma maskFirst n:
  shapeMask (A := A) (depthFaceWord hunit n (firstDepth n) tt) = shapeDrop (shapeId n).
Proof. rewrite depthFaceFirst. now reflexivity. Qed.

Local Lemma faceNext n i a:
  shapeFace (depthFaceWord A n.+1 (nextDepth i) a)
    = shapeKeep (shapeFace (depthFaceWord A n i a)).
Proof. rewrite depthFaceNext. now reflexivity. Qed.

Local Lemma maskNext n i:
  shapeMask (A := A) (depthFaceWord hunit n.+1 (nextDepth i) tt)
    = shapeKeep (shapeMask (depthFaceWord hunit n i tt)).
Proof. rewrite depthFaceNext. now reflexivity. Qed.

Lemma depthFaceMaskId n: forall (i: FaceDepth n) a,
  shapeComp (shapeFace (depthFaceWord A n i a))
    (shapeMask (depthFaceWord hunit n i tt)) = shapeId n.
Proof.
  induction n as [|n IH]; intros [[|i] hi] a.
  - rewrite faceFirst, maskFirst, shapeCompConstDrop, shapeIdL. now reflexivity.
  - now destruct (leR_O_contra hi).
  - rewrite faceFirst, maskFirst, shapeCompConstDrop, shapeIdL. now reflexivity.
  - change (shapeComp
      (shapeKeep (shapeFace (depthFaceWord A n {| depth := i; depthBound := ⇓ hi |} a)))
      (shapeKeep (shapeMask (depthFaceWord hunit n {| depth := i; depthBound := ⇓ hi |} tt)))
      = shapeId n.+1).
    rewrite shapeCompKeep, IH. now reflexivity.
Qed.

Local Lemma supFirst n (i: FaceDepth n) a:
  shapeComp (shapeFace (depthFaceWord A n.+1 (weakenDepth (firstDepth n)) a))
    (shapeMask (depthFaceWord hunit n.+1 (nextDepth i) tt))
  = shapeComp (shapeMask (depthFaceWord hunit n i tt))
      (shapeFace (depthFaceWord A n (firstDepth n) a)).
Proof.
  change (shapeComp (shapeFace (depthFaceWord A n.+1 (firstDepth n.+1) a))
    (shapeMask (depthFaceWord hunit n.+1 (nextDepth i) tt))
    = shapeComp (shapeMask (depthFaceWord hunit n i tt))
      (shapeFace (depthFaceWord A n (firstDepth n) a))).
  rewrite 2 faceFirst, maskNext, shapeCompConstKeep, shapeCompConst, shapeIdL, shapeIdR.
  now reflexivity.
Qed.

Lemma depthFaceMaskSup n: forall (q i: FaceDepth n), depth q <= depth i -> forall a,
  shapeComp (shapeFace (depthFaceWord A n.+1 (weakenDepth q) a))
    (shapeMask (depthFaceWord hunit n.+1 (nextDepth i) tt))
  = shapeComp (shapeMask (depthFaceWord hunit n i tt))
      (shapeFace (depthFaceWord A n q a)).
Proof.
  induction n as [|n IH]; intros [[|q] hq] [[|i] hi] hqi a;
    try (destruct (leR_O_contra hq)); try (destruct (leR_O_contra hi));
    try (destruct (leR_O_contra hqi)).
  - now apply supFirst.
  - now apply supFirst.
  - now apply supFirst.
  - change (shapeComp
      (shapeKeep (shapeFace (depthFaceWord A n.+1
        (weakenDepth {| depth := q; depthBound := ⇓ hq |}) a)))
      (shapeKeep (shapeMask (depthFaceWord hunit n.+1
        (nextDepth {| depth := i; depthBound := ⇓ hi |}) tt)))
    = shapeComp
      (shapeKeep (shapeMask (depthFaceWord hunit n {| depth := i; depthBound := ⇓ hi |} tt)))
      (shapeKeep (shapeFace (depthFaceWord A n {| depth := q; depthBound := ⇓ hq |} a)))).
    rewrite 2 shapeCompKeep.
    apply f_equal. now apply IH.
Qed.

Local Lemma infFirst n (q: FaceDepth n) a:
  shapeComp (shapeFace (depthFaceWord A n.+1 (nextDepth q) a))
    (shapeMask (depthFaceWord hunit n.+1 (weakenDepth (firstDepth n)) tt))
  = shapeComp (shapeMask (depthFaceWord hunit n (firstDepth n) tt))
      (shapeFace (depthFaceWord A n q a)).
Proof.
  change (shapeComp (shapeFace (depthFaceWord A n.+1 (nextDepth q) a))
    (shapeMask (depthFaceWord hunit n.+1 (firstDepth n.+1) tt))
    = shapeComp (shapeMask (depthFaceWord hunit n (firstDepth n) tt))
      (shapeFace (depthFaceWord A n q a))).
  rewrite 2 maskFirst, faceNext, shapeCompKeepDrop, shapeCompDrop, shapeIdL, shapeIdR.
  now reflexivity.
Qed.

Lemma depthFaceMaskInf n: forall (i q: FaceDepth n), depth i <= depth q -> forall a,
  shapeComp (shapeFace (depthFaceWord A n.+1 (nextDepth q) a))
    (shapeMask (depthFaceWord hunit n.+1 (weakenDepth i) tt))
  = shapeComp (shapeMask (depthFaceWord hunit n i tt))
      (shapeFace (depthFaceWord A n q a)).
Proof.
  induction n as [|n IH]; intros [[|i] hi] [[|q] hq] hiq a;
    try (destruct (leR_O_contra hq)); try (destruct (leR_O_contra hi));
    try (destruct (leR_O_contra hiq)).
  - now apply infFirst.
  - now apply infFirst.
  - now apply infFirst.
  - change (shapeComp
      (shapeKeep (shapeFace (depthFaceWord A n.+1
        (nextDepth {| depth := q; depthBound := ⇓ hq |}) a)))
      (shapeKeep (shapeMask (depthFaceWord hunit n.+1
        (weakenDepth {| depth := i; depthBound := ⇓ hi |}) tt)))
    = shapeComp
      (shapeKeep (shapeMask (depthFaceWord hunit n {| depth := i; depthBound := ⇓ hi |} tt)))
      (shapeKeep (shapeFace (depthFaceWord A n {| depth := q; depthBound := ⇓ hq |} a)))).
    rewrite 2 shapeCompKeep.
    apply f_equal. now apply IH.
Qed.

End Generators.


(** Compatible latching lifts are determined by generating degeneracies. *)

Definition GeneratorMaps {A: HSet} (n: nat): Diagram A n -> HSet -> Type :=
  match n as n return Diagram A n -> HSet -> Type with
  | 0 => fun _ _ => unit
  | S n => fun X T => FaceDepth n -> cells X None -> T
  end.

Definition GeneratorRelations {A: HSet} (n: nat):
  forall (X: Diagram A n) (T: HSet), GeneratorMaps n X T -> Type :=
  match n as n return forall (X: Diagram A n) (T: HSet), GeneratorMaps n X T -> Type with
  | 0 => fun _ _ _ => unit
  | S 0 => fun _ _ _ => unit
  | S (S n) => fun X T g =>
      forall (i j: FaceDepth n), depth i <= depth j -> forall x: cells X (Some None),
        g (nextDepth j) (act X (i := None) (j := Some None) (shapeMask (depthFaceWord hunit n i tt)) x) =
        g (weakenDepth i) (act X (i := None) (j := Some None) (shapeMask (depthFaceWord hunit n j tt)) x)
  end.

Definition GeneratorBoundary {A: HSet} (n: nat):
  forall (X: Diagram A n) (T: HSet), (T -> MatchingObject A X) -> GeneratorMaps n X T -> Type :=
  match n as n return forall (X: Diagram A n) (T: HSet),
    (T -> MatchingObject A X) -> GeneratorMaps n X T -> Type with
  | 0 => fun _ _ _ _ => unit
  | S n => fun X T b g => forall i x,
      b (g i x) = latchingBoundary A X (i := None) (shapeMask (depthFaceWord hunit n i tt)) x
  end.

Record GeneratorLifts {A: HSet} {n} {X: Diagram A n} {T: HSet}
  {b: T -> MatchingObject A X} := {
  generator: GeneratorMaps n X T;
  generatorDD: GeneratorRelations n X T generator;
  generatorBoundary: GeneratorBoundary n X T b generator;
}.
Arguments GeneratorLifts {A n} X T b.

Section Generators.
Context {A: HSet} {n} (X: Diagram A n) (T: HSet).
Definition Generators: Type := {g: GeneratorMaps n X T &T GeneratorRelations n X T g}.

Lemma generatorRelationsProp g (h k: GeneratorRelations n X T g): h = k.
Proof.
  destruct n as [|[|m]]; [now destruct h,k|now destruct h,k|].
  repeat first [apply functional_extensionality_dep; intro |apply spropFunext; intro].
  now apply T.(UIP).
Defined.

Definition generatorsToFinite (g: Generators):
  FinitePairwiseBoundary hunit n (maskHomDiagram X T).
Proof.
  unfold Generators in g.
  destruct n as [|N].
  - now exact (tt; tt).
  - exists (fun i _ => g.1 i).
    destruct N as [|k].
    + now exact tt.
    + intros i j hij [] []. apply functional_extensionality_dep; intro x.
      now exact (g.2 i j hij x).
Defined.

Definition generatorsOfFinite (g: FinitePairwiseBoundary hunit n (maskHomDiagram X T)):
  Generators.
Proof.
  unfold Generators.
  destruct n as [|N].
  - now exact (tt; tt).
  - exists (fun i => g.1 i tt).
    destruct N as [|k].
    + now exact tt.
    + intros i j hij x. now exact (f_equal (fun f => f x) (g.2 i j hij tt tt)).
Defined.

Definition generatorsFiniteEquiv:
  Equiv Generators (FinitePairwiseBoundary hunit n (maskHomDiagram X T)).
Proof.
  refine (qinvEquiv generatorsToFinite generatorsOfFinite _ _).
  - intro g. unshelve refine (eq_existT_curried _ _).
    + unfold generatorsToFinite, generatorsOfFinite, Generators in *.
      destruct n as [|N].
      * now destruct g as [[] h].
      * now reflexivity.
    + now apply generatorRelationsProp.
  - intro g. unshelve refine (eq_existT_curried _ _).
    + unfold generatorsToFinite, generatorsOfFinite, Generators in *.
      destruct n as [|N].
      * now destruct g as [[] h].
      * apply functional_extensionality_dep; intro i.
        apply functional_extensionality_dep; now intros [].
    + now apply finitePairwiseBoundaryLawProp.
Defined.

Definition generatorsCoconeEquiv: Equiv Generators (MaskCocone X T) :=
  compEquiv generatorsFiniteEquiv (finitePairwiseMatchingEquiv hunit n (maskHomDiagram X T)).
End Generators.

Lemma generatorsCoconeFace {A: HSet} n (X: Diagram A (S n)) (T: HSet)
  (g: Generators X T) i x:
  (generatorsCoconeEquiv X T g).1 None (depthFaceWord hunit n i tt) x = g.1 i x.
Proof.
  change ((finitePairwiseMatchingEquiv hunit (S n) (maskHomDiagram X T)
    (generatorsToFinite X T g)).1 None (depthFaceWord hunit n i tt) x = g.1 i x).
  now rewrite finitePairwiseMatchingFace.
Defined.

Section Boundary.
Context {A: HSet} {n} (X: Diagram A n) (T: HSet) (b: T -> MatchingObject A X).

Definition coconeGenerators (B: MaskCocone X T): GeneratorMaps n X T :=
  match n as n return forall X: Diagram A n, MaskCocone X T -> GeneratorMaps n X T with
  | 0 => fun _ _ => tt
  | S n => fun X B i => B.1 None (depthFaceWord hunit n i tt)
  end X B.

Lemma maskBoundaryOfGenerators (B: MaskCocone X T)
  (h: GeneratorBoundary n X T b (coconeGenerators B)): MaskBoundary X T b B.
Proof.
  unfold coconeGenerators in h.
  destruct n as [|N].
  - now intros [].
  - intros j r x.
    destruct (properFaceFactor hunit N (rank j) (⇓ (rankBound j)) r) as [i [[] [v e]]].
    rewrite e.
    refine (f_equal b (eq_sym (f_equal (fun f => f x)
      (B.2 j None v (depthFaceWord hunit N i tt)))) • _).
    change (b (B.1 None (depthFaceWord hunit N i tt)
      (act X (i := None) (j := j) (shapeMask v) x)) =
      latchingBoundary A X (i := j)
        (shapeMask (wcomp (depthFaceWord hunit N i tt) v)) x).
    rewrite h, latchingBoundaryComp, shapeMaskComp.
    now reflexivity.
Defined.

Lemma generatorBoundaryProp g (h k: GeneratorBoundary n X T b g): h = k.
Proof.
  destruct n as [|N].
  - now destruct h,k.
  - repeat (apply functional_extensionality_dep; intro). now apply UIP.
Defined.

Lemma maskBoundaryProp B (h k: MaskBoundary X T b B): h = k.
Proof. repeat (apply functional_extensionality_dep; intro). now apply UIP. Defined.

Definition generatorsBoundaryToMask (g: Generators X T)
  (h: GeneratorBoundary n X T b g.1): MaskBoundary X T b (generatorsCoconeEquiv X T g).
Proof.
  apply maskBoundaryOfGenerators.
  unfold coconeGenerators.
  destruct n as [|N].
  - now exact tt.
  - intros i x. change (b ((generatorsCoconeEquiv X T g).1 None
      (depthFaceWord hunit N i tt) x) =
      latchingBoundary A X (i := None) (shapeMask (depthFaceWord hunit N i tt)) x).
    rewrite generatorsCoconeFace. now apply h.
Defined.

Definition generatorsBoundaryOfMask (g: Generators X T)
  (h: MaskBoundary X T b (generatorsCoconeEquiv X T g)):
  GeneratorBoundary n X T b g.1.
Proof.
  destruct n as [|N].
  - now exact tt.
  - intros i x. rewrite <- (generatorsCoconeFace N X T g i x).
    now apply h.
Defined.

Definition generatorBoundaryEquiv (g: Generators X T):
  Equiv (GeneratorBoundary n X T b g.1)
    (MaskBoundary X T b (generatorsCoconeEquiv X T g)) :=
  qinvEquiv (generatorsBoundaryToMask g) (generatorsBoundaryOfMask g)
    (fun _ => generatorBoundaryProp _ _ _) (fun _ => maskBoundaryProp _ _ _).

Definition generatorLiftsSigmaEquiv:
  Equiv (GeneratorLifts X T b) {g: Generators X T &T GeneratorBoundary n X T b g.1}.
Proof.
  refine (qinvEquiv
    (fun G => ((G.(generator); G.(generatorDD)); G.(generatorBoundary)))
    (fun G => {| generator := G.1.1; generatorDD := G.1.2; generatorBoundary := G.2 |}) _ _);
    now intros.
Defined.

Definition generatorLiftsEquiv: Equiv (GeneratorLifts X T b) (LatchingLifts A X T b) :=
  compEquiv generatorLiftsSigmaEquiv
    (compEquiv (sigTEquiv (generatorsCoconeEquiv X T) generatorBoundaryEquiv)
      (symEquiv (latchingEquivMask X T b))).
End Boundary.

Lemma generatorLiftsEq {A: HSet} {n} (X: Diagram A n) (T: HSet)
  (b: T -> MatchingObject A X) (G H: GeneratorLifts X T b)
  (e: G.(generator) = H.(generator)): G = H.
Proof.
  destruct G as [g gr gb], H as [h hr hb]; cbn in e.
  destruct e.
  assert (p: gr = hr) by now apply generatorRelationsProp.
  destruct p.
  assert (p: gb = hb) by now apply generatorBoundaryProp.
  now destruct p.
Defined.

Lemma generatorLiftsFace {A: HSet} n (X: Diagram A (S n)) (T: HSet)
  (b: T -> MatchingObject A X) (G: GeneratorLifts X T b) i x:
  (generatorLiftsEquiv X T b G).(lift) None (shapeMask (depthFaceWord hunit n i tt)) x
    = G.(generator) i x.
Proof.
  change (coconeAction X T (generatorsCoconeEquiv X T (G.(generator); G.(generatorDD)))
    None (shapeMask (depthFaceWord hunit n i tt)) x = G.(generator) i x).
  refine (coconeActionMask X T
    (generatorsCoconeEquiv X T (G.(generator); G.(generatorDD))) None
    (depthFaceWord hunit n i tt) x • _).
  now apply generatorsCoconeFace.
Defined.
