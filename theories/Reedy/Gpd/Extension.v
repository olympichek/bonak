(** Extension of diagrams of homotopy groupoids by a matching map loses no
    information. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet SigT Equiv Notation RewLemmas FinitePrefix HGpd.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas
  LocallyDiscretePseudofunctor HGpdDiagramEq Pseudonatural.
From Bonak.Reedy.Gpd Require Import Reedy.

Set Primitive Projections.
Set Printing Projections.

Section Reconstruction.
Context {A: HSet} {n: nat} (X: Diagram A (S n)).

Definition reconstructed: Diagram A (S n) :=
  extendByMatchingMap A (truncateDiagram X) (cells X None) (matchingMap X).

Definition reconstructionComponent (i: Index (S n)): cells X i -> cells reconstructed i.
Proof. destruct i as [i|]; now exact (fun x => x). Defined.

Definition topNormalization (f: Word A n n) (x: cells X None):
  restrict X (i := None) (j := None) f x = x :=
  phomEq (diagramData X) (a := None) (b := None) (wordEndId n f) x • restrictId X None x.

Lemma topNormalizationId (x: cells X None):
  topNormalization (wid n) x = restrictId X None x.
Proof.
  unfold topNormalization.
  rewrite ((wordSet n n).(UIP) (h := wordEndId n (wid n)) (g := eq_refl)).
  now apply eq_trans_refl_l.
Defined.

Definition reconstructionNaturality (i j: Index (S n))
  (f: Word A (rank j) (rank i)) (x: cells X i):
  reconstructionComponent j (restrict X f x) =
  restrict reconstructed f (reconstructionComponent i x).
Proof.
  destruct i as [i|], j as [j|].
  - now reflexivity.
  - now wordAboveAbsurd.
  - now reflexivity.
  - now exact (topNormalization f x).
Defined.

Lemma reconstructionUnit (i: Index (S n)) (x: cells X i):
  f_equal (reconstructionComponent i) (restrictId X i x) =
  reconstructionNaturality i i (wid (rank i)) x •
    restrictId reconstructed i (reconstructionComponent i x).
Proof.
  destruct i as [i|].
  - cbn [reconstructionComponent reconstructionNaturality].
    rewrite f_equal_id. now symmetry; apply eq_trans_refl_l.
  - change (f_equal (fun x => x) (restrictId X None x) = topNormalization (wid n) x).
    rewrite f_equal_id. now symmetry; apply topNormalizationId.
Defined.

Lemma reconstructionComp (i j k: Index (S n))
  (f: Word A (rank j) (rank i)) (g: Word A (rank k) (rank j)) (x: cells X i):
  f_equal (reconstructionComponent k) (restrictComp X g f x) •
    reconstructionNaturality i k (wcomp f g) x =
  reconstructionNaturality j k g (restrict X f x) •
    (f_equal (restrict reconstructed g) (reconstructionNaturality i j f x) •
      restrictComp reconstructed g f (reconstructionComponent i x)).
Proof.
  destruct i as [i|], j as [j|], k as [k|]; try now wordAboveAbsurd.
  - change (f_equal (fun z => z) (restrictComp X g f x) • eq_refl =
      eq_refl • (eq_refl • restrictComp X g f x)).
    rewrite f_equal_id, 2 eq_trans_refl_l. now reflexivity.
  - change (f_equal (fun z => z) (restrictComp X g f x) • eq_refl =
      eq_refl • (eq_refl • restrictComp X g f x)).
    rewrite f_equal_id, 2 eq_trans_refl_l. now reflexivity.
  - rewrite (wordEndId n f).
    cbn [reconstructionComponent reconstructionNaturality].
    rewrite f_equal_id, topNormalizationId.
    cbn [restrict restrictComp reconstructed extendByMatchingMap diagramData matchingMapData
      matchingMapComp matchingMapRestrict matchingValue matchingMap].
    rewrite eq_trans_refl_l.
    change (restrictComp X (i := Some k) (j := None) (k := None) g (wid n) x =
      f_equal (restrict X (i := Some k) (j := None) g) (restrictId X None x) •
      f_equal (fun w => restrict X (i := Some k) (j := None) w x)
        (eq_sym (f_equal (fun u => wcomp u g) (wordEndId n (wid n)) • wcompIdl g))).
    rewrite ((wordSet n n).(UIP) (h := wordEndId n (wid n)) (g := eq_refl)).
    cbn [f_equal]. rewrite eq_trans_refl_l, fEqualSym.
    now exact (pcompUnitLPt (diagramData X) (pathUnitL _ _ X.(pfStr))
      None (Some k) g (wcompIdl g) x).
  - rewrite (wordEndId n f), (wordEndId n g).
    cbn [reconstructionComponent reconstructionNaturality].
    rewrite f_equal_id, 2 topNormalizationId.
    unfold topNormalization.
    unfold restrictComp at 1.
    pose proof (pcompUnitRPt (diagramData X) (pathUnitR _ _ X.(pfStr))
      None None (wid n) (wordEndId n (wcomp (wid n) (wid n))) x) as e.
    refine (f_equal (fun p => p •
      (phomEq (diagramData X) (a := None) (b := None)
        (wordEndId n (wcomp (wid n) (wid n))) x • restrictId X None x)) e • _).
    cbn [restrict restrictComp reconstructed extendByMatchingMap diagramData matchingMapData
      matchingMapComp matchingMapRestrict].
    rewrite f_equal_id.
    rewrite transCancelMid2. now reflexivity.
Defined.

Definition reconstructionTransformation:
  Pseudonatural (expandPseudofunctor X) (expandPseudofunctor reconstructed) :=
  pathDiagramTransformation X reconstructed reconstructionComponent
    reconstructionNaturality reconstructionUnit reconstructionComp.

Lemma extendBoundaryEq: reconstructed = X.
Proof.
  symmetry. apply (eqvInj (locallyDiscretePseudofunctorEquiv (PrefixCategory A (S n)))).
  apply (hgpdPseudofunctorEq reconstructionTransformation).
  intros [i|]; now exact idEquiv.(eqvIsEquiv).
Defined.
End Reconstruction.

Section Classification.
Context (A: HSet).

Lemma emptyDiagramEq (X: Diagram A 0): emptyDiagram A = X.
Proof.
  pose (emptyFalse := fun i: Index 0 => match i return False with end).
  pose (α := pathDiagramTransformation (emptyDiagram A) X
    (fun i: Index 0 => False_rect _ (emptyFalse i))
    (fun i: Index 0 => False_rect _ (emptyFalse i))
    (fun i: Index 0 => False_rect _ (emptyFalse i))
    (fun i: Index 0 => False_rect _ (emptyFalse i))).
  now exact (eqvInj (locallyDiscretePseudofunctorEquiv (PrefixCategory A 0))
    (hgpdPseudofunctorEq α (fun i: Index 0 => False_rect _ (emptyFalse i)))).
Defined.

Definition splitExtension {n} (X: Diagram A (S n)): ExtensionData (gpdSystem A) n :=
  (truncateDiagram X; (cells X None; matchingMap X)).

Lemma matchingMapExtend {n} (X: Diagram A n) (T: HGpd)
  (b: T -> MatchingObject X) (x: T):
  matchingMap (extendByMatchingMap A X T b) x = b x.
Proof.
  now exact (matchingExt X
    (matchingMap (extendByMatchingMap A X T b) x) (b x) eq_refl eq_refl).
Defined.

Lemma splitJoinExtension {n} (X: ExtensionData (gpdSystem A) n):
  splitExtension (joinExtension X) = X.
Proof.
  destruct X as [X [T b]].
  refine (eq_existT_curried eq_refl _).
  refine (eq_existT_curried eq_refl _).
  apply functional_extensionality; intro x. now apply matchingMapExtend.
Defined.

Definition gpdLaws: MatchingSystemLaws (gpdSystem A) :=
  Build_MatchingSystemLaws (gpdSystem A)
    (fun B: HGpd => (hgpdFamilyMapEquiv B).(eqvIsEquiv))
    emptyDiagramEq
    (fun n => (qinvEquiv (joinExtension (M := gpdSystem A) (n := n))
      splitExtension splitJoinExtension extendBoundaryEq).(eqvIsEquiv))
    (fun n X T b => eq_refl).

End Classification.
