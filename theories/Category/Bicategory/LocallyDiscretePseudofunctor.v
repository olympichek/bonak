(** Path diagrams over a category are equivalent to pseudofunctors from
    its locally discrete bicategory into [HGpd2Cat].

    The action on equality 2-cells is determined by the arrow action.
    Functional extensionality converts the unit comparison homotopies
    into the equality paths stored by [PathDiagram]. The comparison has
    equality round trips for the complete records. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation Funext Equiv RewLemmas.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Bicategory LocallyDiscrete IconPath.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Bonak.Category.Bicategory Require Import PathDiagram.

From Bonak.Category.Bicategory Require Import HGpd2Cat.
From Bonak.Category.Bicategory Require Import Pseudofunctor.

Set Primitive Projections.
Set Printing Projections.

Lemma idTo2Point {X Y: HGpd} {f g: X -> Y} (p: f = g) (x: X):
  @idTo2 HGpd2Cat X Y f g p x = happly p x.
Proof. destruct p. reflexivity. Qed.

Lemma idTo2Funext {X Y: HGpd} {f g: X -> Y} (h: forall x, f x = g x):
  @idTo2 HGpd2Cat X Y f g (functional_extensionality_dep_good f g h) = h.
Proof.
  apply functional_extensionality_dep; intro x.
  rewrite idTo2Point. exact (f_equal__functional_extensionality_dep_good h x).
Qed.

Lemma funextIdTo2 {X Y: HGpd} {f g: X -> Y} (p: f = g):
  functional_extensionality_dep_good f g (@idTo2 HGpd2Cat X Y f g p) = p.
Proof.
  transitivity (functional_extensionality_dep_good f g (happly p)).
  - f_equal. apply functional_extensionality_dep; intro x. apply idTo2Point.
  - apply funextHapply.
Qed.

Section LocallyDiscretePsf.
Context (C: Category) (ob: C.(CObj) -> HGpd).

Definition expandData (N: PathDiagramData C ob):
  PsfData (locallyDiscrete C) HGpd2Cat ob :=
  Build_PsfData (locallyDiscrete C) HGpd2Cat ob
    (fun a b f => N.(phom) f)
    (fun a b f g p x => f_equal (fun w => N.(phom) w x) p)
    (fun a => idTo2 (N.(pid) a))
    (fun a b c f g => N.(pcomp) f g).

Lemma expandCellPath (N: PathDiagramData C ob) {a b} {f g: C.(CHom) a b} (p: f = g):
  (expandData N).(psCell) p = @idTo2 HGpd2Cat (ob a) (ob b) _ _ (f_equal N.(phom) p).
Proof. destruct p. reflexivity. Qed.

Lemma expandUnitPathL (N: PathDiagramData C ob) {a b} (f: C.(CHom) a b):
  @idTo2 HGpd2Cat (ob a) (ob b) _ _ (psfUnitL C ob N f)
  = bwhiskerR ((expandData N).(psUnit) a) ((expandData N).(psHom) f).
Proof.
  unfold psfUnitL. cbn [hgpdUnitL].
  exact (eq_sym (@idTo2WhiskerR HGpd2Cat (ob a) (ob a) (ob b) _ _ (N.(pid) a) (N.(phom) f))).
Qed.

Lemma expandUnitPathR (N: PathDiagramData C ob) {a b} (f: C.(CHom) a b):
  @idTo2 HGpd2Cat (ob a) (ob b) _ _ (psfUnitR C ob N f)
  = bwhiskerL ((expandData N).(psHom) f) ((expandData N).(psUnit) b).
Proof.
  unfold psfUnitR. cbn [hgpdUnitR].
  exact (eq_sym (@idTo2WhiskerL HGpd2Cat (ob a) (ob b) (ob b) (N.(phom) f) _ _ (N.(pid) b))).
Qed.

Lemma expandUnitL (N: PathDiagramData C ob):
  PathDiagramUnitL C ob N ->
  forall a b (f: C.(CHom) a b),
    (expandData N).(psComp) (@bid (locallyDiscrete C) a) f ⨟ (expandData N).(psCell) (@bunitL (locallyDiscrete C) a b f).(isoHom)
    = bwhiskerR ((expandData N).(psUnit) a) ((expandData N).(psHom) f)
      ⨟ (bunitL ((expandData N).(psHom) f)).(isoHom).
Proof.
  intros H a b f.
  pose proof (proj1 (hom2RewEquation (psfUnitL C ob N f)
    (f_equal N.(phom) (C.(cidl) f)) _ _) (H a b f)) as e.
  rewrite expandUnitPathL, <- expandCellPath in e.
  exact e.
Qed.

Lemma expandUnitR (N: PathDiagramData C ob):
  PathDiagramUnitR C ob N ->
  forall a b (f: C.(CHom) a b),
    (expandData N).(psComp) f (@bid (locallyDiscrete C) b) ⨟ (expandData N).(psCell) (@bunitR (locallyDiscrete C) a b f).(isoHom)
    = bwhiskerL ((expandData N).(psHom) f) ((expandData N).(psUnit) b)
      ⨟ (bunitR ((expandData N).(psHom) f)).(isoHom).
Proof.
  intros H a b f.
  pose proof (proj1 (hom2RewEquation (psfUnitR C ob N f)
    (f_equal N.(phom) (C.(cidr) f)) _ _) (H a b f)) as e.
  rewrite expandUnitPathR, <- expandCellPath in e.
  exact e.
Qed.

(** The composition laws of the expanded diagram do not use unit laws. *)

Lemma expandCellComp (N: PathDiagramData C ob): PsfCellComp (expandData N).
Proof. intros a b f g h α β. destruct α, β. reflexivity. Qed.

Lemma expandCompNatL (N: PathDiagramData C ob): PsfCompNatL (expandData N).
Proof.
  intros a b c f g h α. destruct α.
  apply functional_extensionality_dep; intro x. cbn. apply eq_trans_refl_l.
Qed.

Lemma expandCompNatR (N: PathDiagramData C ob): PsfCompNatR (expandData N).
Proof.
  intros a b c f g α h. destruct α.
  apply functional_extensionality_dep; intro x. cbn. apply eq_trans_refl_l.
Qed.

Lemma expandAssoc (N: PathDiagramData C ob) (H: PathDiagramAssoc C ob N):
  PsfAssoc (expandData N).
Proof.
  intros a b c d f g h.
  pose proof (proj1 (hom2RewEquation (B := HGpd2Cat)
    (hgpdAssoc (N.(phom) f) (N.(phom) g) (N.(phom) h))
    (f_equal N.(phom) (C.(cassoc) f g h)) _ _) (H a b c d f g h)) as e.
  rewrite <- expandCellPath in e. exact e.
Qed.

Definition expandPsf (N: PathDiagram C ob):
  Psf (locallyDiscrete C) HGpd2Cat ob.
Proof.
  refine (Build_Psf _ _ _ (expandData (pathData _ _ N)) _).
  constructor.
  - intros; apply hgpdLocallyGroupoid.
  - intros; apply hgpdLocallyGroupoid.
  - intros; reflexivity.
  - apply expandCellComp.
  - apply expandCompNatL.
  - apply expandCompNatR.
  - exact (expandUnitL _ (pathUnitL _ _ N)).
  - exact (expandUnitR _ (pathUnitR _ _ N)).
  - exact (expandAssoc _ (pathAssoc _ _ N)).
Defined.

Definition contractData (F: PsfData (locallyDiscrete C) HGpd2Cat ob):
  PathDiagramData C ob :=
  Build_PathDiagramData C ob
    (fun a b f => F.(psHom) f)
    (fun a => functional_extensionality_dep_good _ _ (F.(psUnit) a))
    (fun a b c f g => F.(psComp) f g).

Lemma contractExpandData (N: PathDiagramData C ob):
  contractData (expandData N) = N.
Proof.
  destruct N as [h u c]; cbn [contractData expandData phom pid pcomp psHom psUnit psComp].
  assert (e: (fun a => functional_extensionality_dep_good _ _ (idTo2 (u a))) = u).
  { apply functional_extensionality_dep; intro a. apply funextIdTo2. }
  exact (f_equal (fun unit => Build_PathDiagramData C ob h unit c) e).
Qed.

Lemma expandContractData (F: PsfData (locallyDiscrete C) HGpd2Cat ob)
  (Hi: forall a b (f: C.(CHom) a b), F.(psCell) (eq_refl: f = f) = id2 (F.(psHom) f)):
  expandData (contractData F) = F.
Proof.
  destruct F as [h c u p]; cbn [expandData contractData psHom psCell psUnit psComp phom pid pcomp] in *.
  assert (ec: (fun a b (f g: C.(CHom) a b) (e: f = g) x =>
    f_equal (fun w => h a b w x) e) = c).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    apply functional_extensionality_dep; intro e.
    destruct e. exact (eq_sym (Hi a b f)). }
  assert (eu: (fun a => @idTo2 HGpd2Cat (ob a) (ob a) _ _
    (functional_extensionality_dep_good _ _ (u a))) = u).
  { apply functional_extensionality_dep; intro a. apply idTo2Funext. }
  exact (f_equal2 (fun cell unit => Build_PsfData (locallyDiscrete C) HGpd2Cat ob h cell unit p) ec eu).
Qed.

Definition contractPsf (F: Psf (locallyDiscrete C) HGpd2Cat ob):
  PathDiagram C ob.
Proof.
  pose (N := contractData F.(psData)).
  pose proof (expandContractData F.(psData) (psCellId _ F.(psLaws))) as ed.
  refine (Build_PathDiagram C ob N _ _ _).
  - intros a b f. apply (proj2 (hom2RewEquation (B := HGpd2Cat)
      (psfUnitL C ob N f) (f_equal N.(phom) (C.(cidl) f)) _ _)).
    rewrite expandUnitPathL, <- expandCellPath.
    pose proof (psUnitL _ F.(psLaws) a b f) as e.
    rewrite <- ed in e. exact e.
  - intros a b f. apply (proj2 (hom2RewEquation (B := HGpd2Cat)
      (psfUnitR C ob N f) (f_equal N.(phom) (C.(cidr) f)) _ _)).
    rewrite expandUnitPathR, <- expandCellPath.
    pose proof (psUnitR _ F.(psLaws) a b f) as e.
    rewrite <- ed in e. exact e.
  - intros a b c d f g h.
    apply (proj2 (hom2RewEquation (B := HGpd2Cat) (hgpdAssoc (N.(phom) f) (N.(phom) g) (N.(phom) h))
      (f_equal N.(phom) (C.(cassoc) f g h)) _ _)).
    rewrite <- expandCellPath.
    pose proof (psAssoc _ F.(psLaws) a b c d f g h) as e.
    rewrite <- ed in e. exact e.
Defined.

Lemma contractExpandPsf (N: PathDiagram C ob): contractPsf (expandPsf N) = N.
Proof.
  apply pathDiagramEqOn. exact (contractExpandData (pathData _ _ N)).
Qed.

Lemma expandContractPsf (F: Psf (locallyDiscrete C) HGpd2Cat ob):
  expandPsf (contractPsf F) = F.
Proof.
  apply psfEqData. exact (expandContractData F.(psData) (psCellId _ F.(psLaws))).
Qed.

Definition locallyDiscretePsfEquiv:
  Equiv (PathDiagram C ob) (Psf (locallyDiscrete C) HGpd2Cat ob) :=
  qinvEquiv expandPsf contractPsf contractExpandPsf expandContractPsf.

End LocallyDiscretePsf.

Definition expandPseudofunctor {C: Category} (F: PathDiagramFamily C):
  Pseudofunctor (locallyDiscrete C) HGpd2Cat :=
  Build_Pseudofunctor (locallyDiscrete C) HGpd2Cat F.(pfObj) (expandPsf C F.(pfObj) F.(pfStr)).

Definition contractPseudofunctor {C: Category} (F: Pseudofunctor (locallyDiscrete C) HGpd2Cat):
  PathDiagramFamily C :=
  Build_PathDiagramFamily C F.(psObj) (contractPsf C F.(psObj) F.(psStr)).

Definition locallyDiscretePseudofunctorEquiv (C: Category):
  Equiv (PathDiagramFamily C) (Pseudofunctor (locallyDiscrete C) HGpd2Cat).
Proof.
  refine (qinvEquiv expandPseudofunctor contractPseudofunctor _ _).
  - intros [ob F]. cbn [expandPseudofunctor contractPseudofunctor psObj psStr pfObj pfStr].
    exact (f_equal (Build_PathDiagramFamily C ob) (retEq (locallyDiscretePsfEquiv C ob) F)).
  - intros [ob F]. cbn [expandPseudofunctor contractPseudofunctor psObj psStr pfObj pfStr].
    exact (f_equal (Build_Pseudofunctor (locallyDiscrete C) HGpd2Cat ob) (secEq (locallyDiscretePsfEquiv C ob) F)).
Defined.

