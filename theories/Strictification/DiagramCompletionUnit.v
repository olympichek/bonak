(** The completion units form a coherent evaluation of a strict diagram
    in its completed path diagram. Each component is a weak equivalence. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Truncation Notation Funext RewLemmas Equiv.
From Bonak.Category Require Import Category Groupoid.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Groupoid Require Import WeakEquivalence SetBased.
From Bonak.Strictification Require Import DiagramEvaluation DiagramDescent.
From Bonak.Category.Groupoid Require Import CompletionPseudofunctor.
From Bonak.Category.Bicategory Require Import HGpd2Cat BicategoryEq Pseudonatural Pseudofunctor
  LocallyDiscrete Groupoids PseudofunctorOps Full PathGroupoid UnivGpd2Cat.
From Bonak.Strictification Require Import DiagramCompletion.
From Bonak.Category.Bicategory Require Import LocallyDiscretePseudofunctor PathDiagram.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Keyed Unification.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Lemma discreteIdTo2 {C: Category} {a b} {f g: C.(CHom) a b} (p: f=g):
  @idTo2 (LocallyDiscrete.locallyDiscrete C) a b f g p = p.
Proof. now destruct p. Defined.

Local Lemma idTo2Refl {B: Bicategory} {a b} (f: Hom B a b):
  @idTo2 B a b f f eq_refl = id2 f.
Proof. now reflexivity. Defined.

Local Lemma idTo2Ncomp {G H: UnivalentGroupoid} (F: Functor G H) (x: G.(CObj)):
  (@idTo2 UnivGpd2Cat G H F F eq_refl).(ncomp) x = cid (F.(fobj) x).
Proof. now reflexivity. Defined.

Module CompletionEvaluationsOn (Tr: PropositionalTruncation)
  (CD: CompletionDiagramsSig Tr).
  Module W := WeakEquivalences Tr.
  Import CD CD.A CD.P.

  Lemma completeDiagramPsUnit: forall {S: Category} (D: Functor S HSetGroupoidCat) (a: S.(CObj))
    (x: P.classifying (D.(fobj) a)),
    (psfData (completeDiagram D)).(psUnit) a x =
    homToId ((liftNat (@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a))).(ncomp) x)
    • homToId ((liftIdentity (D.(fobj) a)).(ncomp) x).
  Proof.
    intros S D a x.
    cbn [completeDiagram composePseudofunctor composePsfData psfData psObj psStr
      psData psUnit psCell structureMapPseudofunctor structureMapData f2obj f2hom
      f2hom2 f2id1 locallyDiscreteFunctor hsetGroupoidDiscreteInclusion
      CD.C.completionPseudofunctor completionPsfData fullInclusion classify].
    rewrite discreteIdTo2, cidr.
    cbn [idTo2 hom2Rew id2 ccomp cid HGpd2Cat hgpdHomCategory BHom ncomp compNatTrans].
    rewrite idTo2Ncomp, homToIdId, idTo2Refl.
    now reflexivity.
  Defined.

  Lemma completeDiagramPsComp: forall {S: Category} (D: Functor S HSetGroupoidCat)
    {a b c: S.(CObj)} (f: S.(CHom) a b) (g: S.(CHom) b c)
    (x: P.classifying (D.(fobj) a)),
    (psfData (completeDiagram D)).(psComp) f g x =
    homToId ((liftComposite (D.(fhom) f) (D.(fhom) g)).(ncomp) x)
    • homToId ((liftNat (@idTo2 HSetGroupoidBicat _ _ _ _ (eq_sym (D.(fcomp) f g)))).(ncomp) x).
  Proof.
    intros S D a b c f g x.
    cbn [completeDiagram composePseudofunctor composePsfData psfData psObj psStr
      psData psComp psCell structureMapPseudofunctor structureMapData f2obj f2hom
      f2hom2 f2comp1 locallyDiscreteFunctor hsetGroupoidDiscreteInclusion
      CD.C.completionPseudofunctor completionPsfData fullInclusion classify].
    rewrite discreteIdTo2. cbn [eq_sym].
    rewrite 3 idTo2Refl. unfold id2. rewrite 2 cidl.
    cbn [ccomp HGpd2Cat hgpdHomCategory BHom ncomp].
    change ((homToId (cid ((liftFunctor (D.(fhom) g)).(fobj)
        ((liftFunctor (D.(fhom) f)).(fobj) x)))
      • homToId ((liftComposite (D.(fhom) f) (D.(fhom) g)).(ncomp) x))
      • homToId ((liftNat (@idTo2 HSetGroupoidBicat _ _ _ _
        (eq_sym (D.(fcomp) f g)))).(ncomp) x)
      = homToId ((liftComposite (D.(fhom) f) (D.(fhom) g)).(ncomp) x)
      • homToId ((liftNat (@idTo2 HSetGroupoidBicat _ _ _ _
        (eq_sym (D.(fcomp) f g)))).(ncomp) x)).
    now rewrite homToIdId, eq_trans_refl_l.
  Defined.

  Local Lemma homToIdPath {A: HGpd} {x y: A} (p: x=y):
    @homToId (pathGpd A) x y p = p.
  Proof.
    now exact (f_equal (@homToId (pathGpd A) x y) (eq_sym (idToHomPath p))
      • @homToIdToHom (pathGpd A) x y p).
  Defined.

  Local Lemma hsetPathImage {G H: HSetGroupoid} {F K: Functor G H}
    (p: F = K) (x: G) (E: Functor H (pathGpd (P.classifying H))):
    E.(fhom) ((@idTo2 HSetGroupoidBicat G H F K p).(ncomp) x)
    = f_equal E.(fobj) (f_equal (fun L: Functor G H => L.(fobj) x) p).
  Proof. destruct p. now apply E.(fid). Defined.

  Definition completionEvaluationFunctor {S: Category} (D: Functor S HSetGroupoidCat) (a: S.(CObj)):
    Functor (D.(fobj) a) (pathGpd ((contractPseudofunctor (completeDiagram D)).(pfObj) a)) :=
    @Build_Functor (D.(fobj) a)
      (pathGpd ((contractPseudofunctor (completeDiagram D)).(pfObj) a))
      (pathCompletionUnit (D.(fobj) a)).(fobj)
      (fun x y u => (pathCompletionUnit (D.(fobj) a)).(fhom) u)
      (pathCompletionUnit (D.(fobj) a)).(fid)
      (fun x y z u v => (pathCompletionUnit (D.(fobj) a)).(fcomp) u v).

  Definition completionEvaluationNaturality {S: Category} (D: Functor S HSetGroupoidCat)
    {a b: S.(CObj)} (f: S.(CHom) a b):
    NatTrans (D.(fhom) f ⨟ᶠ completionEvaluationFunctor D b)
      (completionEvaluationFunctor D a ⨟ᶠ pathFunctor ((psfData (completeDiagram D)).(psHom) f)).
  Proof.
    refine (@Build_NatTrans (D.(fobj) a)
      (pathGpd ((contractPseudofunctor (completeDiagram D)).(pfObj) b))
      (D.(fhom) f ⨟ᶠ completionEvaluationFunctor D b)
      (completionEvaluationFunctor D a ⨟ᶠ pathFunctor ((psfData (completeDiagram D)).(psHom) f))
      (fun x => (liftUnit (D.(fhom) f)).(ncomp) x) _).
    intros x y u.
    change ((pathCompletionUnit (D.(fobj) b)).(fhom) ((D.(fhom) f).(fhom) u)
      • (liftUnit (D.(fhom) f)).(ncomp) y
      = (liftUnit (D.(fhom) f)).(ncomp) x
      • f_equal (liftFunctor (D.(fhom) f)).(fobj) ((pathCompletionUnit (D.(fobj) a)).(fhom) u)).
    refine ((liftUnit (D.(fhom) f)).(nnat) u • _).
    now exact (f_equal (fun q => (liftUnit (D.(fhom) f)).(ncomp) x • q)
      (pathFunctorFhom (liftFunctor (D.(fhom) f)) ((pathCompletionUnit (D.(fobj) a)).(fhom) u))).
  Defined.

  Lemma completionEvaluationUnit {S: Category} (D: Functor S HSetGroupoidCat)
    (a: S.(CObj)) (x: D.(fobj) a):
    (completionEvaluationNaturality D (S.(cid) a)).(ncomp) x
    • f_equal (fun k => k ((completionEvaluationFunctor D a).(fobj) x))
      ((pathData S _ (contractPseudofunctor (completeDiagram D)).(pfStr)).(pid) a)
    = f_equal (completionEvaluationFunctor D a).(fobj)
    (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) a) => F.(fobj) x) (D.(fid) a)).
  Proof.
    change ((liftUnit (D.(fhom) (S.(cid) a))).(ncomp) x
    • f_equal (fun k => k ((pathCompletionUnit (D.(fobj) a)).(fobj) x))
    (functional_extensionality_dep_good _ _ ((psfData (completeDiagram D)).(psUnit) a))
    = f_equal (pathCompletionUnit (D.(fobj) a)).(fobj)
      (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) a) => F.(fobj) x) (D.(fid) a))).
    refine (f_equal (fun p => (liftUnit (D.(fhom) (S.(cid) a))).(ncomp) x • p)
    (f_equal__functional_extensionality_dep_good ((psfData (completeDiagram D)).(psUnit) a)
    ((pathCompletionUnit (D.(fobj) a)).(fobj) x)) • _).
    rewrite completeDiagramPsUnit, 2 homToIdPath.
    refine (eq_sym (eqTransAssoc
    ((liftUnit (D.(fhom) (S.(cid) a))).(ncomp) x)
    ((liftNat (@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a))).(ncomp)
      ((pathCompletionUnit (D.(fobj) a)).(fobj) x))
    ((liftIdentity (D.(fobj) a)).(ncomp) ((pathCompletionUnit (D.(fobj) a)).(fobj) x))) • _).
    refine (f_equal (fun p => p • (liftIdentity (D.(fobj) a)).(ncomp)
    ((pathCompletionUnit (D.(fobj) a)).(fobj) x))
    (liftNatComm (@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a)) x) • _).
    refine (f_equal (fun q => ((pathCompletionUnit (D.(fobj) a)).(fhom)
    ((@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a)).(ncomp) x)
    ⨟ (liftUnit (idFunctor (D.(fobj) a))).(ncomp) x) ⨟ q)
    (liftIdentityAt (D.(fobj) a) x) • _).
    refine ((completedPaths (D.(fobj) a)).(cassoc)
    ((pathCompletionUnit (D.(fobj) a)).(fhom)
    ((@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a)).(ncomp) x))
    ((liftUnit (idFunctor (D.(fobj) a))).(ncomp) x)
    (ginv ((liftUnit (idFunctor (D.(fobj) a))).(ncomp) x)) • _).
    refine (f_equal (fun q => (pathCompletionUnit (D.(fobj) a)).(fhom)
    ((@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a)).(ncomp) x) ⨟ q)
    (ginvR ((liftUnit (idFunctor (D.(fobj) a))).(ncomp) x)) • _).
    refine ((completedPaths (D.(fobj) a)).(cidr)
    ((pathCompletionUnit (D.(fobj) a)).(fhom)
    ((@idTo2 HSetGroupoidBicat _ _ _ _ (D.(fid) a)).(ncomp) x)) • _).
    now exact (hsetPathImage (D.(fid) a) x (pathCompletionUnit (D.(fobj) a))).
  Defined.

  Lemma completionEvaluationComp {S: Category} (D: Functor S HSetGroupoidCat)
    {a b c: S.(CObj)} (f: S.(CHom) a b) (g: S.(CHom) b c) (x: D.(fobj) a):
    f_equal (completionEvaluationFunctor D c).(fobj)
      (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) c) => F.(fobj) x) (D.(fcomp) f g))
    • ((completionEvaluationNaturality D g).(ncomp) ((D.(fhom) f).(fobj) x)
    • (f_equal ((pathData S _ (contractPseudofunctor (completeDiagram D)).(pfStr)).(phom) g)
      ((completionEvaluationNaturality D f).(ncomp) x)
    • ((pathData S _ (contractPseudofunctor (completeDiagram D)).(pfStr)).(pcomp) f g
      ((completionEvaluationFunctor D a).(fobj) x))))
    = (completionEvaluationNaturality D (f ⨟ g)).(ncomp) x.
  Proof.
    change (f_equal (pathCompletionUnit (D.(fobj) c)).(fobj)
      (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) c) => F.(fobj) x) (D.(fcomp) f g))
    • ((liftUnit (D.(fhom) g)).(ncomp) ((D.(fhom) f).(fobj) x)
    • (f_equal (liftFunctor (D.(fhom) g)).(fobj) ((liftUnit (D.(fhom) f)).(ncomp) x)
    • (psfData (completeDiagram D)).(psComp) f g ((pathCompletionUnit (D.(fobj) a)).(fobj) x)))
    = (liftUnit (D.(fhom) (f ⨟ g))).(ncomp) x).
    rewrite completeDiagramPsComp, 2 homToIdPath.
    rewrite <- (pathFunctorFhom (liftFunctor (D.(fhom) g))).
    rewrite <- (eqTransAssoc ((liftUnit (D.(fhom) g)).(ncomp) ((D.(fhom) f).(fobj) x))
      ((liftFunctor (D.(fhom) g)).(fhom) ((liftUnit (D.(fhom) f)).(ncomp) x))).
    rewrite <- (eqTransAssoc ((liftCompositeUnit (D.(fhom) f) (D.(fhom) g)).(ncomp) x)).
    refine (f_equal (fun t => f_equal (pathCompletionUnit (D.(fobj) c)).(fobj)
        (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) c) => F.(fobj) x) (D.(fcomp) f g))
        • (t • (liftNat (@idTo2 HSetGroupoidBicat _ _ _ _ (eq_sym (D.(fcomp) f g)))).(ncomp)
          ((pathCompletionUnit (D.(fobj) a)).(fobj) x)))
      (liftCompositeComm (D.(fhom) f) (D.(fhom) g) x) • _).
    refine (f_equal (fun t => f_equal (pathCompletionUnit (D.(fobj) c)).(fobj)
        (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) c) => F.(fobj) x) (D.(fcomp) f g)) • t)
      (liftNatComm (@idTo2 HSetGroupoidBicat _ _ _ _ (eq_sym (D.(fcomp) f g))) x) • _).
    rewrite hsetPathImage.
    rewrite <- 2 eq_sym_map_distr.
    now apply transSymCancelL.
  Defined.

  Definition completionEvaluation {S: Category} (D: Functor S HSetGroupoidCat):
    DiagramEvaluation D (contractPseudofunctor (completeDiagram D)) :=
    @Build_DiagramEvaluation S D (contractPseudofunctor (completeDiagram D))
      (completionEvaluationFunctor D)
      (fun a b f => completionEvaluationNaturality D f)
      (completionEvaluationUnit D)
      (fun a b c f g x => completionEvaluationComp D f g x).

  Definition completionEvaluationWeak {S: Category} (D: Functor S HSetGroupoidCat)
    (a: S.(CObj)): W.IsWeakEquivalence ((completionEvaluation D).(evalFunctor) a) :=
    P.pathCompletionUnitWeak (D.(fobj) a).
End CompletionEvaluationsOn.

(** A coherent evaluation that is a weak equivalence at each object
    identifies the completion of a strict diagram with its target diagram. *)
Unset Keyed Unification.

Local Lemma expandContractDiagram {I: Category}
  (F: Pseudofunctor (locallyDiscrete I) HGpd2Cat):
  expandPseudofunctor (contractPseudofunctor F) = F.
Proof. now exact (secEq (locallyDiscretePseudofunctorEquiv I) F). Defined.

Module CompletionComparisonsOn (Tr: PropositionalTruncation)
  (CD: CompletionDiagramsSig Tr).
  Module E := CompletionEvaluationsOn Tr CD.
  Module D := CD.
  Module K := DiagramComparisons Tr.
  Module W := WeakEquivalences Tr.
  Import W.

  Definition completeDiagramEq {I: Category} (F: Functor I HSetGroupoidCat)
    (X: PathDiagramFamily I) (Q: DiagramEvaluation F X)
    (wQ: forall i, IsWeakEquivalence (Q.(evalFunctor) i)):
    D.completeDiagram F = expandPseudofunctor X.
  Proof.
    refine (eq_sym (expandContractDiagram (D.completeDiagram F)) • _).
    now exact (@K.evaluationComparisonEq I F
      (contractPseudofunctor (D.completeDiagram F)) X
      (E.completionEvaluation F) Q (E.completionEvaluationWeak F) wQ).
  Defined.
End CompletionComparisonsOn.
