(** A set of representatives generates a strict diagram by closing the
    representatives under all arrows of the indexing category. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation RewLemmas Equiv Truncation.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category Require Import Category FunctorAlgebra.
From Bonak.Category.Groupoid Require Import SetBased WeakEquivalence.
From Bonak.Strictification Require Import DiagramEvaluation.
From Bonak.Category.Bicategory Require Import PathDiagram PathDiagramLemmas PathGroupoid.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Definition conjugate {A: Type} {x x' y y': A}
  (u: x = x') (v: y = y') (p: x = y): x' = y' :=
  eq_sym u • (p • v).

Local Lemma conjugateId {A: Type} {x y: A} (u: x = y):
  conjugate u u eq_refl = eq_refl.
Proof. now destruct u. Defined.

Local Lemma conjugateComp {A: Type} {x x' y y' z z': A}
  (u: x = x') (v: y = y') (w: z = z') (p: x = y) (q: y = z):
  conjugate u w (p • q) = conjugate u v p • conjugate v w q.
Proof. now destruct u, v, w, p, q. Defined.

Local Lemma conjugateTrans {A: Type} {x x' x'' y y' y'': A}
  (u: x = x') (u': x' = x'') (v: y = y') (v': y' = y'') (p: x = y):
  conjugate u' v' (conjugate u v p) = conjugate (u • u') (v • v') p.
Proof. now destruct u, u', v, v', p. Defined.

Local Lemma conjugateMap {A B: Type} (f: A -> B) {x x' y y': A}
  (u: x = x') (v: y = y') (p: x = y):
  f_equal f (conjugate u v p) =
  conjugate (f_equal f u) (f_equal f v) (f_equal f p).
Proof. now destruct u, v, p. Defined.

Local Lemma conjugateNaturality {A B: Type} (f g: A -> B)
  (h: forall x, f x = g x) {x y: A} (p: x = y):
  conjugate (h x) (h y) (f_equal f p) = f_equal g p.
Proof. destruct p. now apply conjugateId. Defined.

Local Lemma conjugateSquare {A: Type} {x x' y y': A}
  (u: x = x') (v: y = y') (p: x = y):
  conjugate u v p • eq_sym v = eq_sym u • p.
Proof. now destruct u, v, p. Defined.

Local Lemma inverseCompositeSquare {A: Type} {a b c d e: A}
  (u: a = b) (v: b = c) (w: c = d) (p: a = e) (q: e = d):
  u • (v • w) = p • q ->
  eq_sym w • (eq_sym v • (eq_sym u • p)) = eq_sym q.
Proof.
  destruct u, v, w, p. cbn. intro H.
  rewrite eq_trans_refl_l in H. now rewrite <- H.
Defined.

Section Charts.
Context {C: Category} (X: PathDiagramFamily C).
Context (S: HSet) (src: S -> C.(CObj)) (val: forall s, X.(pfObj) (src s)).
Let D := pathData C X.(pfObj) X.(pfStr).

Definition chartLabels (i: C.(CObj)): HSet :=
  hsigT (fun s: S => C.(CHom) (src s) i).

Definition chartValue (i: C.(CObj)) (x: chartLabels i): X.(pfObj) i :=
  D.(phom) x.2 (val x.1).

Definition chartGroupoid (i: C.(CObj)): HSetGroupoid :=
  presentationGroupoid (pathGpd (X.(pfObj) i)) (chartLabels i) (chartValue i).

Definition chartEvaluation (i: C.(CObj)):
  Functor (chartGroupoid i) (pathGpd (X.(pfObj) i)) :=
  presentationFunctor (pathGpd (X.(pfObj) i)) (chartLabels i) (chartValue i).

Definition chartAction {i j: C.(CObj)} (k: C.(CHom) i j)
  (x: chartLabels i): chartLabels j := (x.1; x.2 ⨟ k).

Definition chartComposite {i j: C.(CObj)} (k: C.(CHom) i j)
  (x: chartLabels i): D.(phom) k (chartValue i x) = chartValue j (chartAction k x) :=
  D.(pcomp) x.2 k (val x.1).

Definition chartFunctor {i j: C.(CObj)} (k: C.(CHom) i j):
  Functor (chartGroupoid i) (chartGroupoid j).
Proof.
  refine (@Build_Functor (chartGroupoid i) (chartGroupoid j)
    (chartAction k) (fun x y p => conjugate (chartComposite k x) (chartComposite k y)
      (f_equal (D.(phom) k) p)) _ _).
  - intro x. now apply conjugateId.
  - intros x y z p q. cbn. rewrite eq_trans_map_distr.
    now apply conjugateComp.
Defined.

Local Lemma chartCast {i: C.(CObj)} {x x' y y': chartLabels i}
  (p: x = x') (q: y = y') (h: (chartGroupoid i).(CHom) x y):
  castArrow (G := chartGroupoid i) p q h =
  conjugate (f_equal (chartValue i) p) (f_equal (chartValue i) q) h.
Proof. destruct p, q. unfold conjugate. cbn. now rewrite eq_trans_refl_l. Defined.

Definition chartIdentityObject (i: C.(CObj)) (x: chartLabels i):
  chartAction (C.(cid) i) x = x :=
  f_equal (fun f => (x.1; f)) (C.(cidr) x.2).

Lemma chartIdentityValue (i: C.(CObj)) (x: chartLabels i):
  chartComposite (C.(cid) i) x • f_equal (chartValue i) (chartIdentityObject i x)
  = pidPt D i (chartValue i x).
Proof.
  destruct x as [s f].
  change (D.(pcomp) f (C.(cid) i) (val s)
    • f_equal (fun x: chartLabels i => D.(phom) x.2 (val x.1))
      (f_equal (fun f: C.(CHom) (src s) i => (s; f)) (C.(cidr) f))
    = pidPt D i (D.(phom) f (val s))).
  rewrite (pcompUnitRPt D (pathUnitR C X.(pfObj) X.(pfStr)) _ _ f (C.(cidr) f) (val s)).
  rewrite f_equal_compose. now apply transSymCancelR2.
Defined.

Lemma chartFunctorIdentity (i: C.(CObj)):
  chartFunctor (C.(cid) i) ≐ idFunctor (chartGroupoid i).
Proof.
  refine (@Build_FunctorEq (chartGroupoid i) (chartGroupoid i)
    (chartFunctor (C.(cid) i)) (idFunctor (chartGroupoid i)) (chartIdentityObject i) _).
  intros x y p. rewrite chartCast.
  change (conjugate (f_equal (chartValue i) (chartIdentityObject i x))
    (f_equal (chartValue i) (chartIdentityObject i y))
    (conjugate (chartComposite (C.(cid) i) x) (chartComposite (C.(cid) i) y)
      (f_equal (D.(phom) (C.(cid) i)) p)) = p).
  rewrite conjugateTrans, 2 chartIdentityValue.
  refine (conjugateNaturality (D.(phom) (C.(cid) i)) (fun x => x) (pidPt D i) p • _).
  now apply f_equal_id.
Defined.

Definition chartCompositionObject {i j k: C.(CObj)}
  (f: C.(CHom) i j) (g: C.(CHom) j k) (x: chartLabels i):
  chartAction g (chartAction f x) = chartAction (f ⨟ g) x :=
  f_equal (fun h => (x.1; h)) (C.(cassoc) x.2 f g).

Lemma chartCompositionValue {i j k: C.(CObj)}
  (f: C.(CHom) i j) (g: C.(CHom) j k) (x: chartLabels i):
  f_equal (D.(phom) g) (chartComposite f x)
    • (chartComposite g (chartAction f x)
      • f_equal (chartValue k) (chartCompositionObject f g x))
  = D.(pcomp) f g (chartValue i x) • chartComposite (f ⨟ g) x.
Proof.
  destruct x as [s h].
  change (f_equal (D.(phom) g) (D.(pcomp) h f (val s))
    • (D.(pcomp) (h ⨟ f) g (val s)
      • f_equal (fun x: chartLabels k => D.(phom) x.2 (val x.1))
        (f_equal (fun h: C.(CHom) (src s) k => (s; h)) (C.(cassoc) h f g)))
    = D.(pcomp) f g (D.(phom) h (val s)) • D.(pcomp) h (f ⨟ g) (val s)).
  rewrite f_equal_compose.
  now apply (pcompAssocPt D (pathAssoc C X.(pfObj) X.(pfStr))).
Defined.

Lemma chartFunctorComposition {i j k: C.(CObj)}
  (f: C.(CHom) i j) (g: C.(CHom) j k):
  chartFunctor f ⨟ᶠ chartFunctor g ≐ chartFunctor (f ⨟ g).
Proof.
  refine (@Build_FunctorEq (chartGroupoid i) (chartGroupoid k)
    (chartFunctor f ⨟ᶠ chartFunctor g) (chartFunctor (f ⨟ g)) (chartCompositionObject f g) _).
  intros x y p. rewrite chartCast.
  change (conjugate (f_equal (chartValue k) (chartCompositionObject f g x))
    (f_equal (chartValue k) (chartCompositionObject f g y))
    (conjugate (chartComposite g (chartAction f x)) (chartComposite g (chartAction f y))
      (f_equal (D.(phom) g)
        (conjugate (chartComposite f x) (chartComposite f y) (f_equal (D.(phom) f) p)))) =
    conjugate (chartComposite (f ⨟ g) x) (chartComposite (f ⨟ g) y)
      (f_equal (D.(phom) (f ⨟ g)) p)).
  rewrite conjugateMap, 2 conjugateTrans.
  rewrite 2 chartCompositionValue, <- conjugateTrans, f_equal_compose.
  now rewrite (conjugateNaturality
    (fun z => D.(phom) g (D.(phom) f z)) (D.(phom) (f ⨟ g)) (D.(pcomp) f g) p).
Defined.

Definition chartDiagram: Functor C HSetGroupoidCat.
Proof.
  refine (@Build_Functor C HSetGroupoidCat chartGroupoid (fun i j f => chartFunctor f) _ _).
  - intro i. now apply (functorEqPath (chartGroupoid i).(hsetGroupoidUIP)), chartFunctorIdentity.
  - intros i j k f g. apply (functorEqPath (chartGroupoid k).(hsetGroupoidUIP)), feqSym.
    now apply chartFunctorComposition.
Defined.

(** Evaluation is coherent with the original weak action. *)
Definition chartNaturality {i j: C.(CObj)} (f: C.(CHom) i j):
  NatTrans (chartFunctor f ⨟ᶠ chartEvaluation j)
    (chartEvaluation i ⨟ᶠ pathFunctor (D.(phom) f)).
Proof.
  refine (@Build_NatTrans (chartGroupoid i) (pathGpd (X.(pfObj) j))
    (chartFunctor f ⨟ᶠ chartEvaluation j)
    (chartEvaluation i ⨟ᶠ pathFunctor (D.(phom) f))
    (fun x => eq_sym (chartComposite f x)) _).
  intros x y p. now apply conjugateSquare.
Defined.

Definition chartDiagramEvaluation: DiagramEvaluation chartDiagram X.
Proof.
  refine (@Build_DiagramEvaluation C chartDiagram X chartEvaluation
    (fun i j f => chartNaturality f) _ _).
  - intros i x.
    change (eq_sym (chartComposite (C.(cid) i) x) • pidPt D i (chartValue i x) =
      f_equal (chartValue i)
        (f_equal (fun F: Functor (chartGroupoid i) (chartGroupoid i) => F.(fobj) x)
          (chartDiagram.(fid) i))).
    rewrite (@UIP (chartLabels i) _ _
      (f_equal (fun F: Functor (chartGroupoid i) (chartGroupoid i) => F.(fobj) x)
        (chartDiagram.(fid) i)) (chartIdentityObject i x)).
    rewrite <- chartIdentityValue. now apply eq_trans_sym_cancel_l.
  - intros i j k f g x.
    change (f_equal (chartValue k)
      (f_equal (fun F: Functor (chartGroupoid i) (chartGroupoid k) => F.(fobj) x)
        (chartDiagram.(fcomp) f g))
      • (eq_sym (chartComposite g (chartAction f x))
      • (f_equal (D.(phom) g) (eq_sym (chartComposite f x))
      • D.(pcomp) f g (chartValue i x))) = eq_sym (chartComposite (f ⨟ g) x)).
    rewrite (@UIP (chartLabels k) _ _
      (f_equal (fun F: Functor (chartGroupoid i) (chartGroupoid k) => F.(fobj) x)
        (chartDiagram.(fcomp) f g)) (eq_sym (chartCompositionObject f g x))).
    rewrite <- 2 eq_sym_map_distr.
    now apply inverseCompositeSquare, chartCompositionValue.
Defined.
End Charts.

(** A cover of all diagram objects makes chart evaluation a weak
    equivalence in every degree. Truncation is eliminated only into the
    essential-surjectivity proposition. *)
Import Logic.EqNotations.

Module ChartCoverage (Tr: PropositionalTruncation).
  Import Tr.
  Module W := WeakEquivalences Tr.
  Import W W.TF.

  Section Coverage.
  Context {C: Category} (X: PathDiagramFamily C).
  Context (S: HSet) (src: S -> C.(CObj)) (val: forall s, X.(pfObj) (src s)).
  Context (cover: IsSurjective (fun s => ((src s; val s): {i: C.(CObj) &T X.(pfObj) i}))).

  Definition chartValueSurjective (i: C.(CObj)):
    IsSurjective (chartValue X S src val i).
  Proof.
    intro x. refine (trMap _ (cover (i; x))). intros [s e].
    refine (rew [fun t: {i: C.(CObj) &T X.(pfObj) i} =>
      {a: chartLabels S src t.1 &T chartValue X S src val t.1 a = t.2}] e in _).
    refine ((s; C.(cid) (src s)); _).
    now exact (pidPt (pathData C X.(pfObj) X.(pfStr)) (src s) (val s)).
  Defined.

  Definition chartEvaluationWeak (i: C.(CObj)):
    IsWeakEquivalence (chartEvaluation X S src val i) :=
    @Build_IsWeakEquivalence (chartGroupoid X S src val i)
      (pathGpd (X.(pfObj) i)) (chartEvaluation X S src val i)
      (fun x y => idEquiv.(eqvIsEquiv)) (chartValueSurjective i).
  End Coverage.
End ChartCoverage.
