(** Pullback of diagrams along functors: the induced maps of diagrams and
    matching objects, composition and reindexing of pullbacks, and repacking
    of matching objects across truncation of the indexing functor. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import HSet HGpd SigT Funext Notation RewLemmas
  FinitePrefix Equiv.
From Bonak.Category Require Import Category SequentialFunctor.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas LocallyDiscrete
  LocallyDiscretePseudofunctor PseudofunctorOps.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift.

Set Primitive Projections.
Set Printing Projections.
Import FinitePrefix.

(** Natural transformations of indexing functors act on pulled-back diagrams. *)

Section Pullback.
Context {B C: Category} (F: PathDiagramFamily C) (U: Functor B C).

Lemma pullbackCompPoint {i j k: B.(CObj)}
  (f: B.(CHom) i j) (g: B.(CHom) j k) (x: F.(pfObj) (U.(fobj) i)):
  (pathData _ _ (pullbackDiagram U F).(pfStr)).(pcomp) f g x =
    (pathData _ _ F.(pfStr)).(pcomp) (U.(fhom) f) (U.(fhom) g) x
      • phomEq (pathData _ _ F.(pfStr)) (eq_sym (U.(fcomp) f g)) x.
Proof.
  unfold pullbackDiagram.
  cbn [contractPseudofunctor composePseudofunctor structureMapPseudofunctor
    expandPseudofunctor pfStr psStr contractPsf contractData
    pathData pcomp psData composePsfData psComp psfData expandPsf expandData
    structureMapData locallyDiscreteFunctor f2hom f2comp1].
  cbn. unfold phomEq. apply f_equal. apply f_equal.
  now apply (C.(CHom) _ _).(UIP).
Defined.

Lemma pullbackIdPoint (i: B.(CObj)) (x: F.(pfObj) (U.(fobj) i)):
  pidPt (pathData _ _ (pullbackDiagram U F).(pfStr)) i x =
    phomEq (pathData _ _ F.(pfStr)) (U.(fid) i) x
      • pidPt (pathData _ _ F.(pfStr)) (U.(fobj) i) x.
Proof.
  unfold pullbackDiagram, pidPt.
  cbn [contractPseudofunctor composePseudofunctor structureMapPseudofunctor
    expandPseudofunctor pfStr psStr contractPsf contractData
    pathData pid psData composePsfData psUnit psfData expandPsf expandData
    structureMapData locallyDiscreteFunctor f2hom f2id1].
  cbn. unfold happly. etransitivity.
  - now exact (f_equal__functional_extensionality_dep_good _ x).
  - rewrite idTo2Point. unfold phomEq. apply f_equal2.
    + apply f_equal. now apply (C.(CHom) _ _).(UIP).
    + now reflexivity.
Defined.
End Pullback.

Section PrefixPullback.
Context {A: HSet} {n} {C: Category} (F: PathDiagramFamily C)
  (U: Functor (PrefixCategory A n) C).
Lemma pullbackRestrictComp {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: cells (pullbackDiagram U F) k):
  restrictComp (pullbackDiagram U F) f g x =
    (pathData _ _ F.(pfStr)).(pcomp) (U.(fhom) g) (U.(fhom) f) x
      • phomEq (pathData _ _ F.(pfStr)) (eq_sym (U.(fcomp) g f)) x.
Proof. now exact (pullbackCompPoint F U g f x). Defined.
Lemma pullbackRestrictId (i: Index n) (x: cells (pullbackDiagram U F) i):
  restrictId (pullbackDiagram U F) i x =
    phomEq (pathData _ _ F.(pfStr)) (U.(fid) i) x
      • pidPt (pathData _ _ F.(pfStr)) (U.(fobj) i) x.
Proof. now exact (pullbackIdPoint F U i x). Defined.
End PrefixPullback.

Section Map.
Context {A: HSet} {n} {C: Category} (F: PathDiagramFamily C)
  (U V: Functor (PrefixCategory A n) C) (α: NatTrans U V).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation FU := (pullbackDiagram U F).
Local Abbreviation FV := (pullbackDiagram V F).

Definition pullbackCell (i: Index n): cells FU i -> cells FV i :=
  FD.(phom) (α.(ncomp) i).

Definition pullbackNaturality {i j: Index n}
  (f: Word A (rank i) (rank j)) (x: cells FU j):
  restrict FV f (pullbackCell j x) = pullbackCell i (restrict FU f x) :=
  FD.(pcomp) (α.(ncomp) j) (V.(fhom) f) x
    • (phomEq FD (eq_sym (α.(nnat) f)) x
      • eq_sym (FD.(pcomp) (U.(fhom) f) (α.(ncomp) i) x)).

Local Lemma compUnitLNormalized {i j: C.(CObj)}
  (g: C.(CHom) i i) (e: g = C.(cid) i) (f: C.(CHom) i j)
  (h: g ⨟ f = f) (x: F.(pfObj) i):
  FD.(pcomp) g f x • phomEq FD h x =
    f_equal (FD.(phom) f) (phomEq FD e x • pidPt FD i x).
Proof.
  subst g. cbn [phomEq f_equal]. rewrite eq_trans_refl_l.
  rewrite (pcompUnitLPt FD (pathUnitL _ _ F.(pfStr)) i j f h x).
  now apply transSymCancelR2.
Defined.

Local Lemma compUnitRNormalized {i j: C.(CObj)}
  (f: C.(CHom) i j) (g: C.(CHom) j j) (e: g = C.(cid) j)
  (h: f ⨟ g = f) (x: F.(pfObj) i):
  FD.(pcomp) f g x • phomEq FD h x =
    phomEq FD e (FD.(phom) f x) • pidPt FD j (FD.(phom) f x).
Proof.
  subst g. cbn [phomEq f_equal]. rewrite eq_trans_refl_l.
  rewrite (pcompUnitRPt FD (pathUnitR _ _ F.(pfStr)) i j f h x).
  now apply transSymCancelR2.
Defined.

Lemma pullbackNaturalityUnit (i: Index n) (x: cells FU i):
  pullbackNaturality (wid (rank i)) x
    • f_equal (pullbackCell i) (restrictId FU i x)
    = restrictId FV i (pullbackCell i x).
Proof.
  rewrite 2 pullbackRestrictId.
  pose (hU := f_equal (fun w => w ⨟ α.(ncomp) i) (U.(fid) i)
    • C.(cidl) (α.(ncomp) i)).
  pose (hV := f_equal (fun w => α.(ncomp) i ⨟ w) (V.(fid) i)
    • C.(cidr) (α.(ncomp) i)).
  change (pullbackNaturality (wid (rank i)) x
    • f_equal (FD.(phom) (α.(ncomp) i))
      (phomEq FD (U.(fid) i) x • pidPt FD (U.(fobj) i) x) =
    phomEq FD (V.(fid) i) (pullbackCell i x)
      • pidPt FD (V.(fobj) i) (pullbackCell i x)).
  refine (transCongL _ (eq_sym (compUnitLNormalized
    (U.(fhom) (wid (rank i))) (U.(fid) i) (α.(ncomp) i) hU x)) • _).
  unfold pullbackNaturality.
  rewrite eqTransAssoc, transCancelMid2.
  refine (_ • compUnitRNormalized (α.(ncomp) i) (V.(fhom) (wid (rank i)))
    (V.(fid) i) hV x).
  apply transCongL. unfold phomEq.
  refine (eq_sym (mapTrans
    (fun w: C.(CHom) (U.(fobj) i) (V.(fobj) i) => FD.(phom) w x)
    (eq_sym (α.(nnat) (wid (rank i)))) hU) • _).
  apply f_equal. now apply (C.(CHom) _ _).(UIP).
Defined.

Local Lemma sourceTriangle {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)) (x: cells FU k):
  psfComp3 FD (U.(fhom) g) (U.(fhom) f) (α.(ncomp) i) x
    • phomEq FD (f_equal (fun w => w ⨟ α.(ncomp) i) (eq_sym (U.(fcomp) g f))) x
  = f_equal (pullbackCell i) (restrictComp FU f g x)
      • FD.(pcomp) (U.(fhom) (wcomp g f)) (α.(ncomp) i) x.
Proof.
  rewrite pullbackRestrictComp, mapTrans.
  unfold psfComp3. rewrite 2 eqTransAssoc.
  apply transCongL. symmetry.
  now exact (pcompNatLCanonical FD (eq_sym (U.(fcomp) g f)) (α.(ncomp) i) x).
Defined.

Local Lemma targetTriangle {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)) (x: cells FU k):
  psfComp3 FD (α.(ncomp) k) (V.(fhom) g) (V.(fhom) f) x
    • phomEq FD (C.(cassoc) (α.(ncomp) k) (V.(fhom) g) (V.(fhom) f)
      • f_equal (ccomp (α.(ncomp) k)) (eq_sym (V.(fcomp) g f))) x =
  restrictComp FV f g (pullbackCell k x)
    • FD.(pcomp) (α.(ncomp) k) (V.(fhom) (wcomp g f)) x.
Proof.
  unfold phomEq at 1. rewrite mapTrans, <- eqTransAssoc.
  refine (transCongR (psfAssocPt FD (pathAssoc _ _ F.(pfStr))
    (α.(ncomp) k) (V.(fhom) g) (V.(fhom) f) x) _ • _).
  rewrite pullbackRestrictComp, 2 eqTransAssoc.
  apply transCongL. symmetry.
  now exact (pcompNatRCanonical FD (α.(ncomp) k) (eq_sym (V.(fcomp) g f)) x).
Defined.

Lemma pullbackNaturalityComp {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)) (x: cells FU k):
  f_equal (restrict FV f) (pullbackNaturality g x)
    • (pullbackNaturality f (restrict FU g x)
      • f_equal (pullbackCell i) (restrictComp FU f g x)) =
  restrictComp FV f g (pullbackCell k x)
    • pullbackNaturality (wcomp g f) x.
Proof.
  unfold pullbackNaturality, phomEq.
  change (restrict FV f) with (FD.(phom) (V.(fhom) f)).
  change (restrict FU g x) with (FD.(phom) (U.(fhom) g) x).
  refine (transCongR (pcompWhiskerL FD (eq_sym (α.(nnat) g)) (V.(fhom) f) x
    (FD.(pcomp) (α.(ncomp) k) (V.(fhom) g) x)
    (FD.(pcomp) (U.(fhom) g) (α.(ncomp) j) x)) _ • _).
  refine (transCongL _ (transCongR (pcompWhiskerR FD (pathAssoc _ _ F.(pfStr))
    (U.(fhom) g) (v := α.(ncomp) j) (w := V.(fhom) f)
    (v' := U.(fhom) f) (w' := α.(ncomp) i)
    (eq_sym (α.(nnat) f)) x) _) • _).
  refine (conjugatePaste _ _ _ _ _ _ _ _ (sourceTriangle f g x) • _).
  rewrite <- (eqTransAssoc (restrictComp FV f g (pullbackCell k x))
    (FD.(pcomp) (α.(ncomp) k) (V.(fhom) (wcomp g f)) x)).
  rewrite <- targetTriangle.
  rewrite (eqTransAssoc
    (psfComp3 FD (α.(ncomp) k) (V.(fhom) g) (V.(fhom) f) x)).
  apply transCongL.
  rewrite <- (eqTransAssoc _ _ (eq_sym (FD.(pcomp) (U.(fhom) (wcomp g f)) (α.(ncomp) i) x))).
  apply transCongR. unfold phomEq.
  now exact (fEqualUIP (@UIP (C.(CHom) (U.(fobj) k) (V.(fobj) i)))
    (fun w => FD.(phom) w x) _ _ _ _ _ eq_refl).
Defined.

Definition pullbackMap: DiagramMap FU FV.
Proof.
  refine (@Build_DiagramMap A n FU FV pullbackCell
    (fun i j f x => eq_sym (pullbackNaturality f x)) _ _).
  - intros i x. apply (transCancelL (pullbackNaturality (wid (rank i)) x)).
    rewrite transSymCancelL. now apply pullbackNaturalityUnit.
  - intros i j k f g x. rewrite fEqualSym.
    now exact (reversePasting _ _ _ _ _ (pullbackNaturalityComp f g x)).
Defined.

Lemma pullbackMapCell i x: (mapCell pullbackMap) i x = FD.(phom) (α.(ncomp) i) x.
Proof. now reflexivity. Defined.
Lemma pullbackMapNatural {i j} (f: Word A (rank i) (rank j)) (x: cells FU j):
  (mapNatural pullbackMap) f x = eq_sym (pullbackNaturality f x).
Proof. now reflexivity. Defined.
End Map.

(** Identity and vertical composition for maps induced by indexing
    transformations. *)

Local Lemma unitSquare {T: Type} {a b c d e: T}
  (p: a = e) (q: b = e) (r: c = e) (s: d = e):
  ((p • eq_sym q) • ((q • eq_sym r) • eq_sym (s • eq_sym r))) • s = p.
Proof. now destruct p, q, r, s. Defined.

Section Coherence.
Context {A: HSet} {n: nat} {C: Category} (F: PathDiagramFamily C).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).

Lemma pullbackNaturalityIdentity (U: Functor (PrefixCategory A n) C)
  {i j: Index n} (f: Word A (rank i) (rank j))
  (x: cells (pullbackDiagram U F) j):
  f_equal (FD.(phom) (U.(fhom) f)) (pidPt FD (U.(fobj) j) x) =
  pullbackNaturality F U U (idNatTrans U) f x
    • pidPt FD (U.(fobj) i) (FD.(phom) (U.(fhom) f) x).
Proof.
  unfold pullbackNaturality.
  change (f_equal (FD.(phom) (U.(fhom) f)) (pidPt FD (U.(fobj) j) x) =
    (FD.(pcomp) (C.(cid) (U.(fobj) j)) (U.(fhom) f) x
      • (phomEq FD (eq_sym ((idNatTrans U).(nnat) f)) x
        • eq_sym (FD.(pcomp) (U.(fhom) f) (C.(cid) (U.(fobj) i)) x)))
      • pidPt FD (U.(fobj) i) (FD.(phom) (U.(fhom) f) x)).
  rewrite (pcompUnitLPt FD (pathUnitL _ _ F.(pfStr))
    (U.(fobj) j) (U.(fobj) i) (U.(fhom) f) (C.(cidl) (U.(fhom) f)) x).
  rewrite (pcompUnitRPt FD (pathUnitR _ _ F.(pfStr))
    (U.(fobj) j) (U.(fobj) i) (U.(fhom) f) (C.(cidr) (U.(fhom) f)) x).
  assert (e: phomEq FD (eq_sym ((idNatTrans U).(nnat) f)) x =
    phomEq FD (C.(cidl) (U.(fhom) f)) x
      • eq_sym (phomEq FD (C.(cidr) (U.(fhom) f)) x)).
  { refine (f_equal (fun e => phomEq FD e x)
      (@UIP (C.(CHom) (U.(fobj) j) (U.(fobj) i)) _ _
        (eq_sym ((idNatTrans U).(nnat) f))
        (C.(cidl) (U.(fhom) f) • eq_sym (C.(cidr) (U.(fhom) f)))) • _).
    unfold phomEq. now rewrite eq_trans_map_distr, fEqualSym. }
  rewrite e. now symmetry; apply unitSquare.
Defined.

Lemma pullbackNaturalityEq (U V: Functor (PrefixCategory A n) C)
  {α β: NatTrans U V} (e: α = β) {i j: Index n}
  (f: Word A (rank i) (rank j)) (x: cells (pullbackDiagram U F) j):
  f_equal (FD.(phom) (V.(fhom) f))
      (phomEq FD (f_equal (fun γ: NatTrans U V => γ.(ncomp) j) e) x)
    • pullbackNaturality F U V β f x =
  pullbackNaturality F U V α f x
    • phomEq FD (f_equal (fun γ: NatTrans U V => γ.(ncomp) i) e)
      (FD.(phom) (U.(fhom) f) x).
Proof. destruct e. now apply eq_trans_refl_l. Defined.

Lemma pullbackNaturalityEqComponents (U V: Functor (PrefixCategory A n) C)
  {α β: NatTrans U V} (e: α = β) {i j: Index n}
  (f: Word A (rank i) (rank j)) (x: cells (pullbackDiagram U F) j)
  (ti: α.(ncomp) i = β.(ncomp) i) (tj: α.(ncomp) j = β.(ncomp) j):
  f_equal (FD.(phom) (V.(fhom) f)) (phomEq FD tj x)
    • pullbackNaturality F U V β f x =
  pullbackNaturality F U V α f x
    • phomEq FD ti (FD.(phom) (U.(fhom) f) x).
Proof.
  replace ti with (f_equal (fun γ: NatTrans U V => γ.(ncomp) i) e)
    by now apply (C.(CHom) (U.(fobj) i) (V.(fobj) i)).(UIP).
  replace tj with (f_equal (fun γ: NatTrans U V => γ.(ncomp) j) e)
    by now apply (C.(CHom) (U.(fobj) j) (V.(fobj) j)).(UIP).
  now apply pullbackNaturalityEq.
Defined.

Lemma pullbackNaturalityVertical
  (U V W: Functor (PrefixCategory A n) C) (α: NatTrans U V) (β: NatTrans V W)
  {i j: Index n} (f: Word A (rank i) (rank j))
  (x: cells (pullbackDiagram U F) j):
  f_equal (FD.(phom) (W.(fhom) f)) (FD.(pcomp) (α.(ncomp) j) (β.(ncomp) j) x)
    • pullbackNaturality F U W (compNatTrans α β) f x =
  pullbackNaturality F V W β f (FD.(phom) (α.(ncomp) j) x)
    • (f_equal (FD.(phom) (β.(ncomp) i)) (pullbackNaturality F U V α f x)
      • FD.(pcomp) (α.(ncomp) i) (β.(ncomp) i) (FD.(phom) (U.(fhom) f) x)).
Proof.
  symmetry. unfold pullbackNaturality.
  refine (transCongR (pcompWhiskerR FD (pathAssoc _ _ F.(pfStr))
    (α.(ncomp) j) (v := β.(ncomp) j) (w := W.(fhom) f)
    (v' := V.(fhom) f) (w' := β.(ncomp) i) (eq_sym (β.(nnat) f)) x) _ • _).
  refine (transCongL _ (transCongR (pcompWhiskerL FD (eq_sym (α.(nnat) f))
    (β.(ncomp) i) x (FD.(pcomp) (α.(ncomp) j) (V.(fhom) f) x)
    (FD.(pcomp) (U.(fhom) f) (α.(ncomp) i) x)) _) • _).
  refine (conjugatePaste _ _ _ _ _ _ _ _
    (psfAssocPt FD (pathAssoc _ _ F.(pfStr))
      (U.(fhom) f) (α.(ncomp) i) (β.(ncomp) i) x) • _).
  refine (_ • eqTransAssoc
    (f_equal (FD.(phom) (W.(fhom) f)) (FD.(pcomp) (α.(ncomp) j) (β.(ncomp) j) x))
    (FD.(pcomp) (α.(ncomp) j ⨟ β.(ncomp) j) (W.(fhom) f) x) _).
  apply transCongL. apply transCongR. unfold phomEq.
  now exact (fEqualUIP (@UIP (C.(CHom) (U.(fobj) j) (W.(fobj) i)))
    (fun w => FD.(phom) w x) _ _ _ _ eq_refl eq_refl).
Defined.

End Coherence.

(** Composing indexing functors preserves matching values and overlap paths. *)

Lemma pullbackArrowPath {B: Category} {C: Category}
  (U: Functor B C) (F: PathDiagramFamily C)
  {i j} {f g: B.(CHom) i j} (e: f = g) (x: F.(pfObj) (U.(fobj) i)):
  phomEq (pathData _ _ (pullbackDiagram U F).(pfStr)) e x =
    phomEq (pathData _ _ F.(pfStr)) (f_equal U.(fhom) e) x.
Proof. now destruct e. Defined.

Section Composition.
Context {B: Category} {C: Category} {D: Category} (U: Functor B C) (V: Functor C D)
  (F: PathDiagramFamily D).
Local Abbreviation L := (pullbackDiagram U (pullbackDiagram V F)).
Local Abbreviation R := (pullbackDiagram (compFunctor U V) F).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation LD := (pathData _ _ L.(pfStr)).
Local Abbreviation RD := (pathData _ _ R.(pfStr)).

Lemma pullbackCompositeId i x: pidPt LD i x = pidPt RD i x.
Proof.
  refine (pullbackIdPoint (pullbackDiagram V F) U i x • _).
  refine (transCongR (pullbackArrowPath V F (U.(fid) i) x) _ • _).
  refine (transCongL _ (pullbackIdPoint F V (U.(fobj) i) x) • _).
  refine (_ • eq_sym (pullbackIdPoint F (compFunctor U V) i x)).
  unfold phomEq. cbn [compFunctor fid].
  now rewrite eq_trans_map_distr, eqTransAssoc.
Defined.

Lemma pullbackCompositeComp {i j k}
  (f: B.(CHom) i j) (g: B.(CHom) j k) x:
  LD.(pcomp) f g x = RD.(pcomp) f g x.
Proof.
  refine (pullbackCompPoint (pullbackDiagram V F) U f g x • _).
  refine (transCongR (pullbackCompPoint F V (U.(fhom) f) (U.(fhom) g) x) _ • _).
  refine (transCongL _ (pullbackArrowPath V F (eq_sym (U.(fcomp) f g)) x) • _).
  refine (_ • eq_sym (pullbackCompPoint F (compFunctor U V) f g x)).
  rewrite eqTransAssoc. apply transCongL.
  unfold phomEq.
  refine (eq_sym (eq_trans_map_distr
    (fun w: D.(CHom) (V.(fobj) (U.(fobj) i)) (V.(fobj) (U.(fobj) k)) => FD.(phom) w x)
    (eq_sym (V.(fcomp) (U.(fhom) f) (U.(fhom) g)))
    (f_equal V.(fhom) (eq_sym (U.(fcomp) f g)))) • _).
  apply f_equal.
  now apply (D.(CHom) _ _).(UIP).
Defined.
End Composition.

Section Matching.
Context {A: HSet} {p: nat} {C: Category} {D: Category}
  (U: Functor (PrefixCategory A p) C) (V: Functor C D) (F: PathDiagramFamily D).
Local Abbreviation L := (pullbackDiagram U (pullbackDiagram V F)).
Local Abbreviation R := (pullbackDiagram (compFunctor U V) F).

(** Only the proofs of the matching equations change. *)
Definition matchingComposite (b: MatchingObject L): MatchingObject R.
Proof.
  exists b.1. exists b.2.1. split.
  - intros i g.
    exact (matchingUnit b i g • transCongR
      (pullbackCompositeId U V F i (matchingValue b i g))
      (eq_sym (f_equal (matchingValue b i) (wcompIdr g)))).
  - intros i j k f g h.
    exact (matchingComp b f g h • transCongR
      (pullbackCompositeComp U V F g f (matchingValue b k h))
      (matchingPath b (wcomp g f) h)).
Defined.

Definition matchingUncompose (b: MatchingObject R): MatchingObject L.
Proof.
  exists b.1. exists b.2.1. split.
  - intros i g.
    exact (matchingUnit b i g • transCongR
      (eq_sym (pullbackCompositeId U V F i (matchingValue b i g)))
      (eq_sym (f_equal (matchingValue b i) (wcompIdr g)))).
  - intros i j k f g h.
    exact (matchingComp b f g h • transCongR
      (eq_sym (pullbackCompositeComp U V F g f (matchingValue b k h)))
      (matchingPath b (wcomp g f) h)).
Defined.

Lemma matchingUncomposeComposite (b: MatchingObject L):
  matchingUncompose (matchingComposite b) = b.
Proof.
  refine (matchingHomotopy L (b := matchingUncompose (matchingComposite b))
    (c := b) (fun i f => eq_refl) _).
  intros i j f g. now exact (eq_trans_refl_l (matchingPath b f g)).
Defined.

Lemma matchingCompositeUncompose (b: MatchingObject R):
  matchingComposite (matchingUncompose b) = b.
Proof.
  refine (matchingHomotopy R (b := matchingComposite (matchingUncompose b))
    (c := b) (fun i f => eq_refl) _).
  intros i j f g. now exact (eq_trans_refl_l (matchingPath b f g)).
Defined.

Definition matchingCompEquiv: Equiv (MatchingObject L) (MatchingObject R) :=
  qinvEquiv matchingComposite matchingUncompose
    matchingUncomposeComposite matchingCompositeUncompose.

Lemma matchingCompMapPath {b c: MatchingObject L} (e: b = c) i f:
  f_equal (fun z => matchingValue z i f) (f_equal matchingCompEquiv e) =
    f_equal (fun z => matchingValue z i f) e.
Proof. now destruct e. Defined.

End Matching.
Section Boundary.
Context {A: HSet} {p: nat} {C: Category} {D: Category}
  (U: Functor (PrefixCategory A (S p)) C) (V: Functor C D) (F: PathDiagramFamily D).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) U).
Local Abbreviation L := (pullbackDiagram U (pullbackDiagram V F)).
Local Abbreviation R := (pullbackDiagram (compFunctor U V) F).
Local Abbreviation R0 := (pullbackDiagram (compFunctor U0 V) F).

End Boundary.

(** Matching objects vary coherently with their indexing functor. *)

Local Lemma verticalConeAlgebra {T: Type} {a b c z p q d: T}
  (r: a = b) (s: b = c) (t: c = z) (u: a = p) (v: p = q)
  (w: q = c) (h: q = d) (k: d = z)
  (e: r • s = u • (v • w)) (f: h • k = w • t):
  r • (s • t) = (u • (v • h)) • k.
Proof.
  rewrite <- (eqTransAssoc r s t), e, (eqTransAssoc u (v • w) t), (eqTransAssoc v w t).
  rewrite <- f, <- (eqTransAssoc v h k), <- (eqTransAssoc u (v • h) k). now reflexivity.
Defined.

Section Matching.
Context {A: HSet} (p: nat) (C: Category) (F: PathDiagramFamily C).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation FC := (functorCategory (PrefixCategory A p) C).

Definition matchingAction (U V: Functor (PrefixCategory A p) C) (α: NatTrans U V):
  MatchingObject (pullbackDiagram U F) -> MatchingObject (pullbackDiagram V F) :=
  mapMatching (pullbackMap F U V α).

Lemma matchingActionPath (U V: Functor (PrefixCategory A p) C) (α: NatTrans U V)
  (b: MatchingObject (pullbackDiagram U F)) {i j}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) p):
  matchingPath (matchingAction U V α b) f g =
  pullbackNaturality F U V α f (matchingValue b j g)
    • f_equal (FD.(phom) (α.(ncomp) i)) (matchingPath b f g).
Proof.
  change (eq_sym (eq_sym (pullbackNaturality F U V α f (matchingValue b j g)))
      • f_equal (FD.(phom) (α.(ncomp) i)) (matchingPath b f g) =
    pullbackNaturality F U V α f (matchingValue b j g)
      • f_equal (FD.(phom) (α.(ncomp) i)) (matchingPath b f g)).
  now rewrite eq_sym_involutive.
Defined.

Lemma matchingIdentitySquares (U: Functor (PrefixCategory A p) C)
  (b: MatchingObject (pullbackDiagram U F)):
  ComparisonSquares (pullbackDiagram U F)
    (b := matchingAction U U (idNatTrans U) b) (c := b)
    (fun i g => pidPt FD (U.(fobj) i) (matchingValue b i g)).
Proof.
  intros i j f g. rewrite matchingActionPath.
  pose proof (homotopyNat (FD.(phom) (C.(cid) (U.(fobj) i))) (fun x => x)
    (pidPt FD (U.(fobj) i)) (matchingPath b f g)) as H.
  rewrite f_equal_id in H.
  refine (transCongR (pullbackNaturalityIdentity F U f (matchingValue b j g))
    (matchingPath b f g) • _).
  refine (eqTransAssoc _ _ _ • transCongL _ (eq_sym H) • _).
  now symmetry; apply eqTransAssoc.
Defined.

Definition matchingIdentity (U: Functor (PrefixCategory A p) C)
  (b: MatchingObject (pullbackDiagram U F)): matchingAction U U (idNatTrans U) b = b :=
  matchingHomotopy (pullbackDiagram U F)
    (b := matchingAction U U (idNatTrans U) b) (c := b)
    (fun i g => pidPt FD (U.(fobj) i) (matchingValue b i g)) (matchingIdentitySquares U b).

Lemma matchingIdentityValue (U: Functor (PrefixCategory A p) C)
  (b: MatchingObject (pullbackDiagram U F)) i g:
  f_equal (fun z => matchingValue z i g) (matchingIdentity U b) =
  pidPt FD (U.(fobj) i) (matchingValue b i g).
Proof.
  now exact (matchingHomotopyValue (pullbackDiagram U F)
    (b := matchingAction U U (idNatTrans U) b) (c := b)
    (fun i g => pidPt FD (U.(fobj) i) (matchingValue b i g))
    (matchingIdentitySquares U b) i g).
Defined.

Lemma matchingCompositionSquares (U V W: Functor (PrefixCategory A p) C)
  (α: NatTrans U V) (β: NatTrans V W) (b: MatchingObject (pullbackDiagram U F)):
  ComparisonSquares (pullbackDiagram W F)
    (b := matchingAction V W β (matchingAction U V α b))
    (c := matchingAction U W (compNatTrans α β) b)
    (fun i g => FD.(pcomp) (α.(ncomp) i) (β.(ncomp) i) (matchingValue b i g)).
Proof.
  intros i j f g. rewrite 3 matchingActionPath, eq_trans_map_distr.
  eapply verticalConeAlgebra.
  - now exact (pullbackNaturalityVertical F U V W α β f (matchingValue b j g)).
  - now exact (pcompNatPt FD (α.(ncomp) i) (β.(ncomp) i) (matchingPath b f g)).
Defined.

Definition matchingComposition (U V W: Functor (PrefixCategory A p) C)
  (α: NatTrans U V) (β: NatTrans V W) (b: MatchingObject (pullbackDiagram U F)):
  matchingAction V W β (matchingAction U V α b) = matchingAction U W (compNatTrans α β) b :=
  matchingHomotopy (pullbackDiagram W F)
    (b := matchingAction V W β (matchingAction U V α b))
    (c := matchingAction U W (compNatTrans α β) b)
    (fun i g => FD.(pcomp) (α.(ncomp) i) (β.(ncomp) i) (matchingValue b i g))
    (matchingCompositionSquares U V W α β b).

Lemma matchingCompositionValue (U V W: Functor (PrefixCategory A p) C)
  (α: NatTrans U V) (β: NatTrans V W) (b: MatchingObject (pullbackDiagram U F)) i g:
  f_equal (fun z => matchingValue z i g) (matchingComposition U V W α β b) =
  FD.(pcomp) (α.(ncomp) i) (β.(ncomp) i) (matchingValue b i g).
Proof.
  now exact (matchingHomotopyValue (pullbackDiagram W F)
    (b := matchingAction V W β (matchingAction U V α b))
    (c := matchingAction U W (compNatTrans α β) b)
    (fun i g => FD.(pcomp) (α.(ncomp) i) (β.(ncomp) i) (matchingValue b i g))
    (matchingCompositionSquares U V W α β b) i g).
Defined.

Lemma matchingActionMapPath (U V: Functor (PrefixCategory A p) C) (α: NatTrans U V)
  {b c: MatchingObject (pullbackDiagram U F)} (e: b = c) i g:
  f_equal (fun z => matchingValue z i g) (f_equal (matchingAction U V α) e) =
  f_equal (FD.(phom) (α.(ncomp) i)) (f_equal (fun z => matchingValue z i g) e).
Proof. now destruct e. Defined.

Lemma matchingActionArrowPath (U V: Functor (PrefixCategory A p) C)
  {α β: NatTrans U V} (e: α = β) (b: MatchingObject (pullbackDiagram U F)) i g
  (t: α.(ncomp) i = β.(ncomp) i):
  f_equal (fun z => matchingValue z i g) (f_equal (fun α => matchingAction U V α b) e) =
  phomEq FD t (matchingValue b i g).
Proof.
  destruct e. replace t with (@eq_refl _ (α.(ncomp) i))
    by now apply (C.(CHom) _ _).(UIP).
  now reflexivity.
Defined.

Definition matchingDiagramData: PathDiagramData FC
  (fun U => MatchingObject (pullbackDiagram U F)) :=
  @Build_PathDiagramData FC (fun U => MatchingObject (pullbackDiagram U F))
    (fun U V α => matchingAction U V α)
    (fun U => functional_extensionality_dep_good _ _ (matchingIdentity U))
    (fun U V W α β b => matchingComposition U V W α β b).

Lemma matchingPidPoint U b: pidPt matchingDiagramData U b = matchingIdentity U b.
Proof. now exact (f_equal__functional_extensionality_dep_good (matchingIdentity U) b). Defined.

Lemma matchingDiagramArrowValue (U V: Functor (PrefixCategory A p) C)
  {α β: NatTrans U V} (e: α = β) (b: MatchingObject (pullbackDiagram U F)) i g
  (t: α.(ncomp) i = β.(ncomp) i):
  f_equal (fun z => matchingValue z i g) (phomEq matchingDiagramData e b) =
  phomEq FD t (matchingValue b i g).
Proof. now exact (matchingActionArrowPath U V e b i g t). Defined.

Lemma matchingDiagramUnitL: PathDiagramUnitL _ _ matchingDiagramData.
Proof.
  apply (pathDiagramUnitLOfPt matchingDiagramData). intros U V α b.
  change (matchingComposition U U V (idNatTrans U) α b =
    f_equal (matchingAction U V α) (pidPt matchingDiagramData U b)
      • eq_sym (phomEq matchingDiagramData (FC.(cidl) α) b)).
  rewrite matchingPidPoint. apply (matchingPathExt (pullbackDiagram V F)); intros i g.
  rewrite eq_trans_map_distr, fEqualSym, matchingActionMapPath,
    matchingIdentityValue, matchingCompositionValue.
  rewrite (matchingDiagramArrowValue U V (FC.(cidl) α) b i g (C.(cidl) (α.(ncomp) i))).
  now exact (pcompUnitLPt FD (pathUnitL _ _ F.(pfStr))
    (U.(fobj) i) (V.(fobj) i) (α.(ncomp) i) (C.(cidl) (α.(ncomp) i)) (matchingValue b i g)).
Defined.

Lemma matchingDiagramUnitR: PathDiagramUnitR _ _ matchingDiagramData.
Proof.
  apply (pathDiagramUnitROfPt matchingDiagramData). intros U V α b.
  change (matchingComposition U V V α (idNatTrans V) b =
    pidPt matchingDiagramData V (matchingAction U V α b)
      • eq_sym (phomEq matchingDiagramData (FC.(cidr) α) b)).
  rewrite matchingPidPoint. apply (matchingPathExt (pullbackDiagram V F)); intros i g.
  rewrite eq_trans_map_distr, fEqualSym, matchingIdentityValue, matchingCompositionValue.
  rewrite (matchingDiagramArrowValue U V (FC.(cidr) α) b i g (C.(cidr) (α.(ncomp) i))).
  now exact (pcompUnitRPt FD (pathUnitR _ _ F.(pfStr))
    (U.(fobj) i) (V.(fobj) i) (α.(ncomp) i) (C.(cidr) (α.(ncomp) i)) (matchingValue b i g)).
Defined.

Lemma matchingDiagramAssoc: PathDiagramAssoc _ _ matchingDiagramData.
Proof.
  apply (pathDiagramAssocOfPt matchingDiagramData). intros U V W Z α β γ b.
  change (f_equal (matchingAction W Z γ) (matchingComposition U V W α β b)
    • (matchingComposition U W Z (compNatTrans α β) γ b
      • phomEq matchingDiagramData (FC.(cassoc) α β γ) b) =
    matchingComposition V W Z β γ (matchingAction U V α b)
      • matchingComposition U V Z α (compNatTrans β γ) b).
  apply (matchingPathExt (pullbackDiagram Z F)); intros i g.
  rewrite 3 eq_trans_map_distr, matchingActionMapPath, 4 matchingCompositionValue.
  refine (transCongL _ (transCongL _
    (matchingDiagramArrowValue U Z (FC.(cassoc) α β γ) b i g
      (C.(cassoc) (α.(ncomp) i) (β.(ncomp) i) (γ.(ncomp) i)))) • _).
  now exact (pcompAssocPt FD (pathAssoc _ _ F.(pfStr))
    (U.(fobj) i) (V.(fobj) i) (W.(fobj) i) (Z.(fobj) i)
    (α.(ncomp) i) (β.(ncomp) i) (γ.(ncomp) i)
    (C.(cassoc) (α.(ncomp) i) (β.(ncomp) i) (γ.(ncomp) i)) (matchingValue b i g)).
Defined.

Definition matchingPullbackDiagram: PathDiagramFamily FC :=
  @Build_PathDiagramFamily FC (fun U => MatchingObject (pullbackDiagram U F))
    (@Build_PathDiagram FC (fun U => MatchingObject (pullbackDiagram U F))
      matchingDiagramData matchingDiagramUnitL matchingDiagramUnitR matchingDiagramAssoc).

End Matching.

(** Reindexing coherent diagram maps and retained matching boundaries. *)

Lemma mapArrowPath {A: HSet} {n} {X Y: Diagram A n} (F: DiagramMap X Y)
  {i j: Index n} {f g: Word A (rank i) (rank j)} (e: f = g) (x: cells X j):
  f_equal (F.(mapCell) i) (phomEq (diagramData X) (a := j) (b := i) e x)
    • F.(mapNatural) (i := i) (j := j) g x =
  F.(mapNatural) (i := i) (j := j) f x
    • phomEq (diagramData Y) (a := j) (b := i) e (F.(mapCell) j x).
Proof. destruct e. now exact (eq_trans_refl_l _). Defined.

Section Reindex.
Context {A: HSet} {p q} {X Y: Diagram A q}
  (U: Functor (PrefixCategory A p) (PrefixCategory A q)) (F: DiagramMap X Y).

Lemma reindexMapUnit (i: Index p) (x: cells (pullbackDiagram U X) i):
  f_equal (F.(mapCell) (U.(fobj) i)) (restrictId (pullbackDiagram U X) i x) =
  F.(mapNatural) (i := U.(fobj) i) (j := U.(fobj) i) (U.(fhom) (wid (rank i))) x
    • restrictId (pullbackDiagram U Y) i (F.(mapCell) (U.(fobj) i) x).
Proof.
  rewrite (pullbackRestrictId X U i x),
    (pullbackRestrictId Y U i (F.(mapCell) (U.(fobj) i) x)), mapTrans.
  refine (transCongL _ (F.(mapUnit) (U.(fobj) i) x) • _).
  rewrite <- eqTransAssoc.
  refine (transCongR (mapArrowPath F (i := U.(fobj) i) (j := U.(fobj) i)
    (U.(fid) i) x) _ • _).
  now apply eqTransAssoc.
Defined.

Lemma reindexMapComp {i j k: Index p}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: cells (pullbackDiagram U X) k):
  f_equal (F.(mapCell) (U.(fobj) i)) (restrictComp (pullbackDiagram U X) f g x)
    • F.(mapNatural) (i := U.(fobj) i) (j := U.(fobj) k) (U.(fhom) (wcomp g f)) x =
  F.(mapNatural) (i := U.(fobj) i) (j := U.(fobj) j) (U.(fhom) f)
      (restrict (pullbackDiagram U X) g x)
    • (f_equal (restrict (pullbackDiagram U Y) f)
        (F.(mapNatural) (i := U.(fobj) j) (j := U.(fobj) k) (U.(fhom) g) x)
      • restrictComp (pullbackDiagram U Y) f g (F.(mapCell) (U.(fobj) k) x)).
Proof.
  rewrite (pullbackRestrictComp X U f g x),
    (pullbackRestrictComp Y U f g (F.(mapCell) (U.(fobj) k) x)), mapTrans, eqTransAssoc.
  refine (transCongL _ (mapArrowPath F (i := U.(fobj) i) (j := U.(fobj) k)
    (eq_sym (U.(fcomp) g f)) x) • _).
  rewrite <- eqTransAssoc.
  refine (transCongR (F.(mapComp) (i := U.(fobj) i) (j := U.(fobj) j) (k := U.(fobj) k)
    (U.(fhom) f) (U.(fhom) g) x) _ • _).
  now rewrite 2 eqTransAssoc.
Defined.

Definition reindexMap: DiagramMap (pullbackDiagram U X) (pullbackDiagram U Y) :=
  @Build_DiagramMap A p (pullbackDiagram U X) (pullbackDiagram U Y)
    (fun i => F.(mapCell) (U.(fobj) i))
    (fun i j f x => F.(mapNatural) (i := U.(fobj) i) (j := U.(fobj) j) (U.(fhom) f) x)
    reindexMapUnit (fun i j k f g x => reindexMapComp f g x).

End Reindex.

Definition shiftMap {A: HSet} {n} {X Y: Diagram A (S n)} (F: DiagramMap X Y):
  DiagramMap (shiftDiagram X) (shiftDiagram Y) := reindexMap (shiftFunctor A n) F.

Lemma keepMapPaths {A: HSet} {n} {X Y: Diagram A (S n)} (F: DiagramMap X Y)
  (b: MatchingObject X) {i j: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  matchingPath (mapMatching (shiftMap F) (keepMatching X b)) f g =
    matchingPath (keepMatching Y (mapMatching F b)) f g.
Proof.
  rewrite mapMatchingPath, 2 keepMatchingPath, mapMatchingPath.
  change (eq_sym (F.(mapNatural) (keepWord f) (matchingValue b (raiseIndex j) (keepToTop g)))
      • f_equal (F.(mapCell) (raiseIndex i))
        (matchingPath b (keepWord f) (keepToTop g)
          • f_equal (matchingValue b (raiseIndex i)) (keepToTopComp f g)) =
    (eq_sym (F.(mapNatural) (keepWord f) (matchingValue b (raiseIndex j) (keepToTop g)))
      • f_equal (F.(mapCell) (raiseIndex i)) (matchingPath b (keepWord f) (keepToTop g)))
      • f_equal (fun w => F.(mapCell) (raiseIndex i) (matchingValue b (raiseIndex i) w))
        (keepToTopComp f g)).
  rewrite mapTrans, f_equal_compose. now apply eq_sym, eqTransAssoc.
Defined.

Definition keepMap {A: HSet} {n} {X Y: Diagram A (S n)} (F: DiagramMap X Y)
  (b: MatchingObject X):
  mapMatching (shiftMap F) (keepMatching X b) = keepMatching Y (mapMatching F b) :=
  matchingHomotopy (shiftDiagram Y)
    (b := mapMatching (shiftMap F) (keepMatching X b))
    (c := keepMatching Y (mapMatching F b)) (fun i g => eq_refl)
    (fun i j f g => eq_trans_refl_l _ • eq_sym (keepMapPaths F b f g)).

Lemma keepMapValue {A: HSet} {n} {X Y: Diagram A (S n)} (F: DiagramMap X Y)
  (b: MatchingObject X) i g:
  f_equal (fun z => matchingValue z i g) (keepMap F b) = eq_refl.
Proof.
  now exact (matchingHomotopyValue (shiftDiagram Y)
    (b := mapMatching (shiftMap F) (keepMatching X b))
    (c := keepMatching Y (mapMatching F b)) (fun i g => eq_refl)
    (fun i j f g => eq_trans_refl_l _ • eq_sym (keepMapPaths F b f g)) i g).
Defined.

(** Matching-law repacks for the truncation of a pulled-back diagram. *)
Set Keyed Unification.

Section Repack.
Context {A: HSet} {p: nat} {C: Category} (F: PathDiagramFamily C)
  (U: Functor (PrefixCategory A (S p)) C).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) U).
Local Abbreviation S := (pullbackDiagram U0 F).
Local Abbreviation T := (truncateDiagram (pullbackDiagram U F)).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Definition O (i: Index p): HGpd := F.(pfObj) (U.(fobj) (Some i)).
Local Definition h (i j: Index p) (f: Word A (rank j) (rank i)) (x: O i): O j :=
  FD.(phom) (U.(fhom) (a := Some i) (b := Some j) f) x.

Lemma truncationId (i: Index p) (x: O i):
  @eq (h i i (wid (rank i)) x = x) (restrictId S i x) (restrictId T i x).
Proof.
  refine (pullbackIdPoint F U0 i x • _).
  now exact (eq_sym (pullbackIdPoint F U (Some i) x)).
Defined.

Lemma truncationComp (i j k: Index p) (f: Word A (rank j) (rank i))
  (g: Word A (rank k) (rank j)) (x: O i):
  @eq (h j k g (h i j f x) = h i k (wcomp f g) x)
    (restrictComp S g f x) (restrictComp T g f x).
Proof.
  refine (pullbackCompPoint F U0 f g x • _).
  now exact (eq_sym (pullbackCompPoint F U
    (i := Some i) (j := Some j) (k := Some k) f g x)).
Defined.

Definition pullbackMatchingTruncate (b: MatchingObject S): MatchingObject T :=
  @matchingLawRepack A p O h (diagramData S).(pid) (diagramData T).(pid)
    (fun i j k f g x => (diagramData S).(pcomp) (a := i) (b := j) (c := k) f g x)
    (fun i j k f g x => (diagramData T).(pcomp) (a := i) (b := j) (c := k) f g x)
    (pathUnitL _ _ S.(pfStr)) (pathUnitR _ _ S.(pfStr)) (pathAssoc _ _ S.(pfStr))
    (pathUnitL _ _ T.(pfStr)) (pathUnitR _ _ T.(pfStr)) (pathAssoc _ _ T.(pfStr))
    truncationId truncationComp b.

Definition pullbackMatchingUntruncate (b: MatchingObject T): MatchingObject S :=
  @matchingLawRepack A p O h (diagramData T).(pid) (diagramData S).(pid)
    (fun i j k f g x => (diagramData T).(pcomp) (a := i) (b := j) (c := k) f g x)
    (fun i j k f g x => (diagramData S).(pcomp) (a := i) (b := j) (c := k) f g x)
    (pathUnitL _ _ T.(pfStr)) (pathUnitR _ _ T.(pfStr)) (pathAssoc _ _ T.(pfStr))
    (pathUnitL _ _ S.(pfStr)) (pathUnitR _ _ S.(pfStr)) (pathAssoc _ _ S.(pfStr))
    (fun i x => eq_sym (truncationId i x))
    (fun i j k f g x => eq_sym (truncationComp i j k f g x)) b.

End Repack.

(** Truncating the indexing data of a pullback map preserves the chosen
    matching comparisons. *)

Section Maps.
Context {A: HSet} {p: nat} {C: Category} (F: PathDiagramFamily C)
  (U V: Functor (PrefixCategory A (S p)) C) (a: NatTrans U V).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) U).
Local Abbreviation V0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) V).

Definition truncateIndexTransformation: NatTrans U0 V0 := {|
  ncomp i := a.(ncomp) (Some i);
  nnat i j f := a.(nnat) (a := Some i) (b := Some j) f;
|}.

Local Definition matchingMapTruncateSquares (b: MatchingObject (pullbackDiagram U0 F)):
  ComparisonSquares (pullbackDiagram V0 F)
    (b := mapMatching (pullbackMap F U0 V0 truncateIndexTransformation) b)
    (c := pullbackMatchingUntruncate F V
      (mapMatching (truncateMap (pullbackMap F U V a)) (pullbackMatchingTruncate F U b)))
    (fun i f => eq_refl).
Proof.
  intros i j f g.
  now exact (eq_trans_refl_l
    (matchingPath (mapMatching (pullbackMap F U0 V0 truncateIndexTransformation) b) f g)).
Defined.

Definition matchingMapTruncate (b: MatchingObject (pullbackDiagram U0 F)):
  mapMatching (pullbackMap F U0 V0 truncateIndexTransformation) b =
    pullbackMatchingUntruncate F V
      (mapMatching (truncateMap (pullbackMap F U V a)) (pullbackMatchingTruncate F U b)) :=
  matchingHomotopy (pullbackDiagram V0 F)
    (b := mapMatching (pullbackMap F U0 V0 truncateIndexTransformation) b)
    (c := pullbackMatchingUntruncate F V
      (mapMatching (truncateMap (pullbackMap F U V a)) (pullbackMatchingTruncate F U b)))
    (fun i f => eq_refl) (matchingMapTruncateSquares b).

Lemma matchingMapTruncateValue (b: MatchingObject (pullbackDiagram U0 F)) i f:
  f_equal (fun z => matchingValue z i f) (matchingMapTruncate b) = eq_refl.
Proof.
  now exact (matchingHomotopyValue (pullbackDiagram V0 F)
    (b := mapMatching (pullbackMap F U0 V0 truncateIndexTransformation) b)
    (c := pullbackMatchingUntruncate F V
      (mapMatching (truncateMap (pullbackMap F U V a)) (pullbackMatchingTruncate F U b)))
    (fun i f => eq_refl) (matchingMapTruncateSquares b) i f).
Defined.
End Maps.

(** Truncating the indexing data of a matching composite preserves the
    chosen matching comparisons. *)

Section Composite.
Context {A: HSet} {p: nat} {C: Category}
  (V: Functor (PrefixCategory A (S (S p))) C) (F: PathDiagramFamily C).
Local Abbreviation V0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) V).
Local Abbreviation U := (shiftFunctor A p).
Local Abbreviation UF := (shiftFunctor A (S p)).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A))
    (PrefixCategory A (S (S p))) (fun n => n) UF).
Local Abbreviation L := (pullbackDiagram U (pullbackDiagram V0 F)).
Local Abbreviation R := (pullbackDiagram (compFunctor U V0) F).

Local Abbreviation L2 := (pullbackDiagram U0 (pullbackDiagram V F)).
Local Abbreviation R2 := (pullbackDiagram (compFunctor U0 V) F).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).

Lemma flatTruncateId i (x: cells R i): restrictId R i x = restrictId R2 i x.
Proof.
  refine (pullbackIdPoint F (compFunctor U V0) i x • _).
  refine (_ • eq_sym (pullbackIdPoint F (compFunctor U0 V) i x)).
  apply transCongR. unfold phomEq. apply f_equal.
  now apply (C.(CHom) _ _).(UIP).
Defined.

Lemma flatTruncateComp {i j k} (f: Word A (rank i) (rank j))
  (g: Word A (rank j) (rank k)) (x: cells R k):
  restrictComp R f g x = restrictComp R2 f g x.
Proof.
  refine (pullbackCompPoint F (compFunctor U V0) g f x • _).
  refine (_ • eq_sym (pullbackCompPoint F (compFunctor U0 V) g f x)).
  apply transCongL. unfold phomEq. apply f_equal.
  now apply (C.(CHom) _ _).(UIP).
Defined.

Local Definition commonObject (i: Index p): HGpd :=
  F.(pfObj) (V.(fobj) (Some (raiseIndex i))).
Local Definition commonArrow {i j: Index p} (f: Word A (rank i) (rank j)) :=
  V.(fhom) (a := Some (raiseIndex j)) (b := Some (raiseIndex i))
    (keepWord (i := i) (j := j) f).

Lemma inputTruncateId (i: Index p) (x: commonObject i):
  @eq (FD.(phom) (commonArrow (wid (rank i))) x = x)
    (restrictId L i x) (restrictId L2 i x).
Proof.
  refine (pullbackCompositeId U V0 F i x • _).
  refine (_ • eq_sym (pullbackCompositeId U0 V F i x)).
  now exact (flatTruncateId i x).
Defined.

Lemma inputTruncateComp {i j k: Index p}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: commonObject k):
  @eq (FD.(phom) (commonArrow f) (FD.(phom) (commonArrow g) x)
       = FD.(phom) (commonArrow (wcomp g f)) x)
    (restrictComp L f g x) (restrictComp L2 f g x).
Proof.
  refine (pullbackCompositeComp U V0 F g f x • _).
  refine (_ • eq_sym (pullbackCompositeComp U0 V F g f x)).
  now exact (flatTruncateComp f g x).
Defined.

Local Definition commonAction (i j: Index p)
  (f: Word A (rank j) (rank i)) (x: commonObject i): commonObject j :=
  FD.(phom) (commonArrow f) x.

Definition matchingTruncateInput (b: MatchingObject L): MatchingObject L2 :=
  @matchingLawRepack A p commonObject commonAction
    (diagramData L).(pid) (diagramData L2).(pid)
    (fun i j k f g x => (diagramData L).(pcomp) (a := i) (b := j) (c := k) f g x)
    (fun i j k f g x => (diagramData L2).(pcomp) (a := i) (b := j) (c := k) f g x)
    (pathUnitL _ _ L.(pfStr)) (pathUnitR _ _ L.(pfStr)) (pathAssoc _ _ L.(pfStr))
    (pathUnitL _ _ L2.(pfStr)) (pathUnitR _ _ L2.(pfStr)) (pathAssoc _ _ L2.(pfStr))
    inputTruncateId (fun i j k f g x => inputTruncateComp g f x) b.

Definition matchingTruncateOutput (b: MatchingObject R2): MatchingObject R :=
  @matchingLawRepack A p commonObject commonAction
    (diagramData R2).(pid) (diagramData R).(pid)
    (fun i j k f g x => (diagramData R2).(pcomp) (a := i) (b := j) (c := k) f g x)
    (fun i j k f g x => (diagramData R).(pcomp) (a := i) (b := j) (c := k) f g x)
    (pathUnitL _ _ R2.(pfStr)) (pathUnitR _ _ R2.(pfStr)) (pathAssoc _ _ R2.(pfStr))
    (pathUnitL _ _ R.(pfStr)) (pathUnitR _ _ R.(pfStr)) (pathAssoc _ _ R.(pfStr))
    (fun i x => eq_sym (flatTruncateId i x))
    (fun i j k f g x => eq_sym (flatTruncateComp g f x)) b.

Definition matchingCompositeTruncate (b: MatchingObject L):
  matchingCompEquiv U V0 F b =
    matchingTruncateOutput (matchingCompEquiv U0 V F (matchingTruncateInput b)).
Proof.
  refine (matchingHomotopy R
    (b := matchingCompEquiv U V0 F b)
    (c := matchingTruncateOutput (matchingCompEquiv U0 V F (matchingTruncateInput b)))
    (fun i f => eq_refl) _).
  intros i j f g. now exact (eq_trans_refl_l (matchingPath b f g)).
Defined.

Lemma matchingCompositeTruncateValue (b: MatchingObject L) i f:
  @eq (matchingValue b i f = matchingValue b i f)
    (f_equal (fun z => matchingValue z i f) (matchingCompositeTruncate b)) eq_refl.
Proof.
  now exact (matchingHomotopyValue R
    (b := matchingCompEquiv U V0 F b)
    (c := matchingTruncateOutput (matchingCompEquiv U0 V F (matchingTruncateInput b)))
    (fun i f => eq_refl) (fun i j f g => eq_trans_refl_l (matchingPath b f g)) i f).
Defined.

End Composite.

(** Boundary computations for the explicit matching-law repacks. *)

Section Roundtrip.
Context {A: HSet} {p: nat} {C: Category} (F: PathDiagramFamily C)
  (U: Functor (PrefixCategory A (S p)) C).
Local Abbreviation T := (truncateDiagram (pullbackDiagram U F)).

Definition pullbackMatchingTruncateUntruncate (b: MatchingObject T):
  pullbackMatchingTruncate F U (pullbackMatchingUntruncate F U b) = b :=
  matchingHomotopy T
    (b := pullbackMatchingTruncate F U (pullbackMatchingUntruncate F U b)) (c := b)
    (fun i f => eq_refl) (fun i j f g => eq_trans_refl_l (matchingPath b f g)).

Lemma pullbackMatchingTruncateUntruncateValue (b: MatchingObject T) i f:
  @eq (matchingValue b i f = matchingValue b i f)
    (f_equal (fun z => matchingValue z i f) (pullbackMatchingTruncateUntruncate b)) eq_refl.
Proof.
  now exact (matchingHomotopyValue T
    (b := pullbackMatchingTruncate F U (pullbackMatchingUntruncate F U b)) (c := b)
    (fun i f => eq_refl) (fun i j f g => eq_trans_refl_l (matchingPath b f g)) i f).
Defined.
End Roundtrip.

Section CompositionBoundary.
Context {A: HSet} {p: nat} {C D: Category}
  (U: Functor (PrefixCategory A (S p)) C) (V: Functor C D) (F: PathDiagramFamily D).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) U).
Local Abbreviation L := (pullbackDiagram U (pullbackDiagram V F)).
Local Abbreviation R := (pullbackDiagram (compFunctor U V) F).
Local Abbreviation R0 := (pullbackDiagram (compFunctor U0 V) F).

Definition matchingCompUntruncatedBoundary (x: cells L None):
  matchingCompEquiv U0 V F
    (pullbackMatchingUntruncate (pullbackDiagram V F) U (matchingMap L x)) =
  pullbackMatchingUntruncate F (compFunctor U V) (matchingMap R x).
Proof.
  refine (matchingHomotopy R0
    (b := matchingCompEquiv U0 V F
      (pullbackMatchingUntruncate (pullbackDiagram V F) U (matchingMap L x)))
    (c := pullbackMatchingUntruncate F (compFunctor U V) (matchingMap R x))
    (fun i f => eq_refl) _).
  intros i j f g.
  now exact (eq_trans_refl_l _ • eq_sym (pullbackCompositeComp U V F
    (i := None) (j := Some j) (k := Some i) g f x)).
Defined.

Lemma matchingCompUntruncatedBoundaryValue (x: cells L None) i f:
  @eq (matchingValue (matchingMap L x) i f = matchingValue (matchingMap L x) i f)
    (f_equal (fun z => matchingValue z i f) (matchingCompUntruncatedBoundary x)) eq_refl.
Proof.
  now exact (matchingHomotopyValue R0
    (b := matchingCompEquiv U0 V F
      (pullbackMatchingUntruncate (pullbackDiagram V F) U (matchingMap L x)))
    (c := pullbackMatchingUntruncate F (compFunctor U V) (matchingMap R x))
    (fun i f => eq_refl)
    (fun i j f g => eq_trans_refl_l _ • eq_sym (pullbackCompositeComp U V F
      (i := None) (j := Some j) (k := Some i) g f x)) i f).
Defined.
End CompositionBoundary.

Section MapBoundary.
Context {A: HSet} {p: nat} {C: Category} (F: PathDiagramFamily C)
  (U V: Functor (PrefixCategory A (S p)) C) (a: NatTrans U V).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) U).
Local Abbreviation V0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) C (fun n => n) V).
Local Abbreviation a0 := (truncateIndexTransformation U V a).
Local Abbreviation T := (pullbackMap F U V a).

Definition mapMatchingUntruncatedBoundary (x: F.(pfObj) (U.(fobj) None)):
  mapMatching (pullbackMap F U0 V0 a0)
    (pullbackMatchingUntruncate F U (matchingMap (pullbackDiagram U F) x)) =
  pullbackMatchingUntruncate F V
    (matchingMap (pullbackDiagram V F) (T.(mapCell) None x)).
Proof.
  refine (matchingMapTruncate F U V a
    (pullbackMatchingUntruncate F U (matchingMap (pullbackDiagram U F) x)) • _).
  refine (f_equal (fun b => pullbackMatchingUntruncate F V (mapMatching (truncateMap T) b))
    (pullbackMatchingTruncateUntruncate F U (matchingMap (pullbackDiagram U F) x)) • _).
  now exact (f_equal (pullbackMatchingUntruncate F V) (mapBoundary T x)).
Defined.

Local Lemma untruncateReadoutPath
  {b c: MatchingObject (truncateDiagram (pullbackDiagram V F))} (e: b = c) i g:
  f_equal (fun b => matchingValue (pullbackMatchingUntruncate F V b) i g) e =
    f_equal (fun b => matchingValue b i g) e.
Proof. now destruct e. Defined.

Local Lemma truncatedActionReadoutPath
  {b c: MatchingObject (truncateDiagram (pullbackDiagram U F))} (e: b = c) i g:
  f_equal (fun b => matchingValue
    (pullbackMatchingUntruncate F V (mapMatching (truncateMap T) b)) i g) e =
    f_equal (T.(mapCell) (Some i)) (f_equal (fun b => matchingValue b i g) e).
Proof. now destruct e. Defined.

Lemma mapMatchingUntruncatedBoundaryValue (x: F.(pfObj) (U.(fobj) None)) i g:
  f_equal (fun z => matchingValue z i g) (mapMatchingUntruncatedBoundary x) =
    T.(mapNatural) (i := Some i) (j := None) g x.
Proof.
  unfold mapMatchingUntruncatedBoundary. rewrite 2 eq_trans_map_distr.
  refine (transCongR
    (matchingMapTruncateValue F U V a
      (pullbackMatchingUntruncate F U (matchingMap (pullbackDiagram U F) x)) i g)
    _ • _).
  refine (transCongL eq_refl (transCongR
    (f_equal_compose
      (fun b => pullbackMatchingUntruncate F V (mapMatching (truncateMap T) b))
      (fun z => matchingValue z i g)
      (pullbackMatchingTruncateUntruncate F U (matchingMap (pullbackDiagram U F) x))
      • (truncatedActionReadoutPath
          (pullbackMatchingTruncateUntruncate F U (matchingMap (pullbackDiagram U F) x)) i g
        • f_equal (fun e => f_equal (T.(mapCell) (Some i)) e)
            (pullbackMatchingTruncateUntruncateValue F U
              (matchingMap (pullbackDiagram U F) x) i g))) _) • _).
  rewrite 2 eq_trans_refl_l.
  refine (f_equal_compose (pullbackMatchingUntruncate F V)
    (fun z => matchingValue z i g) (mapBoundary T x) • _).
  refine (untruncateReadoutPath (mapBoundary T x) i g • _).
  now exact (@mapBoundaryValue A p (pullbackDiagram U F) (pullbackDiagram V F) T x i g).
Defined.
End MapBoundary.

Unset Keyed Unification.

(** Naturality squares of matching composites and matching actions, with
    their values at each index and word. *)

Section CompositeNaturality.
Context {A: HSet} {p q: nat} {C: Category}
  (U: Functor (PrefixCategory A p) (PrefixCategory A q))
  (V W: Functor (PrefixCategory A q) C) (F: PathDiagramFamily C)
  (alpha: NatTrans V W).

Definition matchingCompositeNatural
  (b: MatchingObject (pullbackDiagram U (pullbackDiagram V F))):
  matchingCompEquiv U W F (mapMatching (reindexMap U (pullbackMap F V W alpha)) b)
    = matchingAction p C F (compFunctor U V) (compFunctor U W)
        (whiskerLNat U alpha) (matchingCompEquiv U V F b).
Proof.
  refine (matchingHomotopy (pullbackDiagram (compFunctor U W) F)
    (b := matchingCompEquiv U W F
      (mapMatching (reindexMap U (pullbackMap F V W alpha)) b))
    (c := matchingAction p C F (compFunctor U V) (compFunctor U W)
      (whiskerLNat U alpha) (matchingCompEquiv U V F b))
    (fun i g => eq_refl) _).
  intros i j f g.
  now exact (eq_trans_refl_l _).
Defined.

Lemma matchingCompositeNaturalValue
  (b: MatchingObject (pullbackDiagram U (pullbackDiagram V F))) i g:
  f_equal (fun z => matchingValue z i g) (matchingCompositeNatural b) = eq_refl.
Proof.
  unfold matchingCompositeNatural.
  now exact (matchingHomotopyValue (pullbackDiagram (compFunctor U W) F)
    (b := matchingCompEquiv U W F
      (mapMatching (reindexMap U (pullbackMap F V W alpha)) b))
    (c := matchingAction p C F (compFunctor U V) (compFunctor U W)
      (whiskerLNat U alpha) (matchingCompEquiv U V F b))
    (fun i g => eq_refl) (fun i j f g => eq_trans_refl_l _) i g).
Defined.

End CompositeNaturality.

Section NaturalSquare.
Context {A: HSet} (p: nat) (C: Category) (F: PathDiagramFamily C)
  (U0 U1 V0 V1: Functor (PrefixCategory A p) C)
  (alpha: NatTrans U0 U1) (beta: NatTrans V0 V1)
  (left: NatTrans U0 V0) (right: NatTrans U1 V1)
  (square: compNatTrans alpha right = compNatTrans left beta).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).

End NaturalSquare.
