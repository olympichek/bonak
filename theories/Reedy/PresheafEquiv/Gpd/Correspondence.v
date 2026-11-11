(** Matching sequences of homotopy groupoids classify pseudofunctors into them. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.PeanoNat.
From Bonak.Lib Require Import HSet SigT Equiv SequentialLimit FinitePrefix
  Univalence HGpd.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Bicategory HGpdBicat PathDiagram
  Pseudofunctor LocallyDiscrete LocallyDiscretePseudofunctor.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy Extension.

Set Primitive Projections.
Set Printing Projections.

(** Splitting a diagram into objects, arrows, comparisons, and coherence
    laws lets each layer of the sequential limit retain its own paths. *)
Section DiagramFields.
Context (C: Category) (O: C.(CObj) -> HGpd).

Definition ArrowData: Type := forall i j, C.(CHom) i j -> O i -> O j.

Definition Comparisons (r: ArrowData): Type :=
  {u: forall i, r i i (C.(cid) i) = fun x => x &T
    forall i j k (f: C.(CHom) i j) (g: C.(CHom) j k) x,
      r j k g (r i j f x) = r i k (C.(ccomp) f g) x}.

Definition comparisonData (r: ArrowData) (d: Comparisons r): PathDiagramData C O :=
  {| phom := r; pid := d.1; pcomp i j k f g := d.2 i j k f g |}.

Definition UnitLAt (r: ArrowData) (d: Comparisons r) a: Type :=
  forall b (f: C.(CHom) a b),
    (comparisonData r d).(pcomp) (C.(cid) a) f
    = hom2Rew (B := HGpdBicat) (eq_sym (psfUnitL C O (comparisonData r d) f))
        (eq_sym (f_equal ((comparisonData r d).(phom) (a := a) (b := b)) (C.(cidl) f)))
        (id2 ((comparisonData r d).(phom) f)).

Definition UnitRAt (r: ArrowData) (d: Comparisons r) a: Type :=
  forall b (f: C.(CHom) a b),
    (comparisonData r d).(pcomp) f (C.(cid) b)
    = hom2Rew (B := HGpdBicat) (eq_sym (psfUnitR C O (comparisonData r d) f))
        (eq_sym (f_equal ((comparisonData r d).(phom) (a := a) (b := b)) (C.(cidr) f)))
        (id2 ((comparisonData r d).(phom) f)).

Definition AssocAt (r: ArrowData) (d: Comparisons r) a: Type :=
  forall b c e (f: C.(CHom) a b) (g: C.(CHom) b c) (h: C.(CHom) c e),
    ((comparisonData r d).(pcomp) f g ▷ (comparisonData r d).(phom) h)
      ⨟₂ ((comparisonData r d).(pcomp) (f ⨟ g) h)
    = hom2Rew (B := HGpdBicat)
        (eq_sym (hgpdAssoc ((comparisonData r d).(phom) f)
          ((comparisonData r d).(phom) g) ((comparisonData r d).(phom) h)))
        (eq_sym (f_equal ((comparisonData r d).(phom) (a := a) (b := e))
          (C.(cassoc) f g h)))
        (((comparisonData r d).(phom) f ◁ (comparisonData r d).(pcomp) g h)
          ⨟₂ ((comparisonData r d).(pcomp) f (g ⨟ h))).

Definition CoherenceAt (r: ArrowData) (d: Comparisons r) a: Type :=
  {l: UnitLAt r d a &T {u: UnitRAt r d a &T AssocAt r d a}}.

Definition Coherences (r: ArrowData) (d: Comparisons r): Type :=
  {l: forall a, UnitLAt r d a &T
    {u: forall a, UnitRAt r d a &T forall a, AssocAt r d a}}.

Definition coherencePointEquiv (r: ArrowData) (d: Comparisons r):
  Equiv (Coherences r d) (forall a, CoherenceAt r d a) :=
  qinvEquiv (fun h a => (h.1 a; (h.2.1 a; h.2.2 a)))
    (fun h => (fun a => (h a).1; (fun a => (h a).2.1; fun a => (h a).2.2)))
    (fun _ => eq_refl) (fun _ => eq_refl).

Definition DiagramOn: Type :=
  {r: ArrowData &T {d: Comparisons r &T Coherences r d}}.

Definition toDiagramOn (F: PathDiagram C O): DiagramOn :=
  (fun i j f => (pathData C O F).(phom) f;
    (((pathData C O F).(pid); fun i j k f g => (pathData C O F).(pcomp) f g);
      (pathUnitL C O F; (pathUnitR C O F; pathAssoc C O F)))).

Definition ofDiagramOn (F: DiagramOn): PathDiagram C O :=
  {| pathData := comparisonData F.1 F.2.1;
     pathUnitL := F.2.2.1;
     pathUnitR := F.2.2.2.1;
     pathAssoc := F.2.2.2.2 |}.

End DiagramFields.

Section FiniteFields.
Context (A: HSet).

Definition truncateArrows {n} {O: Index (S n) -> HGpd}
  (r: ArrowData (PrefixCategory A (S n)) O):
  ArrowData (PrefixCategory A n) (fun i => O (Some i)) :=
  fun i j f => r (Some i) (Some j) f.

Definition truncateComparisons {n} {O: Index (S n) -> HGpd}
  {r: ArrowData (PrefixCategory A (S n)) O}
  (d: Comparisons _ _ r): Comparisons _ _ (truncateArrows r) :=
  (fun i => d.1 (Some i);
    fun i j k f g => d.2 (Some i) (Some j) (Some k) f g).

Definition truncateCoherences {n} {O: Index (S n) -> HGpd}
  {r: ArrowData (PrefixCategory A (S n)) O} {d: Comparisons _ _ r}
  (h: Coherences _ _ r d): Coherences _ _ (truncateArrows r) (truncateComparisons d) :=
  (fun i j f => h.1 (Some i) (Some j) f;
    (fun i j f => h.2.1 (Some i) (Some j) f;
      fun i j k l f g t => h.2.2 (Some i) (Some j) (Some k) (Some l) f g t)).

Definition truncateDiagramOn {n} {O: Index (S n) -> HGpd}
  (F: DiagramOn (PrefixCategory A (S n)) O):
  DiagramOn (PrefixCategory A n) (fun i => O (Some i)) :=
  (truncateArrows F.1; (truncateComparisons F.2.1; truncateCoherences F.2.2)).

Definition diagramFamilyEquiv n:
  Equiv (Diagram A n) {O: Index n -> HGpd &T DiagramOn (PrefixCategory A n) O} :=
  qinvEquiv (fun F => (F.(pfObj); toDiagramOn _ _ F.(pfStr)))
    (fun F => Build_PathDiagramFamily (PrefixCategory A n) F.1 (ofDiagramOn _ _ F.2))
    (fun _ => eq_refl) (fun _ => eq_refl).

End FiniteFields.

(** Every target of an arrow lies at or below its source rank. Consequently all
    outgoing arrows from an object of a finite prefix already lie in that
    prefix, and their data can be indexed by the source alone. *)
Section DescendingSections.
Context (A: HSet).

Definition outgoingSectionsEquiv n i (Q: forall j, Word A j (rank i) -> Type):
  Equiv (forall j f, Q j f) (forall j: Index n, forall f, Q (rank j) f) :=
  boundedSectionsEquiv n (fun j => Word A j (rank i))
    (fun j f => Nat.le_lt_trans _ _ _ (wordBound f) (rankLt i)) Q.

End DescendingSections.

Section GlobalFields.
Context (A: HSet) (O: nat -> HGpd).
Let C := Op (νSemiShape A).

Definition restrictArrows (r: ArrowData C O) n:
  ArrowData (PrefixCategory A n) (fun i => O (rank i)) :=
  fun i j f => r (rank i) (rank j) f.

Definition Outgoing (i: nat): Type := forall j, Word A j i -> O i -> O j.

Definition arrowStageEquiv n:
  Equiv (forall i: Index n, Outgoing (rank i))
    (ArrowData (PrefixCategory A n) (fun i => O (rank i))) :=
  piEquiv (fun i => outgoingSectionsEquiv A n i (fun j f => O (rank i) -> O j)).

Definition arrowLimitEquiv:
  Equiv (ArrowData C O)
    (SequentialLimit (fun n => ArrowData (PrefixCategory A n) (fun i => O (rank i)))
      (fun n => @truncateArrows A n _)).
Proof.
  refine (compEquiv (@sectionLimitEquiv Outgoing) _).
  now exact (sequentialLimitEquiv _ _ arrowStageEquiv (fun _ _ => eq_refl)).
Defined.

Definition restrictComparisons {r: ArrowData C O} (d: Comparisons C O r) n:
  Comparisons _ _ (restrictArrows r n) :=
  (fun i => d.1 (rank i); fun i j k f g => d.2 (rank i) (rank j) (rank k) f g).

Definition ComparisonAt (r: ArrowData C O) i: Type :=
  {u: r i i (wid i) = fun x => x &T
    forall j (f: Word A j i) k (g: Word A k j) x,
      r j k g (r i j f x) = r i k (wcomp f g) x}.

Definition comparisonGlobalEquiv (r: ArrowData C O):
  Equiv (Comparisons C O r) (forall i, ComparisonAt r i) :=
  qinvEquiv
    (fun d i => (d.1 i; fun j f k g => d.2 i j k f g))
    (fun d => (fun i => (d i).1; fun i j k f g => (d i).2 j f k g))
    (fun _ => eq_refl) (fun _ => eq_refl).

Definition comparisonStageEquiv (r: ArrowData C O) n:
  Equiv (forall i: Index n, ComparisonAt r (rank i))
    (Comparisons _ _ (restrictArrows r n)).
Proof.
  refine (compEquiv (symEquiv sigTPiEquiv) _).
  refine (compEquiv (sigTEquivSnd (fun _ => piEquiv (fun i =>
    compEquiv (outgoingSectionsEquiv A n i (fun j f =>
      forall k (g: Word A k j) x,
        r j k g (r (rank i) j f x) = r (rank i) k (wcomp f g) x))
      (piEquiv (fun j => piEquiv (fun f =>
        outgoingSectionsEquiv A n j (fun k g => forall x,
          r (rank j) k g (r (rank i) (rank j) f x)
            = r (rank i) k (wcomp f g) x))))))) _).
  now exact (qinvEquiv
    (fun d => (d.1; fun i j k f g => d.2 i j f k g))
    (fun d => (d.1; fun i j f k g => d.2 i j k f g))
    (fun _ => eq_refl) (fun _ => eq_refl)).
Defined.

Definition comparisonLimitEquiv (r: ArrowData C O):
  Equiv (Comparisons C O r)
    (SequentialLimit
      (fun n => Comparisons _ _ (restrictArrows r n))
      (fun n => @truncateComparisons A n _ _)).
Proof.
  refine (compEquiv (comparisonGlobalEquiv r) _).
  refine (compEquiv (@sectionLimitEquiv (ComparisonAt r)) _).
  now exact (sequentialLimitEquiv _ _ (comparisonStageEquiv r)
    (fun _ _ => eq_refl)).
Defined.

Definition unitLStageEquiv (r: ArrowData C O) (d: Comparisons C O r) n (i: Index n):
  Equiv (UnitLAt C O r d (rank i))
    (UnitLAt _ _ (restrictArrows r n) (restrictComparisons d n) i).
Proof. now apply outgoingSectionsEquiv. Defined.

Definition unitRStageEquiv (r: ArrowData C O) (d: Comparisons C O r) n (i: Index n):
  Equiv (UnitRAt C O r d (rank i))
    (UnitRAt _ _ (restrictArrows r n) (restrictComparisons d n) i).
Proof. now apply outgoingSectionsEquiv. Defined.

Definition assocStageEquiv (r: ArrowData C O) (d: Comparisons C O r) n (i: Index n):
  Equiv (AssocAt C O r d (rank i))
    (AssocAt _ _ (restrictArrows r n) (restrictComparisons d n) i).
Proof.
  refine (compEquiv (qinvEquiv
    (fun h j f k g l t => h j k l f g t)
    (fun h j k l f g t => h j f k g l t)
    (fun _ => eq_refl) (fun _ => eq_refl)) _).
  refine (compEquiv (outgoingSectionsEquiv A n i _) _).
  refine (compEquiv (piEquiv (fun j => piEquiv (fun f =>
    outgoingSectionsEquiv A n j _))) _).
  refine (compEquiv (piEquiv (fun j => piEquiv (fun f =>
    piEquiv (fun k => piEquiv (fun g => outgoingSectionsEquiv A n k _))))) _).
  now exact (qinvEquiv
    (fun h j k l f g t => h j f k g l t)
    (fun h j f k g l t => h j k l f g t)
    (fun _ => eq_refl) (fun _ => eq_refl)).
Defined.

Definition coherencePointStageEquiv (r: ArrowData C O) (d: Comparisons C O r)
  n (i: Index n):
  Equiv (CoherenceAt C O r d (rank i))
    (CoherenceAt _ _ (restrictArrows r n) (restrictComparisons d n) i).
Proof.
  unfold CoherenceAt. refine (sigTEquiv (unitLStageEquiv r d n i) _).
  intro l. refine (sigTEquiv (unitRStageEquiv r d n i) _).
  intro u. now exact (assocStageEquiv r d n i).
Defined.

Definition coherenceStageEquiv (r: ArrowData C O) (d: Comparisons C O r) n:
  Equiv (forall i: Index n, CoherenceAt C O r d (rank i))
    (Coherences _ _ (restrictArrows r n) (restrictComparisons d n)).
Proof.
  refine (compEquiv (piEquiv (coherencePointStageEquiv r d n)) _).
  now exact (symEquiv (coherencePointEquiv (PrefixCategory A n)
    (fun i => O (rank i)) (restrictArrows r n) (restrictComparisons d n))).
Defined.

Definition coherenceLimitEquiv (r: ArrowData C O) (d: Comparisons C O r):
  Equiv (Coherences C O r d)
    (SequentialLimit
      (fun n => Coherences _ _ (restrictArrows r n) (restrictComparisons d n))
      (fun n => @truncateCoherences A n _ _ _)).
Proof.
  refine (compEquiv (coherencePointEquiv C O r d) _).
  refine (compEquiv (@sectionLimitEquiv (CoherenceAt C O r d)) _).
  now exact (sequentialLimitEquiv _ _ (coherenceStageEquiv r d)
    (fun _ _ => eq_refl)).
Defined.

(** Each global restriction has reflexive bonds. Splitting the dependent limit
    and identifying its base with [Comparisons] therefore reduces the remaining
    fibre to the next ordinary sequential limit. *)
Definition comparisonCoherenceLimitEquiv (r: ArrowData C O):
  Equiv (SequentialLimit
    (fun n => {d: Comparisons _ _ (restrictArrows r n) &T
      Coherences _ _ (restrictArrows r n) d})
    (fun n d => (truncateComparisons A d.1; truncateCoherences A d.2)))
    {d: Comparisons C O r &T Coherences C O r d}.
Proof.
  pose (rC := fun n => @truncateComparisons A n _ (restrictArrows r (S n))).
  pose (rL := fun n (d: Comparisons _ _ (restrictArrows r (S n))) =>
    @truncateCoherences A n _ _ d).
  refine (compEquiv (sequentialLimitSigmaEquiv rC rL) _).
  refine (compEquiv (symEquiv (sigTEquivFst
    (B := SequentialLimitFiber
      (fun n d => Coherences _ _ (restrictArrows r n) d) rC rL)
    (comparisonLimitEquiv r))) _).
  now exact (sigTEquivSnd (fun d => symEquiv (coherenceLimitEquiv r d))).
Defined.

Definition fixedObjectLimitEquiv:
  Equiv (SequentialLimit
      (fun n => DiagramOn (PrefixCategory A n) (fun i => O (rank i)))
      (fun n => @truncateDiagramOn A n _))
    (DiagramOn C O).
Proof.
  pose (rA := fun n => @truncateArrows A n (fun i => O (rank i))).
  pose (rS := fun n (r: ArrowData (PrefixCategory A (S n)) (fun i => O (rank i)))
    (d: {d: Comparisons _ _ r &T Coherences _ _ r d}) =>
    (truncateComparisons A d.1; truncateCoherences A d.2)).
  refine (compEquiv (sequentialLimitSigmaEquiv rA rS) _).
  refine (compEquiv (symEquiv (sigTEquivFst
    (B := SequentialLimitFiber
      (fun n r => {d: Comparisons _ _ r &T Coherences _ _ r d}) rA rS)
    arrowLimitEquiv)) _).
  now exact (sigTEquivSnd comparisonCoherenceLimitEquiv).
Defined.

End GlobalFields.

Definition diagramLimitEquivPathDiagram (A: HSet):
  Equiv (SequentialLimit (Diagram A) (fun n => @truncateDiagram A n))
    (PathDiagramFamily (Op (νSemiShape A))).
Proof.
  refine (compEquiv (objectSplitEquiv (fun n O => DiagramOn (PrefixCategory A n) O)
    (fun n O F => @truncateDiagramOn A n O F) (fun n => @truncateDiagram A n)
    (diagramFamilyEquiv A) (fun _ _ => eq_refl) (fixedObjectLimitEquiv A)) _).
  now exact (qinvEquiv
    (fun X => Build_PathDiagramFamily (Op (νSemiShape A)) X.1 (ofDiagramOn _ _ X.2))
    (fun X => (X.(pfObj); toDiagramOn _ _ X.(pfStr)))
    (fun _ => eq_refl) (fun _ => eq_refl)).
Defined.

Section Comparison.
Context (A: HSet).

Definition matchingSeqEquivPseudofunctor:
  Equiv (MatchingSeq (gpdSystem A))
    (Pseudofunctor (locallyDiscrete (Op (νSemiShape A))) HGpdBicat) :=
  compEquiv (matchingSeqEquivDiagramLimit (gpdSystem A)
    (matchingExtensionLaws (gpdSystem A) (gpdLaws A)))
    (compEquiv (diagramLimitEquivPathDiagram A)
      (locallyDiscretePseudofunctorEquiv (Op (νSemiShape A)))).

Definition matchingSeqEqPseudofunctor:
  MatchingSeq (gpdSystem A) =
  Pseudofunctor (locallyDiscrete (Op (νSemiShape A))) HGpdBicat :=
  ua matchingSeqEquivPseudofunctor.

End Comparison.

Definition simplicialMatchingSeqEqPseudofunctor:
  AugmentedSemiSimplicialGpdMatchingSeq
  = Pseudofunctor (locallyDiscrete (Op (νSemiShape hunit))) HGpdBicat :=
  matchingSeqEqPseudofunctor hunit.

Definition cubicalMatchingSeqEqPseudofunctor:
  SemiCubicalGpdMatchingSeq
  = Pseudofunctor (locallyDiscrete (Op (νSemiShape hbool))) HGpdBicat :=
  matchingSeqEqPseudofunctor hbool.
