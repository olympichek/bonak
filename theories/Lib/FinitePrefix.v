(** Finite prefixes of the natural numbers and compatible families on them. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Logic.Eqdep_dec Arith.PeanoNat Lia.
From Bonak.Lib Require Import HSet SigT Equiv Funext RewLemmas Notation SequentialLimit.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** The ranks below [n]. [Some] retains an earlier rank; [None] adds the
    highest rank. Reedy theory calls the rank of an object its degree.

    [Index] is universe monomorphic, in one fixed universe. Two universe
    instances of a polymorphic [Index] at a variable [n] are not convertible,
    and Rocq up to 9.3 gives the occurrences of [Index] in the type of a
    monomorphic definition different instances. *)
Monomorphic Fixpoint Index (n: nat): Type :=
  match n with
  | 0 => Empty_set
  | S n => option (Index n)
  end.

Fixpoint rank {n: nat}: Index n -> nat :=
  match n as k return Index k -> nat with
  | 0 => fun i => match i with end
  | S k => fun i =>
      match i with
      | None => k
      | Some j => @rank k j
      end
  end.

Lemma rankLt {n} (i: Index n): Nat.lt (rank i) n.
Proof.
  revert i; induction n as [|n IH]; intro i.
  - now destruct i.
  - destruct i as [i|]; cbn.
    + now apply Nat.lt_lt_succ_r, IH.
    + now apply Nat.lt_succ_diag_r.
Defined.

Fixpoint ofNat (n k: nat): k < n -> Index n.
Proof.
  destruct n as [|n]; intro h.
  - exfalso. now lia.
  - destruct (Nat.eq_dec k n) as [e|e].
    + now exact None.
    + refine (Some (ofNat n k _)). now lia.
Defined.

Lemma rankOfNat n k (h: k < n): rank (ofNat n k h) = k.
Proof.
  induction n as [|n IH].
  - now lia.
  - cbn [ofNat]. destruct (Nat.eq_dec k n) as [e|e]; cbn.
    + now exact (eq_sym e).
    + now apply IH.
Defined.

Lemma rankInjective {n} (i j: Index n): rank i = rank j -> i = j.
Proof.
  induction n as [|n IH].
  - now destruct i.
  - destruct i as [i|], j as [j|]; cbn.
    + intro h. now exact (f_equal Some (IH i j h)).
    + pose proof (rankLt i). now lia.
    + pose proof (rankLt j). now lia.
    + intro h. now reflexivity.
Defined.

Definition IndexAt (n k: nat): Type := {i: Index n &T rank i = k}.

Definition atRank n k (h: k < n): IndexAt n k :=
  (ofNat n k h; rankOfNat n k h).

Lemma indexAtEq {n k} (x y: IndexAt n k): x = y.
Proof.
  destruct x as [i p], y as [j q].
  assert (e: i = j) by (apply rankInjective; now exact (p • eq_sym q)).
  destruct e. apply f_equal. now apply Eqdep_dec.UIP_dec, Nat.eq_dec.
Defined.

Definition weakenIndexAt {n k} (i: IndexAt n k): IndexAt (S n) k :=
  (Some i.1; i.2).

(** A compatible family of sections on finite prefixes determines one section
    on all natural numbers. Its coherence paths are retained for arbitrary [B]. *)
Definition SectionLimit (B: nat -> Type): Type :=
  SequentialLimit (fun n => forall i: Index n, B (rank i)) (fun n x i => x (Some i)).

Definition restrictSections {B: nat -> Type} (p: forall k, B k): SectionLimit B :=
  ((fun n i => p (rank i)); fun n => eq_refl).

Definition assembleSections {B: nat -> Type} (c: SectionLimit B): forall k, B k :=
  fun n => c.1 (S n) None.

Fixpoint restrictAssembleSectionAt {B: nat -> Type} (c: SectionLimit B) (n: nat):
  forall i: Index n, assembleSections c (rank i) = c.1 n i :=
  match n as n0 return forall i: Index n0,
    assembleSections c (rank i) = c.1 n0 i with
  | 0 => fun i => match i with end
  | S k => fun i =>
      match i with
      | Some j => restrictAssembleSectionAt c k j • eq_sym (happly (c.2 k) j)
      | None => eq_refl
      end
  end.

Definition restrictAssembleSectionStage {B: nat -> Type} (c: SectionLimit B) n:
  (restrictSections (assembleSections c)).1 n = c.1 n :=
  functional_extensionality_dep_good _ _ (restrictAssembleSectionAt c n).

Lemma restrictAssembleSectionBond {B: nat -> Type} (c: SectionLimit B) n:
  f_equal (fun x: forall i: Index (S n), B (rank i) => fun i => x (Some i))
    (restrictAssembleSectionStage c (S n)) • c.2 n = restrictAssembleSectionStage c n.
Proof.
  apply happlyInj; intro i. unfold happly.
  rewrite eq_trans_map_distr.
  refine (f_equal (fun q => q • happly (c.2 n) i)
    (f_equal_compose
      (fun x: forall i: Index (S n), B (rank i) => fun i => x (Some i))
      (fun x: forall i: Index n, B (rank i) => x i) (restrictAssembleSectionStage c (S n))
      • f_equal__functional_extensionality_dep_good
          (restrictAssembleSectionAt c (S n)) (Some i)) • _).
  refine (transSymCancelR2 (restrictAssembleSectionAt c n i) (happly (c.2 n) i) • _).
  symmetry. unfold restrictAssembleSectionStage.
  now exact (f_equal__functional_extensionality_dep_good (restrictAssembleSectionAt c n) i).
Defined.

Lemma restrictAssembleSections {B: nat -> Type} (c: SectionLimit B):
  restrictSections (assembleSections c) = c.
Proof.
  apply (sequentialLimitEq _ _ (restrictAssembleSectionStage c)); intro n.
  cbn. rewrite eq_trans_refl_l. now apply restrictAssembleSectionBond.
Defined.

Definition sectionLimitEquiv {B: nat -> Type}: Equiv (forall k, B k) (SectionLimit B) :=
  qinvEquiv restrictSections assembleSections (fun p => eq_refl) restrictAssembleSections.

(** Sections supported below a finite rank can be indexed by the
    corresponding finite prefix without changing their values. *)
Section BoundedSections.
Context (n: nat) (P: nat -> Type) (bound: forall k, P k -> k < n)
  (Q: forall k, P k -> Type).

Definition restrictBoundedSection (s: forall k p, Q k p)
  (i: Index n) (p: P (rank i)): Q (rank i) p := s (rank i) p.

Definition readBoundedSection (s: forall (i: Index n) p, Q (rank i) p)
  {k} (i: IndexAt n k): forall p: P k, Q k p.
Proof. destruct i as [i e]. now destruct e; exact (s i). Defined.

Definition extendBoundedSection (s: forall (i: Index n) p, Q (rank i) p)
  k (p: P k): Q k p := readBoundedSection s (atRank n k (bound k p)) p.

Lemma restrictExtendBoundedSection (s: forall (i: Index n) p, Q (rank i) p):
  restrictBoundedSection (extendBoundedSection s) = s.
Proof.
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro p.
  unfold restrictBoundedSection, extendBoundedSection.
  rewrite (indexAtEq (atRank n (rank i) (bound (rank i) p)) (i; eq_refl)).
  now reflexivity.
Defined.

Lemma extendRestrictBoundedSection (s: forall k p, Q k p):
  extendBoundedSection (restrictBoundedSection s) = s.
Proof.
  apply functional_extensionality_dep; intro k.
  apply functional_extensionality_dep; intro p.
  unfold extendBoundedSection.
  generalize (atRank n k (bound k p)); intros [i e].
  now destruct e.
Defined.

Definition boundedSectionsEquiv:
  Equiv (forall k p, Q k p) (forall (i: Index n) p, Q (rank i) p) :=
  qinvEquiv restrictBoundedSection extendBoundedSection
    extendRestrictBoundedSection restrictExtendBoundedSection.

End BoundedSections.

(** A limit of diagrams on finite prefixes splits into one object at every
    rank and, over those objects, a limit of the remaining structure. The
    coherence paths of the object assignments are preserved. *)
Section ObjectSplit.
Context {V: Type} (Structure: forall n, (Index n -> V) -> Type)
  (truncS: forall n (O: Index (S n) -> V),
    Structure (S n) O -> Structure n (fun i => O (Some i))).

Definition FixedObjectLimit (O: nat -> V): Type :=
  SequentialLimit (fun n => Structure n (fun i => O (rank i)))
    (fun n => truncS n _).

Definition objectSplitEquiv {X: nat -> Type} (tr: forall n, X (S n) -> X n)
  (e: forall n, Equiv (X n) {O: Index n -> V &T Structure n O})
  (comm: forall n x, e n (tr n x) =
    ((fun i => (e (S n) x).1 (Some i)); truncS n _ (e (S n) x).2))
  {G: (nat -> V) -> Type} (fixed: forall O, Equiv (FixedObjectLimit O) (G O)):
  Equiv (SequentialLimit X tr) {O: nat -> V &T G O}.
Proof.
  pose (r := fun n (O: Index (S n) -> V) (i: Index n) => O (Some i)).
  refine (compEquiv (sequentialLimitEquiv tr
    (fun n z => (r n z.1; truncS n z.1 z.2)) e comm) _).
  refine (compEquiv (sequentialLimitSigmaEquiv r truncS) _).
  refine (compEquiv (symEquiv (sigTEquivFst
    (B := SequentialLimitFiber Structure r truncS)
    (@sectionLimitEquiv (fun _ => V)))) _).
  now exact (sigTEquivSnd fixed).
Defined.

End ObjectSplit.

(** Compatible h-set-valued tables can be read at any common finite bound. *)
Section Tables.
Context (P: nat -> nat -> HSet).

Definition Table n: HSet := hforall i j: Index n, P (rank i) (rank j).
Definition truncateTable n (t: Table (S n)): Table n :=
  fun i j => t (Some i) (Some j).
Definition TableLimit := SequentialLimit (fun n => Table n) truncateTable.

Definition readTable {n i j} (t: Table n) (x: IndexAt n i) (y: IndexAt n j): P i j.
Proof.
  destruct x as [x p], y as [y q]. now destruct p, q; exact (t x y).
Defined.

Lemma readSome {n i j} (t: Table (S n)) (x: IndexAt n i) (y: IndexAt n j):
  readTable t (weakenIndexAt x) (weakenIndexAt y) = readTable (truncateTable n t) x y.
Proof. destruct x as [x p], y as [y q]. now destruct p, q. Defined.

Definition readBound (c: TableLimit) n i j (hi: i < n) (hj: j < n): P i j :=
  readTable (c.1 n) (atRank n i hi) (atRank n j hj).

Lemma readBoundIrrel (c: TableLimit) n i j (hi hi': i < n) (hj hj': j < n):
  readBound c n i j hi hj = readBound c n i j hi' hj'.
Proof.
  unfold readBound. now rewrite (indexAtEq (atRank n i hi) (atRank n i hi')),
    (indexAtEq (atRank n j hj) (atRank n j hj')).
Defined.

Lemma readBoundStep (c: TableLimit) n i j (hi: i < n) (hj: j < n)
  (hi': i < S n) (hj': j < S n):
  readBound c (S n) i j hi' hj' = readBound c n i j hi hj.
Proof.
  unfold readBound.
  rewrite (indexAtEq (atRank (S n) i hi') (weakenIndexAt (atRank n i hi))),
    (indexAtEq (atRank (S n) j hj') (weakenIndexAt (atRank n j hj))).
  rewrite readSome. now rewrite c.2.
Defined.

Lemma readBoundMono (c: TableLimit) n m (h: n <= m) i j
  (hi: i < n) (hj: j < n) (hi': i < m) (hj': j < m):
  readBound c m i j hi' hj' = readBound c n i j hi hj.
Proof.
  induction h as [|m h IH].
  - now apply readBoundIrrel.
  - assert (hmi: i < m) by now lia.
    assert (hmj: j < m) by now lia.
    rewrite (readBoundStep c m i j hmi hmj hi' hj'). now apply IH.
Defined.

(** Any pair of ranks occurs in a finite prefix. Coherence makes its
    value independent of the chosen bound. *)
Definition assembleTable (c: TableLimit) i j: P i j :=
  readBound c (S (Nat.max i j)) i j
    (proj2 (Nat.lt_succ_r _ _) (Nat.le_max_l i j))
    (proj2 (Nat.lt_succ_r _ _) (Nat.le_max_r i j)).

Lemma assembleTableRead (c: TableLimit) n i j (hi: i < n) (hj: j < n):
  assembleTable c i j = readBound c n i j hi hj.
Proof.
  unfold assembleTable.
  assert (h: S (Nat.max i j) <= n) by now lia.
  symmetry. now apply readBoundMono.
Defined.

Lemma assembleTableAt (c: TableLimit) n (i j: Index n):
  assembleTable c (rank i) (rank j) = c.1 n i j.
Proof.
  rewrite (assembleTableRead c n (rank i) (rank j) (rankLt i) (rankLt j)).
  unfold readBound.
  rewrite (indexAtEq (atRank n (rank i) (rankLt i)) (i; eq_refl)),
    (indexAtEq (atRank n (rank j) (rankLt j)) (j; eq_refl)).
  now reflexivity.
Defined.

Definition restrictTable (p: forall i j, P i j): TableLimit :=
  ((fun n (i j: Index n) => p (rank i) (rank j)); fun _ => eq_refl).

Lemma restrictTableRead (p: forall i j, P i j) n i j (hi: i < n) (hj: j < n):
  readBound (restrictTable p) n i j hi hj = p i j.
Proof.
  unfold readBound. generalize (atRank n i hi), (atRank n j hj).
  intros [x e] [y f]. now destruct e, f.
Defined.

End Tables.

