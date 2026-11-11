(** Compatible generating faces determine the full matching object. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet Notation LeSProp Equiv Funext FinitePrefix.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Presheaf Require Import νSemiShape GeneratingFaces.
From Bonak.Reedy Require Import Reedy Coskeleton.

Set Primitive Projections.
Set Printing Projections.


Polymorphic Fixpoint rankBound {n}: forall i: Index n, (rank i).+1 <= n.
Proof.
  destruct n as [|n]; intro i.
  - now destruct i.
  - destruct i as [i|]; cbn.
    + now exact (↑ (rankBound n i)).
    + now apply leR_refl.
Defined.

Section Boundary.
Context (A: HSet).
Local Abbreviation Diagram := (Functor (Op (νSemiShape A)) HSetCat).

Definition presheafDiagram (F: Diagram) n: Reedy.Diagram A n := {|
  Reedy.cells i := F.(fobj) (rank i);
  Reedy.restrict i j f := F.(fhom) (a := rank j) (b := rank i) f;
  Reedy.restrictId i x := fhomIdPt F (rank i) x;
  Reedy.restrictComp i j k f g x := fhomCompPt F g f x;
|}.

Fixpoint properFaceFactor n: forall m, m <= n -> forall u: Word A m n.+1,
  {i: FaceDepth n &T {a: A &T {v: Word A m n &T
    u = wcomp (depthFaceWord A n i a) v}}}.
Proof.
  destruct n as [|n]; intros m hm u.
  - destruct m as [|m]; [|now destruct (leR_O_contra hm)].
    destruct u as [[a []]|u]; [|destruct u].
    now exact (firstDepth 0; (a; (wnil; eq_refl))).
  - destruct u as [[a u]|u].
    + refine (firstDepth n.+1; (a; (u; _))).
      rewrite depthFaceFirst, wcomp_skip, wcompIdl. now reflexivity.
    + destruct m as [|m]; [destruct u|].
      destruct (properFaceFactor n m (⇓ hm) u) as [i [a [v e]]].
      refine (nextDepth i; (a; (wkeep v; _))).
      rewrite depthFaceNext, wcomp_keep_keep. now exact (f_equal wkeep e).
Defined.

Lemma matchingFacesExt n (F: Diagram)
  (b c: Reedy.MatchingObject A (presheafDiagram F n.+1))
  (h: forall i a, b.1 None (depthFaceWord A n i a)
    = c.1 None (depthFaceWord A n i a)): b = c.
Proof.
  apply Reedy.matchingExt; intros j u.
  destruct (properFaceFactor n (rank j) (⇓ (rankBound j)) u) as [i [a [v e]]].
  rewrite e.
  now exact (eq_sym (b.2 j None v (depthFaceWord A n i a))
    • f_equal (F.(fhom) v) (h i a)
    • c.2 j None v (depthFaceWord A n i a)).
Defined.

Definition shiftedDiagram (F: Diagram): Diagram := compFunctor (νSemiShapeShift A) F.

Definition RawBoundary n (F: Diagram): Type :=
  match n with 0 => unit | S n => FaceDepth n -> A -> F.(fobj) n end.

Definition shiftRawBoundary n (F: Diagram): RawBoundary n.+1 F -> RawBoundary n (shiftedDiagram F) :=
  match n with 0 => fun _ => tt | S n => fun b i a => b (nextDepth i) a end.

Definition TopBoundaryLaw n (F: Diagram): RawBoundary n.+1 F -> Type :=
  match n as n return RawBoundary n.+1 F -> Type with
  | 0 => fun _ => unit
  | S n => fun b => forall (i: FaceDepth n) a c,
      F.(fhom) (wskip a (wid n)) (b (nextDepth i) c)
        = F.(fhom) (depthFaceWord A n i c) (b (firstDepth n.+1) a)
  end.

Fixpoint BoundaryLaws n (F: Diagram): RawBoundary n F -> Type :=
  match n as n return RawBoundary n F -> Type with
  | 0 => fun _ => unit
  | S n => fun b => (TopBoundaryLaw n F b *
      BoundaryLaws n (shiftedDiagram F) (shiftRawBoundary n F b))%type
  end.

Fixpoint boundaryEval N: forall (F: Diagram) (b: RawBoundary N F)
  m (u: Word A m N), m.+1 <= N -> F.(fobj) m.
Proof.
  destruct N as [|N]; intros F b m u h.
  - now destruct (leR_O_contra h).
  - destruct u as [[a u]|u].
    + now exact (F.(fhom) (a := N) (b := m) u (b (firstDepth N) a)).
    + destruct m as [|m]; [destruct u|].
      now exact (boundaryEval N (shiftedDiagram F) (shiftRawBoundary N F b) m u (⇓ h)).
Defined.

Definition cellRawBoundary N (F: Diagram): F.(fobj) N -> RawBoundary N F :=
  match N with
  | 0 => fun _ => tt
  | S n => fun x i a => F.(fhom) (depthFaceWord A n i a) x
  end.

Lemma cellRawShift n (F: Diagram) (x: F.(fobj) n.+1):
  shiftRawBoundary n F (cellRawBoundary n.+1 F x)
    = cellRawBoundary n (shiftedDiagram F) x.
Proof. destruct n; now reflexivity. Qed.

Lemma boundaryEvalCell N: forall (F: Diagram) m (u: Word A m N) h x,
  boundaryEval N F (cellRawBoundary N F x) m u h = F.(fhom) u x.
Proof.
  induction N as [|N IH]; intros F m u h x.
  - now destruct (leR_O_contra h).
  - destruct u as [[a u]|u].
    + cbn [boundaryEval cellRawBoundary]. rewrite depthFaceFirst.
      rewrite (fhomCompPt F (wskip a (wid N)) u x).
      change (F.(fhom) (wcomp (wskip a (wid N)) u) x = F.(fhom) (wskip a u) x).
      rewrite wcomp_skip, wcompIdl. now reflexivity.
    + destruct m as [|m]; [destruct u|].
      cbn [boundaryEval]. rewrite cellRawShift. now exact (IH (shiftedDiagram F) m u (⇓ h) x).
Qed.

Definition RawBoundaryMap N {F G: Diagram} (α: NatTrans F G):
  RawBoundary N F -> RawBoundary N G -> Type :=
  match N with
  | 0 => fun _ _ => unit
  | S n => fun b c => forall i a, α.(ncomp) n (b i a) = c i a
  end.

Lemma boundaryEvalMap N: forall (F G: Diagram) (α: NatTrans F G)
  (b: RawBoundary N F) (c: RawBoundary N G), RawBoundaryMap N α b c ->
  forall m (u: Word A m N) h,
    α.(ncomp) m (boundaryEval N F b m u h) = boundaryEval N G c m u h.
Proof.
  induction N as [|N IH]; intros F G α b c H m u h.
  - now destruct (leR_O_contra h).
  - destruct u as [[a u]|u].
    + cbn [boundaryEval].
      now exact (f_equal (fun f => f (b (firstDepth N) a)) (α.(nnat) u)
        • f_equal (G.(fhom) u) (H (firstDepth N) a)).
    + destruct m as [|m]; [destruct u|].
      apply (IH (shiftedDiagram F) (shiftedDiagram G) (whiskerLNat (νSemiShapeShift A) α)).
      destruct N as [|N]; [now exact tt|]. intros i a. now exact (H (nextDepth i) a).
Qed.

Definition topFaceNat (F: Diagram) (a: A): NatTrans (shiftedDiagram F) F.
Proof.
  refine (Build_NatTrans _ _ (shiftedDiagram F) F
    (fun n => F.(fhom) (wskip a (wid n))) _).
  intros n m u. apply functional_extensionality_dep; intro x.
  change (F.(fhom) (wskip a (wid m)) (F.(fhom) (wkeep u) x)
    = F.(fhom) u (F.(fhom) (wskip a (wid n)) x)).
  rewrite 2 fhomCompPt.
  change (F.(fhom) (wcomp (wkeep u) (wskip a (wid m))) x
    = F.(fhom) (wcomp (wskip a (wid n)) u) x).
  rewrite wcomp_keep_skip, wcomp_skip, wcompIdr, wcompIdl. now reflexivity.
Defined.

Lemma boundaryEvalTop N (F: Diagram) (b: RawBoundary N.+1 F)
  (H: BoundaryLaws N.+1 F b) m (u: Word A m N) (h: m.+1 <= N) a:
  F.(fhom) (wskip a (wid m))
    (boundaryEval N (shiftedDiagram F) (shiftRawBoundary N F b) m u h)
  = F.(fhom) u (b (firstDepth N) a).
Proof.
  refine (boundaryEvalMap N (shiftedDiagram F) F (topFaceNat F a)
    (shiftRawBoundary N F b) (cellRawBoundary N F (b (firstDepth N) a)) _ m u h • _).
  - destruct N as [|N]; [now exact tt|]. intros i c. now exact (fst H i a c).
  - now apply boundaryEvalCell.
Qed.

Lemma functorSkip (F: Diagram) {m k} (u: Word A k m) a (x: F.(fobj) m.+1):
  F.(fhom) (wskip a u) x = F.(fhom) u (F.(fhom) (wskip a (wid m)) x).
Proof.
  rewrite fhomCompPt.
  change (F.(fhom) (wskip a u) x = F.(fhom) (wcomp (wskip a (wid m)) u) x).
  rewrite wcomp_skip, wcompIdl. now reflexivity.
Qed.

Lemma boundaryEvalComp N: forall (F: Diagram) (b: RawBoundary N F) (H: BoundaryLaws N F b)
  m (g: Word A m N) (hg: m.+1 <= N) k (f: Word A k m) (hf: k.+1 <= N),
  boundaryEval N F b k (wcomp g f) hf = F.(fhom) f (boundaryEval N F b m g hg).
Proof.
  induction N as [|N IH]; intros F b H m g hg k f hf.
  - now destruct (leR_O_contra hg).
  - destruct g as [[a g]|g].
    + cbn [wcomp boundaryEval]. now exact (eq_sym (fhomCompPt F g f (b (firstDepth N) a))).
    + destruct m as [|m]; [destruct g|]. destruct f as [[a f]|f].
      * cbn [wcomp boundaryEval].
        change (F.(fhom) (wcomp g f) (b (firstDepth N) a) =
          F.(fhom) (wskip a f)
            (boundaryEval N (shiftedDiagram F) (shiftRawBoundary N F b) m g (⇓ hg))).
        rewrite (functorSkip F f a _), (boundaryEvalTop N F b H m g (⇓ hg) a).
        now exact (eq_sym (fhomCompPt F g f (b (firstDepth N) a))).
      * destruct k as [|k]; [destruct f|].
        now exact (IH (shiftedDiagram F) (shiftRawBoundary N F b) (snd H)
          m g (⇓ hg) k f (⇓ hf)).
Qed.

Definition boundaryMatching N (F: Diagram) (b: RawBoundary N F) (H: BoundaryLaws N F b):
  Reedy.MatchingObject A (presheafDiagram F N).
Proof.
  exists (fun i u => boundaryEval N F b (rank i) u (rankBound i)).
  intros i j f u.
  now exact (eq_sym (boundaryEvalComp N F b H (rank j) u (rankBound j)
    (rank i) f (rankBound i))).
Defined.

Lemma boundaryEvalFace n: forall (F: Diagram) (b: RawBoundary n.+1 F) i a,
  boundaryEval n.+1 F b n (depthFaceWord A n i a) leR_refl = b i a.
Proof.
  induction n as [|n IH]; intros F b [[|j] h] a.
  - now exact (fhomIdPt F 0 (b (firstDepth 0) a)).
  - now destruct (leR_O_contra h).
  - now exact (fhomIdPt F n.+1 (b (firstDepth n.+1) a)).
  - now exact (IH (shiftedDiagram F) (shiftRawBoundary n.+1 F b)
      {| depth := j; depthBound := ⇓ h |} a).
Qed.

Definition matchingRaw N (F: Diagram):
  Reedy.MatchingObject A (presheafDiagram F N) -> RawBoundary N F :=
  match N as N return Reedy.MatchingObject A (presheafDiagram F N) -> RawBoundary N F with
  | 0 => fun _ => tt
  | S n => fun b i a => b.1 None (depthFaceWord A n i a)
  end.

Definition PairwiseBoundaryLaw N (F: Diagram): RawBoundary N F -> Type :=
  match N as N return RawBoundary N F -> Type with
  | 0 => fun _ => unit
  | S 0 => fun _ => unit
  | S (S n) => fun b => forall (i j: FaceDepth n), depth i <= depth j -> forall a c,
      F.(fhom) (depthFaceWord A n i a) (b (nextDepth j) c)
        = F.(fhom) (depthFaceWord A n j c) (b (weakenDepth i) a)
  end.
Lemma pairwiseBoundaryShift n (F: Diagram) (b: RawBoundary n.+1 F)
  (H: PairwiseBoundaryLaw n.+1 F b):
  PairwiseBoundaryLaw n (shiftedDiagram F) (shiftRawBoundary n F b).
Proof.
  destruct n as [|[|n]]; [now exact tt|now exact tt|].
  intros i j hij a c.
  now exact (H (nextDepth i) (nextDepth j) (⇑ hij) a c).
Qed.
Fixpoint pairwiseBoundaryLaws N (F: Diagram) (b: RawBoundary N F)
  (H: PairwiseBoundaryLaw N F b): BoundaryLaws N F b.
Proof.
  destruct N as [|N]; [now exact tt|]. refine (_, _).
  - destruct N as [|N]; [now exact tt|]. intros i a c.
    rewrite <- depthFaceFirst. now exact (H (firstDepth N) i leR_O a c).
  - now exact (pairwiseBoundaryLaws N (shiftedDiagram F) (shiftRawBoundary N F b)
      (pairwiseBoundaryShift N F b H)).
Defined.
Lemma depthFaceExchange n: forall (i j: FaceDepth n), depth i <= depth j -> forall a c,
  wcomp (depthFaceWord A n.+1 (nextDepth j) c) (depthFaceWord A n i a)
    = wcomp (depthFaceWord A n.+1 (weakenDepth i) a) (depthFaceWord A n j c).
Proof.
  induction n as [|n IH]; intros [[|i] hi] [[|j] hj] hij a c;
    try (now destruct (leR_O_contra hi)); try (now destruct (leR_O_contra hj));
    try (now destruct (leR_O_contra hij)).
  - cbn. now reflexivity.
  - change (wcomp (wkeep (depthFaceWord A n.+1 (firstDepth n.+1) c)) (wskip a (wid n.+1))
      = wcomp (wskip a (wid n.+2)) (depthFaceWord A n.+1 (firstDepth n.+1) c)).
    rewrite wcomp_keep_skip, wcomp_skip, wcompIdr, wcompIdl. now reflexivity.
  - change (wcomp (wkeep (depthFaceWord A n.+1 {| depth := j.+1; depthBound := hj |} c)) (wskip a (wid n.+1))
      = wcomp (wskip a (wid n.+2)) (depthFaceWord A n.+1 {| depth := j.+1; depthBound := hj |} c)).
    rewrite wcomp_keep_skip, wcomp_skip, wcompIdr, wcompIdl. now reflexivity.
  - change (wkeep (wcomp (depthFaceWord A n.+1 (nextDepth {| depth := j; depthBound := ⇓ hj |}) c)
      (depthFaceWord A n {| depth := i; depthBound := ⇓ hi |} a))
      = wkeep (wcomp (depthFaceWord A n.+1 (weakenDepth {| depth := i; depthBound := ⇓ hi |}) a)
      (depthFaceWord A n {| depth := j; depthBound := ⇓ hj |} c))).
    apply f_equal. now exact (IH {| depth := i; depthBound := ⇓ hi |}
      {| depth := j; depthBound := ⇓ hj |} (⇓ hij) a c).
Qed.
Lemma matchingPairwiseLaw N (F: Diagram)
  (b: Reedy.MatchingObject A (presheafDiagram F N)):
  PairwiseBoundaryLaw N F (matchingRaw N F b).
Proof.
  destruct N as [|[|n]]; [now exact tt|now exact tt|].
  intros i j hij a c.
  pose proof (b.2 (Some None) None (depthFaceWord A n i a)
    (depthFaceWord A n.+1 (nextDepth j) c)) as h1.
  pose proof (b.2 (Some None) None (depthFaceWord A n j c)
    (depthFaceWord A n.+1 (weakenDepth i) a)) as h2.
  change (F.(fhom) (depthFaceWord A n i a) (matchingRaw n.+2 F b (nextDepth j) c)
    = b.1 (Some None) (wcomp (depthFaceWord A n.+1 (nextDepth j) c)
      (depthFaceWord A n i a))) in h1.
  change (F.(fhom) (depthFaceWord A n j c) (matchingRaw n.+2 F b (weakenDepth i) a)
    = b.1 (Some None) (wcomp (depthFaceWord A n.+1 (weakenDepth i) a)
      (depthFaceWord A n j c))) in h2.
  rewrite (depthFaceExchange n i j hij a c) in h1.
  now exact (h1 • eq_sym h2).
Defined.

Definition PairwiseBoundary N (F: Diagram): Type :=
  {b: RawBoundary N F &T PairwiseBoundaryLaw N F b}.
Lemma pairwiseBoundaryLawProp N (F: Diagram) b (h h': PairwiseBoundaryLaw N F b): h = h'.
Proof.
  destruct N as [|[|n]]; try (destruct h,h'; now reflexivity).
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply Funext.spropFunext; intro hij.
  repeat (apply functional_extensionality_dep; intro). now apply (F.(fobj) n).(UIP).
Qed.
Definition pairwiseToMatching N (F: Diagram) (b: PairwiseBoundary N F):
  Reedy.MatchingObject A (presheafDiagram F N) :=
  boundaryMatching N F b.1 (pairwiseBoundaryLaws N F b.1 b.2).
Definition matchingToPairwise N (F: Diagram) (b: Reedy.MatchingObject A (presheafDiagram F N)):
  PairwiseBoundary N F := (matchingRaw N F b; matchingPairwiseLaw N F b).
Lemma pairwiseMatchingRet N (F: Diagram) (b: PairwiseBoundary N F):
  matchingToPairwise N F (pairwiseToMatching N F b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - destruct N as [|N]; [destruct b as [[] h]; now reflexivity|].
    apply functional_extensionality_dep; intro i.
    apply functional_extensionality_dep; intro a. now apply boundaryEvalFace.
  - now apply pairwiseBoundaryLawProp.
Qed.
Lemma pairwiseMatchingSec N (F: Diagram) (b: Reedy.MatchingObject A (presheafDiagram F N)):
  pairwiseToMatching N F (matchingToPairwise N F b) = b.
Proof.
  destruct N as [|N].
  - apply Reedy.matchingExt; now intros [].
  - apply matchingFacesExt; intros i a. now apply boundaryEvalFace.
Qed.
Definition pairwiseMatchingEquiv N (F: Diagram):
  Equiv (PairwiseBoundary N F) (Reedy.MatchingObject A (presheafDiagram F N)) :=
  qinvEquiv (pairwiseToMatching N F) (matchingToPairwise N F)
    (pairwiseMatchingRet N F) (pairwiseMatchingSec N F).

Lemma pairwiseMatchingFace n (F: Diagram) (b: PairwiseBoundary n.+1 F) i a:
  (pairwiseMatchingEquiv n.+1 F b).1 None (depthFaceWord A n i a) = b.1 i a.
Proof. now apply boundaryEvalFace. Defined.

End Boundary.

(** The same boundary description for a finite diagram uses its actual
    highest cell set. The coskeleton supplies the ambient functor without
    changing the finite cells or their restriction maps up to equivalence. *)
Section FiniteBoundary.
Context (A: HSet).

Lemma finiteMatchingFacesExt n (D: Reedy.Diagram A n.+1)
  (b c: Reedy.MatchingObject A D)
  (h: forall i a, b.1 None (depthFaceWord A n i a)
    = c.1 None (depthFaceWord A n i a)): b = c.
Proof.
  apply Reedy.matchingExt; intros j u.
  destruct (properFaceFactor A n (rank j) (⇓ (rankBound j)) u) as [i [a [v e]]].
  rewrite e.
  now exact (eq_sym (b.2 j None v (depthFaceWord A n i a))
    • f_equal (D.(Reedy.restrict) (i := j) (j := None) v) (h i a)
    • c.2 j None v (depthFaceWord A n i a)).
Qed.

Definition FiniteRawBoundary N: Reedy.Diagram A N -> Type :=
  match N as N return Reedy.Diagram A N -> Type with
  | 0 => fun _ => unit
  | S n => fun D => FaceDepth n -> A -> D.(Reedy.cells) None
  end.

Definition FinitePairwiseBoundaryLaw N:
  forall D: Reedy.Diagram A N, FiniteRawBoundary N D -> Type :=
  match N as N return forall D: Reedy.Diagram A N, FiniteRawBoundary N D -> Type with
  | 0 => fun _ _ => unit
  | S 0 => fun _ _ => unit
  | S (S n) => fun D b =>
      forall (i j: FaceDepth n), depth i <= depth j -> forall a c,
        D.(Reedy.restrict) (i := Some None) (j := None) (depthFaceWord A n i a)
          (b (nextDepth j) c)
        = D.(Reedy.restrict) (i := Some None) (j := None) (depthFaceWord A n j c)
          (b (weakenDepth i) a)
  end.

Definition FinitePairwiseBoundary N (D: Reedy.Diagram A N): Type :=
  {b: FiniteRawBoundary N D &T FinitePairwiseBoundaryLaw N D b}.

Lemma finitePairwiseBoundaryLawProp N (D: Reedy.Diagram A N)
  b (h h': FinitePairwiseBoundaryLaw N D b): h = h'.
Proof.
  destruct N as [|[|n]]; try (destruct h,h'; now reflexivity).
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply Funext.spropFunext; intro hij.
  repeat (apply functional_extensionality_dep; intro).
  now apply (D.(Reedy.cells) (Some None)).(UIP).
Qed.

Definition finiteRawToCoskeleton N (D: Reedy.Diagram A N):
  FiniteRawBoundary N D -> RawBoundary A N (coskeleton A N D).
Proof.
  destruct N as [|n].
  - now exact (fun _ => tt).
  - now exact (fun b i a => invEq (coskeletonCells A (S n) D None) (b i a)).
Defined.

Definition finiteRawOfCoskeleton N (D: Reedy.Diagram A N):
  RawBoundary A N (coskeleton A N D) -> FiniteRawBoundary N D.
Proof.
  destruct N as [|n].
  - now exact (fun _ => tt).
  - now exact (fun b i a => coskeletonCells A (S n) D None (b i a)).
Defined.

Lemma finitePairwiseToCoskeletonLaw N (D: Reedy.Diagram A N)
  b (h: FinitePairwiseBoundaryLaw N D b):
  PairwiseBoundaryLaw A N (coskeleton A N D) (finiteRawToCoskeleton N D b).
Proof.
  destruct N as [|[|n]]; [now exact tt|now exact tt|].
  intros i j hij a c.
  apply (eqvInj (coskeletonCells A n.+2 D (Some None))).
  change (coskeletonCells A n.+2 D (Some None)
      ((coskeleton A n.+2 D).(fhom) (depthFaceWord A n i a)
        (invEq (coskeletonCells A n.+2 D None) (b (nextDepth j) c)))
    = coskeletonCells A n.+2 D (Some None)
      ((coskeleton A n.+2 D).(fhom) (depthFaceWord A n j c)
        (invEq (coskeletonCells A n.+2 D None) (b (weakenDepth i) a)))).
  rewrite 2 (coskeletonCellsNatural A n.+2 D (Some None) None), 2 secEq.
  now exact (h i j hij a c).
Qed.

Lemma finitePairwiseOfCoskeletonLaw N (D: Reedy.Diagram A N)
  b (h: PairwiseBoundaryLaw A N (coskeleton A N D) b):
  FinitePairwiseBoundaryLaw N D (finiteRawOfCoskeleton N D b).
Proof.
  destruct N as [|[|n]]; [now exact tt|now exact tt|].
  intros i j hij a c.
  change (D.(Reedy.restrict) (i := Some None) (j := None) (depthFaceWord A n i a)
      (coskeletonCells A n.+2 D None (b (nextDepth j) c))
    = D.(Reedy.restrict) (i := Some None) (j := None) (depthFaceWord A n j c)
      (coskeletonCells A n.+2 D None (b (weakenDepth i) a))).
  rewrite <- 2 (coskeletonCellsNatural A n.+2 D (Some None) None).
  now exact (f_equal (coskeletonCells A n.+2 D (Some None)) (h i j hij a c)).
Qed.

Definition finitePairwiseToCoskeleton N (D: Reedy.Diagram A N)
  (b: FinitePairwiseBoundary N D): PairwiseBoundary A N (coskeleton A N D) :=
  (finiteRawToCoskeleton N D b.1; finitePairwiseToCoskeletonLaw N D b.1 b.2).

Definition finitePairwiseOfCoskeleton N (D: Reedy.Diagram A N)
  (b: PairwiseBoundary A N (coskeleton A N D)): FinitePairwiseBoundary N D :=
  (finiteRawOfCoskeleton N D b.1; finitePairwiseOfCoskeletonLaw N D b.1 b.2).

Lemma finitePairwiseCoskeletonRet N (D: Reedy.Diagram A N)
  (b: FinitePairwiseBoundary N D):
  finitePairwiseOfCoskeleton N D (finitePairwiseToCoskeleton N D b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - destruct N as [|n].
    + now destruct b as [[] h].
    + apply functional_extensionality_dep; intro i.
      apply functional_extensionality_dep; intro a. now apply secEq.
  - now apply finitePairwiseBoundaryLawProp.
Qed.

Lemma finitePairwiseCoskeletonSec N (D: Reedy.Diagram A N)
  (b: PairwiseBoundary A N (coskeleton A N D)):
  finitePairwiseToCoskeleton N D (finitePairwiseOfCoskeleton N D b) = b.
Proof.
  unshelve refine (eq_existT_curried _ _).
  - destruct N as [|n].
    + now destruct b as [[] h].
    + apply functional_extensionality_dep; intro i.
      apply functional_extensionality_dep; intro a. now apply retEq.
  - now apply pairwiseBoundaryLawProp.
Qed.

Definition finitePairwiseCoskeletonEquiv N (D: Reedy.Diagram A N):
  Equiv (FinitePairwiseBoundary N D) (PairwiseBoundary A N (coskeleton A N D)) :=
  qinvEquiv (finitePairwiseToCoskeleton N D) (finitePairwiseOfCoskeleton N D)
    (finitePairwiseCoskeletonRet N D) (finitePairwiseCoskeletonSec N D).

Definition finitePairwiseMatchingEquiv N (D: Reedy.Diagram A N):
  Equiv (FinitePairwiseBoundary N D) (Reedy.MatchingObject A D) :=
  compEquiv (finitePairwiseCoskeletonEquiv N D)
    (compEquiv (pairwiseMatchingEquiv A N (coskeleton A N D))
      (coskeletonMatching A N D)).

Lemma finitePairwiseMatchingFace n (D: Reedy.Diagram A n.+1)
  (b: FinitePairwiseBoundary n.+1 D) i a:
  (finitePairwiseMatchingEquiv n.+1 D b).1 None (depthFaceWord A n i a) = b.1 i a.
Proof.
  change (coskeletonCells A n.+1 D None
    ((pairwiseMatchingEquiv A n.+1 (coskeleton A n.+1 D)
      (finitePairwiseToCoskeleton n.+1 D b)).1 None (depthFaceWord A n i a)) = b.1 i a).
  rewrite pairwiseMatchingFace.
  now apply secEq.
Defined.

End FiniteBoundary.
