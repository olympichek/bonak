(** Shifted diagrams: indices raised by one rank, kept words, the shift and
    base diagrams of a diagram, case analysis of words into the shifted rank,
    matching values recombined from the kept and top faces, and the kept
    boundary of a cell. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat
  Logic.Eqdep_dec.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Funext Notation RewLemmas
  FinitePrefix.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas LocallyDiscrete
  LocallyDiscretePseudofunctor PseudofunctorOps.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Reedy.Gpd Require Import Reedy Matching.

Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations FinitePrefix.

(** The coordinate shift and top-face maps of finite coherent diagrams. *)

Fixpoint raiseIndex {n}: Index n -> Index (S n) :=
  match n as n return Index n -> Index (S n) with
  | 0 => fun i => match i with end
  | S n => fun i =>
      match i with None => None | Some j => Some (raiseIndex j) end
  end.

Lemma rankRaise {n} (i: Index n): rank (raiseIndex i) = S (rank i).
Proof.
  induction n as [|n IH]; [now destruct i|].
  destruct i as [i|]; [now exact (IH i)|now reflexivity].
Defined.

Fixpoint zeroIndex n: Index (S n) :=
  match n with 0 => None | S n => Some (zeroIndex n) end.

Lemma rankZero n: rank (zeroIndex n) = 0.
Proof. now induction n. Defined.

Fixpoint splitIndex n: Index (S n) -> unit + Index n :=
  match n as n return Index (S n) -> unit + Index n with
  | 0 => fun i => match i with None => inl tt | Some j => match j with end end
  | S n => fun i =>
      match i with
      | None => inr None
      | Some j =>
          match splitIndex n j with inl _ => inl tt | inr k => inr (Some k) end
      end
  end.

Definition joinIndex {n} (i: unit + Index n): Index (S n) :=
  match i with inl _ => zeroIndex n | inr j => raiseIndex j end.

Lemma joinSplitIndex n (i: Index (S n)): joinIndex (splitIndex n i) = i.
Proof.
  induction n as [|n IH].
  - now destruct i as [[]|].
  - destruct i as [i|]; [|now reflexivity].
    cbn [splitIndex].
    specialize (IH i).
    destruct (splitIndex n i) as [[]|j]; cbn [joinIndex] in IH |- *;
      now exact (f_equal Some IH).
Defined.

Definition indexView {n} (i: Index (S n)):
  (i = zeroIndex n) + {j: Index n &T i = raiseIndex j}.
Proof.
  pose proof (joinSplitIndex n i) as e.
  destruct (splitIndex n i) as [[]|j]; cbn [joinIndex] in e.
  - now left; symmetry.
  - now right; exact (j; eq_sym e).
Defined.

Definition castWord {A: HSet} {i j k l: nat}
  (p: i = k) (q: j = l) (f: Word A i j): Word A k l :=
  match p, q with eq_refl, eq_refl => f end.

Lemma castWordId {A: HSet} {i j: nat} (p: i = j):
  castWord (A := A) p p (wid i) = wid j.
Proof. now destruct p. Defined.

Lemma castWordComp {A: HSet} {i j k i' j' k': nat}
  (p: i = i') (q: j = j') (r: k = k')
  (f: Word A i j) (g: Word A j k):
  wcomp (castWord q r g) (castWord p q f) = castWord p r (wcomp g f).
Proof. now destruct p, q, r. Defined.

Definition keepWord {A: HSet} {n} {i j: Index n}
  (f: Word A (rank i) (rank j)): Word A (rank (raiseIndex i)) (rank (raiseIndex j)) :=
  castWord (eq_sym (rankRaise i)) (eq_sym (rankRaise j)) (wkeep f).

Definition keepToTop {A: HSet} {n} {i: Index n}
  (f: Word A (rank i) n): Word A (rank (raiseIndex i)) (S n) :=
  castWord (eq_sym (rankRaise i)) eq_refl (wkeep f).

Lemma keepWordId {A: HSet} {n} (i: Index n):
  keepWord (A := A) (wid (rank i)) = wid (rank (raiseIndex i)).
Proof.
  unfold keepWord.
  change (castWord (A := A) (eq_sym (rankRaise i)) (eq_sym (rankRaise i))
    (wid (S (rank i))) = wid (rank (raiseIndex i))).
  now apply castWordId.
Defined.

Lemma keepWordComp {A: HSet} {n} {i j k: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)):
  wcomp (keepWord g) (keepWord f) = keepWord (wcomp g f).
Proof.
  unfold keepWord. rewrite castWordComp.
  now rewrite wcomp_keep_keep.
Defined.

Lemma keepToTopComp {A: HSet} {n} {i j: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  wcomp (keepToTop g) (keepWord f) = keepToTop (wcomp g f).
Proof.
  unfold keepToTop, keepWord. rewrite castWordComp.
  now rewrite wcomp_keep_keep.
Defined.

Definition shiftFunctor (A: HSet) n: Functor (PrefixCategory A n) (PrefixCategory A (S n)) := {|
  fobj := raiseIndex;
  fhom i j f := keepWord (i := j) (j := i) f;
  fid i := keepWordId i;
  fcomp i j k f g := eq_sym (keepWordComp g f);
|}.

Definition pullbackDiagram {C D: Category} (F: Functor C D) (X: PathDiagramFamily D):
  PathDiagramFamily C :=
  contractPseudofunctor (composePseudofunctor
    (structureMapPseudofunctor (locallyDiscreteFunctor F)) (expandPseudofunctor X)).

Definition shiftDiagram {A: HSet} {n} (X: Diagram A (S n)): Diagram A n :=
  pullbackDiagram (shiftFunctor A n) X.

Definition baseDiagram {A: HSet} {n} (X: Diagram A (S n)): Diagram A n :=
  truncateDiagram X.

Definition topFaceWord {A: HSet} {n} (i: Index n) (a: A):
  Word A (rank i) (rank (raiseIndex i)) :=
  castWord eq_refl (eq_sym (rankRaise i)) (wskip a (wid (rank i))).

Lemma topFaceWordNatural {A: HSet} {n} {i j: Index n}
  (f: Word A (rank i) (rank j)) (a: A):
  wcomp (keepWord f) (topFaceWord i a) = wcomp (topFaceWord j a) f.
Proof.
  unfold keepWord, topFaceWord.
  rewrite castWordComp.
  change (castWord eq_refl (eq_sym (rankRaise j))
      (wcomp (wkeep f) (wskip a (wid (rank i))))
    = wcomp (castWord eq_refl (eq_sym (rankRaise j)) (wskip a (wid (rank j))))
      (castWord eq_refl eq_refl f)).
  rewrite castWordComp.
  now rewrite wcomp_keep_skip, wcomp_skip, wcompIdr, wcompIdl.
Defined.

Definition topFace {A: HSet} {n} (X: Diagram A (S n)) (a: A) (i: Index n):
  cells (shiftDiagram X) i -> cells (baseDiagram X) i :=
  restrict X (i := Some i) (j := raiseIndex i) (topFaceWord i a).

Lemma shiftRestrictComp {A: HSet} {n} (X: Diagram A (S n))
  {i j k: Index n} (f: Word A (rank i) (rank j))
  (g: Word A (rank j) (rank k)) (x: cells (shiftDiagram X) k):
  restrictComp (shiftDiagram X) f g x =
    restrictComp X (keepWord f) (keepWord g) x
      • f_equal (fun w => restrict X (i := raiseIndex i) (j := raiseIndex k) w x)
          (keepWordComp f g).
Proof.
  unfold restrictComp, shiftDiagram, diagramData, pullbackDiagram.
  cbn [contractPseudofunctor composePseudofunctor structureMapPseudofunctor
    expandPseudofunctor pfStr psStr contractPsf contractData
    pathData pcomp psData composePsfData psComp psfData expandPsf expandData
    structureMapData locallyDiscreteFunctor f2hom f2comp1 shiftFunctor fhom fcomp].
  cbn.
  apply f_equal. apply f_equal.
  now apply (wordSet (A := A) (rank (raiseIndex i)) (rank (raiseIndex k))).(UIP).
Defined.

Lemma shiftRestrictId {A: HSet} {n} (X: Diagram A (S n))
  (i: Index n) (x: cells (shiftDiagram X) i):
  restrictId (shiftDiagram X) i x =
    f_equal (fun w => restrict X (i := raiseIndex i) (j := raiseIndex i) w x)
      (keepWordId i) • restrictId X (raiseIndex i) x.
Proof.
  unfold restrictId, shiftDiagram, diagramData, pullbackDiagram, pidPt.
  cbn [contractPseudofunctor composePseudofunctor structureMapPseudofunctor
    expandPseudofunctor pfStr psStr contractPsf contractData
    pathData pid psData composePsfData psUnit psfData expandPsf expandData
    structureMapData locallyDiscreteFunctor f2hom f2id1 shiftFunctor fhom fid].
  cbn.
  unfold happly.
  etransitivity.
  - now exact (f_equal__functional_extensionality_dep_good _ x).
  - rewrite idTo2Point.
    apply f_equal2.
    + apply f_equal.
      now apply (wordSet (A := A) (rank (raiseIndex i)) (rank (raiseIndex i))).(UIP).
    + now reflexivity.
Defined.

Definition keepMatching {A: HSet} {n} (X: Diagram A (S n))
  (b: MatchingObject X): MatchingObject (shiftDiagram X) :=
  matchingMap (shiftDiagram
    (extendByMatchingMap A X gunit (fun _ => b))) tt.

Lemma keepMatchingPath {A: HSet} {n} (X: Diagram A (S n))
  (b: MatchingObject X) {i j: Index n}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  matchingPath (keepMatching X b) f g =
    matchingPath b (keepWord f) (keepToTop g)
      • f_equal (matchingValue b (raiseIndex i)) (keepToTopComp f g).
Proof.
  change (restrictComp
      (shiftDiagram (extendByMatchingMap A X gunit (fun _ => b)))
      (i := Some i) (j := Some j) (k := None) f g tt =
      matchingPath b (keepWord f) (keepToTop g)
        • f_equal (matchingValue b (raiseIndex i)) (keepToTopComp f g)).
  rewrite shiftRestrictComp.
  apply f_equal. apply f_equal.
  now apply (wordSet (A := A) (rank (raiseIndex i)) (S n)).(UIP).
Defined.

(** Keeping a cell boundary is its boundary in the shifted diagram.
    The target matching types agree by conversion, including their unit
    and compositor data. *)
Lemma keepBoundary {A: HSet} {n} (D: Diagram A (S (S n))) (x: cells D None):
  keepMatching (truncateDiagram D) (matchingMap D x)
    = matchingMap (shiftDiagram D) x.
Proof.
  apply (matchingExt (shiftDiagram (truncateDiagram D))
    (keepMatching (truncateDiagram D) (matchingMap D x))
    (matchingMap (shiftDiagram D) x) eq_refl).
  apply functional_extensionality_dep; intro i.
  apply functional_extensionality_dep; intro j.
  apply functional_extensionality_dep; intro f.
  apply functional_extensionality_dep; intro g.
  change (matchingPath (keepMatching (truncateDiagram D) (matchingMap D x)) f g
    = matchingPath (matchingMap (shiftDiagram D) x) f g).
  rewrite keepMatchingPath.
  change (restrictComp D (i := Some (raiseIndex i)) (j := Some (raiseIndex j))
      (k := None) (keepWord f) (keepToTop g) x
      • f_equal
        (fun w => restrict D (i := Some (raiseIndex i)) (j := None) w x)
        (keepToTopComp f g)
    = restrictComp (shiftDiagram D) (i := Some i) (j := Some j) (k := None) f g x).
  rewrite shiftRestrictComp.
  apply f_equal. apply f_equal.
  now apply (wordSet (A := A) (rank (raiseIndex i)) (S n)).(UIP).
Defined.

(** Constructor cases for composable words in a shifted finite prefix. *)

Definition mixedWord {A: HSet} {n} {i j: Index n} (a: A)
  (f: Word A (rank i) (rank j)):
  Word A (@rank (S n) (Some i)) (rank (raiseIndex j)) :=
  castWord eq_refl (eq_sym (rankRaise j)) (wskip a f).

Lemma mixedWordFactor {A: HSet} {n} {i j: Index n} (a: A)
  (f: Word A (rank i) (rank j)):
  wcomp (topFaceWord j a) f = mixedWord a f.
Proof.
  unfold topFaceWord, mixedWord.
  change (wcomp (castWord eq_refl (eq_sym (rankRaise j)) (wskip a (wid (rank j))))
    (castWord eq_refl eq_refl f) =
    castWord eq_refl (eq_sym (rankRaise j)) (wskip a f)).
  rewrite castWordComp, wcomp_skip, wcompIdl. now reflexivity.
Defined.

Lemma mixedToTopComp {A: HSet} {n} {i j: Index n} (a: A)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  wcomp (keepToTop g) (mixedWord a f) = wskip a (wcomp g f).
Proof.
  unfold keepToTop, mixedWord.
  rewrite castWordComp. now rewrite wcomp_keep_skip.
Defined.

Lemma mixedWordComp {A: HSet} {n} {i j k: Index n} (a: A)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)):
  wcomp (keepWord g) (mixedWord a f) = mixedWord a (wcomp g f).
Proof.
  unfold keepWord, mixedWord. rewrite castWordComp.
  now rewrite wcomp_keep_skip.
Defined.

Lemma mixedWordCompRetained {A: HSet} {n} {i j k: Index n} (a: A)
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k)):
  wcomp (mixedWord a g) f = mixedWord a (wcomp g f).
Proof.
  unfold mixedWord.
  change (wcomp (castWord eq_refl (eq_sym (rankRaise k)) (wskip a g))
    (castWord eq_refl eq_refl f) =
    castWord eq_refl (eq_sym (rankRaise k)) (wskip a (wcomp g f))).
  rewrite castWordComp, wcomp_skip. now reflexivity.
Defined.

Local Definition indexEqDec {n} (i j: Index n): {i = j} + {i <> j}.
Proof.
  destruct (Nat.eq_dec (rank i) (rank j)) as [e|e].
  - now left; apply rankInjective.
  - right. intro h. now apply e; exact (f_equal (@rank n) h).
Defined.

Local Definition indexSet n: HSet := {|
  Dom := Index n; UIP := fun i j => @UIP_dec (Index n) (@indexEqDec n) i j;
|}.

Local Definition IndexedWords (A: HSet) n m: HSet :=
  hsigT (A := indexSet n) (fun i => wordSet (A := A) (rank i) m).

Local Lemma indexedWordsSecond {A: HSet} {n m} {i: Index n}
  {f g: Word A (rank i) m} (p: ((i; f): IndexedWords A n m) = (i; g)): f = g.
Proof.
  pose proof (projT2_eq p) as e.
  change ((rew [fun k: Index n => Word A (rank k) m] (projT1_eq p) in f) = g) in e.
  now exact (eq_rect (projT1_eq p)
    (fun q => (rew [fun k: Index n => Word A (rank k) m] q in f) = g)
    e eq_refl (@UIP (indexSet n) i i (projT1_eq p) eq_refl)).
Defined.

Local Lemma raiseIndexInjective {n} (i j: Index n): raiseIndex i = raiseIndex j -> i = j.
Proof.
  intro e. apply rankInjective.
  pose proof (f_equal (@rank (S n)) e) as h.
  rewrite 2 rankRaise in h. now injection h.
Defined.

Local Lemma castWordInjective {A: HSet} {i j k l} (p: i = k) (q: j = l)
  (f g: Word A i j): castWord p q f = castWord p q g -> f = g.
Proof. now destruct p, q. Defined.

Local Lemma castWordCancel {A: HSet} {i j k l} (p: i = k) (q: j = l)
  (f: Word A i j): castWord (eq_sym p) (eq_sym q) (castWord p q f) = f.
Proof. now destruct p, q. Defined.

Local Lemma castWordSeparate {A: HSet} {i j k l} (p: i = k) (q: j = l)
  (f: Word A i j): castWord eq_refl q (castWord p eq_refl f) = castWord p q f.
Proof. now destruct p, q. Defined.

Local Lemma castWordTargetUncast {A: HSet} {i j k l} (p: i = k) (q: l = j)
  (f: Word A i j):
  castWord eq_refl q (castWord p (eq_sym q) f) = castWord p eq_refl f.
Proof. now destruct p, q. Defined.

Local Definition wordTag {A: HSet} {i n} (f: Word A i (S n)): bool :=
  match f with inl _ => true | inr _ => false end.

Local Lemma wordTagCast {A: HSet} {i k n} (p: i = k) (f: Word A i (S n)):
  wordTag (castWord p eq_refl f) = wordTag f.
Proof. now destruct p. Defined.

Local Definition WordTail (A: HSet) i n: Type :=
  match i return Type with 0 => Empty_set | S i => Word A i n end.
Local Definition keepTail {A: HSet} {i k n} (p: i = S k) (f: WordTail A i n):
  Word A k n := rew [fun i => WordTail A i n] p in f.

Local Lemma keepTailWord {A: HSet} {i k n} (p: i = S k) (f: WordTail A i n):
  castWord (eq_sym p) eq_refl (wkeep (keepTail p f)) =
    @inr (A * Word A i n) (WordTail A i n) f.
Proof. now subst i. Defined.

Local Lemma keepToTopInjective {A: HSet} {n} {i: Index n}
  (f g: Word A (rank i) n): keepToTop f = keepToTop g -> f = g.
Proof.
  unfold keepToTop. intro e. apply castWordInjective in e. now injection e.
Defined.

Local Lemma keepWordInjective {A: HSet} {n} {i j: Index n}
  (f g: Word A (rank i) (rank j)): keepWord f = keepWord g -> f = g.
Proof.
  unfold keepWord. intro e. apply castWordInjective in e. now injection e.
Defined.

Local Lemma constructorFiberProp {C: Type} {D: HSet} (f: C -> D)
  (inj: forall x y, f x = f y -> x = y) (d: D)
  (u v: {c: C &T f c = d}): u = v.
Proof.
  destruct u as [u p], v as [v q].
  destruct (inj u v (p • eq_sym q)). apply f_equal. now apply D.(UIP).
Defined.

Section TopWords.
Context {A: HSet} {n: nat}.
Local Definition TopCode: Type :=
  {i: Index (S n) &T {a: A &T Word A (rank i) n}} +
  {i: Index n &T Word A (rank i) n}.
Local Definition topCodeWord (c: TopCode): IndexedWords A (S n) (S n) :=
  match c with
  | inl (i; (a; f)) => (i; wskip a f)
  | inr (i; f) => (raiseIndex i; keepToTop f)
  end.

Local Lemma topCodeInjective (c d: TopCode): topCodeWord c = topCodeWord d -> c = d.
Proof.
  destruct c as [[i [a f]]|[i f]], d as [[j [b g]]|[j g]]; intro e.
  - pose proof (projT1_eq e) as h. cbn in h. destruct h.
    pose proof (indexedWordsSecond e) as h. injection h as ha hf. now destruct ha, hf.
  - pose proof (f_equal (fun z: IndexedWords A (S n) (S n) => wordTag z.2) e) as h.
    change (true = wordTag (keepToTop g)) in h.
    unfold keepToTop in h. rewrite wordTagCast in h. now discriminate.
  - pose proof (f_equal (fun z: IndexedWords A (S n) (S n) => wordTag z.2) e) as h.
    change (wordTag (keepToTop f) = true) in h.
    unfold keepToTop in h. rewrite wordTagCast in h. now discriminate.
  - pose proof (raiseIndexInjective i j (projT1_eq e)) as h. destruct h.
    pose proof (keepToTopInjective f g (indexedWordsSecond e)) as h. now destruct h.
Defined.

Local Definition topWordView (i: Index (S n)) (f: Word A (rank i) (S n)):
  {c: TopCode &T topCodeWord c = (i; f)}.
Proof.
  destruct f as [[a f]|f].
  - now exact (inl (i; (a; f)); eq_refl).
  - destruct (indexView i) as [e|[j e]]; subst i.
    + exfalso. revert f. rewrite rankZero. now intros [].
    + exists (inr (j; keepTail (rankRaise j) f)).
      apply (eq_existT_curried eq_refl). now apply keepTailWord.
Defined.

Definition topWordElim
  (P: forall (i: Index (S n)), Word A (rank i) (S n) -> Type)
  (skip: forall i a f, P i (wskip a f))
  (keep: forall i f, P (raiseIndex i) (keepToTop f))
  (i: Index (S n)) (f: Word A (rank i) (S n)): P i f.
Proof.
  destruct (topWordView i f) as [c e].
  refine (rew [fun z: IndexedWords A (S n) (S n) => P z.1 z.2] e in _).
  destruct c as [[j [a g]]|[j g]].
  - now exact (skip j a g).
  - now exact (keep j g).
Defined.

Lemma topWordElimSkip
  (P: forall (i: Index (S n)), Word A (rank i) (S n) -> Type)
  (skip: forall i a f, P i (wskip a f))
  (keep: forall i f, P (raiseIndex i) (keepToTop f)) i a f:
  topWordElim P skip keep i (wskip a f) = skip i a f.
Proof.
  unfold topWordElim.
  rewrite (constructorFiberProp topCodeWord topCodeInjective _
    (topWordView i (wskip a f)) (inl (i; (a; f)); eq_refl)). now reflexivity.
Defined.

Lemma topWordElimKeep
  (P: forall (i: Index (S n)), Word A (rank i) (S n) -> Type)
  (skip: forall i a f, P i (wskip a f))
  (keep: forall i f, P (raiseIndex i) (keepToTop f)) i f:
  topWordElim P skip keep (raiseIndex i) (keepToTop f) = keep i f.
Proof.
  unfold topWordElim.
  rewrite (constructorFiberProp topCodeWord topCodeInjective _
    (topWordView (raiseIndex i) (keepToTop f)) (inr (i; f); eq_refl)). now reflexivity.
Defined.
End TopWords.

Section RaisedWords.
Context {A: HSet} {n: nat} (j: Index n).
Local Definition RaisedCode: Type :=
  {i: Index n &T {a: A &T Word A (rank i) (rank j)}} +
  {i: Index n &T Word A (rank i) (rank j)}.
Local Definition raisedCodeWord (c: RaisedCode): IndexedWords A (S n) (rank (raiseIndex j)) :=
  match c with
  | inl (i; (a; f)) => (Some i; mixedWord a f)
  | inr (i; f) => (raiseIndex i; keepWord f)
  end.

Local Lemma raisedCodeInjective (c d: RaisedCode): raisedCodeWord c = raisedCodeWord d -> c = d.
Proof.
  destruct c as [[i [a f]]|[k f]], d as [[l [b g]]|[l g]]; intro e.
  - pose proof (projT1_eq e) as h. cbn in h. injection h as h. destruct h.
    pose proof (indexedWordsSecond e) as h.
    unfold mixedWord in h. apply castWordInjective in h.
    injection h as ha hf. now destruct ha, hf.
  - pose proof (f_equal (fun z: IndexedWords A (S n) (rank (raiseIndex j)) =>
      wordTag (castWord eq_refl (rankRaise j) z.2)) e) as h.
    change (wordTag (castWord eq_refl (rankRaise j) (mixedWord a f)) =
      wordTag (castWord eq_refl (rankRaise j) (keepWord g))) in h.
    unfold mixedWord, keepWord in h. rewrite 2 castWordTargetUncast, 2 wordTagCast in h.
    now discriminate.
  - pose proof (f_equal (fun z: IndexedWords A (S n) (rank (raiseIndex j)) =>
      wordTag (castWord eq_refl (rankRaise j) z.2)) e) as h.
    change (wordTag (castWord eq_refl (rankRaise j) (keepWord f)) =
      wordTag (castWord eq_refl (rankRaise j) (mixedWord b g))) in h.
    unfold mixedWord, keepWord in h. rewrite 2 castWordTargetUncast, 2 wordTagCast in h.
    now discriminate.
  - pose proof (raiseIndexInjective k l (projT1_eq e)) as h. destruct h.
    pose proof (keepWordInjective f g (indexedWordsSecond e)) as h. now destruct h.
Defined.

Local Definition raisedWordViewAt (i: Index (S n)) (f: Word A (rank i) (S (rank j))):
  {c: RaisedCode &T raisedCodeWord c = (i; castWord eq_refl (eq_sym (rankRaise j)) f)}.
Proof.
  destruct f as [[a f]|f].
  - destruct i as [i|].
    + now exact (inl (i; (a; f)); eq_refl).
    + exfalso. now exact (noWordAbove (rankLt j) f).
  - destruct (indexView i) as [e|[k e]]; subst i.
    + exfalso. revert f. rewrite rankZero. now intros [].
    + exists (inr (k; keepTail (rankRaise k) f)).
      apply (eq_existT_curried eq_refl).
      unfold keepWord. rewrite <- castWordSeparate, keepTailWord. now reflexivity.
Defined.

Local Definition raisedWordView (i: Index (S n)) (f: Word A (rank i) (rank (raiseIndex j))):
  {c: RaisedCode &T raisedCodeWord c = (i; f)}.
Proof.
  pose proof (raisedWordViewAt i (castWord eq_refl (rankRaise j) f)) as v.
  exists v.1. refine (v.2 • _).
  apply (eq_existT_curried eq_refl).
  now exact (castWordCancel eq_refl (rankRaise j) f).
Defined.

Definition raisedWordElim
  (P: forall (i: Index (S n)), Word A (rank i) (rank (raiseIndex j)) -> Type)
  (mixed: forall i a f, P (Some i) (mixedWord a f))
  (keep: forall i f, P (raiseIndex i) (keepWord f))
  (i: Index (S n)) (f: Word A (rank i) (rank (raiseIndex j))): P i f.
Proof.
  destruct (raisedWordView i f) as [c e].
  refine (rew [fun z: IndexedWords A (S n) (rank (raiseIndex j)) => P z.1 z.2] e in _).
  destruct c as [[k [a g]]|[k g]].
  - now exact (mixed k a g).
  - now exact (keep k g).
Defined.

Lemma raisedWordElimMixed
  (P: forall (i: Index (S n)), Word A (rank i) (rank (raiseIndex j)) -> Type)
  (mixed: forall i a f, P (Some i) (mixedWord a f))
  (keep: forall i f, P (raiseIndex i) (keepWord f)) i a f:
  raisedWordElim P mixed keep (Some i) (mixedWord a f) = mixed i a f.
Proof.
  unfold raisedWordElim.
  rewrite (constructorFiberProp raisedCodeWord raisedCodeInjective _
    (raisedWordView (Some i) (mixedWord a f)) (inl (i; (a; f)); eq_refl)). now reflexivity.
Defined.

Lemma raisedWordElimKeep
  (P: forall (i: Index (S n)), Word A (rank i) (rank (raiseIndex j)) -> Type)
  (mixed: forall i a f, P (Some i) (mixedWord a f))
  (keep: forall i f, P (raiseIndex i) (keepWord f)) i f:
  raisedWordElim P mixed keep (raiseIndex i) (keepWord f) = keep i f.
Proof.
  unfold raisedWordElim.
  rewrite (constructorFiberProp raisedCodeWord raisedCodeInjective _
    (raisedWordView (raiseIndex i) (keepWord f)) (inr (i; f); eq_refl)). now reflexivity.
Defined.
End RaisedWords.

Section ComposableWords.
Context {A: HSet} {n: nat}
  (P: forall (i j: Index (S n)), Word A (rank i) (rank j) -> Word A (rank j) (S n) -> Type)
  (skip: forall i j f a g, P i j f (wskip a g))
  (mixed: forall (i j: Index n) a f g, P (Some i) (raiseIndex j) (mixedWord a f) (keepToTop g))
  (keep: forall (i j: Index n) f g, P (raiseIndex i) (raiseIndex j) (keepWord f) (keepToTop g)).

Definition composableWordsElim (i j: Index (S n))
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (S n)): P i j f g :=
  topWordElim (fun j g => forall i f, P i j f g)
    (fun j a g i f => skip i j f a g)
    (fun j g i f => raisedWordElim j (fun i f => P i (raiseIndex j) f (keepToTop g))
      (fun i a f => mixed i j a f g) (fun i f => keep i j f g) i f)
    j g i f.

Lemma composableWordsElimSkip i j f a g:
  composableWordsElim i j f (wskip a g) = skip i j f a g.
Proof. unfold composableWordsElim. now rewrite topWordElimSkip. Defined.

Lemma composableWordsElimMixed i j a f g:
  composableWordsElim (Some i) (raiseIndex j) (mixedWord a f) (keepToTop g) = mixed i j a f g.
Proof. unfold composableWordsElim. rewrite topWordElimKeep. now rewrite raisedWordElimMixed. Defined.

Lemma composableWordsElimKeep i j f g:
  composableWordsElim (raiseIndex i) (raiseIndex j) (keepWord f) (keepToTop g) = keep i j f g.
Proof. unfold composableWordsElim. rewrite topWordElimKeep. now rewrite raisedWordElimKeep. Defined.
End ComposableWords.

(** Assemble the value assignments of a boundary from its two word
    constructors. *)

Local Lemma indexViewRaise {n} (i: Index n): indexView (raiseIndex i) = inr (i; eq_refl).
Proof.
  destruct (indexView (raiseIndex i)) as [e|[j e]].
  - pose proof (f_equal rank e) as h.
    rewrite rankRaise, rankZero in h. now discriminate.
  - assert (h: i = j).
    { apply rankInjective, Nat.succ_inj.
      now exact (eq_sym (rankRaise i) • f_equal rank e • rankRaise j). }
    destruct h.
    rewrite (Eqdep_dec.UIP_dec (@indexEqDec (S n)) e eq_refl). now reflexivity.
Defined.

Definition KeepInput (A: HSet) (n k: nat): Type :=
  match k with 0 => Empty_set | S k => Word A k n end.

Section Values.
Context {A: HSet} {n} (X: Diagram A (S n)).

Definition keptValue (b: MatchingValues (shiftDiagram X)) (i: Index (S n))
  (f: KeepInput A n (rank i)): cells X i.
Proof.
  destruct (indexView i) as [e|[j e]].
  - subst i. now destruct (rew [KeepInput A n] rankZero n in f).
  - subst i.
    now exact (b j (rew [KeepInput A n] rankRaise j in f)).
Defined.

Lemma keptValueRaise (b: MatchingValues (shiftDiagram X)) (i: Index n)
  (f: KeepInput A n (rank (raiseIndex i))):
  keptValue b (raiseIndex i) f = b i (rew [KeepInput A n] rankRaise i in f).
Proof. unfold keptValue. rewrite indexViewRaise. now reflexivity. Defined.

Definition mergeValues (b: MatchingValues (shiftDiagram X)) (y: A -> cells X None):
  MatchingValues X :=
  fun i f => match f with
  | inl (a, g) => restrict X (i := i) (j := None) g (y a)
  | inr g => keptValue b i g
  end.

Local Lemma wordKeepElim {k l} (e: k = S l) (f: Word A l n) {T: Type}
  (skip: forall a: A, Word A k n -> T) (keep: KeepInput A n k -> T):
  (match castWord (eq_sym e) eq_refl (wkeep f) with
  | inl (a, g) => skip a g
  | inr g => keep g
  end) = keep (rew [KeepInput A n] (eq_sym e) in (f: KeepInput A n (S l))).
Proof. now subst k. Defined.

Lemma mergeValuesKeep (b: MatchingValues (shiftDiagram X)) (y: A -> cells X None)
  (i: Index n) (f: Word A (rank i) n):
  mergeValues b y (raiseIndex i) (keepToTop f) = b i f.
Proof.
  unfold mergeValues, keepToTop.
  rewrite wordKeepElim, keptValueRaise, rew_sym_cancel_r. now reflexivity.
Defined.

Definition skippedValueComparison (m: MatchingObject X) (a: A)
  (i: Index (S n)) (f: Word A (rank i) n):
  restrict X (i := i) (j := None) f (skippedTop X m a) = matchingValue m i (wskip a f) :=
  matchingPath m (i := i) (j := None) f (wskip a (wid n))
    • f_equal (matchingValue m i) (skippedWord a f).

Lemma skippedValueSquares (m: MatchingObject X) (a: A)
  (i j: Index (S n)) (f: Word A (rank i) (rank j)) (g: Word A (rank j) n):
  f_equal (restrict X f) (skippedValueComparison m a j g)
    • matchingPath m f (wskip a g)
  = restrictComp X (i := i) (j := j) (k := None) f g (skippedTop X m a)
    • skippedValueComparison m a i (wcomp g f).
Proof.
  unfold skippedValueComparison.
  rewrite eq_trans_map_distr, eqTransAssoc.
  refine (transCongL _ (matchingPathNatural X m f (skippedWord a g)) • _).
  assert (e: f_equal (fun u => wcomp u f) (skippedWord a g) =
    eq_sym (wcompAssoc (wskip a (wid n)) g f) • skippedWord a (wcomp g f)).
  { now apply (wordSet (A := A) (rank i) (S n)).(UIP). }
  rewrite e, eq_trans_map_distr, <- 2 eqTransAssoc.
  refine (transCongR (eqTransAssoc _ _ _) _ • _).
  refine (transCongR (matchingComp m (i := i) (j := j) (k := None)
    f g (wskip a (wid n))) _ • _).
  now apply eqTransAssoc.
Defined.

End Values.

(** The kept boundary of a cell has reflexive matching values. *)

Lemma matchingExtValue {A: HSet} {n: nat} (X: Diagram A n)
  (b c: MatchingObject X) (e: b.1 = c.1)
  (q: rew [MatchingPaths X] e in b.2.1 = c.2.1) i f:
  f_equal (fun z => matchingValue z i f) (matchingExt X b c e q) =
    f_equal (fun v => v i f) e.
Proof.
  destruct b as [bv [bp bl]], c as [cv [cp cl]].
  cbn in e, q |- *.
  destruct e. cbn in q |- *. destruct q.
  unfold matchingExt.
  now destruct (Reedy.matchingLawsHProp X bp bl cl).
Defined.

Lemma keepBoundaryValue {A: HSet} {n: nat}
  (D: Diagram A (S (S n))) (x: cells D None) i f:
  f_equal (fun z => matchingValue z i f) (keepBoundary D x) = eq_refl.
Proof.
  unfold keepBoundary.
  now apply matchingExtValue.
Defined.
