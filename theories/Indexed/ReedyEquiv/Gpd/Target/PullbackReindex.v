(** Reindexing coherent diagrams along composite and shifted source functors:
    casts of padded words, the cells of a shifted prefix, the unshifted and
    zero prefixes, relations between diagram arrows, and the faces of residual
    and cell shifts. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat.
From Bonak.Lib Require Import HSet HGpd SigT Equiv Funext Notation RewLemmas
  FinitePrefix NatLemmas LeSProp PathSquares.
From Bonak.Category Require Import Category CategoryEq.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas IconPath.
From Bonak.Presheaf Require Import νSemiShape WordTensor.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Pseudofunctor.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift Pullback.
From Bonak.Indexed.ReedyEquiv.Gpd.Target Require Import ShiftedPrefix.

Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations FinitePrefix WordTensor.

(** Reindexing coherent diagrams along composite and shifted source functors. *)

Local Lemma castTrans {A: HSet} {i j k l m n: nat}
  (p: i = k) (q: j = l) (r: k = m) (s: l = n) (f: Word A i j):
  wordCast r s (wordCast p q f) = wordCast (p • r) (q • s) f.
Proof. now destruct p, q, r, s. Defined.

Local Lemma castProof {A: HSet} {i j k l: nat}
  (p p': i = k) (q q': j = l) (f: Word A i j):
  wordCast p q f = wordCast p' q' f.
Proof. now destruct (natUIP p p'), (natUIP q q'). Defined.

Local Lemma castKeep {A: HSet} {i j k l: nat}
  (p: i = k) (q: j = l) (f: Word A i j):
  wordCast (f_equal S p) (f_equal S q) (wkeep f) = wkeep (wordCast p q f).
Proof. now destruct p, q. Defined.

Local Lemma castInjective {A: HSet} {i j k l: nat}
  (p: i = k) (q: j = l) (f g: Word A i j):
  wordCast p q f = wordCast p q g -> f = g.
Proof. now destruct p, q. Defined.

Local Lemma paddedCast {A: HSet} (k: nat) {i j i' j': nat}
  (p: i = i') (q: j = j') (f: Word A i j):
  paddedWord k (wordCast p q f) =
    wordCast (f_equal (fun n => n + k) p) (f_equal (fun n => n + k) q)
      (paddedWord k f).
Proof. now destruct p, q. Defined.

Local Lemma tensorKeep {A: HSet} (k: nat) {r s: nat} (f: Word A r s):
  wordCast (Nat.add_succ_r k r) (Nat.add_succ_r k s)
    (tensor (wid k) (wkeep f)) = wkeep (tensor (wid k) f).
Proof.
  induction k as [|k IH].
  - replace (Nat.add_succ_r 0 r) with (@eq_refl nat (S r)) by now apply natUIP.
    replace (Nat.add_succ_r 0 s) with (@eq_refl nat (S s)) by now apply natUIP.
    now reflexivity.
  - replace (Nat.add_succ_r (S k) r) with (f_equal S (Nat.add_succ_r k r))
      by now apply natUIP.
    replace (Nat.add_succ_r (S k) s) with (f_equal S (Nat.add_succ_r k s))
      by now apply natUIP.
    change (wordCast (f_equal S (Nat.add_succ_r k r))
      (f_equal S (Nat.add_succ_r k s)) (wkeep (tensor (wid k) (wkeep f))) =
      wkeep (wkeep (tensor (wid k) f))).
    now rewrite castKeep, IH.
Defined.

Local Lemma paddedKeep {A: HSet} (k: nat) {r s: nat} (f: Word A r s):
  paddedWord k (wkeep f) = wkeep (paddedWord k f).
Proof.
  unfold paddedWord.
  replace (Nat.add_comm k (S r)) with
    (Nat.add_succ_r k r • f_equal S (Nat.add_comm k r)) by now apply natUIP.
  replace (Nat.add_comm k (S s)) with
    (Nat.add_succ_r k s • f_equal S (Nat.add_comm k s)) by now apply natUIP.
  rewrite <- castTrans, tensorKeep. now apply castKeep.
Defined.

Local Lemma paddedSucc {A: HSet} (k: nat) {r s: nat} (f: Word A r s):
  wordCast (Nat.add_succ_r r k) (Nat.add_succ_r s k) (paddedWord (S k) f) =
    wkeep (paddedWord k f).
Proof.
  unfold paddedWord. rewrite castTrans.
  replace (Nat.add_comm (S k) r • Nat.add_succ_r r k) with
    (f_equal S (Nat.add_comm k r)) by now apply natUIP.
  replace (Nat.add_comm (S k) s • Nat.add_succ_r s k) with
    (f_equal S (Nat.add_comm k s)) by now apply natUIP.
  now apply castKeep.
Defined.

Local Lemma paddedZero {A: HSet} {r s: nat} (f: Word A r s):
  wordCast (Nat.add_0_r r) (Nat.add_0_r s) (paddedWord 0 f) = f.
Proof.
  unfold paddedWord. rewrite castTrans.
  replace (Nat.add_comm 0 r • Nat.add_0_r r) with (@eq_refl nat r)
    by now apply natUIP.
  replace (Nat.add_comm 0 s • Nat.add_0_r s) with (@eq_refl nat s)
    by now apply natUIP.
  now reflexivity.
Defined.

Local Lemma wordFamilyTransport {A: HSet} {J: Type} {u v: J -> nat}
  (e: u = v) (i j: J) (f: Word A (u j) (u i)):
  rew [fun o => Word A (o j) (o i)] e in f =
    wordCast (happly e j) (happly e i) f.
Proof. now destruct e. Defined.

Local Lemma wordFunctorEq {A: HSet} {B: Category}
  (U V: Functor B (Op (νSemiShape A)))
  (e: forall i, U.(fobj) i = V.(fobj) i)
  (h: forall i j (f: B.(CHom) i j), wordCast (e j) (e i) (U.(fhom) f) = V.(fhom) f):
  U = V.
Proof.
  apply (functorEq U V (functional_extensionality_dep_good _ _ e)).
  intros i j f.
  refine (wordFamilyTransport (functional_extensionality_dep_good _ _ e)
    i j (U.(fhom) f) • _).
  refine (f_equal2 (fun p q => wordCast p q (U.(fhom) f))
    (f_equal__functional_extensionality_dep_good e j)
    (f_equal__functional_extensionality_dep_good e i) • _).
  now exact (h i j f).
Defined.

Definition shiftPrefixFunctorEq {A: HSet} (p k: nat):
  compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) =
    shiftPrefixFunctor A p (S k).
Proof.
  apply (@wordFunctorEq A (PrefixCategory A p)
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p (S k)) (fun i: Index p =>
    f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))).
  intros i j f.
  change (wordCast
    (f_equal (fun n => n + k) (rankRaise j) • eq_sym (Nat.add_succ_r (rank j) k))
    (f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))
    (paddedWord k (wordCast (eq_sym (rankRaise j)) (eq_sym (rankRaise i)) (wkeep f)))
    = paddedWord (S k) f).
  rewrite paddedCast, castTrans, paddedKeep.
  apply (castInjective (Nat.add_succ_r (rank j) k) (Nat.add_succ_r (rank i) k)).
  rewrite castTrans, paddedSucc.
  now exact (castProof _ eq_refl _ eq_refl _).
Defined.

Local Lemma castGen {A: HSet} {n m: nat}
  (p: n = m) (q: S n = S m) (j: nat) (a: A):
  wordCast p q (wgen n j a) = wgen m j a.
Proof.
  replace q with (f_equal S p) by now apply natUIP.
  now destruct p.
Defined.

Local Lemma tensorIdGen {A: HSet} (k r q: nat) (Hq: q <= r) (a: A):
  wordCast eq_refl (Nat.add_succ_r k r) (tensor (wid k) (wgen r q a)) =
    wgen (k + r) q a.
Proof.
  induction k as [|k IH].
  - replace (Nat.add_succ_r 0 r) with (@eq_refl nat (S r)) by now apply natUIP.
    now reflexivity.
  - replace (Nat.add_succ_r (S k) r) with (f_equal S (Nat.add_succ_r k r))
      by now apply natUIP.
    change (wordCast (f_equal S (@eq_refl nat (k + r)))
      (f_equal S (Nat.add_succ_r k r)) (wkeep (tensor (wid k) (wgen r q a))) =
      wgen (S (k + r)) q a).
    rewrite castKeep, IH. now rewrite (wgenLift (Hq ↕ leR_add_l k) a).
Defined.

Lemma paddedGen {A: HSet} (k r q: nat) (Hq: q <= r) (a: A):
  paddedWord k (wgen r q a) = wgen (r + k) q a.
Proof.
  unfold paddedWord.
  refine (castProof _ (eq_refl • Nat.add_comm k r) _
    (Nat.add_succ_r k r • f_equal S (Nat.add_comm k r)) _ • _).
  rewrite <- castTrans, tensorIdGen by exact Hq.
  now apply castGen.
Defined.

Lemma shiftTopWord {A: HSet} {p: nat} (k: nat) (i: Index p) (a: A):
  wordCast eq_refl
    (f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))
    (paddedWord k (topFaceWord i a)) = residualWord (rank i) (wgen k 0 a).
Proof.
  change (wordCast eq_refl
    (f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))
    (paddedWord k (wordCast eq_refl (eq_sym (rankRaise i)) (wskip a (wid (rank i)))))
    = residualWord (rank i) (wgen k 0 a)).
  rewrite paddedCast, castTrans.
  apply (castInjective eq_refl (Nat.add_succ_r (rank i) k)).
  rewrite castTrans, (residualGen (rank i) k 0 leR_O a).
  refine (castProof _ eq_refl _ eq_refl _ • _).
  cbn [wordCast]. rewrite <- (wgenTop (rank i) a).
  rewrite (paddedGen k (rank i) (rank i) leR_refl a), Nat.add_0_r.
  now reflexivity.
Defined.

Definition diagramIsoEquiv {C: Category} (F: PathDiagramFamily C)
  {i j: C.(CObj)} (e: Iso C i j): Equiv (F.(pfObj) i) (F.(pfObj) j).
Proof.
  pose (D := pathData _ _ F.(pfStr)).
  refine (qinvEquiv (D.(phom) e.(isoHom))
    (D.(phom) (inverse e.(isoInvertible))) _ _).
  - intro x. exact (D.(pcomp) e.(isoHom) (inverse e.(isoInvertible)) x
      • (phomEq D (inverseR e.(isoInvertible)) x • pidPt D i x)).
  - intro x. exact (D.(pcomp) (inverse e.(isoInvertible)) e.(isoHom) x
      • (phomEq D (inverseL e.(isoInvertible)) x • pidPt D j x)).
Defined.

Definition paddedTopNat {A: HSet} (p k: nat) (a: A):
  NatTrans (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p k).
Proof.
  refine {| ncomp i := paddedWord k (topFaceWord i a) |}.
  intros i j f.
  exact (paddedComp k (topFaceWord j a) (keepWord f)
    • (f_equal (paddedWord k) (topFaceWordNatural f a)
      • eq_sym (paddedComp k f (topFaceWord i a)))).
Defined.


Local Lemma idToHomCompWord {A: HSet} {i n m: nat} (e: n = m)
  (f: Word A i n) (g: Word A i m) (h: wordCast eq_refl e f = g):
  wcomp (@idToHom (Op (νSemiShape A)) n m e) g = f.
Proof. destruct e; cbn [wordCast] in h. subst g. now apply wcompIdl. Defined.

Lemma shiftTopNatComp {A: HSet} (p k: nat) (a: A):
  compNatTrans
    (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
      (shiftPrefixFunctorEq p k))
    (residualNat p (wgen k 0 a)) = paddedTopNat p k a.
Proof.
  apply natTransEq; intro i. cbn [compNatTrans ncomp paddedTopNat].
  rewrite natComponent. apply idToHomCompWord.
  replace (f_equal (fun U => U.(fobj) i) (shiftPrefixFunctorEq p k)) with
    (f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))
    by now apply natUIP.
  now apply shiftTopWord.
Defined.

Local Lemma flattenNaturalityAlgebra {T: Type} {a b c d e f: T}
  (p: a = b) (q: e = f) (e1: b = c) (e2: c = d) (e3: f = d) (e0: b = f)
  (h: e1 • (e2 • eq_sym e3) = e0):
  (p • e1) • (e2 • eq_sym (q • e3)) = p • (e0 • eq_sym q).
Proof.
  destruct p, e1, e2, q, e3. cbn in h |- *.
  now rewrite <- h.
Defined.

Local Lemma mappedTriangle {X Y: Type} (f: X -> Y) {a b c d: X}
  (p: a = b) (q: b = c) (r: d = c) (s: a = d)
  (h: p • (q • eq_sym r) = s):
  f_equal f p • (f_equal f q • eq_sym (f_equal f r)) = f_equal f s.
Proof. destruct p, q, r. cbn in h |- *. now rewrite <- h. Defined.

Lemma topFaceNaturalityFlatten {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (a: A) {i j: Index p}
  (f: Word A (rank i) (rank j))
  (x: cells (shiftDiagram (shiftedPrefix (S p) k F)) j):
  topFaceNaturality (shiftedPrefix (S p) k F) a f x =
  pullbackNaturality F
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p k) (paddedTopNat p k a) f x.
Proof.
  unfold topFaceNaturality, pullbackNaturality, shiftedPrefix.
  rewrite 2 pullbackRestrictComp.
  apply flattenNaturalityAlgebra.
  unfold phomEq.
  change (fun w: Word A (rank i) (rank (raiseIndex j)) =>
    (diagramData (pullbackDiagram (shiftPrefixFunctor A (S p) k) F)).(phom)
      (a := raiseIndex j) (b := Some i) w x)
    with (fun w: Word A (rank i) (rank (raiseIndex j)) =>
      (pathData _ _ F.(pfStr)).(phom) (paddedWord k w) x).
  rewrite <- (f_equal_compose
    (@paddedWord A k (rank i) (rank (raiseIndex j)))
    (fun w => (pathData _ _ F.(pfStr)).(phom) w x)).
  apply (@mappedTriangle (Word A (rank i + k) (rank (raiseIndex j) + k))
    (F.(pfObj) (rank i + k)) (fun w => (pathData _ _ F.(pfStr)).(phom) w x)).
  now apply (wordSet (A := A) (rank i + k) (rank (raiseIndex j) + k)).(UIP).
Defined.

Local Definition pathIso {C: Category} {i j: C.(CObj)} (e: i = j): Iso C i j.
Proof.
  refine {| isoHom := idToHom e; isoInvertible := _ |}.
  destruct e. now refine {| inverse := C.(cid) i;
    inverseR := C.(cidl) _; inverseL := C.(cidl) _ |}.
Defined.

(** Moving the retained coordinate into the residual index uses the
    diagram's action on the rank isomorphism, including its unit path. *)
Definition shiftPrefixCell {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  Equiv (F.(pfObj) (S p + k)) (F.(pfObj) (p + S k)) :=
  diagramIsoEquiv F (@pathIso (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k))).

Definition shiftPrefixBridge {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  Equiv (MatchingObject (shiftDiagram (shiftedPrefix (S p) k F)))
    (MatchingObject (shiftedPrefix p (S k) F)) :=
  compEquiv
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F)
    (diagramIsoEquiv (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F)
      (@pathIso (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
        (shiftPrefixFunctorEq p k))).

Local Definition topFaceFlattenSquares {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (a: A)
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F))):
  ComparisonSquares (shiftedPrefix p k F)
    (b := topFaceMatching (shiftedPrefix (S p) k F) a b)
    (c := matchingAction p (Op (νSemiShape A)) F
      (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
      (shiftPrefixFunctor A p k) (paddedTopNat p k a)
      (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b))
    (fun _ _ => eq_refl).
Proof.
  intros i j f g.
  change (eq_refl •
    (eq_sym (eq_sym (pullbackNaturality F
      (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
      (shiftPrefixFunctor A p k) (paddedTopNat p k a) f (matchingValue b j g)))
      • f_equal (topFace (shiftedPrefix (S p) k F) a i) (matchingPath b f g)) =
    (eq_sym (eq_sym (topFaceNaturality (shiftedPrefix (S p) k F) a f
      (matchingValue b j g)))
      • f_equal (topFace (shiftedPrefix (S p) k F) a i) (matchingPath b f g)) • eq_refl).
  rewrite eq_trans_refl_l, eq_trans_refl_r, 2 eq_sym_involutive.
  now exact (transCongR
    (eq_sym (topFaceNaturalityFlatten p k F a (i := i) (j := j) f (matchingValue b j g)))
    (f_equal (topFace (shiftedPrefix (S p) k F) a i) (matchingPath b f g))).
Defined.

Definition topFaceFlatten {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (a: A)
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F))):
  topFaceMatching (shiftedPrefix (S p) k F) a b =
  matchingAction p (Op (νSemiShape A)) F
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p k) (paddedTopNat p k a)
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b) :=
  matchingHomotopy (shiftedPrefix p k F)
    (b := topFaceMatching (shiftedPrefix (S p) k F) a b)
    (c := matchingAction p (Op (νSemiShape A)) F
      (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
      (shiftPrefixFunctor A p k) (paddedTopNat p k a)
      (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b))
    (fun _ _ => eq_refl) (topFaceFlattenSquares p k F a b).

Lemma topFaceFlattenValue {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (a: A)
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F)))
  (i: Index p) (g: Word A (rank i) p):
  f_equal (fun z => matchingValue z i g) (topFaceFlatten p k F a b) = eq_refl.
Proof.
  now exact (matchingHomotopyValue (shiftedPrefix p k F)
    (b := topFaceMatching (shiftedPrefix (S p) k F) a b)
    (c := matchingAction p (Op (νSemiShape A)) F
      (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
      (shiftPrefixFunctor A p k) (paddedTopNat p k a)
      (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b))
    (fun _ _ => eq_refl) (topFaceFlattenSquares p k F a b) i g).
Defined.

Lemma shiftPrefixTopFace {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (a: A)
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F))):
  topFaceMatching (shiftedPrefix (S p) k F) a b =
    residualMatching p F (wgen k 0 a) (shiftPrefixBridge p k F b).
Proof.
  refine (topFaceFlatten p k F a b • _). symmetry.
  refine (matchingComposition p (Op (νSemiShape A)) F
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p (S k)) (shiftPrefixFunctor A p k)
    (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
      (shiftPrefixFunctorEq p k)) (residualNat p (wgen k 0 a))
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b) • _).
  now exact (f_equal (fun α => matchingAction p (Op (νSemiShape A)) F
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p k) α
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b))
    (shiftTopNatComp p k a)).
Defined.

Local Lemma castSkip {A: HSet} {i j k l: nat}
  (p: i = k) (q: j = l) (a: A) (f: Word A i j):
  wordCast p (f_equal S q) (wskip a f) = wskip a (wordCast p q f).
Proof. now destruct p, q. Defined.

Local Lemma tensorCastLeft {A: HSet} {i j k l r s: nat}
  (p: i = k) (q: j = l) (u: Word A i j) (v: Word A r s):
  tensor (wordCast p q u) v =
    wordCast (f_equal (fun n => n + r) p) (f_equal (fun n => n + s) q) (tensor u v).
Proof. now destruct p, q. Defined.

Local Lemma tensorAssoc {A: HSet} {k l r s m n: nat}
  (u: Word A k l) (v: Word A r s) (w: Word A m n):
  wordCast (Nat.add_assoc k r m) (Nat.add_assoc l s n) (tensor u (tensor v w)) =
    tensor (tensor u v) w.
Proof.
  revert k u; induction l as [|l IH]; intros k u.
  - destruct k as [|k]; [|now destruct u].
    replace (Nat.add_assoc 0 r m) with (@eq_refl nat (r + m)) by now apply natUIP.
    replace (Nat.add_assoc 0 s n) with (@eq_refl nat (s + n)) by now apply natUIP.
    now reflexivity.
  - replace (Nat.add_assoc (S l) s n) with (f_equal S (Nat.add_assoc l s n))
      by now apply natUIP.
    destruct u as [[a u]|u].
    + change (wordCast (Nat.add_assoc k r m) (f_equal S (Nat.add_assoc l s n))
        (wskip a (tensor u (tensor v w))) = wskip a (tensor (tensor u v) w)).
      now rewrite castSkip, IH.
    + destruct k as [|k]; [now destruct u|].
      replace (Nat.add_assoc (S k) r m) with (f_equal S (Nat.add_assoc k r m))
        by now apply natUIP.
      change (wordCast (f_equal S (Nat.add_assoc k r m)) (f_equal S (Nat.add_assoc l s n))
        (wkeep (tensor u (tensor v w))) = wkeep (tensor (tensor u v) w)).
      now rewrite castKeep, IH.
Defined.

Local Lemma residualSucc {A: HSet} (r: nat) {k l: nat} (u: Word A k l):
  wordCast (Nat.add_succ_r r k) (Nat.add_succ_r r l)
    (residualWord r (residualWord 1 u)) = residualWord (S r) u.
Proof.
  unfold residualWord. rewrite tensorCastLeft, 2 castTrans.
  rewrite <- tensorAssoc, castTrans.
  now apply castProof.
Defined.

Local Lemma residualRankCast {A: HSet} {r s: nat} (e: r = s)
  {k l: nat} (u: Word A k l):
  wordCast (f_equal (fun n => n + k) e) (f_equal (fun n => n + l) e)
    (residualWord r u) = residualWord s u.
Proof. now destruct e. Defined.

Local Lemma residualRaiseWord {A: HSet} {p: nat} (i: Index p)
  {k l: nat} (u: Word A k l):
  wordCast
    (f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))
    (f_equal (fun n => n + l) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) l))
    (residualWord (rank (raiseIndex i)) u) = residualWord (rank i) (residualWord 1 u).
Proof.
  rewrite <- castTrans, residualRankCast.
  rewrite <- (residualSucc (rank i) u), castTrans.
  refine (castProof _ eq_refl _ eq_refl _).
Defined.

Local Lemma castIdToHomSquare {A: HSet} {i j k l: nat}
  (p: i = k) (q: j = l) (f: Word A i j) (g: Word A k l)
  (h: wordCast p q f = g):
  wcomp f (@idToHom (Op (νSemiShape A)) i k p) =
    wcomp (@idToHom (Op (νSemiShape A)) j l q) g.
Proof.
  destruct p, q; cbn [wordCast] in h. subst g.
  change (wcomp f (wid i) = wcomp (wid j) f).
  now rewrite wcompIdr, wcompIdl.
Defined.

Lemma shiftPrefixResidualNat {A: HSet} (p: nat)
{k l: nat} (u: Word A k l):
  compNatTrans (whiskerLNat (shiftFunctor A p) (residualNat (S p) u))
    (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _ (shiftPrefixFunctorEq p k)) =
  compNatTrans (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _ (shiftPrefixFunctorEq p l))
    (residualNat p (residualWord 1 u)).
Proof.
  apply natTransEq; intro i.
  cbn [compNatTrans ncomp whiskerLNat]. rewrite 2 natComponent.
  apply castIdToHomSquare.
  replace (f_equal (fun U => U.(fobj) i) (shiftPrefixFunctorEq p k)) with
    (f_equal (fun n => n + k) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) k))
    by now apply natUIP.
  replace (f_equal (fun U => U.(fobj) i) (shiftPrefixFunctorEq p l)) with
    (f_equal (fun n => n + l) (rankRaise i) • eq_sym (Nat.add_succ_r (rank i) l))
    by now apply natUIP.
  now apply residualRaiseWord.
Defined.

Lemma residualOneGen {A: HSet} (k q: nat) (Hq: q <= k) (a: A):
  residualWord 1 (wgen k q a) = wgen (S k) (S q) a.
Proof.
  pose proof (residualGen 1 k q Hq a) as h.
  replace (Nat.add_succ_r 1 k) with (@eq_refl nat (S (S k))) in h
    by now apply natUIP.
  now exact h.
Defined.

Definition wholeCellShiftNat (A: HSet) (p: nat):
  NatTrans (wholeCellFunctor A (S p))
    (compFunctor (wholeCellFunctor A 1) (wholeCellFunctor A p)).
Proof.
  refine {| ncomp k := @idToHom (Op (νSemiShape A)) _ _
    (eq_sym (Nat.add_succ_r p k)) |}.
  intros l k u.
  apply castIdToHomSquare.
  change (wordCast (eq_sym (Nat.add_succ_r p k)) (eq_sym (Nat.add_succ_r p l))
    (residualWord (S p) u) = residualWord p (residualWord 1 u)).
  rewrite <- (residualSucc p u), castTrans.
  now apply (castProof _ eq_refl _ eq_refl).
Defined.

Definition shiftedResidualFunctor (A: HSet) (p: nat):
  Functor (Op (νSemiShape A))
    (functorCategory (PrefixCategory A p) (Op (νSemiShape A))).
Proof.
  refine {| fobj k := compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k);
    fhom l k u := whiskerLNat (shiftFunctor A p) (residualNat (S p) u) |}.
  - intro k. apply natTransEq; intro i.
    now exact (residualId (rank (raiseIndex i)) k).
  - intros k l m u v. apply natTransEq; intro i.
    now exact (eq_sym (residualComp (rank (raiseIndex i)) v u)).
Defined.

Definition shiftPrefixResidualTransformation (A: HSet) (p: nat):
  NatTrans (shiftedResidualFunctor A p)
    (compFunctor (wholeCellFunctor A 1) (residualFunctor A p)).
Proof.
  refine {| ncomp k :=
    @idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
      (shiftPrefixFunctorEq p k) |}.
  intros l k u. now exact (shiftPrefixResidualNat p u).
Defined.

Definition rankFunctor (A: HSet) (p: nat):
  Functor (PrefixCategory A p) (Op (νSemiShape A)) := {|
  fobj := @rank p; fhom i j f := f; fid i := eq_refl;
  fcomp i j k f g := eq_refl;
|}.

Definition unshiftedPrefix {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))): Diagram A p :=
  @Build_PathDiagramFamily (PrefixCategory A p) (fun i => F.(pfObj) (rank i))
    (@Build_PathDiagram (PrefixCategory A p) (fun i => F.(pfObj) (rank i))
      (@Build_PathDiagramData (PrefixCategory A p) (fun i => F.(pfObj) (rank i))
        (fun i j f => (pathData _ _ F.(pfStr)).(phom) f)
        (fun i => (pathData _ _ F.(pfStr)).(pid) (rank i))
        (fun i j k f g => (pathData _ _ F.(pfStr)).(pcomp) f g))
      (fun i j f => pathUnitL _ _ F.(pfStr) (rank i) (rank j) f)
      (fun i j f => pathUnitR _ _ F.(pfStr) (rank i) (rank j) f)
      (fun i j k l f g h => pathAssoc _ _ F.(pfStr)
        (rank i) (rank j) (rank k) (rank l) f g h)).

Definition zeroPrefixFunctorEq {A: HSet} (p: nat):
  shiftPrefixFunctor A p 0 = rankFunctor A p.
Proof.
  apply (@wordFunctorEq A (PrefixCategory A p)
    (shiftPrefixFunctor A p 0) (rankFunctor A p)
    (fun i: Index p => Nat.add_0_r (rank i))).
  intros i j f. now apply paddedZero.
Defined.

Definition unshiftedPullbackEq {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  pullbackDiagram (rankFunctor A p) F = unshiftedPrefix p F.
Proof.
  apply (f_equal (@Build_PathDiagramFamily (PrefixCategory A p)
    (fun i => F.(pfObj) (rank i)))).
  apply pathDiagramEqOn.
  assert (ei: (pathData _ _ (pullbackDiagram (rankFunctor A p) F).(pfStr)).(pid) =
    (pathData _ _ (unshiftedPrefix p F).(pfStr)).(pid)).
  { apply functional_extensionality_dep; intro i. apply happlyInj; intro x.
    change (pidPt (pathData _ _ (pullbackDiagram (rankFunctor A p) F).(pfStr)) i x =
      pidPt (pathData _ _ F.(pfStr)) (rank i) x).
    rewrite pullbackIdPoint. now apply eq_trans_refl_l. }
  assert (ec: @pcomp _ _ (pathData _ _ (pullbackDiagram (rankFunctor A p) F).(pfStr)) =
    @pcomp _ _ (pathData _ _ (unshiftedPrefix p F).(pfStr))).
  { repeat (apply functional_extensionality_dep; intro).
    rewrite pullbackCompPoint. now reflexivity. }
  now exact (f_equal2 (fun i c => @Build_PathDiagramData (PrefixCategory A p)
    (fun j => F.(pfObj) (rank j))
    (fun i j f => (pathData _ _ F.(pfStr)).(phom) f) i c) ei ec).
Defined.

Definition zeroPrefixEq {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  shiftedPrefix p 0 F = unshiftedPrefix p F :=
  f_equal (fun U => pullbackDiagram U F) (zeroPrefixFunctorEq p)
    • unshiftedPullbackEq p F.

(** Taking the equality one rank higher makes the boundary comparison
    a direct instance of dependent transport. *)
Definition zeroPrefixBridge {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))):
  Equiv (MatchingObject (shiftedPrefix p 0 F)) (MatchingObject (unshiftedPrefix p F)) :=
  rewEquiv (fun D => MatchingObject D)
    (f_equal (@truncateDiagram A p) (zeroPrefixEq (S p) F)).

Local Lemma boundaryTransport {A: HSet} {p: nat} {X Y: Diagram A (S p)}
  (e: X = Y) (x: cells X None):
  rew [fun D => MatchingObject D] (f_equal (@truncateDiagram A p) e) in
    matchingMap X x =
  matchingMap Y (rew [fun D: Diagram A (S p) => cells D None] e in x).
Proof. now destruct e. Defined.

Lemma zeroPrefixBoundaryTransport {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (x: F.(pfObj) (p + 0)):
  zeroPrefixBridge p F (partialBoundary p F 0 x) =
    matchingMap (unshiftedPrefix (S p) F)
      (eq_rect (shiftedPrefix (S p) 0 F)
        (fun D: Diagram A (S p) => cells D None) x
        (unshiftedPrefix (S p) F) (zeroPrefixEq (S p) F)).
Proof.
  now exact (@boundaryTransport A p (shiftedPrefix (S p) 0 F)
    (unshiftedPrefix (S p) F) (zeroPrefixEq (S p) F) x).
Defined.

Local Lemma fixedDiagramObjects {C: Category} (O: C.(CObj) -> HGpd)
  {S T: PathDiagram C O} (e: S = T) (i: C.(CObj)):
  f_equal (fun D: PathDiagramFamily C => D.(pfObj) i)
    (f_equal (@Build_PathDiagramFamily C O) e) = eq_refl.
Proof. now destruct e. Defined.

Local Lemma unshiftedPullbackCell {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (i: Index p):
  f_equal (fun D: Diagram A p => cells D i) (unshiftedPullbackEq p F) = eq_refl.
Proof.
  unfold unshiftedPullbackEq.
  now apply (@fixedDiagramObjects (PrefixCategory A p)
    (fun j: Index p => F.(pfObj) (rank j))).
Defined.

Lemma zeroPrefixCell {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (i: Index p):
  f_equal (fun D: Diagram A p => cells D i) (zeroPrefixEq p F) =
    f_equal F.(pfObj) (Nat.add_0_r (rank i)).
Proof.
  unfold zeroPrefixEq. rewrite eq_trans_map_distr.
  refine (transCongL _ (unshiftedPullbackCell p F i) • _).
  refine (eq_trans_refl_r _ • _).
  refine (f_equal_compose
    (fun U: Functor (PrefixCategory A p) (Op (νSemiShape A)) => pullbackDiagram U F)
    (fun D: Diagram A p => cells D i) (zeroPrefixFunctorEq p) • _).
  change (f_equal (fun U: Functor (PrefixCategory A p) (Op (νSemiShape A)) =>
    F.(pfObj) (U.(fobj) i)) (zeroPrefixFunctorEq p) =
    f_equal F.(pfObj) (Nat.add_0_r (rank i))).
  refine (eq_sym (f_equal_compose
    (fun U: Functor (PrefixCategory A p) (Op (νSemiShape A)) => U.(fobj) i) F.(pfObj)
    (zeroPrefixFunctorEq p)) • _).
  apply f_equal. now apply natUIP.
Defined.

Lemma zeroPrefixBoundary {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) (x: F.(pfObj) (p + 0)):
  zeroPrefixBridge p F (partialBoundary p F 0 x) =
    matchingMap (unshiftedPrefix (S p) F)
      (rew [fun n => F.(pfObj) n] (Nat.add_0_r p) in x).
Proof.
  refine (zeroPrefixBoundaryTransport p F x • _). apply f_equal.
  refine (rew_map GDom (fun D: Diagram A (S p) => cells D None)
    (zeroPrefixEq (S p) F) x • _).
  refine (f_equal (fun e: F.(pfObj) (p + 0) = F.(pfObj) p =>
    eq_rect (F.(pfObj) (p + 0)) GDom x (F.(pfObj) p) e)
    (zeroPrefixCell (S p) F None) • _).
  now exact (eq_sym (rew_map GDom F.(pfObj) (Nat.add_0_r p) x)).
Defined.

(** A source relation gives an exchange path in a coherent diagram.
    Pullback and coherent maps preserve these paths. *)
Definition diagramRelation {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {i j j' k: C.(CObj)}
  (v: C.(CHom) i j) (u: C.(CHom) j k)
  (v': C.(CHom) i j') (u': C.(CHom) j' k)
  (e: v ⨟ u = v' ⨟ u') (x: O i):
  D.(phom) u (D.(phom) v x) = D.(phom) u' (D.(phom) v' x) :=
  D.(pcomp) v u x • (phomEq D e x • eq_sym (D.(pcomp) v' u' x)).

Lemma diagramRelationEdges {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {i j j' k: C.(CObj)}
  (v V: C.(CHom) i j) (u U: C.(CHom) j k)
  (v' V': C.(CHom) i j') (u' U': C.(CHom) j' k)
  (ev: v = V) (eu: u = U) (ev': v' = V') (eu': u' = U')
  (e: v ⨟ u = v' ⨟ u') (E: V ⨟ U = V' ⨟ U') (x: O i):
  (phomEq D eu (D.(phom) v x) • f_equal (D.(phom) U) (phomEq D ev x))
    • diagramRelation D V U V' U' E x =
  diagramRelation D v u v' u' e x
    • (phomEq D eu' (D.(phom) v' x) • f_equal (D.(phom) U') (phomEq D ev' x)).
Proof.
  destruct ev, eu, ev', eu'.
  destruct (@UIP (C.(CHom) i k) _ _ e E).
  now apply eq_trans_refl_l.
Defined.

Local Lemma inverseRelation {T: Type} {a b c d: T}
  (p: a = b) (q: b = c) (r: d = c):
  eq_sym (p • (q • eq_sym r)) = r • (eq_sym q • eq_sym p).
Proof. now destruct p, q, r. Defined.

Lemma diagramRelationReverse {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {i j j' k: C.(CObj)}
  (v: C.(CHom) i j) (u: C.(CHom) j k)
  (v': C.(CHom) i j') (u': C.(CHom) j' k)
  (e: v ⨟ u = v' ⨟ u') (x: O i):
  eq_sym (diagramRelation D v u v' u' e x) =
    diagramRelation D v' u' v u (eq_sym e) x.
Proof.
  unfold diagramRelation, phomEq. rewrite fEqualSym.
  now apply inverseRelation.
Defined.

Lemma diagramRelationChangeRight {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {i j j' k: C.(CObj)}
  (v: C.(CHom) i j) (u: C.(CHom) j k)
  (v': C.(CHom) i j') (u' U': C.(CHom) j' k) (eu': u' = U')
  (e: v ⨟ u = v' ⨟ u') (E: v ⨟ u = v' ⨟ U') (x: O i):
  diagramRelation D v u v' u' e x • phomEq D eu' (D.(phom) v' x) =
    diagramRelation D v u v' U' E x.
Proof.
  destruct eu'. destruct (@UIP (C.(CHom) i k) _ _ e E).
  now reflexivity.
Defined.

Local Lemma flattenRelation {X Y: Type} (f: X -> Y)
  {x0 x1 x2 x3: X} {y0 y1: Y}
  (p: y0 = f x0) (q: y1 = f x3)
  (a: x0 = x1) (b: x1 = x2) (c: x3 = x2):
  (p • f_equal f a) • (f_equal f b • eq_sym (q • f_equal f c)) =
    p • (f_equal f (a • (b • eq_sym c)) • eq_sym q).
Proof. now destruct a, b, c. Defined.

Definition functorRelation {B C: Category} (U: Functor B C)
  {i j j' k: B.(CObj)} (v: B.(CHom) i j) (u: B.(CHom) j k)
  (v': B.(CHom) i j') (u': B.(CHom) j' k) (e: v ⨟ u = v' ⨟ u'):
  U.(fhom) v ⨟ U.(fhom) u = U.(fhom) v' ⨟ U.(fhom) u' :=
  eq_sym (U.(fcomp) v u) • (f_equal U.(fhom) e • U.(fcomp) v' u').

Lemma pullbackDiagramRelation {B C: Category} (U: Functor B C)
  (F: PathDiagramFamily C) {i j j' k: B.(CObj)}
  (v: B.(CHom) i j) (u: B.(CHom) j k)
  (v': B.(CHom) i j') (u': B.(CHom) j' k)
  (e: v ⨟ u = v' ⨟ u')
  (E: U.(fhom) v ⨟ U.(fhom) u = U.(fhom) v' ⨟ U.(fhom) u')
  (x: F.(pfObj) (U.(fobj) i)):
  diagramRelation (pathData _ _ (pullbackDiagram U F).(pfStr)) v u v' u' e x =
    diagramRelation (pathData _ _ F.(pfStr))
      (U.(fhom) v) (U.(fhom) u) (U.(fhom) v') (U.(fhom) u') E x.
Proof.
  unfold diagramRelation. rewrite 2 pullbackCompPoint.
  change (phomEq (pathData _ _ (pullbackDiagram U F).(pfStr)) e x)
    with (f_equal (fun w => (pathData _ _ F.(pfStr)).(phom) (U.(fhom) w) x) e).
  unfold phomEq.
  rewrite <- (f_equal_compose (@fhom B C U i k)
    (fun w => (pathData _ _ F.(pfStr)).(phom) w x)).
  refine (flattenRelation
    (fun w: C.(CHom) (U.(fobj) i) (U.(fobj) k) => (pathData _ _ F.(pfStr)).(phom) w x)
    _ _ _ _ _ • _).
  apply transCongL. apply transCongR. apply f_equal.
  now apply (C.(CHom) (U.(fobj) i) (U.(fobj) k)).(UIP).
Defined.

Local Lemma relationMapAlgebra {T: Type}
  {x0 x1 x2 x3 y0 y1 y2 y3: T}
  (f1: x0 = x1) (fe: x1 = x2) (f2: x3 = x2)
  (g1: y0 = y1) (ge: y1 = y2) (g2: y3 = y2)
  (a: x0 = y0) (a': x3 = y3) (h1: x1 = y1) (h2: x2 = y2)
  (c1: f1 • h1 = a • g1) (ce: fe • h2 = h1 • ge)
  (c2: f2 • h2 = a' • g2):
  a • (g1 • (ge • eq_sym g2)) = (f1 • (fe • eq_sym f2)) • a'.
Proof.
  destruct f1, fe, f2, a, g1, ge, g2.
  cbn in c1, ce, c2 |- *.
  rewrite eq_trans_refl_l in c1, ce, c2.
  now rewrite <- c2, ce, c1.
Defined.

Local Lemma diagramMapArrow {A: HSet} {n} {X Y: Diagram A n}
  (M: DiagramMap X Y) {i j: Index n} {u v: Word A (rank i) (rank j)}
  (e: u = v) (x: cells X j):
  f_equal (M.(mapCell) i) (phomEq (diagramData X) (a := j) (b := i) e x)
    • M.(mapNatural) (i := i) (j := j) v x =
  M.(mapNatural) (i := i) (j := j) u x
    • phomEq (diagramData Y) (a := j) (b := i) e (M.(mapCell) j x).
Proof. destruct e. now apply eq_trans_refl_l. Defined.

Lemma diagramMapRelation {A: HSet} {n} {X Y: Diagram A n}
  (M: DiagramMap X Y) {i j j' k: Index n}
  (u: Word A (rank i) (rank j)) (v: Word A (rank j) (rank k))
  (u': Word A (rank i) (rank j')) (v': Word A (rank j') (rank k))
  (e: wcomp v u = wcomp v' u') (x: cells X k):
  (M.(mapNatural) (i := i) (j := j) u (restrict X (i := j) (j := k) v x) • f_equal (restrict Y (i := i) (j := j) u) (M.(mapNatural) (i := j) (j := k) v x))
    • diagramRelation (diagramData Y) (i := k) (j := j) (j' := j') (k := i) v u v' u' e (M.(mapCell) k x) =
  f_equal (M.(mapCell) i) (diagramRelation (diagramData X) (i := k) (j := j) (j' := j') (k := i) v u v' u' e x)
    • (M.(mapNatural) (i := i) (j := j') u' (restrict X (i := j') (j := k) v' x) • f_equal (restrict Y (i := i) (j := j') u') (M.(mapNatural) (i := j') (j := k) v' x)).
Proof.
  unfold diagramRelation. rewrite 2 eq_trans_map_distr, fEqualSym.
  apply (relationMapAlgebra
    (f_equal (M.(mapCell) i) (restrictComp X (i := i) (j := j) (k := k) u v x))
    (f_equal (M.(mapCell) i) (phomEq (diagramData X) (a := k) (b := i) e x))
    (f_equal (M.(mapCell) i) (restrictComp X (i := i) (j := j') (k := k) u' v' x))
    (restrictComp Y (i := i) (j := j) (k := k) u v (M.(mapCell) k x))
    (phomEq (diagramData Y) (a := k) (b := i) e (M.(mapCell) k x))
    (restrictComp Y (i := i) (j := j') (k := k) u' v' (M.(mapCell) k x))
    _ _ (M.(mapNatural) (i := i) (j := k) (wcomp v u) x) (M.(mapNatural) (i := i) (j := k) (wcomp v' u') x)).
  - refine (M.(mapComp) (i := i) (j := j) (k := k) u v x • _). now apply eq_sym, eqTransAssoc.
  - now apply diagramMapArrow.
  - refine (M.(mapComp) (i := i) (j := j') (k := k) u' v' x • _). now apply eq_sym, eqTransAssoc.
Defined.

(** Moving one coordinate into the residual index preserves the chosen
    face comparisons and their exchange squares. *)
Section ResidualShiftMaps.
Context {A: HSet} {B: Category} (F: PathDiagramFamily B)
  (U V: Functor (Op (νSemiShape A)) B)
  (alpha: NatTrans U (compFunctor (wholeCellFunctor A 1) V)).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation C := (ofPsfTot A (pullbackDiagram V F)).
Local Abbreviation D := (ofPsfTot A (pullbackDiagram U F)).

Definition residualShiftCell k: D.(G0) k -> C.(G0) (S k) :=
  FD.(phom) (alpha.(ncomp) k).

Local Definition sourcePrefix (N: nat) :=
  compFunctor (rankFunctor A N) U.
Local Definition targetPrefix (N: nat) :=
  compFunctor (rankFunctor A N) (compFunctor (wholeCellFunctor A 1) V).
Local Definition prefixShiftMap (N: nat) :=
  pullbackMap F (sourcePrefix N) (targetPrefix N)
    (whiskerLNat (rankFunctor A N) alpha).

Definition residualShiftFace k q (Hq: q <= k) (a: A) (x: D.(G0) (S k)):
  residualShiftCell k (D.(GFace) k q Hq a x) =
    C.(GFace) (S k) (S q) (⇑ Hq) a (residualShiftCell (S k) x) :=
  (prefixShiftMap (S (S k))).(mapNatural)
      (i := Some None) (j := None) (wgen k q a) x
    • phomEq FD (f_equal (V.(fhom)) (residualOneGen k q Hq a))
        (residualShiftCell (S k) x).

Lemma residualShiftFaceRelation k q (Hq: q <= k) (a: A) (x: D.(G0) (S k))
  (H: U.(fhom) (wgen k q a) ⨟ alpha.(ncomp) k =
    alpha.(ncomp) (S k) ⨟ V.(fhom) (wgen (S k) (S q) a)):
  residualShiftFace k q Hq a x =
    diagramRelation FD (U.(fhom) (wgen k q a)) (alpha.(ncomp) k)
      (alpha.(ncomp) (S k)) (V.(fhom) (wgen (S k) (S q) a)) H x.
Proof.
  unfold residualShiftFace.
  change (eq_sym (diagramRelation FD (alpha.(ncomp) (S k))
    (V.(fhom) (residualWord 1 (wgen k q a)))
    (U.(fhom) (wgen k q a)) (alpha.(ncomp) k)
    (eq_sym (alpha.(nnat) (wgen k q a))) x)
    • phomEq FD (f_equal V.(fhom) (residualOneGen k q Hq a))
      (residualShiftCell (S k) x) =
    diagramRelation FD (U.(fhom) (wgen k q a)) (alpha.(ncomp) k)
      (alpha.(ncomp) (S k)) (V.(fhom) (wgen (S k) (S q) a)) H x).
  refine (transCongR
    (diagramRelationReverse FD (alpha.(ncomp) (S k))
      (V.(fhom) (residualWord 1 (wgen k q a)))
      (U.(fhom) (wgen k q a)) (alpha.(ncomp) k)
      (eq_sym (alpha.(nnat) (wgen k q a))) x)
    (phomEq FD (f_equal V.(fhom) (residualOneGen k q Hq a))
      (residualShiftCell (S k) x)) • _).
  now exact (diagramRelationChangeRight FD
    (U.(fhom) (wgen k q a)) (alpha.(ncomp) k) (alpha.(ncomp) (S k))
    (V.(fhom) (residualWord 1 (wgen k q a))) (V.(fhom) (wgen (S k) (S q) a))
    (f_equal V.(fhom) (residualOneGen k q Hq a))
    (eq_sym (eq_sym (alpha.(nnat) (wgen k q a)))) H x).
Defined.

Local Definition lowIndex k: Index (S (S (S k))) := Some (Some None).
Local Definition middleIndex k: Index (S (S (S k))) := Some None.
Local Definition highIndex k: Index (S (S (S k))) := None.

Local Lemma sourcePrefixExchange k q (Hq: q <= k) r (Hr: r <= q) (a c: A)
  (x: D.(G0) (S (S k))):
  diagramRelation (diagramData (pullbackDiagram (sourcePrefix (S (S (S k)))) F))
    (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c) x = D.(GFaceCoh) k q Hq r Hr a c x.
Proof.
  pose (E := functorRelation U
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c)).
  refine (pullbackDiagramRelation (sourcePrefix (S (S (S k)))) F
    (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c) E x • _).
  now exact (eq_sym (pullbackDiagramRelation U F
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c) E x)).
Defined.

Local Definition normalizeShiftFace k q (Hq: q <= k) (a: A) (x: C.(G0) (S (S k))):
  FD.(phom) (V.(fhom) (residualWord 1 (wgen k q a))) x =
    C.(GFace) (S k) (S q) (⇑ Hq) a x :=
  phomEq FD (f_equal (V.(fhom)) (residualOneGen k q Hq a)) x.

Local Lemma targetPrefixExchange k q (Hq: q <= k) r (Hr: r <= q) (a c: A)
  (x: C.(G0) (S (S (S k)))):
  (normalizeShiftFace k q Hq a
      (FD.(phom) (V.(fhom) (residualWord 1 (wgen (S k) r c))) x)
    • f_equal (C.(GFace) (S k) (S q) (⇑ Hq) a)
      (normalizeShiftFace (S k) r (Hr ↕ (↑ Hq)) c x))
    • C.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c x =
  diagramRelation (diagramData (pullbackDiagram (targetPrefix (S (S (S k)))) F))
    (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c) x
    • (normalizeShiftFace k r (Hr ↕ Hq) c
      (FD.(phom) (V.(fhom) (residualWord 1 (wgen (S k) (S q) a))) x)
      • f_equal (C.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) c)
        (normalizeShiftFace (S k) (S q) (⇑ Hq) a x)).
Proof.
  pose (E := functorRelation (targetPrefix (S (S (S k))))
    (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c)).
  pose (E' := functorRelation V
    (wgen (S (S k)) (S r) c) (wgen (S k) (S q) a)
    (wgen (S (S k)) (S (S q)) a) (wgen (S k) (S r) c)
    (wgenExchange (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c)).
  refine (transCongL _ (pullbackDiagramRelation V F
    (wgen (S (S k)) (S r) c) (wgen (S k) (S q) a)
    (wgen (S (S k)) (S (S q)) a) (wgen (S k) (S r) c)
    (wgenExchange (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c) E' x) • _).
  refine (diagramRelationEdges FD
    (V.(fhom) (residualWord 1 (wgen (S k) r c))) (V.(fhom) (wgen (S (S k)) (S r) c))
    (V.(fhom) (residualWord 1 (wgen k q a))) (V.(fhom) (wgen (S k) (S q) a))
    (V.(fhom) (residualWord 1 (wgen (S k) (S q) a)))
      (V.(fhom) (wgen (S (S k)) (S (S q)) a))
    (V.(fhom) (residualWord 1 (wgen k r c))) (V.(fhom) (wgen (S k) (S r) c))
    (f_equal V.(fhom) (residualOneGen (S k) r (Hr ↕ (↑ Hq)) c))
    (f_equal V.(fhom) (residualOneGen k q Hq a))
    (f_equal V.(fhom) (residualOneGen (S k) (S q) (⇑ Hq) a))
    (f_equal V.(fhom) (residualOneGen k r (Hr ↕ Hq) c)) E E' x • _).
  now exact (transCongR (eq_sym (pullbackDiagramRelation (targetPrefix (S (S (S k)))) F
    (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
    (wgen (S k) r c) (wgen k q a) (wgen (S k) (S q) a) (wgen k r c)
    (wgenExchange k q Hq r Hr a c) E x)) _).
Defined.

Lemma residualShiftFaceCoh k q (Hq: q <= k) r (Hr: r <= q) (a c: A)
  (x: D.(G0) (S (S k))):
  (residualShiftFace k q Hq a (D.(GFace) (S k) r (Hr ↕ (↑ Hq)) c x)
    • f_equal (C.(GFace) (S k) (S q) (⇑ Hq) a)
      (residualShiftFace (S k) r (Hr ↕ (↑ Hq)) c x))
    • C.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c
      (residualShiftCell (S (S k)) x) =
  f_equal (residualShiftCell k) (D.(GFaceCoh) k q Hq r Hr a c x)
    • (residualShiftFace k r (Hr ↕ Hq) c (D.(GFace) (S k) (S q) (⇑ Hq) a x)
      • f_equal (C.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) c)
        (residualShiftFace (S k) (S q) (⇑ Hq) a x)).
Proof.
  pose (N := S (S (S k))).
  pose (X := pullbackDiagram (sourcePrefix N) F).
  pose (Y := pullbackDiagram (targetPrefix N) F).
  pose (M := prefixShiftMap N).
  pose (u := wgen k q a). pose (v := wgen (S k) r c).
  pose (u' := wgen k r c). pose (v' := wgen (S k) (S q) a).
  pose (e := wgenExchange k q Hq r Hr a c).
  pose proof (diagramMapRelation M
    (i := lowIndex k) (j := middleIndex k) (j' := middleIndex k) (k := highIndex k)
    u v u' v' e x) as rawSquareA.
  pose (squareA := rawSquareA • transCongR
    (f_equal (fun h => f_equal (residualShiftCell k) h)
      (sourcePrefixExchange k q Hq r Hr a c x))
    (M.(mapNatural) (i := lowIndex k) (j := middleIndex k) u'
        (restrict X (i := middleIndex k) (j := highIndex k) v' x)
      • f_equal (restrict Y (i := lowIndex k) (j := middleIndex k) u')
        (M.(mapNatural) (i := middleIndex k) (j := highIndex k) v' x))).
  pose proof (targetPrefixExchange k q Hq r Hr a c
    (residualShiftCell (S (S k)) x)) as squareB.
  pose proof (composeForwardFaceSquare
    (residualShiftCell k) (residualShiftCell (S k)) (residualShiftCell (S (S k)))
    (fun y => y) (fun y => y) (fun y => y)
    (D.(GFace) k q Hq a) (D.(GFace) k r (Hr ↕ Hq) c)
    (D.(GFace) (S k) r (Hr ↕ (↑ Hq)) c) (D.(GFace) (S k) (S q) (⇑ Hq) a)
    (restrict Y (i := lowIndex k) (j := middleIndex k) u)
    (restrict Y (i := lowIndex k) (j := middleIndex k) u')
    (restrict Y (i := middleIndex k) (j := highIndex k) v)
    (restrict Y (i := middleIndex k) (j := highIndex k) v')
    (C.(GFace) (S k) (S q) (⇑ Hq) a) (C.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) c)
    (C.(GFace) (S (S k)) (S r) (⇑ (Hr ↕ (↑ Hq))) c)
    (C.(GFace) (S (S k)) (S (S q)) (⇑ (⇑ Hq)) a)
    (M.(mapNatural) (i := lowIndex k) (j := middleIndex k) u)
    (M.(mapNatural) (i := lowIndex k) (j := middleIndex k) u')
    (M.(mapNatural) (i := middleIndex k) (j := highIndex k) v)
    (M.(mapNatural) (i := middleIndex k) (j := highIndex k) v')
    (normalizeShiftFace k q Hq a) (normalizeShiftFace k r (Hr ↕ Hq) c)
    (normalizeShiftFace (S k) r (Hr ↕ (↑ Hq)) c)
    (normalizeShiftFace (S k) (S q) (⇑ Hq) a)
    (D.(GFaceCoh) k q Hq r Hr a c)
    (diagramRelation (diagramData Y)
      (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
      v u v' u' e)
    (C.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c)
    x squareA) as pasted.
  assert (squareB':
    (normalizeShiftFace k q Hq a
      (restrict Y (i := middleIndex k) (j := highIndex k) v
        (residualShiftCell (S (S k)) x))
      • f_equal (C.(GFace) (S k) (S q) (⇑ Hq) a)
        (normalizeShiftFace (S k) r (Hr ↕ (↑ Hq)) c
          (residualShiftCell (S (S k)) x)))
      • C.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c
        (residualShiftCell (S (S k)) x) =
    f_equal (fun y => y) (diagramRelation (diagramData Y)
      (i := highIndex k) (j := middleIndex k) (j' := middleIndex k) (k := lowIndex k)
      v u v' u' e (residualShiftCell (S (S k)) x))
      • (normalizeShiftFace k r (Hr ↕ Hq) c
        (restrict Y (i := middleIndex k) (j := highIndex k) v'
          (residualShiftCell (S (S k)) x))
        • f_equal (C.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) c)
          (normalizeShiftFace (S k) (S q) (⇑ Hq) a
            (residualShiftCell (S (S k)) x)))).
  { rewrite f_equal_id. now exact squareB. }
  specialize (pasted squareB').
  rewrite 4 f_equal_id in pasted.
  now exact pasted.
Defined.

End ResidualShiftMaps.

(** The selected whole-cell map acts on the rank isomorphism in the
    original diagram. Its face comparison is the generic source comparison. *)
Section ShiftCells.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation C := (ofPsfTot A (wholeCellDiagram p F)).
Local Abbreviation D := (ofPsfTot A (wholeCellDiagram (S p) F)).

Definition shiftCellFace k q (Hq: q <= k) (a: A) (x: D.(G0) (S k)):
  shiftPrefixCell p k F (D.(GFace) k q Hq a x) =
    C.(GFace) (S k) (S q) (⇑ Hq) a (shiftPrefixCell p (S k) F x) :=
  residualShiftFace F (wholeCellFunctor A (S p)) (wholeCellFunctor A p) (wholeCellShiftNat A p) k q Hq a x.

Lemma shiftCellFaceRelation k q (Hq: q <= k) (a: A) (x: D.(G0) (S k))
  (H: wcomp (residualWord (S p) (wgen k q a))
      (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k))) =
    wcomp (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p (S k))))
      (residualWord p (wgen (S k) (S q) a))):
  shiftCellFace k q Hq a x =
    diagramRelation FD (residualWord (S p) (wgen k q a))
      (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k)))
      (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p (S k))))
      (residualWord p (wgen (S k) (S q) a)) H x.
Proof.
  now exact (residualShiftFaceRelation F (wholeCellFunctor A (S p)) (wholeCellFunctor A p) (wholeCellShiftNat A p) k q Hq a x H).
Defined.

Lemma shiftCellFaceCoh k q (Hq: q <= k) r (Hr: r <= q) (a c: A)
  (x: D.(G0) (S (S k))):
  (shiftCellFace k q Hq a (D.(GFace) (S k) r (Hr ↕ (↑ Hq)) c x)
    • f_equal (C.(GFace) (S k) (S q) (⇑ Hq) a)
      (shiftCellFace (S k) r (Hr ↕ (↑ Hq)) c x))
    • C.(GFaceCoh) (S k) (S q) (⇑ Hq) (S r) (⇑ Hr) a c
      (shiftPrefixCell p (S (S k)) F x) =
  f_equal (shiftPrefixCell p k F) (D.(GFaceCoh) k q Hq r Hr a c x)
    • (shiftCellFace k r (Hr ↕ Hq) c (D.(GFace) (S k) (S q) (⇑ Hq) a x)
      • f_equal (C.(GFace) (S k) (S r) (⇑ (Hr ↕ Hq)) c)
        (shiftCellFace (S k) (S q) (⇑ Hq) a x)).
Proof.
  now exact (residualShiftFaceCoh F (wholeCellFunctor A (S p)) (wholeCellFunctor A p) (wholeCellShiftNat A p) k q Hq r Hr a c x).
Defined.

Definition shiftCellComparisonFace k q (Hq: q <= k) (a: A) (x: D.(G0) (S k)):
  C.(GFace) (S k) (S q) (⇑ Hq) a (shiftPrefixCell p (S k) F x) =
    shiftPrefixCell p k F (D.(GFace) k q Hq a x) :=
  eq_sym (shiftCellFace k q Hq a x).

End ShiftCells.
