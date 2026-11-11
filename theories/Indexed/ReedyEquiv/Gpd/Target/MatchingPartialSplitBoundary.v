(** Boundaries under the partial matching split equivalence: the split maps
    the partial boundary of a whole cell to the matching-step boundary of its
    shift, compatibly with faces. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.PeanoNat.
From Bonak.Lib Require Import HSet HGpd SigT Notation RewLemmas FinitePrefix
  Equiv NatLemmas LeSProp.
From Bonak.Category Require Import Category SequentialFunctor.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas.
From Bonak.Presheaf Require Import νSemiShape WordTensor.
From Bonak.Presentation.Gpd Require Import Presentation.
From Bonak.Presentation.PresheafEquiv.Gpd Require Import Pseudofunctor.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Cone.
From Bonak.Reedy.Gpd Require Import Reedy PathAlgebra Matching Shift Pullback.
From Bonak.Indexed.ReedyEquiv.Gpd.Target Require Import ShiftedPrefix
  PullbackReindex MatchingSplit MatchingPartialSplit MatchingPartialSplitFace.

Set Primitive Projections.
Set Printing Projections.
Import FinitePrefix WordTensor.

(** The kept and final boundary comparisons through law repacks of the
    truncated diagrams. *)
Set Keyed Unification.

Local Lemma keepBoundaryPath {A: HSet} {p: nat} (D: Diagram A (S (S p)))
  (x: cells D None) {i j: Index p}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) p):
  matchingPath (matchingMap (shiftDiagram D) x) f g =
    matchingPath (keepMatching (truncateDiagram D) (matchingMap D x)) f g.
Proof.
  pose proof (matchingPathSquares (shiftDiagram (truncateDiagram D))
    (keepBoundary D x) i j f g) as h.
  refine (eq_sym (eq_trans_refl_l
    (matchingPath (matchingMap (shiftDiagram D) x) f g)) • _).
  refine (eq_sym (f_equal
    (fun v => f_equal (restrict (shiftDiagram (truncateDiagram D)) f) v
      • matchingPath (matchingMap (shiftDiagram D) x) f g)
    (keepBoundaryValue D x j g)) • _).
  refine (h • _).
  now exact (f_equal
    (fun v => matchingPath (keepMatching (truncateDiagram D) (matchingMap D x)) f g • v)
    (keepBoundaryValue D x i (wcomp g f))).
Defined.

Section KeptBoundary.
Context {A: HSet} (p k: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation Vfull := (shiftPrefixFunctor A (S (S p)) k).
Local Abbreviation Ufull := (shiftFunctor A (S p)).
Local Abbreviation U0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A))
    (PrefixCategory A (S (S p))) (fun n => n) Ufull).
Local Abbreviation L2 := (pullbackDiagram U0 (pullbackDiagram Vfull F)).
Local Abbreviation D := (shiftedPrefix (S (S p)) k F).
Local Abbreviation oldBoundary x :=
  (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x)).
Local Abbreviation newBoundary x :=
  (matchingMap (shiftDiagram D) x).

(** The kept boundary path stated for the shifted prefix. Instantiating the
    generic lemma once keeps the two forms of the truncated diagram apart. *)
Local Lemma keepBoundaryPathPrefix (x: F.(pfObj) (S p + k)) {i j: Index p}
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) p):
  matchingPath (newBoundary x) f g = matchingPath (oldBoundary x) f g.
Proof. now exact (@keepBoundaryPath A p D x i j f g). Defined.

Local Lemma inputKeepBoundarySquares (x: F.(pfObj) (S p + k)):
  @ComparisonSquares A p L2
    (matchingTruncateInput Vfull F (oldBoundary x))
    (pullbackMatchingUntruncate (pullbackDiagram Vfull F) Ufull (newBoundary x))
    (fun i g => eq_refl).
Proof.
  intros i j f g.
  now exact (eq_trans_refl_l _ • keepBoundaryPathPrefix x f g).
Defined.

Definition inputKeepBoundary (x: F.(pfObj) (S p + k)):
  matchingTruncateInput Vfull F (oldBoundary x) =
    pullbackMatchingUntruncate (pullbackDiagram Vfull F) Ufull (newBoundary x) :=
  matchingHomotopy L2
    (b := matchingTruncateInput Vfull F (oldBoundary x))
    (c := pullbackMatchingUntruncate (pullbackDiagram Vfull F) Ufull (newBoundary x))
    (fun i g => eq_refl) (inputKeepBoundarySquares x).

Lemma inputKeepBoundaryValue (x: F.(pfObj) (S p + k))
  (i: Index p) (g: Word A (rank i) p):
  f_equal (fun z: MatchingObject L2 => matchingValue z i g) (inputKeepBoundary x) = eq_refl.
Proof.
  now exact (matchingHomotopyValue L2
    (b := matchingTruncateInput Vfull F (oldBoundary x))
    (c := pullbackMatchingUntruncate (pullbackDiagram Vfull F) Ufull (newBoundary x))
    (fun i g => eq_refl)
    (inputKeepBoundarySquares x) i g).
Defined.
End KeptBoundary.

Section FinalBoundary.
Context {A: HSet} (p k: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation V := (shiftPrefixFunctor A (S p) (S k)).
Local Abbreviation Y := (shiftedPrefix p (S k) F).
Local Abbreviation boundary y := (matchingMap (shiftedPrefix (S p) (S k) F) y).

Definition finalUntruncateBoundary (y: F.(pfObj) (p + S k)):
  pullbackMatchingUntruncate F V (boundary y) = partialBoundary p F (S k) y :=
  matchingHomotopy Y
    (b := pullbackMatchingUntruncate F V (boundary y))
    (c := partialBoundary p F (S k) y) (fun i g => eq_refl)
    (fun i j f g => eq_trans_refl_l (matchingPath (boundary y) f g)).

Lemma finalUntruncateBoundaryValue (y: F.(pfObj) (p + S k))
  (i: Index p) (g: Word A (rank i) p):
  f_equal (fun z: MatchingObject Y => matchingValue z i g) (finalUntruncateBoundary y) = eq_refl.
Proof.
  now exact (matchingHomotopyValue Y
    (b := pullbackMatchingUntruncate F V (boundary y))
    (c := partialBoundary p F (S k) y) (fun i g => eq_refl)
    (fun i j f g => eq_trans_refl_l (matchingPath (boundary y) f g)) i g).
Defined.
End FinalBoundary.

(** The boundary of a shifted prefix cell agrees with the bridged kept
    boundary. *)


Section Boundary.
Context {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))).

Local Abbreviation FD := (pathData _ _ F.(pfStr)).

Local Abbreviation U :=
  (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k)).
Local Abbreviation V := (shiftPrefixFunctor A p (S k)).
Local Abbreviation UF :=
  (compFunctor (shiftFunctor A (S p)) (shiftPrefixFunctor A (S (S p)) k)).
Local Abbreviation VF := (shiftPrefixFunctor A (S p) (S k)).
Local Abbreviation α :=
  (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A)))
    U V (shiftPrefixFunctorEq p k)).
Local Abbreviation αF :=
  (@idToHom (functorCategory (PrefixCategory A (S p)) (Op (νSemiShape A)))
    UF VF (shiftPrefixFunctorEq (S p) k)).
Local Abbreviation UF0 :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A))
    (PrefixCategory A (S (S p))) (fun n => n) (shiftFunctor A (S p))).

(** Restriction compares the component arrows in the shape category.
    It does not require equality between paths of functors. *)
Definition shiftPrefixNatTruncate: NatTrans U V := {|
  ncomp i := αF.(ncomp) (Some i);
  nnat i j f := αF.(nnat) (a := Some i) (b := Some j) f;
|}.

Lemma shiftPrefixNatTruncateEq: shiftPrefixNatTruncate = α.
Proof.
  apply natTransEq; intro i.
  change (αF.(ncomp) (Some i) = α.(ncomp) i).
  rewrite 2 natComponent.
  apply f_equal. now apply natUIP.
Defined.

Lemma shiftPrefixNatBase (i: Index p):
  α.(ncomp) i = αF.(ncomp) (Some i).
Proof.
  rewrite 2 natComponent.
  apply f_equal. now apply natUIP.
Defined.

Lemma shiftPrefixNatTop:
  αF.(ncomp) None =
    @idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k)).
Proof.
  rewrite natComponent.
  apply f_equal. now apply natUIP.
Defined.

Local Abbreviation Vfull := (shiftPrefixFunctor A (S (S p)) k).
Local Abbreviation Ufull := (shiftFunctor A (S p)).
Local Abbreviation R2 := (pullbackDiagram (compFunctor UF0 Vfull) F).
Local Abbreviation UT :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) (Op (νSemiShape A))
    (fun n => n) UF).
Local Abbreviation VT :=
  (SequentialFunctor.truncateFunctor (Op (νSemiShape A)) (Op (νSemiShape A))
    (fun n => n) VF).
Local Abbreviation aT := (truncateIndexTransformation UF VF αF).
Local Definition outputRepack :=
  @matchingTruncateOutput A p (Op (νSemiShape A)) Vfull F.

Local Definition flatMapTruncateSquares (b: MatchingObject R2):
  ComparisonSquares (pullbackDiagram V F)
    (b := mapMatching (pullbackMap F U V shiftPrefixNatTruncate) (outputRepack b))
    (c := mapMatching (pullbackMap F UT VT aT) b) (fun i f => eq_refl).
Proof.
  intros i j f g.
  now exact (eq_trans_refl_l
    (matchingPath (mapMatching (pullbackMap F UT VT aT) b) f g)).
Defined.

Local Definition flatMapTruncate (b: MatchingObject R2):
  mapMatching (pullbackMap F U V shiftPrefixNatTruncate) (outputRepack b) =
    mapMatching (pullbackMap F UT VT aT) b :=
  matchingHomotopy (pullbackDiagram V F)
    (b := mapMatching (pullbackMap F U V shiftPrefixNatTruncate) (outputRepack b))
    (c := mapMatching (pullbackMap F UT VT aT) b)
    (fun i f => eq_refl) (flatMapTruncateSquares b).

Local Lemma flatMapTruncateValue (b: MatchingObject R2) i g:
  f_equal (fun z => matchingValue z i g) (flatMapTruncate b) = eq_refl.
Proof.
  now exact (matchingHomotopyValue (pullbackDiagram V F)
    (b := mapMatching (pullbackMap F U V shiftPrefixNatTruncate) (outputRepack b))
    (c := mapMatching (pullbackMap F UT VT aT) b)
    (fun i f => eq_refl) (flatMapTruncateSquares b) i g).
Defined.

Local Lemma actionOutputCompPath
  {b c: MatchingObject (pullbackDiagram UF0 (pullbackDiagram Vfull F))}
  (e: b = c) i g:
  f_equal (fun z => matchingValue z i g)
    (f_equal (fun b => matchingAction p (Op (νSemiShape A)) F U V α
      (outputRepack (matchingCompEquiv UF0 Vfull F b))) e) =
    f_equal (FD.(phom) (α.(ncomp) i)) (f_equal (fun b => matchingValue b i g) e).
Proof. now destruct e. Defined.

Local Lemma actionOutputPath {b c: MatchingObject R2} (e: b = c) i g:
  f_equal (fun z => matchingValue z i g)
    (f_equal (fun b => matchingAction p (Op (νSemiShape A)) F U V α (outputRepack b)) e) =
    f_equal (FD.(phom) (α.(ncomp) i)) (f_equal (fun b => matchingValue b i g) e).
Proof. now destruct e. Defined.

Definition shiftPrefixBoundary (x: F.(pfObj) (S p + k)):
  shiftPrefixBridge p k F
    (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x)) =
    partialBoundary p F (S k) (shiftPrefixCell p k F x).
Proof.
  change (matchingAction p (Op (νSemiShape A)) F U V α
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F
      (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x))) =
    partialBoundary p F (S k) (shiftPrefixCell p k F x)).
  refine (f_equal (matchingAction p (Op (νSemiShape A)) F U V α)
    (matchingCompositeTruncate Vfull F
      (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x))) • _).
  refine (f_equal (fun b => matchingAction p (Op (νSemiShape A)) F U V α
    (outputRepack (matchingCompEquiv UF0 Vfull F b))) (inputKeepBoundary p k F x) • _).
  cbv beta iota zeta delta [shiftDiagram shiftedPrefix].
  Local Opaque MatchingObject matchingAction outputRepack matchingCompEquiv
    pullbackMatchingUntruncate matchingMap.
  lazymatch goal with |- @eq ?P (?act (?repack ?current)) ?rhs =>
    let ty := type of repack in
    lazymatch ty with forall _ : ?Dom, _ =>
      refine (@eq_trans P _ _ rhs
        (@f_equal Dom P (fun b: Dom => act (repack b)) current _ _) _)
    end
  end.
  now exact (matchingCompUntruncatedBoundary Ufull Vfull F x).
  Local Transparent MatchingObject matchingAction outputRepack matchingCompEquiv
    pullbackMatchingUntruncate matchingMap.
  refine (f_equal (fun β => matchingAction p (Op (νSemiShape A)) F U V β
    (outputRepack (pullbackMatchingUntruncate F UF (matchingMap (pullbackDiagram UF F) x))))
    (eq_sym shiftPrefixNatTruncateEq) • _).
  refine (flatMapTruncate
    (pullbackMatchingUntruncate F UF (matchingMap (pullbackDiagram UF F) x)) • _).
  refine (mapMatchingUntruncatedBoundary F UF VF αF x • _).
  refine (finalUntruncateBoundary p k F ((pullbackMap F UF VF αF).(mapCell) None x) • _).
  now exact (f_equal (partialBoundary p F (S k)) (phomEq FD shiftPrefixNatTop x)).
Defined.

Definition shiftPrefixBoundaryValues (x: F.(pfObj) (S p + k))
  (i: Index p) (g: Word A (rank i) p):
  matchingValue
    (shiftPrefixBridge p k F
      (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x))) i g =
  matchingValue (partialBoundary p F (S k) (shiftPrefixCell p k F x)) i g :=
  phomEq FD (shiftPrefixNatBase i) (FD.(phom) (UF.(fhom) (a := None) (b := Some i) g) x)
    • (eq_sym (pullbackNaturality F UF VF αF (i := Some i) (j := None) g x)
      • f_equal (FD.(phom) (VF.(fhom) (a := None) (b := Some i) g))
          (phomEq FD shiftPrefixNatTop x)).

Lemma shiftPrefixBoundaryValue (x: F.(pfObj) (S p + k)) i g:
  f_equal (fun z => matchingValue z i g) (shiftPrefixBoundary x) =
    shiftPrefixBoundaryValues x i g.
Proof.
  unfold shiftPrefixBoundary. rewrite 7 eq_trans_map_distr.
  rewrite (matchingActionMapPath p (Op (νSemiShape A)) F U V α
    (matchingCompositeTruncate Vfull F
      (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x))) i g).
  rewrite (matchingCompositeTruncateValue Vfull F
    (keepMatching (shiftedPrefix (S p) k F) (partialBoundary (S p) F k x)) i g).
  rewrite (actionOutputCompPath (inputKeepBoundary p k F x) i g).
  rewrite (inputKeepBoundaryValue p k F x i g).
  rewrite (actionOutputPath (matchingCompUntruncatedBoundary Ufull Vfull F x) i g).
  rewrite (matchingCompUntruncatedBoundaryValue Ufull Vfull F x i g).
  rewrite (matchingActionArrowPath p (Op (νSemiShape A)) F U V
    (eq_sym shiftPrefixNatTruncateEq)
    (outputRepack (pullbackMatchingUntruncate F UF (matchingMap (pullbackDiagram UF F) x)))
    i g (shiftPrefixNatBase i)).
  rewrite (flatMapTruncateValue
    (pullbackMatchingUntruncate F UF (matchingMap (pullbackDiagram UF F) x)) i g).
  rewrite (mapMatchingUntruncatedBoundaryValue F UF VF αF x i g).
  rewrite (finalUntruncateBoundaryValue p k F
    ((pullbackMap F UF VF αF).(mapCell) None x) i g).
  rewrite (partialBoundaryMapPath p F (S k) (phomEq FD shiftPrefixNatTop x) i g).
  cbn [f_equal].
  assert (stripUnits: forall (T: Type) (a b c d: T)
    (u: a = b) (v: b = c) (w: c = d),
    eq_refl • (eq_refl • (eq_refl • (u • (eq_refl • (v • (eq_refl • w))))))
      = u • (v • w)).
  { intros T a b c d u v w. now destruct u, v, w. }
  cbv beta iota zeta delta [matchingValue outputRepack matchingTruncateOutput
    matchingLawRepack pullbackMatchingUntruncate matchingMap
    SigT.projT1 SigT.projT2 mapNatural pullbackMap pullbackCell].
  lazymatch goal with
  | |- @eq (@eq ?T ?a ?d)
      (eq_refl • (eq_refl • (eq_refl • (?u • (eq_refl • (?v • (eq_refl • ?w))))))) ?rhs =>
      lazymatch type of u with @eq _ _ ?b =>
        lazymatch type of v with @eq _ _ ?c =>
          refine (@eq_trans (@eq T a d) _ (u • (v • w)) rhs
            (stripUnits T a b c d u v w) _)
        end
      end
  end.
  now reflexivity.
Defined.

Definition shiftPrefixBoundaryWord (i: Index p) (g: Word A (rank i) p):
  UF.(fhom) (a := None) (b := Some i) g ⨟ α.(ncomp) i =
  @idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k))
    ⨟ VF.(fhom) (a := None) (b := Some i) g :=
  f_equal (fun w => UF.(fhom) (a := None) (b := Some i) g ⨟ w)
      (shiftPrefixNatBase i)
    • (αF.(nnat) (a := None) (b := Some i) g
      • f_equal (fun w => w ⨟ VF.(fhom) (a := None) (b := Some i) g)
          shiftPrefixNatTop).

Local Lemma diagramRelationChangeEnds {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {a b b' c: C.(CObj)}
  (v: C.(CHom) a b) (u U: C.(CHom) b c)
  (v' V': C.(CHom) a b') (u': C.(CHom) b' c)
  (eu: u = U) (ev': v' = V')
  (e: v ⨟ u = V' ⨟ u') (E: v ⨟ U = v' ⨟ u') (x: O a):
  phomEq D eu (D.(phom) v x)
    • (diagramRelation D v U v' u' E x
      • f_equal (D.(phom) u') (phomEq D ev' x)) =
    diagramRelation D v u V' u' e x.
Proof.
  destruct eu, ev'.
  destruct (@UIP (C.(CHom) a c) _ _ E e).
  now apply eq_trans_refl_l.
Defined.

Lemma shiftPrefixBoundaryValueRelation (x: F.(pfObj) (S p + k)) i g:
  f_equal (fun z => matchingValue z i g) (shiftPrefixBoundary x) =
  diagramRelation FD (UF.(fhom) (a := None) (b := Some i) g) (α.(ncomp) i)
    (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k)))
    (VF.(fhom) (a := None) (b := Some i) g) (shiftPrefixBoundaryWord i g) x.
Proof.
  rewrite (shiftPrefixBoundaryValue x i g). unfold shiftPrefixBoundaryValues.
  lazymatch goal with |- _ = ?rhs =>
    change (phomEq FD (shiftPrefixNatBase i)
        (FD.(phom) (UF.(fhom) (a := None) (b := Some i) g) x)
      • (eq_sym (diagramRelation FD (αF.(ncomp) None)
          (VF.(fhom) (a := None) (b := Some i) g)
          (UF.(fhom) (a := None) (b := Some i) g) (αF.(ncomp) (Some i))
          (eq_sym (αF.(nnat) (a := None) (b := Some i) g)) x)
        • f_equal (FD.(phom) (VF.(fhom) (a := None) (b := Some i) g))
            (phomEq FD shiftPrefixNatTop x)) = rhs)
  end.
  rewrite diagramRelationReverse. now apply diagramRelationChangeEnds.
Defined.

End Boundary.

(** The partial matching split equivalence maps the boundary of a whole cell
    to the matching boundary of its shift. *)

Definition diagramFactorAlong {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {a b c: C.(CObj)}
  (s: C.(CHom) a b) (g: C.(CHom) b c) (t: C.(CHom) a c)
  (factor: s ⨟ g = t) (x: O a):
  D.(phom) g (D.(phom) s x) = D.(phom) t x :=
  D.(pcomp) s g x • phomEq D factor x.

Local Lemma diagramForkRelation {C: Category} {O: C.(CObj) -> HGpd}
  (D: PathDiagramData C O) {a b b' c: C.(CObj)}
  (v: C.(CHom) a b) (u: C.(CHom) b c)
  (v': C.(CHom) a b') (u': C.(CHom) b' c) (w: C.(CHom) a c)
  (e1: v ⨟ u = w) (e2: v' ⨟ u' = w)
  (E: v ⨟ u = v' ⨟ u') (x: O a):
  (D.(pcomp) v u x • phomEq D e1 x)
    • eq_sym (D.(pcomp) v' u' x • phomEq D e2 x) =
  diagramRelation D v u v' u' E x.
Proof.
  destruct e2.
  destruct (@UIP (C.(CHom) a c) _ _ e1 E).
  unfold diagramRelation, phomEq. cbn [f_equal].
  now apply eqTransAssoc.
Defined.

Definition splitBoundaryWord {A: HSet} {p: nat} (i: Index p)
  (g: Word A (rank i) p) (a: A):
  wcomp (keepToTop g) (topFaceWord i a) = wcomp (wskip a (wid p)) g :=
  keepTopFaceWord g a • eq_sym (skippedWord a g).

Definition shiftTopComponent {A: HSet} (p k: nat) a (i: Index p):
  (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
    (shiftPrefixFunctorEq p k)).(ncomp) i ⨟ residualWord (rank i) (wgen k 0 a) =
  paddedWord k (topFaceWord i a) :=
  f_equal (fun β: NatTrans
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p k) => β.(ncomp) i) (shiftTopNatComp p k a).

Lemma shiftPrefixTopFaceValue {A: HSet} (p k: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) a
  (b: MatchingObject (shiftDiagram (shiftedPrefix (S p) k F))) i g:
  f_equal (fun z => matchingValue z i g) (shiftPrefixTopFace p k F a b) =
  eq_sym (diagramFactorAlong (pathData _ _ F.(pfStr))
    ((@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
      (shiftPrefixFunctorEq p k)).(ncomp) i)
    (residualWord (rank i) (wgen k 0 a)) (paddedWord k (topFaceWord i a))
    (shiftTopComponent p k a i) (matchingValue b i g)).
Proof.
  unfold shiftPrefixTopFace.
  lazymatch goal with |- context [f_equal ?h (?u • ?v)] =>
    rewrite (eq_trans_map_distr h u v)
  end.
  lazymatch goal with |- context [f_equal ?h (eq_sym ?u)] =>
    rewrite (fEqualSym h u)
  end.
  rewrite (topFaceFlattenValue p k F a b i g).
  lazymatch goal with |- context [f_equal ?h (?u • ?v)] =>
    rewrite (eq_trans_map_distr h u v)
  end.
  rewrite (matchingCompositionValue p (Op (νSemiShape A)) F
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p (S k)) (shiftPrefixFunctor A p k)
    (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A)))
      _ _ (shiftPrefixFunctorEq p k))
    (residualNat p (wgen k 0 a))
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b) i g).
  rewrite (matchingActionArrowPath p (Op (νSemiShape A)) F
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) k))
    (shiftPrefixFunctor A p k) (shiftTopNatComp p k a)
    (matchingCompEquiv (shiftFunctor A p) (shiftPrefixFunctor A (S p) k) F b)
    i g (shiftTopComponent p k a i)).
  cbv beta iota zeta delta [matchingValue matchingAction mapMatching mapValues
    pullbackMap mapCell pullbackCell matchingCompEquiv qinvEquiv eqvFun matchingComposite
    SigT.projT1 SigT.projT2].
  now apply eq_trans_refl_l.
Defined.

Lemma boundaryNaturalValueRelation {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (x: F.(pfObj) (p + l)) (i: Index p) g:
  f_equal (fun z => matchingValue z i g) (boundaryNatural p F u x) =
  diagramRelation (pathData _ _ F.(pfStr))
    (paddedWord l g) (residualWord (rank i) u)
    (residualWord p u) (paddedWord k g) (paddedResidual g u) x.
Proof.
  rewrite (boundaryNaturalValue p F u x i g).
  lazymatch goal with |- _ = ?rhs =>
    change (eq_sym (diagramRelation (pathData _ _ F.(pfStr))
      (residualWord p u) (paddedWord k g) (paddedWord l g) (residualWord (rank i) u)
      (eq_sym (paddedResidual g u)) x) = rhs)
  end.
  now rewrite diagramRelationReverse, eq_sym_involutive.
Defined.

Lemma diagramIsoCubeAlong {C: Category} (F: PathDiagramFamily C)
  {a0 a1 b0 b1 c0 c1: C.(CObj)}
  (e0: a0 = b0) (e1: a1 = b1)
  (s0: C.(CHom) a0 b0) (s1: C.(CHom) a1 b1)
  (s0Id: s0 = idToHom e0) (s1Id: s1 = idToHom e1)
  (f: C.(CHom) a0 a1) (g: C.(CHom) b0 b1) (h: C.(CHom) c0 c1)
  (t0: C.(CHom) a0 c0) (t1: C.(CHom) a1 c1)
  (z0: C.(CHom) b0 c0) (z1: C.(CHom) b1 c1)
  (reindex: f ⨟ s1 = s0 ⨟ g)
  (factor0: s0 ⨟ z0 = t0) (factor1: s1 ⨟ z1 = t1)
  (raw: f ⨟ t1 = t0 ⨟ h) (normalized: g ⨟ z1 = z0 ⨟ h)
  (x: F.(pfObj) a0):
  let D := pathData _ _ F.(pfStr) in
  f_equal (D.(phom) z1) (diagramRelation D f s1 s0 g reindex x)
    • (diagramRelation D g z1 z0 h normalized (D.(phom) s0 x)
      • f_equal (D.(phom) h) (diagramFactorAlong D s0 z0 t0 factor0 x)) =
  diagramFactorAlong D s1 z1 t1 factor1 (D.(phom) f x)
    • diagramRelation D f t1 t0 h raw x.
Proof.
  subst s0 s1.
  now exact (diagramIsoCube F e0 e1 f g h t0 t1 z0 z1
    reindex factor0 factor1 raw normalized x).
Defined.

Local Lemma removeCubeFactor {T: Type} {a b c d e: T}
  (p: a = b) (q: b = c) (r: c = d) (s: a = e) (t: e = d)
  (cube: p • (q • r) = s • t): p • q = (s • t) • eq_sym r.
Proof. now destruct r. Defined.

Section WholeBoundary.
Context {A: HSet} (p k: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation Q := (MatchingPartialPresentation p F).
Local Abbreviation fullPrefix := (shiftPrefixFunctor A (S (S p)) k).
Local Abbreviation α :=
  (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
    (shiftPrefixFunctorEq p k)).
Local Abbreviation wholeShift :=
  (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k))).

Definition wholeBoundaryTopWord (a: A):
  wholeShift ⨟ residualWord p (wgen k 0 a) = paddedWord k (wskip a (wid p)) :=
  eq_sym (f_equal
    (fun w: Word A (p + S k) (S p + k) => wcomp w (residualWord p (wgen k 0 a)))
    (shiftPrefixNatTop p k))
    • f_equal (fun β: NatTrans
        (compFunctor (shiftFunctor A (S p)) (shiftPrefixFunctor A (S (S p)) k))
        (shiftPrefixFunctor A (S p) k) => β.(ncomp) None)
        (shiftTopNatComp (S p) k a).

Definition wholeBoundaryTop (x: F.(pfObj) (S p + k)) (a: A):
  ((matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x)).2 a).1 =
  FD.(phom) (residualWord p (wgen k 0 a)) (shiftPrefixCell p k F x) :=
  eq_sym (diagramFactorAlong FD wholeShift (residualWord p (wgen k 0 a))
    (paddedWord k (wskip a (wid p))) (wholeBoundaryTopWord a) x).

Definition wholeBoundaryPaddedWord (i: Index p) (g: Word A (rank i) p) (a: A):
  wcomp (paddedWord k (keepToTop g)) (paddedWord k (topFaceWord i a)) =
    wcomp (paddedWord k (wskip a (wid p))) (paddedWord k g) :=
  functorRelation fullPrefix
    (i := None) (j := Some (raiseIndex i)) (j' := Some None) (k := Some (Some i))
    (keepToTop g) (topFaceWord i a) (wskip a (wid p)) g (splitBoundaryWord i g a).

Lemma wholeBoundaryAttachmentValue (x: F.(pfObj) (S p + k)) a i g:
  f_equal (fun z => matchingValue z i g)
    ((matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x)).2 a).2 =
  diagramFactorAlong FD (α.(ncomp) i) (residualWord (rank i) (wgen k 0 a))
    (paddedWord k (topFaceWord i a)) (shiftTopComponent p k a i)
    (FD.(phom) (paddedWord k (keepToTop g)) x)
  • diagramRelation FD (paddedWord k (keepToTop g)) (paddedWord k (topFaceWord i a))
      (paddedWord k (wskip a (wid p))) (paddedWord k g) (wholeBoundaryPaddedWord i g a) x.
Proof.
  lazymatch goal with |- @eq ?E (f_equal ?rd ?pth) ?rhs =>
    let rd' := eval lazy beta iota zeta delta [Pseudofunctor.psObj
      PseudofunctorOps.structureMapPseudofunctor
      LocallyDiscrete.locallyDiscreteFunctor BicategoryEq.f2obj
      residualFunctor fobj] in rd in
    change (@eq E (f_equal rd' pth) rhs)
  end.
  lazymatch goal with |- @eq ?E (f_equal ?rd ?pth) ?rhs =>
    let pth' := eval lazy beta iota zeta delta [matchingPartialSplitEquiv compEquiv
      matchingStepBridge sigTEquiv sigTEquivSnd sigTEquivFst piEquiv
      matchingSplitEquiv qinvEquiv eqvFun SigT.projT1 SigT.projT2] in pth in
    change (@eq E (f_equal rd pth') rhs)
  end.
  lazymatch goal with |- @eq ?E (f_equal ?rd ?pth) ?rhs =>
    let pth' := eval lazy beta iota zeta delta
      [prependPathEquiv
        qinvEquiv eqvFun] in pth in
    change (@eq E (f_equal rd pth') rhs)
  end.
  lazymatch goal with |- @eq ?E ?lhs ?rhs =>
    lazymatch rhs with @eq_trans _ _ _ _ ?r1 ?r2 =>
      let T1 := type of r1 in let T2 := type of r2 in
      lazymatch T1 with @eq ?B ?s ?m =>
        lazymatch T2 with @eq _ _ ?t => change (@eq (@eq B s t) lhs rhs) end
      end
    end
  end.
  lazymatch goal with |- @eq ?E (@f_equal _ _ _ _ _ ?pth) ?rhs =>
    lazymatch pth with @eq_trans ?T _ _ _ _ _ =>
      let rdT := constr:(fun z: T => z.1 i g) in
      change (@eq E (f_equal rdT pth) rhs)
    end
  end.
  lazymatch goal with
  | |- @eq _ (@f_equal _ _ _ _ _ (@eq_trans _ ?y ?mid _ _ _)) _ =>
    lazymatch mid with
    | @topFaceMatching ?AA ?nn ?XX ?aa ?bb =>
      lazymatch bb with
      | context [@splitMatching _ _ _ ?mm] =>
        pose proof (@splitAttachmentPrependReadout AA nn XX mm aa y) as prependFn
      end
    end
  end.
  (* Align the universe instances of the selected prefix path with those of
     the generic helper: [constr_eq] records the universe constraints, which
     makes the application [prependFn eTyped] below check instantly. *)
  lazymatch goal with
  | |- @eq _ (@f_equal _ _ _ _ _ (@eq_trans _ _ ?mid _ ?e _)) _ =>
    lazymatch mid with
    | @topFaceMatching _ _ ?X0 _ ?b0 =>
      lazymatch b0 with context [@splitMatching _ _ ?X1 _] => constr_eq X0 X1 end
    end;
    let ET := type of e in let FT := type of prependFn in
    lazymatch FT with forall _: @eq ?T2 ?y2 ?z2, _ =>
    lazymatch ET with @eq ?T1 ?y1 ?z1 =>
      constr_eq T1 T2; constr_eq y1 y2;
      let TN1 := eval lazy beta iota zeta delta
        [MatchingObject gsigT hgpdOfHSet GDom hsigT HSet.Dom] in T1 in
      let TN2 := eval lazy beta iota zeta delta
        [MatchingObject gsigT hgpdOfHSet GDom hsigT HSet.Dom] in T2 in
      constr_eq TN1 TN2;
      lazymatch z1 with @topFaceMatching ?A1 ?n1 ?X1 ?a1 ?b1 =>
      lazymatch z2 with @topFaceMatching ?A2 ?n2 ?X2 ?a2 ?b2 =>
        constr_eq A1 A2; constr_eq n1 n2; constr_eq X1 X2; constr_eq a1 a2;
        let BN1 := eval lazy beta iota zeta delta [splitMatching SigT.projT1] in b1 in
        let BN2 := eval lazy beta iota zeta delta [splitMatching SigT.projT1] in b2 in
        constr_eq BN1 BN2
      end end
    end end
  end.
  lazymatch goal with
  | |- @eq _ (@f_equal _ _ _ _ _ (@eq_trans _ _ _ _ ?e _)) _ =>
    let ET := type of e in
    let ET' := eval lazy beta iota zeta delta [splitMatching SigT.projT1] in ET in
    pose (eTyped := e);
    change ET' in (type of eTyped)
  end.
  let FT := type of prependFn in
  let FT' := eval lazy beta iota zeta delta [splitMatching SigT.projT1 SigT.projT2] in FT in
  change FT' in prependFn.
  pose proof (prependFn eTyped i g) as hprepend.
  refine (hprepend • _).
  unfold eTyped.
  lazymatch goal with |- context [f_equal ?rd (eq_sym ?e)] =>
  rewrite (fEqualSym rd e)
  end.
  lazymatch goal with |- context [shiftPrefixTopFace ?pp ?kk ?FF ?aa ?bb] =>
  rewrite (shiftPrefixTopFaceValue pp kk FF aa bb i g)
  end.
  rewrite eq_sym_involutive.
  lazymatch goal with |- context [mixedComparison ?XX ?mm ?aa] =>
  pose proof (splitMatchingPathValue XX mm aa i g) as hscalar
  end.
  let HT := type of hscalar in
  let HT' := eval lazy beta iota zeta delta [splitMatching SigT.projT1 SigT.projT2] in HT in
  change HT' in hscalar.
  rewrite hscalar.
  cbn [splitMatching].
  lazymatch goal with
  | |- context [matchingValue (keepMatching ?XX ?mm) ?ii ?gg] =>
    change (matchingValue (keepMatching XX mm) ii gg)
      with (matchingValue mm (raiseIndex ii) (keepToTop gg))
  end.
  change
  (matchingValue (partialBoundary (S p) F k x) (raiseIndex i) (keepToTop g))
  with (FD.(phom) (paddedWord k (keepToTop g)) x).
  apply transCongL.
  unfold mixedComparisonValue, skippedValueComparison.
  lazymatch goal with |- context [matchingPath ?mm _ _] =>
  let mm' := eval lazy beta iota zeta delta [partialBoundary] in mm in
  lazymatch mm' with @matchingMap _ _ ?DD ?xx =>
    pose proof (diagramForkRelation (diagramData DD)
      (a := None) (b := Some (raiseIndex i)) (b' := Some None)
      (c := Some (Some i))
      (keepToTop g) (topFaceWord i a) (wskip a (wid p)) g (wskip a g)
      (keepTopFaceWord g a) (skippedWord a g) (splitBoundaryWord i g a) xx)
      as hfork
  end
  end.
  refine (hfork • _).
  now exact (pullbackDiagramRelation fullPrefix F
  (i := None) (j := Some (raiseIndex i)) (j' := Some None) (k := Some (Some i))
  (keepToTop g) (topFaceWord i a) (wskip a (wid p)) g
  (splitBoundaryWord i g a) (wholeBoundaryPaddedWord i g a) x).
Defined.

Lemma wholeBoundaryAttachment (x: F.(pfObj) (S p + k)) a:
  f_equal (residualMatching p F (wgen k 0 a)) (shiftPrefixBoundary p k F x)
    • boundaryNatural p F (wgen k 0 a) (shiftPrefixCell p k F x) =
  ((matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x)).2 a).2
    • f_equal (partialBoundary p F k) (wholeBoundaryTop x a).
Proof.
  apply (matchingPathExt (shiftedPrefix p k F)); intros i g.
  lazymatch goal with |- @eq _ (f_equal ?rd (?u • ?v)) _ =>
    rewrite (mapTrans rd u v)
  end.
  lazymatch goal with |- @eq _ _ (f_equal ?rd (?u • ?v)) =>
    rewrite (mapTrans rd u v)
  end.
  rewrite (residualMatchingMapPath p F (wgen k 0 a)
    (shiftPrefixBoundary p k F x) i g).
  rewrite (shiftPrefixBoundaryValueRelation
    p k F x i g).
  rewrite (boundaryNaturalValueRelation p F (wgen k 0 a)
    (shiftPrefixCell p k F x) i g).
  rewrite (wholeBoundaryAttachmentValue x a i g).
  rewrite (partialBoundaryMapPath p F k (wholeBoundaryTop x a) i g).
  unfold wholeBoundaryTop. rewrite fEqualSym.
  apply removeCubeFactor.
  now exact (diagramIsoCubeAlong F (eq_sym (Nat.add_succ_r p k))
    (f_equal (fun U: Functor (PrefixCategory A p) (Op (νSemiShape A)) =>
      U.(fobj) i) (shiftPrefixFunctorEq p k))
    wholeShift (α.(ncomp) i) eq_refl (natComponent (shiftPrefixFunctorEq p k) i)
    (paddedWord k (keepToTop g)) (paddedWord (S k) g) (paddedWord k g)
    (paddedWord k (wskip a (wid p))) (paddedWord k (topFaceWord i a))
    (residualWord p (wgen k 0 a)) (residualWord (rank i) (wgen k 0 a))
    (shiftPrefixBoundaryWord p k i g)
    (wholeBoundaryTopWord a) (shiftTopComponent p k a i)
    (wholeBoundaryPaddedWord i g a) (paddedResidual g (wgen k 0 a)) x).
Defined.

Definition wholeBoundary (x: F.(pfObj) (S p + k)):
  matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x) =
    matchingStepBoundary p F k (shiftPrefixCell p k F x) :=
  attachmentEq (fun a => residualMatching p F (wgen k 0 a)) (partialBoundary p F k)
    (matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x))
    (matchingStepBoundary p F k (shiftPrefixCell p k F x))
    (shiftPrefixBoundary p k F x) (wholeBoundaryTop x)
    (wholeBoundaryAttachment x).

Lemma wholeBoundaryBase (x: F.(pfObj) (S p + k)):
  f_equal (fun z: MatchingStep p F k => z.1) (wholeBoundary x) =
    shiftPrefixBoundary p k F x.
Proof.
  now exact (attachmentEqBase (fun a => residualMatching p F (wgen k 0 a))
    (partialBoundary p F k)
    (matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x))
    (matchingStepBoundary p F k (shiftPrefixCell p k F x))
    (shiftPrefixBoundary p k F x) (wholeBoundaryTop x)
    (wholeBoundaryAttachment x)).
Defined.

Lemma wholeBoundaryCell (x: F.(pfObj) (S p + k)) a:
  f_equal (fun z: MatchingStep p F k => (z.2 a).1) (wholeBoundary x) =
    wholeBoundaryTop x a.
Proof.
  now exact (attachmentEqTop (fun a => residualMatching p F (wgen k 0 a))
    (partialBoundary p F k)
    (matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x))
    (matchingStepBoundary p F k (shiftPrefixCell p k F x))
    (shiftPrefixBoundary p k F x) (wholeBoundaryTop x)
    (wholeBoundaryAttachment x) a).
Defined.

End WholeBoundary.

(** The whole-cell boundary comparison is compatible with the faces of the
    partial matching split. *)

Lemma boundaryNaturalityValueRelation {A: HSet} (p: nat)
  (F: PathDiagramFamily (Op (νSemiShape A))) {k l: nat} (u: Word A k l)
  (x: F.(pfObj) (p + l)) (i: Index p) (g: Word A (rank i) p):
  f_equal (fun z: MatchingObject (shiftedPrefix p k F) => matchingValue z i g) (boundaryNaturality p F u x) =
  diagramRelation (pathData _ _ F.(pfStr))
    (residualWord p u) (paddedWord k g) (paddedWord l g) (residualWord (rank i) u)
    (eq_sym (paddedResidual g u)) x.
Proof.
  unfold boundaryNaturality.
  rewrite fEqualSym, boundaryNaturalValueRelation.
  now exact (diagramRelationReverse _ _ _ _ _ _ _).
Defined.

Section Modification.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation FD := (pathData _ _ F.(pfStr)).
Local Abbreviation MD := (matchingPullbackDiagram (A := A) p (Op (νSemiShape A)) F).
Local Abbreviation P := (MatchingPartialPresentation (S p) F).
Local Abbreviation Q := (MatchingStepPresentation p F).
Local Abbreviation C := (ofPsfTot A (wholeCellDiagram p F)).
Local Abbreviation D := (ofPsfTot A (wholeCellDiagram (S p) F)).
Local Abbreviation α k :=
  (@idToHom (functorCategory (PrefixCategory A p) (Op (νSemiShape A))) _ _
    (shiftPrefixFunctorEq (A := A) p k)).
Local Abbreviation wholeShift k :=
  (@idToHom (Op (νSemiShape A)) _ _ (eq_sym (Nat.add_succ_r p k))).

Definition wholeShiftFaceWord k q (Hq: q <= k) a:
  wcomp (residualWord (S p) (wgen k q a)) (wholeShift k) =
    wcomp (wholeShift (S k)) (residualWord p (wgen (S k) (S q) a)) :=
  (wholeCellShiftNat A p).(nnat) (wgen k q a)
    • f_equal (fun w: Word A (S k) (S (S k)) =>
        wcomp (wholeShift (S k)) (residualWord p w))
        (residualOneGen k q Hq a).

Definition componentShiftFaceWord k q (Hq: q <= k) a (i: Index p):
  wcomp (residualWord (rank (raiseIndex i)) (wgen k q a)) ((α k).(ncomp) i) =
    wcomp ((α (S k)).(ncomp) i) (residualWord (rank i) (wgen (S k) (S q) a)) :=
  f_equal (fun β: NatTrans
    (compFunctor (shiftFunctor A p) (shiftPrefixFunctor A (S p) (S k)))
    (shiftPrefixFunctor A p (S k)) => β.(ncomp) i)
    (shiftPrefixResidualFace p k q Hq a).

Lemma splitBaseMapPathValue k {b c: P.(G0) k} (e: b = c)
  (i: Index p) (g: Word A (rank i) p):
  f_equal (fun z: MatchingObject (shiftedPrefix p (S k) F) => matchingValue z i g) (f_equal (splitBaseMap p F k) e) =
  f_equal (FD.(phom) ((α k).(ncomp) i))
    (f_equal (fun z: P.(G0) k => matchingValue z (raiseIndex i) (keepToTop g)) e).
Proof. now destruct e. Defined.

Lemma splitBaseFaceValue k q (Hq: q <= k) a (m: P.(G0) (S k))
  (i: Index p) (g: Word A (rank i) p):
  f_equal (fun z: MatchingObject (shiftedPrefix p (S k) F) => matchingValue z i g) (splitBaseFace p F k q Hq a m) =
  diagramRelation FD (residualWord (rank (raiseIndex i)) (wgen k q a))
    ((α k).(ncomp) i) ((α (S k)).(ncomp) i)
    (residualWord (rank i) (wgen (S k) (S q) a))
    (componentShiftFaceWord k q Hq a i)
    (matchingValue m (raiseIndex i) (keepToTop g)).
Proof.
  unfold splitBaseFace. rewrite eq_trans_map_distr,
    matchingActionMapPath, keptResidualFaceValue.
  cbn [f_equal]. rewrite eq_trans_refl_l.
  rewrite (residualShiftFaceRelation MD (shiftedResidualFunctor A p)
    (residualFunctor A p) (shiftPrefixResidualTransformation A p)
    k q Hq a (keptResidualMap p F (S k) m) (shiftPrefixResidualFace p k q Hq a)).
  now exact (matchingRelationValue p (Op (νSemiShape A)) F _ _ _ _
    (shiftPrefixResidualFace p k q Hq a) (keptResidualMap p F (S k) m)
    i g (componentShiftFaceWord k q Hq a i)).
Defined.

Lemma wholeBoundaryBaseModification k q (Hq: q <= k) a (x: D.(G0) (S k)):
  shiftPrefixBoundary p k F (D.(GFace) k q Hq a x)
    • (f_equal (partialBoundary p F (S k)) (shiftCellFace p F k q Hq a x)
      • boundaryNaturality p F (wgen (S k) (S q) a) (shiftPrefixCell p (S k) F x)) =
  f_equal (splitBaseMap p F k) (boundaryNaturality (S p) F (wgen k q a) x)
    • (splitBaseFace p F k q Hq a (partialBoundary (S p) F (S k) x)
      • f_equal (residualMatching p F (wgen (S k) (S q) a))
          (shiftPrefixBoundary p (S k) F x)).
Proof.
  apply (matchingPathExt (shiftedPrefix p (S k) F)); intros i g.
  rewrite 4 eq_trans_map_distr, partialBoundaryMapPath, splitBaseMapPathValue.
  rewrite (splitBaseFaceValue k q Hq a (partialBoundary (S p) F (S k) x) i g).
  rewrite (residualMatchingMapPath p F (wgen (S k) (S q) a)
    (shiftPrefixBoundary p (S k) F x) i g).
  rewrite (shiftPrefixBoundaryValueRelation
    p (S k) F x i g).
  rewrite (shiftPrefixBoundaryValueRelation
    p k F (D.(GFace) k q Hq a x) i g).
  rewrite (boundaryNaturalityValueRelation p F (wgen (S k) (S q) a)
    (shiftPrefixCell p (S k) F x) i g).
  rewrite (boundaryNaturalityValueRelation (S p) F (wgen k q a) x
    (raiseIndex i) (keepToTop g)).
  rewrite (shiftCellFaceRelation p F k q Hq a x (wholeShiftFaceWord k q Hq a)).
  now exact (diagramBoundaryCubeAlong F
    (eq_sym (Nat.add_succ_r p (S k))) (eq_sym (Nat.add_succ_r p k))
    (f_equal (fun U: Functor (PrefixCategory A p) (Op (νSemiShape A)) => U.(fobj) i) (shiftPrefixFunctorEq (A := A) p (S k)))
    (f_equal (fun U: Functor (PrefixCategory A p) (Op (νSemiShape A)) => U.(fobj) i) (shiftPrefixFunctorEq (A := A) p k))
    (wholeShift (S k)) (wholeShift k) ((α (S k)).(ncomp) i) ((α k).(ncomp) i)
    eq_refl eq_refl (natComponent (shiftPrefixFunctorEq (A := A) p (S k)) i)
    (natComponent (shiftPrefixFunctorEq (A := A) p k) i)
    (residualWord (S p) (wgen k q a)) (residualWord p (wgen (S k) (S q) a))
    (residualWord (rank (raiseIndex i)) (wgen k q a))
    (residualWord (rank i) (wgen (S k) (S q) a))
    (paddedWord (S k) (keepToTop g)) (paddedWord k (keepToTop g))
    (paddedWord (S (S k)) g) (paddedWord (S k) g)
    (wholeShiftFaceWord k q Hq a) (componentShiftFaceWord k q Hq a i)
    (shiftPrefixBoundaryWord p (S k) i g)
    (shiftPrefixBoundaryWord p k i g)
    (eq_sym (paddedResidual (keepToTop g) (wgen k q a)))
    (eq_sym (paddedResidual g (wgen (S k) (S q) a))) x).
Defined.

Definition wholeMixedWord k q (Hq: q <= k) a c:
  wcomp (residualWord p (wgen (S k) (S q) a)) (residualWord p (wgen k 0 c)) =
    wcomp (residualWord p (wgen (S k) 0 c)) (residualWord p (wgen k q a)) :=
  f_equal (fun β: NatTrans (shiftPrefixFunctor A (S p) (S (S k)))
    (shiftPrefixFunctor A (S p) k) => β.(ncomp) (None: Index (S p)))
    (residualNatExchange (A := A) (S p) k q Hq a c).

Lemma wholeCellMixedReverse k q (Hq: q <= k) a c (x: C.(G0) (S (S k))):
  eq_sym (C.(GFaceCoh) k q Hq 0 leR_O a c x) =
  diagramRelation FD (residualWord p (wgen (S k) (S q) a))
    (residualWord p (wgen k 0 c)) (residualWord p (wgen (S k) 0 c))
    (residualWord p (wgen k q a)) (wholeMixedWord k q Hq a c) x.
Proof.
  lazymatch goal with |- _ = ?rhs =>
    change (eq_sym (diagramRelation (pathData _ _ (wholeCellDiagram p F).(pfStr))
      (wgen (S k) 0 c) (wgen k q a) (wgen (S k) (S q) a) (wgen k 0 c)
      (wgenExchange k q Hq 0 leR_O a c) x) = rhs)
  end.
  rewrite (pullbackDiagramRelation (wholeCellFunctor A p) F
    (wgen (S k) 0 c) (wgen k q a) (wgen (S k) (S q) a) (wgen k 0 c)
    (wgenExchange k q Hq 0 leR_O a c) (eq_sym (wholeMixedWord k q Hq a c)) x).
  refine (diagramRelationReverse _ _ _ _ _ _ _ • _).
  now rewrite eq_sym_involutive.
Defined.

Local Lemma removeBothCubeFactors {T: Type} {a b c d e: T}
  (u: a = b) (v: b = c) (r: c = d) (s: a = e) (t: e = d)
  (cube: u • (v • r) = s • t): eq_sym s • (u • v) = t • eq_sym r.
Proof.
  destruct s, r. cbn in cube |- *.
  rewrite eq_trans_refl_l in cube |- *. now exact cube.
Defined.

Lemma wholeBoundaryCellModification k q (Hq: q <= k) a
  (x: D.(G0) (S k)) c:
  wholeBoundaryTop p k F (D.(GFace) k q Hq a x) c
    • (f_equal (C.(GFace) k 0 leR_O c) (shiftCellFace p F k q Hq a x)
      • eq_sym (C.(GFaceCoh) k q Hq 0 leR_O a c (shiftPrefixCell p (S k) F x))) =
  f_equal (fun z: P.(G0) k => matchingValue z None (wskip c (wid p)))
      (boundaryNaturality (S p) F (wgen k q a) x)
    • f_equal (C.(GFace) k q Hq a) (wholeBoundaryTop p (S k) F x c).
Proof.
  unfold wholeBoundaryTop.
  rewrite fEqualSym, boundaryNaturalityValueRelation,
    (shiftCellFaceRelation p F k q Hq a x (wholeShiftFaceWord k q Hq a)),
    wholeCellMixedReverse.
  apply removeBothCubeFactors.
  now exact (diagramIsoCubeAlong F (eq_sym (Nat.add_succ_r p (S k)))
    (eq_sym (Nat.add_succ_r p k)) (wholeShift (S k)) (wholeShift k) eq_refl eq_refl
    (residualWord (S p) (wgen k q a)) (residualWord p (wgen (S k) (S q) a))
    (residualWord p (wgen k q a))
    (paddedWord (S k) (wskip c (wid p))) (paddedWord k (wskip c (wid p)))
    (residualWord p (wgen (S k) 0 c)) (residualWord p (wgen k 0 c))
    (wholeShiftFaceWord k q Hq a)
    (wholeBoundaryTopWord p (S k) c) (wholeBoundaryTopWord p k c)
    (eq_sym (paddedResidual (wskip c (wid p)) (wgen k q a)))
    (wholeMixedWord k q Hq a c) x).
Defined.

Local Lemma stepBoundaryBaseAp k {x y: C.(G0) (S k)} (e: x = y):
  f_equal (fun z: MatchingStep p F k => z.1)
    (f_equal (matchingStepBoundary p F k) e) =
  f_equal (partialBoundary p F (S k)) e.
Proof. now destruct e. Defined.

Local Lemma stepBoundaryCellAp k {x y: C.(G0) (S k)} (e: x = y) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1)
    (f_equal (matchingStepBoundary p F k) e) =
  f_equal (C.(GFace) k 0 leR_O c) e.
Proof. now destruct e. Defined.

Local Lemma stepFaceBaseAp k q (Hq: q <= k) a {x y: Q.(G0) (S k)} (e: x = y):
  f_equal (fun z: MatchingStep p F k => z.1) (f_equal (Q.(GFace) k q Hq a) e) =
  f_equal (residualMatching p F (wgen (S k) (S q) a))
    (f_equal (fun z: MatchingStep p F (S k) => z.1) e).
Proof. now destruct e. Defined.

Local Lemma stepFaceCellAp k q (Hq: q <= k) a {x y: Q.(G0) (S k)} (e: x = y) c:
  f_equal (fun z: MatchingStep p F k => (z.2 c).1) (f_equal (Q.(GFace) k q Hq a) e) =
  f_equal (C.(GFace) k q Hq a)
    (f_equal (fun z: MatchingStep p F (S k) => (z.2 c).1) e).
Proof. now destruct e. Defined.

(** This square compares the chosen boundary path with both chosen face
    paths, for every whole cell. *)
Lemma wholeBoundaryModification k q (Hq: q <= k) a (x: D.(G0) (S k)):
  wholeBoundary p k F (D.(GFace) k q Hq a x)
    • (f_equal (matchingStepBoundary p F k) (shiftCellFace p F k q Hq a x)
      • matchingStepBoundaryFace p F k q Hq a (shiftPrefixCell p (S k) F x)) =
  (f_equal (matchingPartialSplitEquiv p F k)
      (boundaryNaturality (S p) F (wgen k q a) x)
    • matchingPartialSplitFace p F k q Hq a (partialBoundary (S p) F (S k) x))
      • f_equal (Q.(GFace) k q Hq a) (wholeBoundary p (S k) F x).
Proof.
  apply (matchingStepPathExt p F k).
  - rewrite 4 eq_trans_map_distr.
    rewrite (stepBoundaryBaseAp k (shiftCellFace p F k q Hq a x)).
    rewrite (matchingStepBoundaryFaceBase p F k q Hq a (shiftPrefixCell p (S k) F x)).
    rewrite (matchingPartialSplitMapPathBase p F k
      (boundaryNaturality (S p) F (wgen k q a) x)).
    rewrite (matchingPartialSplitFaceBase p F k q Hq a
      (partialBoundary (S p) F (S k) x)).
    rewrite (stepFaceBaseAp k q Hq a (wholeBoundary p (S k) F x)).
    rewrite (wholeBoundaryBase p k F (D.(GFace) k q Hq a x)).
    rewrite (wholeBoundaryBase p (S k) F x).
    refine (wholeBoundaryBaseModification k q Hq a x • _).
    rewrite <- (splitBaseFaceFormula p F k q Hq a
      (partialBoundary (S p) F (S k) x)).
    now exact (eq_sym (eqTransAssoc _ _ _)).
  - intro c. rewrite 4 eq_trans_map_distr.
    rewrite (stepBoundaryCellAp k (shiftCellFace p F k q Hq a x) c).
    rewrite (matchingStepBoundaryFaceCell p F k q Hq a
      (shiftPrefixCell p (S k) F x) c).
    rewrite (matchingPartialSplitMapPathCell p F k
      (boundaryNaturality (S p) F (wgen k q a) x) c).
    rewrite (matchingPartialSplitFaceCell p F k q Hq a
      (partialBoundary (S p) F (S k) x) c).
    rewrite (stepFaceCellAp k q Hq a (wholeBoundary p (S k) F x) c).
    rewrite (wholeBoundaryCell p k F (D.(GFace) k q Hq a x) c).
    rewrite (wholeBoundaryCell p (S k) F x c).
    now exact (wholeBoundaryCellModification k q Hq a x c).
Defined.

Lemma wholeBoundaryActionModification k q (Hq: q <= k) a (x: D.(G0) (S k)):
  wholeBoundary p k F (D.(GFace) k q Hq a x)
    • (f_equal (matchingStepBoundary p F k)
        (eq_sym (shiftCellComparisonFace p F k q Hq a x))
      • matchingStepBoundaryFace p F k q Hq a (shiftPrefixCell p (S k) F x)) =
  (f_equal (matchingPartialSplitEquiv p F k)
      (boundaryNaturality (S p) F (wgen k q a) x)
    • matchingPartialSplitFace p F k q Hq a (partialBoundary (S p) F (S k) x))
      • f_equal (Q.(GFace) k q Hq a) (wholeBoundary p (S k) F x).
Proof.
  unfold shiftCellComparisonFace. rewrite eq_sym_involutive.
  now apply wholeBoundaryModification.
Defined.

Lemma wholeBoundaryModelSquare k q (Hq: q <= k) a (x: D.(G0) (S k)):
  f_equal (matchingPartialSplitEquiv p F k)
      (boundaryNaturality (S p) F (wgen k q a) x)
    • (matchingPartialSplitFace p F k q Hq a (partialBoundary (S p) F (S k) x)
      • f_equal (Q.(GFace) k q Hq a) (wholeBoundary p (S k) F x)) =
  wholeBoundary p k F (D.(GFace) k q Hq a x)
    • (f_equal (matchingStepBoundary p F k)
        (eq_sym (shiftCellComparisonFace p F k q Hq a x))
      • matchingStepBoundaryFace p F k q Hq a (shiftPrefixCell p (S k) F x)).
Proof.
  now exact (eq_sym (wholeBoundaryActionModification k q Hq a x
    • eqTransAssoc
      (f_equal (matchingPartialSplitEquiv p F k)
        (boundaryNaturality (S p) F (wgen k q a) x))
      (matchingPartialSplitFace p F k q Hq a (partialBoundary (S p) F (S k) x))
      (f_equal (Q.(GFace) k q Hq a) (wholeBoundary p (S k) F x)))).
Defined.

End Modification.

Unset Keyed Unification.

(** The boundary and boundary-face fields of the partial matching split
    equivalence, in the argument order of the residual target. *)

Section Fields.
Context {A: HSet} (p: nat) (F: PathDiagramFamily (Op (νSemiShape A))).
Local Abbreviation P := (MatchingPartialPresentation (S p) F).
Local Abbreviation Q := (MatchingStepPresentation p F).
Local Abbreviation D := (ofPsfTot A (wholeCellDiagram (S p) F)).

Definition matchingPartialSplitBoundary k (x: F.(pfObj) (S p + k)):
  matchingPartialSplitEquiv p F k (partialBoundary (S p) F k x) =
    matchingStepBoundary p F k (shiftPrefixCell p k F x) :=
  wholeBoundary p k F x.

Definition matchingPartialSplitBoundaryFace k q (Hq: q <= k) a (x: D.(G0) (S k)):
  f_equal (matchingPartialSplitEquiv p F k)
      (boundaryNaturality (S p) F (wgen k q a) x)
    • (matchingPartialSplitFace p F k q Hq a (partialBoundary (S p) F (S k) x)
      • f_equal (Q.(GFace) k q Hq a) (matchingPartialSplitBoundary (S k) x)) =
  matchingPartialSplitBoundary k (D.(GFace) k q Hq a x)
    • (f_equal (matchingStepBoundary p F k)
        (eq_sym (shiftCellComparisonFace p F k q Hq a x))
      • matchingStepBoundaryFace p F k q Hq a (shiftPrefixCell p (S k) F x)) :=
  wholeBoundaryModelSquare p F k q Hq a x.

End Fields.
