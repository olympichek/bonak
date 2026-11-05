(** H-set diagrams on the ν-shape category, whose morphisms include
    degeneracies. Latching is not trivial here: the next level has to carry
    lifts of the lower cells, compatible with their prescribed boundaries. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat.
From Bonak.Lib Require Import HSet SigT FinitePrefix.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Presheaf.Dgn Require Import Generators.
From Bonak.Reedy Require Export MatchingSystem.
From Bonak.Reedy.Dgn Require Import ShapeAction.

Set Primitive Projections.
Set Printing Projections.

Definition Diagram (A: HSet) (n: nat): Type :=
  Functor (Op (PrefixCategory A n)) HSetCat.

Definition cells {A n} (X: Diagram A n) (i: Index n): HSet := X.(fobj) i.

Definition act {A n} (X: Diagram A n) {i j}
  (s: Shape A (rank i) (rank j)): cells X j -> cells X i :=
  X.(fhom) (a := j) (b := i) s.

Lemma actId {A n} (X: Diagram A n) i (x: cells X i): act X (shapeId (rank i)) x = x.
Proof. now exact (fhomIdPt X i x). Defined.

Lemma actComp {A n} (X: Diagram A n) {i j k}
  (s: Shape A (rank i) (rank j)) (t: Shape A (rank j) (rank k)) (x: cells X k):
  act X s (act X t x) = act X (shapeComp s t) x.
Proof. now exact (fhomCompPt X (a := k) (b := j) (c := i) t s x). Defined.

Definition truncateDiagram {A n} (X: Diagram A (S n)): Diagram A n := {|
  fobj i := X.(fobj) (Some i);
  fhom i j s := X.(fhom) (a := Some i) (b := Some j) s;
  fid i := X.(fid) (Some i);
  fcomp i j k s t := X.(fcomp) (a := Some i) (b := Some j) (c := Some k) s t;
|}.

Section Matching.
Context (A: HSet).

Definition matchingData {n} (X: Diagram A n): HSet :=
  hforall (i: Index n) (f: Shape A (rank i) n), cells X i.

(** The full lower boundary retains its value on every map from a lower rank. *)
Definition MatchingObject {n} (X: Diagram A n): HSet :=
  {b: matchingData X &
    hforall (i j: Index n) (f: Shape A (rank i) (rank j)) (g: Shape A (rank j) n),
      hEq (act X f (b j g)) (b i (shapeComp f g))}.

Lemma matchingExt {n} {X: Diagram A n} (b c: MatchingObject X)
  (e: forall i f, b.1 i f = c.1 i f): b = c.
Proof.
  destruct b as [b hb], c as [c hc]; cbn in e.
  assert (p: b = c).
  { repeat (apply functional_extensionality_dep; intro). now apply e. }
  destruct p. apply f_equal.
  repeat (apply functional_extensionality_dep; intro). now apply UIP.
Defined.

(** Each incoming map of the contravariant diagram has a prescribed lower boundary. *)
Definition latchingBoundary {n} (X: Diagram A n) {i: Index n}
  (d: Shape A n (rank i)) (x: cells X i): MatchingObject X.
Proof.
  exists (fun j f => act X (i := j) (j := i) (shapeComp f d) x).
  intros j k f g. rewrite actComp, shapeAssoc. now reflexivity.
Defined.

End Matching.

(** A cocone on the lower incoming maps presents a map from the latching
    object. Its components lift the prescribed map to the matching object. *)
Record LatchingLifts {A: HSet} {n} {X: Diagram A n} {T: HSet}
  {b: T -> MatchingObject A X} := {
  lift: forall i: Index n, Shape A n (rank i) -> cells X i -> T;
  liftBoundary: forall i d x, b (lift i d x) = latchingBoundary A X d x;
  liftComp: forall (i j: Index n) (d: Shape A n (rank i))
    (f: Shape A (rank i) (rank j)) (x: cells X j),
    lift i d (act X f x) = lift j (shapeComp d f) x;
}.
Arguments LatchingLifts {A n} X T b.

Lemma latchingLiftsEq {A: HSet} {n} {X: Diagram A n} {T: HSet}
  {b: T -> MatchingObject A X} (L K: @LatchingLifts A n X T b)
  (e: forall i d x, L.(lift) i d x = K.(lift) i d x): L = K.
Proof.
  destruct L as [l lb lc], K as [k kb kc]; cbn in e.
  assert (p: l = k).
  { repeat (apply functional_extensionality_dep; intro). now apply e. }
  destruct p.
  assert (p: lb = kb).
  { repeat (apply functional_extensionality_dep; intro). now apply UIP. }
  destruct p.
  assert (p: lc = kc).
  { repeat (apply functional_extensionality_dep; intro). now apply UIP. }
  now destruct p.
Defined.

Section Construction.
Context (A: HSet).

Definition matchingMapCells {n} (X: Diagram A n) (T: HSet) (i: Index (S n)): HSet :=
  match i with Some i => cells X i | None => T end.

Definition extensionFace {n} (X: Diagram A n) {T: HSet}
  (b: T -> MatchingObject A X) (i j: Index (S n)):
  Word A (rank i) (rank j) -> matchingMapCells X T j -> matchingMapCells X T i.
Proof.
  destruct i as [i|], j as [j|].
  - now exact (fun f => act X (i := i) (j := j) (shapeFace f)).
  - now exact (fun f x => (b x).1 i (shapeFace f)).
  - intro f. now wordAboveAbsurd.
  - now exact (fun _ x => x).
Defined.

Definition extensionMask {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) (i j: Index (S n)):
  Word hunit (rank i) (rank j) -> matchingMapCells X T i -> matchingMapCells X T j.
Proof.
  destruct i as [i|], j as [j|].
  - now exact (fun d => act X (i := j) (j := i) (shapeMask d)).
  - now exact (fun d => L.(lift) i (shapeMask d)).
  - intro d. now wordAboveAbsurd.
  - now exact (fun _ x => x).
Defined.

Lemma extensionFaceId {n} (X: Diagram A n) {T: HSet}
  (b: T -> MatchingObject A X) i (x: matchingMapCells X T i):
  extensionFace X b i i (wid (rank i)) x = x.
Proof.
  destruct i as [i|].
  - now exact (actId X i x).
  - now reflexivity.
Defined.

Lemma extensionMaskId {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) i (x: matchingMapCells X T i):
  extensionMask X L i i (wid (rank i)) x = x.
Proof.
  destruct i as [i|].
  - now exact (actId X i x).
  - now reflexivity.
Defined.

Lemma extensionFaceComp {n} (X: Diagram A n) {T: HSet}
  (b: T -> MatchingObject A X) (i j k: Index (S n))
  (f: Word A (rank i) (rank j)) (g: Word A (rank j) (rank k))
  (x: matchingMapCells X T k):
  extensionFace X b i j f (extensionFace X b j k g x)
    = extensionFace X b i k (wcomp g f) x.
Proof.
  destruct i as [i|], j as [j|], k as [k|]; cbn [extensionFace];
    try now wordAboveAbsurd.
  - rewrite actComp, shapeFaceComp. now reflexivity.
  - rewrite (b x).2, shapeFaceComp. now reflexivity.
  - rewrite (wordEndId n g), wcompIdl. now reflexivity.
  - now reflexivity.
Defined.

Lemma extensionMaskComp {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) (i j k: Index (S n))
  (r: Word hunit (rank i) (rank j)) (s: Word hunit (rank j) (rank k))
  (x: matchingMapCells X T i):
  extensionMask X L j k s (extensionMask X L i j r x)
    = extensionMask X L i k (wcomp s r) x.
Proof.
  destruct i as [i|], j as [j|], k as [k|]; cbn [extensionMask];
    try now wordAboveAbsurd.
  - rewrite actComp, shapeMaskComp. now reflexivity.
  - rewrite L.(liftComp), shapeMaskComp. now reflexivity.
  - rewrite (wordEndId n s), wcompIdl. now reflexivity.
  - now reflexivity.
Defined.

Definition extensionNormal {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) {i j: Index (S n)}
  (s: Shape A (rank i) (rank j)):
  matchingMapCells X T j -> matchingMapCells X T i :=
  normalAction (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) s.

Lemma extensionNormalLower {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) (i j: Index n) (s: Shape A (rank i) (rank j))
  (x: cells X j):
  extensionNormal X L (i := Some i) (j := Some j) s x = act X s x.
Proof.
  destruct s as [k [r f]].
  destruct (atRank n k (Nat.le_lt_trans _ _ _ (wordBound r) (rankLt i))) as [m em].
  destruct em. unfold extensionNormal.
  rewrite (normalActionFactor (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) (Some i) (Some j) (Some m)).
  change (act X (shapeMask r) (act X (shapeFace f) x) = act X (rank m; (r, f)) x).
  rewrite actComp, shapeFactor. now reflexivity.
Defined.

Lemma extensionNormalBoundary {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) (i: Index n) (s: Shape A (rank i) n) (x: T):
  extensionNormal X L (i := Some i) (j := None) s x = (b x).1 i s.
Proof.
  destruct s as [k [r f]].
  destruct (atRank n k (Nat.le_lt_trans _ _ _ (wordBound r) (rankLt i))) as [m em].
  destruct em. unfold extensionNormal.
  rewrite (normalActionFactor (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) (Some i) None (Some m)).
  change (act X (shapeMask r) ((b x).1 m (shapeFace f)) = (b x).1 i (rank m; (r, f))).
  rewrite (b x).2, shapeFactor. now reflexivity.
Defined.

Lemma extensionNormalLift {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) (j: Index n) (s: Shape A n (rank j)) (x: cells X j):
  extensionNormal X L (i := None) (j := Some j) s x = L.(lift) j s x.
Proof.
  destruct s as [k [r f]].
  destruct (atRank n k (Nat.le_lt_trans _ _ _ (wordBound f) (rankLt j))) as [m em].
  destruct em. unfold extensionNormal.
  rewrite (normalActionFactor (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) None (Some j) (Some m)).
  change (L.(lift) m (shapeMask r) (act X (shapeFace f) x) = L.(lift) j (rank m; (r, f)) x).
  rewrite L.(liftComp), shapeFactor. now reflexivity.
Defined.

Lemma extensionFaceMask {n} (X: Diagram A n) {T: HSet} {b: T -> MatchingObject A X}
  (L: LatchingLifts X T b) (i j k: Index (S n))
  (f: Word A (rank i) (rank j)) (r: Word hunit (rank k) (rank j))
  (x: matchingMapCells X T k):
  extensionFace X b i j f (extensionMask X L k j r x)
    = extensionNormal X L (cross f r) x.
Proof.
  destruct i as [i|], j as [j|], k as [k|]; try now wordAboveAbsurd.
  - rewrite extensionNormalLower.
    change (act X (shapeFace f) (act X (shapeMask r) x) = act X (cross f r) x).
    rewrite actComp, shapeCross. now reflexivity.
  - rewrite extensionNormalLower.
    change ((b (L.(lift) k (shapeMask r) x)).1 i (shapeFace f) = act X (cross f r) x).
    rewrite L.(liftBoundary).
    change (act X (i := i) (j := k) (shapeComp (shapeFace f) (shapeMask r)) x
      = act X (cross f r) x).
    now rewrite shapeCross.
  - rewrite (wordEndId n r), crossIdR.
    unfold extensionNormal, shapeFace.
    rewrite (normalActionFactor (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) (Some i) None (Some i)).
    change ((b x).1 i (shapeFace f) =
      act X (i := i) (j := i) (shapeMask (wid (rank i))) ((b x).1 i (shapeFace f))).
    now symmetry; apply actId.
  - rewrite (wordEndId n f), crossIdL.
    unfold extensionNormal, shapeMask.
    rewrite (normalActionFactor (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) None (Some k) (Some k)).
    change (L.(lift) k (shapeMask r) x =
      L.(lift) k (shapeMask r) (act X (i := k) (j := k) (shapeFace (wid (rank k))) x)).
    apply f_equal. now symmetry; apply actId.
  - rewrite (wordEndId n f), (wordEndId n r), crossIdL.
    unfold extensionNormal, shapeMask.
    rewrite (normalActionFactor (matchingMapCells X T) (extensionFace X b)
    (fun i j => extensionMask X L j i) None None None). now reflexivity.
Defined.

Definition extensionFaceMaskStructure {n} (X: Diagram A n) {T: HSet}
  {b: T -> MatchingObject A X} (L: LatchingLifts X T b):
  FaceMask (A := A) (matchingMapCells X T) := {|
  face := extensionFace X b;
  mask i j := extensionMask X L j i;
  faceId := extensionFaceId X b;
  maskId := extensionMaskId X L;
  faceComp := extensionFaceComp X b;
  maskComp i j k r s x := extensionMaskComp X L k j i s r x;
  faceMask := extensionFaceMask X L;
|}.

Definition extensionAction {n} (X: Diagram A n) {T: HSet}
  {b: T -> MatchingObject A X} (L: LatchingLifts X T b) (i j: Index (S n)):
  Shape A (rank i) (rank j) -> matchingMapCells X T j -> matchingMapCells X T i.
Proof.
  destruct i as [i|], j as [j|].
  - now exact (fun s => act X (i := i) (j := j) s).
  - now exact (fun s x => (b x).1 i s).
  - now exact (fun s => L.(lift) j s).
  - now exact (fun s => extensionNormal X L (i := None) (j := None) s).
Defined.

Lemma extensionActionNormal {n} (X: Diagram A n) {T: HSet}
  {b: T -> MatchingObject A X} (L: LatchingLifts X T b) (i j: Index (S n))
  (s: Shape A (rank i) (rank j)) (x: matchingMapCells X T j):
  extensionAction X L i j s x = action (extensionFaceMaskStructure X L) s x.
Proof.
  destruct i as [i|], j as [j|]; symmetry.
  - now exact (extensionNormalLower X L i j s x).
  - now exact (extensionNormalBoundary X L i s x).
  - now exact (extensionNormalLift X L j s x).
  - now reflexivity.
Defined.

Definition extendByMatchingMap {n} (X: Diagram A n) (T: HSet)
  (b: T -> MatchingObject A X) (L: LatchingLifts X T b): Diagram A (S n).
Proof.
  refine {| fobj := matchingMapCells X T; fhom i j s := extensionAction X L j i s |}.
  - intros [i|].
    + now exact (X.(fid) i).
    + apply functional_extensionality_dep; intro x.
      rewrite extensionActionNormal. now apply actionId.
  - intros [i|] [j|] [k|] s t;
      try (now exact (X.(fcomp) (a := i) (b := j) (c := k) s t));
      apply functional_extensionality_dep; intro x;
      change (extensionAction X L _ _ (shapeComp t s) x =
        extensionAction X L _ _ t (extensionAction X L _ _ s x));
      rewrite 3 extensionActionNormal; now symmetry; apply actionComp.
Defined.

(** A filler family with a cocone lifting the lower diagram. Compatibility with
    the prescribed boundary is the latching-to-matching condition. *)
Definition LiftedFamily {n} (X: Diagram A n): Type :=
  {E: MatchingObject A X -> HSet &T
    LatchingLifts X (hsigT E) (fun x => x.1)}.

Definition emptyDiagram: Diagram A 0.
Proof.
  refine {| fobj := fun i: Index 0 => match i with end;
    fhom := fun (i j: Index 0) => match i with end |}; now intros [].
Defined.

Definition dgnSystem: ExtensionSystem := {|
  stages := {|
    PartialDiagram := Diagram A;
    truncate n := @truncateDiagram A n;
    emptyPartial := emptyDiagram;
  |};
  FillerData n X := LiftedFamily X;
  extendDiagram n X E :=
    extendByMatchingMap X (hsigT E.1) (fun x => x.1) E.2;
|}.

End Construction.

Arguments LatchingLifts A {n} X T b.

Definition SimplicialDgnMatchingSeq := MatchingSeq (dgnSystem hunit).
Definition CubicalDgnMatchingSeq := MatchingSeq (dgnSystem hbool).
