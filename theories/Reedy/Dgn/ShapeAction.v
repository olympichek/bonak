(** Actions of the normal forms of ν-shape on a finite family of h-sets. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.PeanoNat.
From Bonak.Lib Require Import HSet SigT FinitePrefix.
From Bonak.Category Require Import Category Full.
From Bonak.Presheaf.Dgn Require Import Generators.

Set Primitive Projections.
Set Printing Projections.

(** The actions are used at the universes of the diagram cells, which are
    constrained by the ν-shape prefix categories. *)
Set Universe Polymorphism.

(** The full ν-shape category on the ranks below [N]. *)
Definition PrefixCategory (A: HSet) (N: nat): Category :=
  fullCategory (νShape A) (@rank N).

(** Fold a normal form through its uniquely determined intermediate rank. *)
Definition shapeFactorFold {A: HSet} {N p q: nat} {Y: Type}
  (body: forall m: Index N, Word hunit (rank m) p -> Word A (rank m) q -> Y)
  k (r: Word hunit k p) (f: Word A k q) (m: IndexAt N k): Y.
Proof. destruct m as [m e]. destruct e. now exact (body m r f). Defined.

Definition boundedShapeFold {A: HSet} {N p q: nat} {Y: Type}
  (body: forall m: Index N, Word hunit (rank m) p -> Word A (rank m) q -> Y)
  (s: Shape A p q) (h: Nat.lt s.1 N): Y :=
  shapeFactorFold body s.1 (fst s.2) (snd s.2) (atRank N s.1 h).

Lemma boundedShapeFoldFactor {A: HSet} {N p q: nat} {Y: Type}
  (body: forall m: Index N, Word hunit (rank m) p -> Word A (rank m) q -> Y)
  (m: Index N) (r: Word hunit (rank m) p) (f: Word A (rank m) q) h:
  boundedShapeFold body (rank m; (r, f)) h = body m r f.
Proof.
  unfold boundedShapeFold; cbn.
  rewrite (indexAtEq (atRank N (rank m) h) (m; eq_refl)). now reflexivity.
Defined.

Section NormalForms.
Context {A: HSet} {N: nat} (C: Index N -> HSet).

Definition FaceAction: Type :=
  forall i j, Word A (rank i) (rank j) -> C j -> C i.
Definition MaskAction: Type :=
  forall i j, Word hunit (rank j) (rank i) -> C j -> C i.

Context (F: FaceAction) (D: MaskAction).

Definition normalAction {i j: Index N}
  (s: Shape A (rank i) (rank j)): C j -> C i :=
  boundedShapeFold (fun m r f x => D i m r (F m j f x)) s
    (Nat.le_lt_trans _ _ _ (wordBound (fst s.2)) (rankLt i)).

Lemma normalActionFactor (i j m: Index N)
  (r: Word hunit (rank m) (rank i)) (f: Word A (rank m) (rank j)) (x: C j):
  normalAction (rank m; (r, f)) x = D i m r (F m j f x).
Proof. unfold normalAction. now rewrite boundedShapeFoldFactor. Defined.

End NormalForms.

Record FaceMask {A: HSet} {N: nat} {C: Index N -> HSet} := {
  face: FaceAction C;
  mask: MaskAction C;
  faceId i (x: C i): face i i (wid (rank i)) x = x;
  maskId i (x: C i): mask i i (wid (rank i)) x = x;
  faceComp i j k (f: Word A (rank i) (rank j))
    (g: Word A (rank j) (rank k)) (x: C k):
    face i j f (face j k g x) = face i k (wcomp g f) x;
  maskComp i j k (r: Word hunit (rank j) (rank i))
    (s: Word hunit (rank k) (rank j)) (x: C k):
    mask i j r (mask j k s x) = mask i k (wcomp r s) x;
  faceMask i j k (f: Word A (rank i) (rank j))
    (r: Word hunit (rank k) (rank j)) (x: C k):
    face i j f (mask j k r x) = normalAction C face mask (cross f r) x;
}.
Arguments FaceMask {A N} C.

Section Action.
Context {A: HSet} {N: nat} {C: Index N -> HSet} (X: FaceMask (A := A) C).

Definition action {i j: Index N} (s: Shape A (rank i) (rank j)): C j -> C i :=
  normalAction C X.(face) X.(mask) s.

Lemma actionFactor (i j m: Index N)
  (r: Word hunit (rank m) (rank i)) (f: Word A (rank m) (rank j)) (x: C j):
  action (rank m; (r, f)) x = X.(mask) i m r (X.(face) m j f x).
Proof. now apply normalActionFactor. Defined.

Lemma actionId i (x: C i): action (shapeId (rank i)) x = x.
Proof.
  unfold shapeId. rewrite actionFactor, X.(faceId).
  now apply X.(maskId).
Defined.

Lemma actionComp (i j k: Index N)
  (s: Shape A (rank i) (rank j)) (t: Shape A (rank j) (rank k)) (x: C k):
  action s (action t x) = action (shapeComp s t) x.
Proof.
  destruct s as [p [r f]], t as [q [d g]].
  destruct (atRank N p (Nat.le_lt_trans _ _ _ (wordBound r) (rankLt i))) as [m em].
  destruct em.
  destruct (atRank N q (Nat.le_lt_trans _ _ _ (wordBound d) (rankLt j))) as [l el].
  destruct el.
  rewrite 2 actionFactor, X.(faceMask).
  unfold shapeComp; cbn.
  destruct (cross f d) as [p [u v]].
  destruct (atRank N p (Nat.le_lt_trans _ _ _ (wordBound u) (rankLt m))) as [o eo].
  destruct eo.
  change (X.(mask) i m r (action (rank o; (u, v)) (X.(face) l k g x))
    = action (rank o; (wcomp r u, wcomp g v)) x).
  rewrite 2 actionFactor, X.(faceComp), X.(maskComp).
  now reflexivity.
Defined.

End Action.
