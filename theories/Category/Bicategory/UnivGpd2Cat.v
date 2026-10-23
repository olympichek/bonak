(** The bicategory of univalent groupoids, functors, and natural transformations. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.Category Require Import Category CategoryEq Groupoid.
From Bonak.Category.Bicategory Require Export Bicategory.
From Bonak.Category.Bicategory Require Import Groupoids Full.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Set Keyed Unification.

Definition UnivGpd2Cat: Bicategory :=
  fullBicategory GroupoidBicat (fun G: UnivalentGroupoid => G.(underlyingGroupoid)).

Definition univGpdLocallyGroupoid: IsLocallyGroupoid UnivGpd2Cat :=
  fun G H F F' α => natInvertible α.

(** Transport along functor equalities is determined by their object parts. *)
Lemma ncompHom2Rew {G H: UnivalentGroupoid} {F F' K K': Functor G H}
  (p: F = F') (q: K = K') (α: NatTrans F K) (x: G.(CObj)):
  (@hom2Rew UnivGpd2Cat G H F F' K K' p q α).(ncomp) x
  = rew [fun o => H.(CHom) (F'.(fobj) x) (o x)] (f_equal fobj q) in
    rew [fun o => H.(CHom) (o x) (K.(fobj) x)] (f_equal fobj p) in
    α.(ncomp) x.
Proof. exact (ncompRew p q α x). Qed.

Lemma ncompHom2RewOn {G H: UnivalentGroupoid} {Fo Ko: G.(CObj) -> H.(CObj)}
  (zF wF: FunctorOn Fo) (zK wK: FunctorOn Ko)
  (p: ofFunctorOn zF = ofFunctorOn wF) (q: ofFunctorOn zK = ofFunctorOn wK)
  (hp: f_equal fobj p = eq_refl) (hq: f_equal fobj q = eq_refl)
  (α: NatTrans (ofFunctorOn zF) (ofFunctorOn zK)) (x: G.(CObj)):
  (@hom2Rew UnivGpd2Cat G H _ _ _ _ p q α).(ncomp) x = α.(ncomp) x.
Proof. exact (ncompRewOn zF wF zK wK p q hp hq α x). Qed.
