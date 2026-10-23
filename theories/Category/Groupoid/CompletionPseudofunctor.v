Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Category Groupoid.
From Bonak.Category.Bicategory Require Import Bicategory Pseudofunctor Groupoids.
From Bonak.Category.Groupoid Require Import SetBased Descent CompletionAction Precomposition.
Set Primitive Projections.
Set Universe Polymorphism.

Set Universe Minimization ToSet.
Set Keyed Unification.

(** The unit laws for the completion action follow by restricting the
    comparison cells to represented objects. *)
Module CompletionUnits (T: PropositionalTruncation).
  Module A := CompletionAction T.
  Import A A.B.C A.P A.P.D.
  Set Universe Polymorphism.
  Local Opaque completedPaths pathCompletionUnit descend descentUnit extendNat.

  Local Lemma imageInverseCancel {G H: Groupoid} (F: Functor G H)
    {a b: G.(CObj)} {c: H.(CObj)} (u: G.(CHom) a b) (r: H.(CHom) c (F.(fobj) a)):
    (r ⨟ F.(fhom) u) ⨟ F.(fhom) (ginv u) = r.
  Proof.
    rewrite cassoc, <- F.(fcomp), ginvR, F.(fid). now apply cidr.
  Qed.

  Local Lemma inverseCancelFront {G: Groupoid} {a b c: G.(CObj)}
    (u: G.(CHom) a b) (f: G.(CHom) a c): u ⨟ (ginv u ⨟ f) = f.
  Proof. rewrite <- cassoc, ginvR. now apply cidl. Qed.

  Lemma liftUnitLawL {G H: HSetGroupoid} (F: Functor G H):
    compNatTrans (liftComposite (idFunctor G) F) (liftNat (functorUnitL F))
    = compNatTrans (whiskerRNat (liftIdentity G) (liftFunctor F)) (functorUnitL (liftFunctor F)).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)).
    apply natTransEq; intro a.
    change ((liftComposite (idFunctor G) F).(ncomp) ((pathCompletionUnit G).(fobj) a)
      ⨟ (liftNat (functorUnitL F)).(ncomp) ((pathCompletionUnit G).(fobj) a)
      = (liftFunctor F).(fhom) ((liftIdentity G).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ⨟ cid ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))).
    apply (groupoidCancelL ((liftCompositeUnit (idFunctor G) F).(ncomp) a)).
    transitivity ((liftUnit F).(ncomp) a).
    - refine (eq_sym ((completedPaths H).(cassoc)
        ((liftCompositeUnit (idFunctor G) F).(ncomp) a)
        ((liftComposite (idFunctor G) F).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ((liftNat (functorUnitL F)).(ncomp) ((pathCompletionUnit G).(fobj) a))) • _).
      refine (f_equal (fun v => v ⨟ (liftNat (functorUnitL F)).(ncomp)
        ((pathCompletionUnit G).(fobj) a)) (liftCompositeComm (idFunctor G) F a) • _).
      refine (liftNatComm (functorUnitL F) a • _).
      change ((pathCompletionUnit H).(fhom) (cid (F.(fobj) a)) ⨟ (liftUnit F).(ncomp) a
        = (liftUnit F).(ncomp) a).
      now rewrite (pathCompletionUnit H).(fid), cidl.
    - apply eq_sym.
      refine (f_equal (fun v => (liftCompositeUnit (idFunctor G) F).(ncomp) a
        ⨟ ((liftFunctor F).(fhom) v ⨟ cid ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))))
        (liftIdentityAt G a) • _).
      refine (f_equal (fun v => (liftCompositeUnit (idFunctor G) F).(ncomp) a ⨟ v)
        ((completedPaths H).(cidr) ((liftFunctor F).(fhom)
          (ginv ((liftUnit (idFunctor G)).(ncomp) a)))) • _).
      now exact (imageInverseCancel (liftFunctor F) ((liftUnit (idFunctor G)).(ncomp) a)
        ((liftUnit F).(ncomp) a)).
  Qed.

  Lemma liftUnitLawR {G H: HSetGroupoid} (F: Functor G H):
    compNatTrans (liftComposite F (idFunctor H)) (liftNat (functorUnitR F))
    = compNatTrans (whiskerLNat (liftFunctor F) (liftIdentity H)) (functorUnitR (liftFunctor F)).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)).
    apply natTransEq; intro a.
    change ((liftComposite F (idFunctor H)).(ncomp) ((pathCompletionUnit G).(fobj) a)
      ⨟ (liftNat (functorUnitR F)).(ncomp) ((pathCompletionUnit G).(fobj) a)
      = (liftIdentity H).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))
        ⨟ cid ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))).
    apply (groupoidCancelL ((liftCompositeUnit F (idFunctor H)).(ncomp) a)).
    transitivity ((liftUnit F).(ncomp) a).
    - refine (eq_sym ((completedPaths H).(cassoc)
        ((liftCompositeUnit F (idFunctor H)).(ncomp) a)
        ((liftComposite F (idFunctor H)).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ((liftNat (functorUnitR F)).(ncomp) ((pathCompletionUnit G).(fobj) a))) • _).
      refine (f_equal (fun v => v ⨟ (liftNat (functorUnitR F)).(ncomp)
        ((pathCompletionUnit G).(fobj) a)) (liftCompositeComm F (idFunctor H) a) • _).
      refine (liftNatComm (functorUnitR F) a • _).
      change ((pathCompletionUnit H).(fhom) (cid (F.(fobj) a)) ⨟ (liftUnit F).(ncomp) a
        = (liftUnit F).(ncomp) a).
      now rewrite (pathCompletionUnit H).(fid), cidl.
    - apply eq_sym.
      refine (f_equal (fun v => (liftCompositeUnit F (idFunctor H)).(ncomp) a ⨟ v)
        ((completedPaths H).(cidr) ((liftIdentity H).(ncomp)
          ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a)))) • _).
      refine ((completedPaths H).(cassoc) ((liftUnit (idFunctor H)).(ncomp) (F.(fobj) a))
        ((liftFunctor (idFunctor H)).(fhom) ((liftUnit F).(ncomp) a))
        ((liftIdentity H).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))) • _).
      refine (f_equal (fun v => (liftUnit (idFunctor H)).(ncomp) (F.(fobj) a) ⨟ v)
        ((liftIdentity H).(nnat) ((liftUnit F).(ncomp) a)) • _).
      refine (f_equal (fun v => (liftUnit (idFunctor H)).(ncomp) (F.(fobj) a)
        ⨟ (v ⨟ (liftUnit F).(ncomp) a)) (liftIdentityAt H (F.(fobj) a)) • _).
      now exact (inverseCancelFront ((liftUnit (idFunctor H)).(ncomp) (F.(fobj) a))
        ((liftUnit F).(ncomp) a)).
  Qed.
End CompletionUnits.

(** The two ways to compose three lifted functors agree after restriction
    along the completion unit. Faithful precomposition gives associativity. *)
Module CompletionAssociativity (T: PropositionalTruncation).
  Module U := CompletionUnits T.
  Module A := U.A.
  Import A A.B.C A.P A.P.D.
  Set Universe Polymorphism.
  Local Opaque completedPaths pathCompletionUnit descend descentUnit extendNat.

  Definition liftTripleUnit {G H K L: HSetGroupoid}
    (F: Functor G H) (E: Functor H K) (J: Functor K L) (a: G.(CObj)) :=
    (liftUnit J).(ncomp) (E.(fobj) (F.(fobj) a))
      ⨟ (liftFunctor J).(fhom) ((liftCompositeUnit F E).(ncomp) a).

  Lemma liftTripleLeft {G H K L: HSetGroupoid}
    (F: Functor G H) (E: Functor H K) (J: Functor K L) (a: G.(CObj)):
    liftTripleUnit F E J a
      ⨟ (liftFunctor J).(fhom) ((liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a))
    = (liftCompositeUnit (compFunctor F E) J).(ncomp) a.
  Proof.
    unfold liftTripleUnit. rewrite cassoc.
    refine (f_equal (fun v => (liftUnit J).(ncomp) (E.(fobj) (F.(fobj) a)) ⨟ v)
      (eq_sym ((liftFunctor J).(fcomp) ((liftCompositeUnit F E).(ncomp) a)
        ((liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a)))) • _).
    now exact (f_equal (fun v => (liftUnit J).(ncomp) (E.(fobj) (F.(fobj) a))
      ⨟ (liftFunctor J).(fhom) v) (liftCompositeComm F E a)).
  Qed.

  Lemma liftTripleRight {G H K L: HSetGroupoid}
    (F: Functor G H) (E: Functor H K) (J: Functor K L) (a: G.(CObj)):
    liftTripleUnit F E J a
      ⨟ (liftComposite E J).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))
    = (liftCompositeUnit F (compFunctor E J)).(ncomp) a.
  Proof.
    unfold liftTripleUnit.
    refine (f_equal (fun v => ((liftUnit J).(ncomp) (E.(fobj) (F.(fobj) a)) ⨟ v)
      ⨟ (liftComposite E J).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a)))
      ((liftFunctor J).(fcomp) ((liftUnit E).(ncomp) (F.(fobj) a))
        ((liftFunctor E).(fhom) ((liftUnit F).(ncomp) a))) • _).
    rewrite <- ((completedPaths L).(cassoc) ((liftUnit J).(ncomp) (E.(fobj) (F.(fobj) a)))).
    change (((liftCompositeUnit E J).(ncomp) (F.(fobj) a)
      ⨟ (liftFunctor J).(fhom) ((liftFunctor E).(fhom) ((liftUnit F).(ncomp) a)))
      ⨟ (liftComposite E J).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))
      = (liftCompositeUnit F (compFunctor E J)).(ncomp) a).
    rewrite cassoc.
    refine (f_equal (fun v => (liftCompositeUnit E J).(ncomp) (F.(fobj) a) ⨟ v)
      ((liftComposite E J).(nnat) ((liftUnit F).(ncomp) a)) • _).
    rewrite <- cassoc.
    now exact (f_equal (fun v => v ⨟ (liftFunctor (compFunctor E J)).(fhom) ((liftUnit F).(ncomp) a))
      (liftCompositeComm E J (F.(fobj) a))).
  Qed.

  Lemma liftAssociativity {G H K L: HSetGroupoid}
    (F: Functor G H) (E: Functor H K) (J: Functor K L):
    compNatTrans
      (compNatTrans (whiskerRNat (liftComposite F E) (liftFunctor J)) (liftComposite (compFunctor F E) J))
      (liftNat (functorAssoc F E J))
    = compNatTrans (functorAssoc (liftFunctor F) (liftFunctor E) (liftFunctor J))
      (compNatTrans (whiskerLNat (liftFunctor F) (liftComposite E J)) (liftComposite F (compFunctor E J))).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths L)).
    apply natTransEq; intro a.
    change (((liftFunctor J).(fhom) ((liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a))
      ⨟ (liftComposite (compFunctor F E) J).(ncomp) ((pathCompletionUnit G).(fobj) a))
      ⨟ (liftNat (functorAssoc F E J)).(ncomp) ((pathCompletionUnit G).(fobj) a)
      = cid _ ⨟ ((liftComposite E J).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))
        ⨟ (liftComposite F (compFunctor E J)).(ncomp) ((pathCompletionUnit G).(fobj) a))).
    rewrite cidl. apply (groupoidCancelL (liftTripleUnit F E J a)).
    transitivity ((liftUnit (compFunctor F (compFunctor E J))).(ncomp) a).
    - rewrite <- 2 cassoc.
      refine (f_equal (fun v => (v
        ⨟ (liftComposite (compFunctor F E) J).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ⨟ (liftNat (functorAssoc F E J)).(ncomp) ((pathCompletionUnit G).(fobj) a))
        (liftTripleLeft F E J a) • _).
      refine (f_equal (fun v => v ⨟ (liftNat (functorAssoc F E J)).(ncomp)
        ((pathCompletionUnit G).(fobj) a)) (liftCompositeComm (compFunctor F E) J a) • _).
      refine (liftNatComm (functorAssoc F E J) a • _).
      change ((pathCompletionUnit L).(fhom) (cid (J.(fobj) (E.(fobj) (F.(fobj) a))))
        ⨟ (liftUnit (compFunctor F (compFunctor E J))).(ncomp) a
        = (liftUnit (compFunctor F (compFunctor E J))).(ncomp) a).
      now rewrite (pathCompletionUnit L).(fid), cidl.
    - apply eq_sym. rewrite <- cassoc.
      refine (f_equal (fun v => v ⨟ (liftComposite F (compFunctor E J)).(ncomp)
        ((pathCompletionUnit G).(fobj) a)) (liftTripleRight F E J a) • _).
      now exact (liftCompositeComm F (compFunctor E J) a).
  Qed.
End CompletionAssociativity.

(** The action on functors and natural transformations, together with its
    unit and associativity laws, defines a pseudofunctor. *)
Module CompletionPseudofunctor (T: PropositionalTruncation).
  Module V := CompletionAssociativity T.
  Module U := V.U.
  Module A := V.A.
  Import A A.B.C A.P A.P.D U V.
  Set Universe Polymorphism.

  Definition completionPsfLaws: PsfLaws completionPsfData.
  Proof.
    refine (@Build_PsfLaws HSetGroupoidBicat B.CompletionHomBicat (fun G => G)
      completionPsfData _ _ _ _ _ _ _ _ _).
    - intro G. now apply natInvertible.
    - intros G H K F E. now apply natInvertible.
    - intros G H F. now apply liftNatIdentity.
    - intros G H F F' F'' α β. now apply liftNatCompose.
    - intros G H K F E E' α. now apply liftCompositeNatL.
    - intros G H K F F' α E. now apply liftCompositeNatR.
    - intros G H F. now apply liftUnitLawL.
    - intros G H F. now apply liftUnitLawR.
    - intros G H K L F E J. now apply liftAssociativity.
  Defined.

  Definition completionPseudofunctor: Pseudofunctor HSetGroupoidBicat B.CompletionHomBicat :=
    @Build_Pseudofunctor HSetGroupoidBicat B.CompletionHomBicat (fun G => G)
      (@Build_Psf HSetGroupoidBicat B.CompletionHomBicat (fun G => G) completionPsfData completionPsfLaws).
End CompletionPseudofunctor.
