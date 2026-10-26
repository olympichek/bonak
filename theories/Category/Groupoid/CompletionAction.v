(** The canonical action on completed groupoids and its comparison cells.
    Every comparison is obtained by descent through the source completion unit.
    The formulas at represented objects determine all 2-cell equations. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Truncation.
From Bonak.Category Require Import Category Groupoid.
From Bonak.Category.Bicategory Require Import Bicategory Pseudofunctor Groupoids Full UnivGpd2Cat.
From Bonak.Category.Groupoid Require Import SetBased Descent Completion Precomposition.
Set Keyed Unification.
Set Primitive Projections.
Set Universe Polymorphism.

(** Groupoids with h-set objects and functors between their completions as
    hom-categories. Reindexing preserves the bicategory operations. *)
Module CompletionBicategories (T: PropositionalTruncation).
  Module C := PathCompletion T.
  Set Universe Polymorphism.
  Set Universe Minimization ToSet.
  Unset Keyed Unification.

  Definition CompletionHomBicat: Bicategory :=
    fullBicategory UnivGpd2Cat (fun G: HSetGroupoid => C.completedPaths G).
End CompletionBicategories.

Module CompletionAction (T: PropositionalTruncation).
  Module B := CompletionBicategories T.
  Module P := GroupoidPrecomposition T.
  Import B.C P P.D.
  (** Comparison laws use the represented-object equations below, so descent
      remains folded during conversion. *)
  Local Opaque completedPaths pathCompletionUnit descend descentUnit extendNat.
  Set Universe Polymorphism.

  Definition liftFunctor {G H: HSetGroupoid} (F: Functor G H):
    Functor (completedPaths G) (completedPaths H) :=
    descend (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)
      (compFunctor F (pathCompletionUnit H)).

  Definition liftUnit {G H: HSetGroupoid} (F: Functor G H):
    NatTrans (compFunctor F (pathCompletionUnit H))
      (compFunctor (pathCompletionUnit G) (liftFunctor F)) :=
    descentUnit (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)
      (compFunctor F (pathCompletionUnit H)).

  Definition liftNatSource {G H: HSetGroupoid} {F F': Functor G H} (α: NatTrans F F'):
    NatTrans (compFunctor (pathCompletionUnit G) (liftFunctor F))
      (compFunctor (pathCompletionUnit G) (liftFunctor F')) :=
    compNatTrans (natInv (liftUnit F))
      (compNatTrans (whiskerRNat α (pathCompletionUnit H)) (liftUnit F')).

  Definition liftNat {G H: HSetGroupoid} {F F': Functor G H} (α: NatTrans F F'):
    NatTrans (liftFunctor F) (liftFunctor F') :=
    extendNat (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)
      (liftFunctor F) (liftFunctor F') (liftNatSource α).

  Lemma liftNatAt {G H: HSetGroupoid} {F F': Functor G H} (α: NatTrans F F')
    (a: G.(CObj)):
    (liftNat α).(ncomp) ((pathCompletionUnit G).(fobj) a) =
      conjugateArrow ((liftUnit F).(ncomp) a) ((liftUnit F').(ncomp) a)
        ((pathCompletionUnit H).(fhom) (α.(ncomp) a)).
  Proof.
    now exact (f_equal (fun n => n.(ncomp) a)
      (restrictExtend (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)
        (liftFunctor F) (liftFunctor F') (liftNatSource α))).
  Qed.

  Lemma liftNatComm {G H: HSetGroupoid} {F F': Functor G H} (α: NatTrans F F')
    (a: G.(CObj)):
    (liftUnit F).(ncomp) a ⨟ (liftNat α).(ncomp) ((pathCompletionUnit G).(fobj) a)
    = (pathCompletionUnit H).(fhom) (α.(ncomp) a) ⨟ (liftUnit F').(ncomp) a.
  Proof.
    rewrite liftNatAt. unfold conjugateArrow.
    now rewrite <- cassoc, ginvR, cidl.
  Qed.

  Definition liftIdentitySource (G: HSetGroupoid):
    NatTrans (compFunctor (pathCompletionUnit G) (liftFunctor (idFunctor G)))
      (compFunctor (pathCompletionUnit G) (idFunctor (completedPaths G))) := {|
    ncomp := (natInv (liftUnit (idFunctor G))).(ncomp);
    nnat a b f := (natInv (liftUnit (idFunctor G))).(nnat) f;
  |}.

  Definition liftIdentity (G: HSetGroupoid):
    NatTrans (liftFunctor (idFunctor G)) (idFunctor (completedPaths G)) :=
    extendNat (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths G)
      _ _ (liftIdentitySource G).

  Lemma liftIdentityAt (G: HSetGroupoid) (a: G.(CObj)):
    (liftIdentity G).(ncomp) ((pathCompletionUnit G).(fobj) a)
    = ginv ((liftUnit (idFunctor G)).(ncomp) a).
  Proof.
    now exact (f_equal (fun n => n.(ncomp) a)
      (restrictExtend (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths G)
        _ _ (liftIdentitySource G))).
  Qed.

  Definition liftCompositeUnit {G H K: HSetGroupoid} (F: Functor G H) (E: Functor H K):
    NatTrans (compFunctor (compFunctor F E) (pathCompletionUnit K))
      (compFunctor (pathCompletionUnit G) (compFunctor (liftFunctor F) (liftFunctor E))).
  Proof.
    pose (α := whiskerLNat F (liftUnit E)).
    pose (β := whiskerRNat (liftUnit F) (liftFunctor E)).
    refine {| ncomp a := α.(ncomp) a ⨟ β.(ncomp) a; nnat := _ |}.
    intros a b f.
    change ((pathCompletionUnit K).(fhom) (E.(fhom) (F.(fhom) f))
      ⨟ (α.(ncomp) b ⨟ β.(ncomp) b)
      = (α.(ncomp) a ⨟ β.(ncomp) a)
      ⨟ (liftFunctor E).(fhom) ((liftFunctor F).(fhom) ((pathCompletionUnit G).(fhom) f))).
    rewrite <- cassoc.
    refine (f_equal (fun v => v ⨟ β.(ncomp) b) (α.(nnat) f) • _).
    rewrite cassoc.
    refine (f_equal (fun v => α.(ncomp) a ⨟ v) (β.(nnat) f) • _).
    now apply eq_sym, cassoc.
  Defined.

  Definition liftCompositeSource {G H K: HSetGroupoid} (F: Functor G H) (E: Functor H K):
    NatTrans (compFunctor (pathCompletionUnit G) (compFunctor (liftFunctor F) (liftFunctor E)))
      (compFunctor (pathCompletionUnit G) (liftFunctor (compFunctor F E))) :=
    compNatTrans (natInv (liftCompositeUnit F E)) (liftUnit (compFunctor F E)).

  Definition liftComposite {G H K: HSetGroupoid} (F: Functor G H) (E: Functor H K):
    NatTrans (compFunctor (liftFunctor F) (liftFunctor E)) (liftFunctor (compFunctor F E)) :=
    extendNat (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths K)
      _ _ (liftCompositeSource F E).

  Lemma liftCompositeAt {G H K: HSetGroupoid} (F: Functor G H) (E: Functor H K) (a: G.(CObj)):
    (liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a)
    = ginv ((liftCompositeUnit F E).(ncomp) a) ⨟ (liftUnit (compFunctor F E)).(ncomp) a.
  Proof.
    now exact (f_equal (fun n => n.(ncomp) a)
      (restrictExtend (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths K)
        _ _ (liftCompositeSource F E))).
  Qed.

  Lemma liftCompositeComm {G H K: HSetGroupoid} (F: Functor G H) (E: Functor H K) (a: G.(CObj)):
    (liftCompositeUnit F E).(ncomp) a
      ⨟ (liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a)
    = (liftUnit (compFunctor F E)).(ncomp) a.
  Proof. rewrite liftCompositeAt, <- cassoc, ginvR. now apply cidl. Qed.

  Lemma liftNatIdentity {G H: HSetGroupoid} (F: Functor G H):
    liftNat (idNatTrans F) = idNatTrans (liftFunctor F).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)).
    apply natTransEq; intro a.
    change ((liftNat (idNatTrans F)).(ncomp) ((pathCompletionUnit G).(fobj) a)
      = cid ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))).
    rewrite liftNatAt. cbn [idNatTrans].
    rewrite (pathCompletionUnit H).(fid). now apply conjugateId.
  Qed.

  Lemma liftNatCompose {G H: HSetGroupoid} {F F' F'': Functor G H}
    (α: NatTrans F F') (β: NatTrans F' F''):
    liftNat (compNatTrans α β) = compNatTrans (liftNat α) (liftNat β).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths H)).
    apply natTransEq; intro a.
    change ((liftNat (compNatTrans α β)).(ncomp) ((pathCompletionUnit G).(fobj) a)
      = (liftNat α).(ncomp) ((pathCompletionUnit G).(fobj) a)
        ⨟ (liftNat β).(ncomp) ((pathCompletionUnit G).(fobj) a)).
    rewrite 3 liftNatAt. cbn [compNatTrans].
    refine (f_equal (conjugateArrow ((liftUnit F).(ncomp) a) ((liftUnit F'').(ncomp) a))
      ((pathCompletionUnit H).(fcomp) (α.(ncomp) a) (β.(ncomp) a)) • _).
    now apply eq_sym, conjugateComp.
  Qed.

  Lemma liftCompositeNatL {G H K: HSetGroupoid} (F: Functor G H)
    {E E': Functor H K} (α: NatTrans E E'):
    compNatTrans (whiskerLNat (liftFunctor F) (liftNat α)) (liftComposite F E')
    = compNatTrans (liftComposite F E) (liftNat (whiskerLNat F α)).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths K)).
    apply natTransEq; intro a.
    change ((liftNat α).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))
      ⨟ (liftComposite F E').(ncomp) ((pathCompletionUnit G).(fobj) a)
      = (liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a)
        ⨟ (liftNat (whiskerLNat F α)).(ncomp) ((pathCompletionUnit G).(fobj) a)).
    apply (groupoidCancelL ((liftCompositeUnit F E).(ncomp) a)).
    transitivity ((pathCompletionUnit K).(fhom) (α.(ncomp) (F.(fobj) a))
      ⨟ (liftUnit (compFunctor F E')).(ncomp) a).
    - change (((liftUnit E).(ncomp) (F.(fobj) a)
        ⨟ (liftFunctor E).(fhom) ((liftUnit F).(ncomp) a))
        ⨟ ((liftNat α).(ncomp) ((liftFunctor F).(fobj) ((pathCompletionUnit G).(fobj) a))
          ⨟ (liftComposite F E').(ncomp) ((pathCompletionUnit G).(fobj) a))
        = (pathCompletionUnit K).(fhom) (α.(ncomp) (F.(fobj) a))
          ⨟ (liftUnit (compFunctor F E')).(ncomp) a).
      rewrite <- cassoc.
      rewrite ((completedPaths K).(cassoc) ((liftUnit E).(ncomp) (F.(fobj) a))).
      refine (f_equal (fun v => ((liftUnit E).(ncomp) (F.(fobj) a) ⨟ v)
        ⨟ (liftComposite F E').(ncomp) ((pathCompletionUnit G).(fobj) a))
        ((liftNat α).(nnat) ((liftUnit F).(ncomp) a)) • _).
      rewrite <- ((completedPaths K).(cassoc) ((liftUnit E).(ncomp) (F.(fobj) a))).
      refine (f_equal (fun v => (v ⨟ (liftFunctor E').(fhom) ((liftUnit F).(ncomp) a))
        ⨟ (liftComposite F E').(ncomp) ((pathCompletionUnit G).(fobj) a))
        (liftNatComm α (F.(fobj) a)) • _).
      rewrite ((completedPaths K).(cassoc) ((pathCompletionUnit K).(fhom) (α.(ncomp) (F.(fobj) a)))),
        ((completedPaths K).(cassoc) ((pathCompletionUnit K).(fhom) (α.(ncomp) (F.(fobj) a)))).
      now exact (f_equal (fun v => (pathCompletionUnit K).(fhom) (α.(ncomp) (F.(fobj) a)) ⨟ v)
        (liftCompositeComm F E' a)).
    - apply eq_sym.
      now exact (eq_sym ((completedPaths K).(cassoc) ((liftCompositeUnit F E).(ncomp) a)
        ((liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ((liftNat (whiskerLNat F α)).(ncomp) ((pathCompletionUnit G).(fobj) a)))
        • f_equal (fun v => v ⨟ (liftNat (whiskerLNat F α)).(ncomp)
            ((pathCompletionUnit G).(fobj) a)) (liftCompositeComm F E a)
        • liftNatComm (whiskerLNat F α) a).
  Qed.

  Lemma liftCompositeNatR {G H K: HSetGroupoid} {F F': Functor G H}
    (α: NatTrans F F') (E: Functor H K):
    compNatTrans (whiskerRNat (liftNat α) (liftFunctor E)) (liftComposite F' E)
    = compNatTrans (liftComposite F E) (liftNat (whiskerRNat α E)).
  Proof.
    apply (precomposeFaithful (pathCompletionUnit G) (pathCompletionUnitWeak G) (completedPaths K)).
    apply natTransEq; intro a.
    change ((liftFunctor E).(fhom) ((liftNat α).(ncomp) ((pathCompletionUnit G).(fobj) a))
      ⨟ (liftComposite F' E).(ncomp) ((pathCompletionUnit G).(fobj) a)
      = (liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a)
        ⨟ (liftNat (whiskerRNat α E)).(ncomp) ((pathCompletionUnit G).(fobj) a)).
    apply (groupoidCancelL ((liftCompositeUnit F E).(ncomp) a)).
    transitivity ((pathCompletionUnit K).(fhom) (E.(fhom) (α.(ncomp) a))
      ⨟ (liftUnit (compFunctor F' E)).(ncomp) a).
    - change (((liftUnit E).(ncomp) (F.(fobj) a)
        ⨟ (liftFunctor E).(fhom) ((liftUnit F).(ncomp) a))
        ⨟ ((liftFunctor E).(fhom) ((liftNat α).(ncomp) ((pathCompletionUnit G).(fobj) a))
          ⨟ (liftComposite F' E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        = (pathCompletionUnit K).(fhom) (E.(fhom) (α.(ncomp) a))
          ⨟ (liftUnit (compFunctor F' E)).(ncomp) a).
      rewrite <- cassoc.
      rewrite ((completedPaths K).(cassoc) ((liftUnit E).(ncomp) (F.(fobj) a))).
      refine (f_equal (fun v => ((liftUnit E).(ncomp) (F.(fobj) a) ⨟ v)
        ⨟ (liftComposite F' E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        (eq_sym ((liftFunctor E).(fcomp) ((liftUnit F).(ncomp) a)
          ((liftNat α).(ncomp) ((pathCompletionUnit G).(fobj) a)))) • _).
      refine (f_equal (fun v => ((liftUnit E).(ncomp) (F.(fobj) a)
        ⨟ (liftFunctor E).(fhom) v)
        ⨟ (liftComposite F' E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        (liftNatComm α a) • _).
      refine (f_equal (fun v => ((liftUnit E).(ncomp) (F.(fobj) a) ⨟ v)
        ⨟ (liftComposite F' E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ((liftFunctor E).(fcomp) ((pathCompletionUnit H).(fhom) (α.(ncomp) a))
          ((liftUnit F').(ncomp) a)) • _).
      rewrite <- ((completedPaths K).(cassoc) ((liftUnit E).(ncomp) (F.(fobj) a))).
      refine (f_equal (fun v => (v ⨟ (liftFunctor E).(fhom) ((liftUnit F').(ncomp) a))
        ⨟ (liftComposite F' E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        (eq_sym ((liftUnit E).(nnat) (α.(ncomp) a))) • _).
      rewrite ((completedPaths K).(cassoc) ((pathCompletionUnit K).(fhom) (E.(fhom) (α.(ncomp) a)))),
        ((completedPaths K).(cassoc) ((pathCompletionUnit K).(fhom) (E.(fhom) (α.(ncomp) a)))).
      now exact (f_equal (fun v => (pathCompletionUnit K).(fhom) (E.(fhom) (α.(ncomp) a)) ⨟ v)
        (liftCompositeComm F' E a)).
    - apply eq_sym.
      now exact (eq_sym ((completedPaths K).(cassoc) ((liftCompositeUnit F E).(ncomp) a)
        ((liftComposite F E).(ncomp) ((pathCompletionUnit G).(fobj) a))
        ((liftNat (whiskerRNat α E)).(ncomp) ((pathCompletionUnit G).(fobj) a)))
        • f_equal (fun v => v ⨟ (liftNat (whiskerRNat α E)).(ncomp)
            ((pathCompletionUnit G).(fobj) a)) (liftCompositeComm F E a)
        • liftNatComm (whiskerRNat α E) a).
  Qed.

  Definition completionPsfData: PsfData HSetGroupoidBicat B.CompletionHomBicat (fun G => G) :=
    @Build_PsfData HSetGroupoidBicat B.CompletionHomBicat (fun G => G)
      (fun G H F => liftFunctor F) (fun G H F F' α => liftNat α)
      liftIdentity (fun G H K F E => liftComposite F E).
End CompletionAction.
