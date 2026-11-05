(** Functors on a countable family of objects are determined by their
    compatible restrictions to finite prefixes. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Arith.PeanoNat Lia.
From Bonak.Lib Require Import HSet SigT Equiv SequentialLimit FinitePrefix.
From Bonak.Category Require Import Category CategoryEq Full.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Section FunctorLimits.
Context (C D: Category) (objects: nat -> C.(CObj)).

Definition PrefixCategory n: Category :=
  fullCategory C (fun i: Index n => objects (rank i)).
Definition FunctorPrefix n := Functor (PrefixCategory n) D.

Definition truncateFunctor {n} (F: FunctorPrefix (S n)): FunctorPrefix n := {|
  fobj i := F.(fobj) (Some i);
  fhom i j f := F.(fhom) (a := Some i) (b := Some j) f;
  fid i := F.(fid) (Some i);
  fcomp i j k f g := F.(fcomp) (a := Some i) (b := Some j) (c := Some k) f g;
|}.

Definition DiagramOn {n} (O: Index n -> D.(CObj)): HSet :=
  {r: hforall (i j: Index n) (f: C.(CHom) (objects (rank i)) (objects (rank j))),
      D.(CHom) (O i) (O j) &
   {e: hforall i: Index n, hEq (r i i (cid (objects (rank i)))) (cid (O i)) &
    hforall (i j k: Index n)
      (f: C.(CHom) (objects (rank i)) (objects (rank j)))
      (g: C.(CHom) (objects (rank j)) (objects (rank k))),
      hEq (r i k (f ⨟ g)) (r i j f ⨟ r j k g)}}.

Definition toDiagramOn {n} (F: FunctorPrefix n):
  {O: Index n -> D.(CObj) &T DiagramOn O} :=
  (F.(fobj); (fun i j f => F.(fhom) f;
    (F.(fid); fun i j k f g => F.(fcomp) f g))).

Definition ofDiagramOn {n} (F: {O: Index n -> D.(CObj) &T DiagramOn O}):
  FunctorPrefix n := {|
  fobj := F.1;
  fhom i j f := F.2.1 i j f;
  fid := F.2.2.1;
  fcomp i j k f g := F.2.2.2 i j k f g;
|}.

Definition diagramFamilyEquiv n:
  Equiv (FunctorPrefix n) {O: Index n -> D.(CObj) &T DiagramOn O} :=
  qinvEquiv toDiagramOn ofDiagramOn (fun _ => eq_refl) (fun _ => eq_refl).

Definition truncateDiagramOn {n} {O: Index (S n) -> D.(CObj)}
  (r: DiagramOn O): DiagramOn (fun i => O (Some i)) :=
  (fun i j f => r.1 (Some i) (Some j) f;
   (fun i => r.2.1 (Some i);
    fun i j k f g => r.2.2 (Some i) (Some j) (Some k) f g)).

Lemma diagramOnEq {n} {O: Index n -> D.(CObj)} (r s: DiagramOn O)
  (h: forall i j f, r.1 i j f = s.1 i j f): r = s.
Proof.
  destruct r as [r [ri rc]], s as [s [si sc]]; cbn in h.
  assert (e: r = s).
  { repeat (apply functional_extensionality_dep; intro). now apply h. }
  destruct e. apply f_equal.
  assert (e: ri = si).
  { repeat (apply functional_extensionality_dep; intro). now apply (D.(CHom) _ _).(UIP). }
  destruct e. apply f_equal.
  repeat (apply functional_extensionality_dep; intro). now apply (D.(CHom) _ _).(UIP).
Defined.

Section FixedObjects.
Context (O: nat -> D.(CObj)).

Definition DiagramOnLimit :=
  SequentialLimit (fun n => DiagramOn (fun i: Index n => O (rank i)))
    (fun n => @truncateDiagramOn n _).

Definition arrowLimit (F: DiagramOnLimit):
  TableLimit (fun i j => hpiT
    (fun _: C.(CHom) (objects i) (objects j) => D.(CHom) (O i) (O j))) :=
  ((fun n => (F.1 n).1); fun n => f_equal (fun r => r.1) (F.2 n)).

Definition assembleArrow (F: DiagramOnLimit) i j:
  C.(CHom) (objects i) (objects j) -> D.(CHom) (O i) (O j) :=
  assembleTable _ (arrowLimit F) i j.

Lemma assembleArrowAt (F: DiagramOnLimit) n (i j: Index n):
  assembleArrow F (rank i) (rank j) = (F.1 n).1 i j.
Proof. now exact (assembleTableAt _ (arrowLimit F) n i j). Defined.

Definition assembleFunctor (F: DiagramOnLimit): Functor (fullCategory C objects) D.
Proof.
  refine {| fobj := O; fhom i j f := assembleArrow F i j f |}.
  - intro i.
    pose proof (assembleArrowAt F (S i) None None) as h.
    change (assembleArrow F i i = (F.1 (S i)).1 None None) in h.
    rewrite h. now exact ((F.1 (S i)).2.1 None).
  - intros i j k f g.
    assert (bound: forall n (ii jj kk: Index n)
      (ff: C.(CHom) (objects (rank ii)) (objects (rank jj)))
      (gg: C.(CHom) (objects (rank jj)) (objects (rank kk))),
      assembleArrow F (rank ii) (rank kk) (ff ⨟ gg) =
      assembleArrow F (rank ii) (rank jj) ff ⨟
        assembleArrow F (rank jj) (rank kk) gg).
    { intros n ii jj kk ff gg. rewrite 3 assembleArrowAt.
      now exact ((F.1 n).2.2 ii jj kk ff gg). }
    set (n := S (Nat.max i (Nat.max j k))).
    assert (hi: i < n) by (unfold n; now lia).
    assert (hj: j < n) by (unfold n; now lia).
    assert (hk: k < n) by (unfold n; now lia).
    clearbody n. generalize (atRank n i hi), (atRank n j hj), (atRank n k hk).
    clear hi hj hk. intros [ii ei] [jj ej] [kk ek].
    destruct ei, ej, ek. now apply bound.
Defined.

Definition restrictFunctorOn
  (F: @FunctorOn (fullCategory C objects) D O): DiagramOnLimit :=
  ((fun n => (fun i j f => F.1 (rank i) (rank j) f;
    (fun i => F.2.1 (rank i);
     fun i j k f g => F.2.2 (rank i) (rank j) (rank k) f g)));
   fun _ => eq_refl).

Definition fixedObjectLimitEquiv:
  Equiv DiagramOnLimit (@FunctorOn (fullCategory C objects) D O).
Proof.
  refine (qinvEquiv (fun F => toFunctorOn (assembleFunctor F)) restrictFunctorOn _ _).
  - intro F. apply eq_sigT_uncurried.
    assert (e: (restrictFunctorOn (toFunctorOn (assembleFunctor F))).1 = F.1).
    { apply functional_extensionality_dep; intro n.
      apply diagramOnEq. intros i j f.
      change (assembleArrow F (rank i) (rank j) f = (F.1 n).1 i j f).
      now rewrite assembleArrowAt. }
    exists e. apply functional_extensionality_dep; intro n.
    now apply (DiagramOn (fun i: Index n => O (rank i))).(UIP).
  - intro F. apply functorOnEq. intros i j f.
    change (assembleArrow (restrictFunctorOn F) i j f = F.1 i j f).
    unfold assembleArrow, assembleTable.
    change (readBound _ (restrictTable
      (fun i j => hpiT (fun _: C.(CHom) (objects i) (objects j) => D.(CHom) (O i) (O j)))
      (fun i j => F.1 i j))
      (S (Nat.max i j)) i j
      (proj2 (Nat.lt_succ_r _ _) (Nat.le_max_l i j))
      (proj2 (Nat.lt_succ_r _ _) (Nat.le_max_r i j)) f = F.1 i j f).
    now rewrite restrictTableRead.
Defined.
End FixedObjects.

Definition finiteFunctorLimitEquiv:
  Equiv (SequentialLimit FunctorPrefix (fun n => @truncateFunctor n))
    (Functor (fullCategory C objects) D).
Proof.
  refine (compEquiv (objectSplitEquiv (fun n O => DiagramOn O)
    (fun n O d => truncateDiagramOn d) (fun n => @truncateFunctor n)
    diagramFamilyEquiv (fun _ _ => eq_refl) fixedObjectLimitEquiv) _).
  now exact (qinvEquiv (fun z => ofFunctorOn z.2)
    (fun F => (F.(fobj); toFunctorOn F))
    (fun _ => eq_refl) (fun _ => eq_refl)).
Defined.

End FunctorLimits.
