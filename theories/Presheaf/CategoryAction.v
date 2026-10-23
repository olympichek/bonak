(** Interpreting the generating faces of the ν-semi-shape category in an
    arbitrary category. The exchange law makes word interpretation respect
    composition. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp NatLemmas.
From Bonak.Category Require Import Category.
From Bonak.Presheaf Require Import νSemiShape.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Record CategoryFaceStr {A: HSet} {C: Category} := {
  CS0: nat -> C.(CObj);
  CSFace n q (Hq: q <= n) (ε: A): C.(CHom) (CS0 (S n)) (CS0 n);
}.
Arguments CategoryFaceStr A C : clear implicits.

Definition categoryShift {A C} (Q: CategoryFaceStr A C): CategoryFaceStr A C := {|
  CS0 n := Q.(CS0) (S n);
  CSFace n q Hq ε := Q.(CSFace) (S n) q (↑ Hq) ε;
|}.

Definition CategoryCoh {A C} (Q: CategoryFaceStr A C): Prop :=
  forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A),
    Q.(CSFace) (S n) r (Hr ↕ (↑ Hq)) ω ⨟ Q.(CSFace) n q Hq ε =
    Q.(CSFace) (S n) (S q) (⇑ Hq) ε ⨟ Q.(CSFace) n r (Hr ↕ Hq) ω.

Definition categoryCohShift {A C} {Q: CategoryFaceStr A C} (H: CategoryCoh Q):
  CategoryCoh (categoryShift Q) :=
  fun n q Hq r Hr ε ω => H (S n) q (↑ Hq) r Hr ε ω.

Fixpoint categoryApplyW {A C} (m: nat):
  forall n (w: Word A n m) (Q: CategoryFaceStr A C), C.(CHom) (Q.(CS0) m) (Q.(CS0) n).
Proof.
  destruct m as [|m].
  - intros n w Q. destruct n as [|n]. now exact (cid _). now destruct w.
  - intros n w Q. destruct w as [(ε, w)|w].
    + now exact (Q.(CSFace) m m leR_refl ε ⨟ categoryApplyW A C m n w Q).
    + destruct n as [|n]. now destruct w.
      now exact (categoryApplyW A C m n w (categoryShift Q)).
Defined.
Arguments categoryApplyW {A C} m {n} w Q.

Lemma categoryApplyWId {A C n} (Q: CategoryFaceStr A C):
  categoryApplyW n (wid n) Q = cid _.
Proof.
  revert Q; induction n as [|n IH]; intro Q.
  - now reflexivity.
  - now exact (IH (categoryShift Q)).
Defined.

Lemma categoryApplyWNat {A C} (m: nat): forall n (w: Word A n m)
  (Q: CategoryFaceStr A C)
  (T: forall k (ε: A), C.(CHom) (Q.(CS0) (S k)) (Q.(CS0) k))
  (HT: forall k q (Hq: q <= k) (ε ω: A),
    Q.(CSFace) (S k) q (↑ Hq) ω ⨟ T k ε =
    T (S k) ε ⨟ Q.(CSFace) k q Hq ω) (ε: A),
  T m ε ⨟ categoryApplyW m w Q =
  categoryApplyW m w (categoryShift Q) ⨟ T n ε.
Proof.
  induction m as [|m IH]; intros n w Q T HT ε.
  - destruct n as [|n]; [|now destruct w].
    cbn. now rewrite C.(cidr), C.(cidl).
  - destruct w as [(b, w)|w].
    + cbn [categoryApplyW].
      rewrite <- C.(cassoc), <- HT, C.(cassoc), (IH n w Q T HT ε).
      now apply eq_sym, C.(cassoc).
    + destruct n as [|n]; [now destruct w|].
      now exact (IH n w (categoryShift Q) (fun k => T (S k))
        (fun k q Hq ε ω => HT (S k) q (↑ Hq) ε ω) ε).
Defined.

Lemma categoryApplyWComp {A C} (p: nat): forall m n (g: Word A m p) (f: Word A n m)
  (Q: CategoryFaceStr A C) (HQ: CategoryCoh Q),
  categoryApplyW p g Q ⨟ categoryApplyW m f Q = categoryApplyW p (wcomp g f) Q.
Proof.
  induction p as [|p IH]; intros m n g f Q HQ.
  - destruct m as [|m]; [|now destruct g].
    destruct n as [|n]; [|now destruct f].
    destruct g, f. now apply C.(cidl).
  - destruct g as [(b, g)|g].
    + cbn [categoryApplyW wcomp]. rewrite C.(cassoc). now rewrite (IH m n g f Q HQ).
    + destruct m as [|m]; [now destruct g|].
      destruct f as [(a, f)|f].
      * cbn [categoryApplyW wcomp]. rewrite <- C.(cassoc).
        refine (f_equal (fun h => h ⨟ categoryApplyW m f Q)
          (eq_sym (categoryApplyWNat p m g Q
            (fun k ε => Q.(CSFace) k k leR_refl ε)
            (fun k q Hq ε ω => HQ k k leR_refl q Hq ε ω) a)) • _).
        rewrite C.(cassoc). now rewrite (IH m n g f Q HQ).
      * destruct n as [|n]; [now destruct f|].
        now exact (IH m n g f (categoryShift Q) (categoryCohShift HQ)).
Defined.

Lemma categoryApplyWGen {A C} (Q: CategoryFaceStr A C)
  (n q: nat) (Hq: q <= n) (ε: A):
  categoryApplyW (S n) (wgen n q ε) Q = Q.(CSFace) n q Hq ε.
Proof.
  revert Q q Hq; induction n as [|n IH]; intros Q q Hq.
  - pose proof (leR0Eq Hq) as e; subst q. now apply C.(cidr).
  - destruct (Nat.eqb q (S n)) eqn:e.
    + pose proof (natEqbEq q (S n) e) as eq; subst q.
      rewrite (wgenTop (S n) ε).
      now exact (f_equal (fun h => Q.(CSFace) (S n) (S n) leR_refl ε ⨟ h)
        (categoryApplyWId Q) • C.(cidr) _).
    + assert (Hq': q <= n) by now exact (leRDown q n Hq e).
      rewrite (wgenLift Hq' ε). now exact (IH (categoryShift Q) q Hq').
Defined.

Lemma categoryApplyWFhom {A C} (m: nat): forall n (w: Word A n m)
  (F: Functor (Op (νSemiShape A)) C)
  (SF: forall k q (Hq: q <= k) (ε: A), C.(CHom) (F.(fobj) (S k)) (F.(fobj) k))
  (HSF: forall k q (Hq: q <= k) (ε: A),
    SF k q Hq ε = F.(fhom) (a := S k) (b := k) (wgen k q ε)),
  categoryApplyW m w {| CS0 := F.(fobj); CSFace := SF |} = F.(fhom) w.
Proof.
  induction m as [|m IH]; intros n w F SF HSF.
  - destruct n as [|n]; [|now destruct w].
    destruct w. now exact (eq_sym (F.(fid) 0)).
  - destruct w as [(ε, w)|w].
    + cbn [categoryApplyW]. rewrite (IH n w F SF HSF), HSF, <- F.(fcomp).
      now apply f_equal, wgenSkip.
    + destruct n as [|n]; [now destruct w|].
      now exact (IH n w (νSemiShapeShift A ⨟ᶠ F)
        (fun k q Hq ε => SF (S k) q (↑ Hq) ε)
        (fun k q Hq ε => HSF (S k) q (↑ Hq) ε
          • f_equal (fun v => F.(fhom) (a := S (S k)) (b := S k) v)
              (wgenLift Hq ε))).
Defined.
