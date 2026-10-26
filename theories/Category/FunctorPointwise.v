(** Pointwise strict equality of functors. Object comparisons are paths,
    and arrow comparisons are equalities after transport along those paths. *)
Set Warnings "-notation-overridden".
From Bonak.Category Require Export Category.
From Bonak.Lib Require Import HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Definition castArrow {G: Category} {x x' y y': G.(CObj)}
  (p: x = x') (q: y = y') (f: G.(CHom) x y): G.(CHom) x' y'.
Proof. now destruct p, q. Defined.

Lemma castArrowId {G: Category} {x y: G.(CObj)} (p: x = y):
  castArrow p p (G.(cid) x) = G.(cid) y.
Proof. now destruct p. Defined.

Lemma castArrowComp {G: Category} {x x' y y' z z': G.(CObj)}
  (p: x = x') (q: y = y') (r: z = z') (f: G.(CHom) x y) (g: G.(CHom) y z):
  castArrow p r (f ⨟ g) = castArrow p q f ⨟ castArrow q r g.
Proof. now destruct p, q, r. Defined.

Lemma castArrowTrans {G: Category} {x x' x'' y y' y'': G.(CObj)}
  (p: x = x') (p': x' = x'') (q: y = y') (q': y' = y'') (f: G.(CHom) x y):
  castArrow (p • p') (q • q') f = castArrow p' q' (castArrow p q f).
Proof. now destruct p, p', q, q'. Defined.

Lemma castArrowCancel {G: Category} {x x' y y': G.(CObj)}
  (p: x = x') (q: y = y') (f: G.(CHom) x y):
  castArrow (eq_sym p) (eq_sym q) (castArrow p q f) = f.
Proof. now destruct p, q. Defined.

Lemma mapCastArrow {G H: Category} (F: Functor G H) {x x' y y': G.(CObj)}
  (p: x = x') (q: y = y') (f: G.(CHom) x y):
  F.(fhom) (castArrow p q f) =
  castArrow (f_equal F.(fobj) p) (f_equal F.(fobj) q) (F.(fhom) f).
Proof. now destruct p, q. Defined.

Record FunctorEq {G H: Category} {F L: Functor G H}: Prop := {
  objEq: forall x, F.(fobj) x = L.(fobj) x;
  homEq: forall x y (f: G.(CHom) x y),
    castArrow (objEq x) (objEq y) (F.(fhom) f) = L.(fhom) f;
}.
Arguments FunctorEq {G H} F L.
Arguments Build_FunctorEq {G H F L} & _ _.
Infix "≐" := FunctorEq (at level 70, no associativity).

Definition feqRefl {G H: Category} (F: Functor G H): F ≐ F :=
  Build_FunctorEq (fun _ => eq_refl) (fun _ _ _ => eq_refl).

Definition feqTrans {G H: Category} {F L R: Functor G H}
  (e: F ≐ L) (h: L ≐ R): F ≐ R.
Proof.
  refine (Build_FunctorEq (fun x => e.(objEq) x • h.(objEq) x) _).
  intros x y f. cbn beta.
  rewrite (castArrowTrans (G := H) (e.(objEq) x) (h.(objEq) x)
    (e.(objEq) y) (h.(objEq) y)), (e.(homEq) x y f).
  now apply h.(homEq).
Defined.

Infix "•ᶠ" := feqTrans (at level 65, left associativity).

Definition feqSym {G H: Category} {F L: Functor G H} (e: F ≐ L): L ≐ F.
Proof.
  refine (Build_FunctorEq (fun x => eq_sym (e.(objEq) x)) _).
  intros x y f. cbn beta. rewrite <- (e.(homEq) x y f). now apply (castArrowCancel (G := H)).
Defined.

Definition feqWhiskerL {G H K: Category} (F: Functor G H)
  {L R: Functor H K} (e: L ≐ R): F ⨟ᶠ L ≐ F ⨟ᶠ R :=
  Build_FunctorEq
    (fun x => e.(objEq) (F.(fobj) x)) (fun x y f => e.(homEq) _ _ (F.(fhom) f)).

Definition feqWhiskerR {G H K: Category} {F L: Functor G H}
  (e: F ≐ L) (R: Functor H K): F ⨟ᶠ R ≐ L ⨟ᶠ R.
Proof.
  refine (Build_FunctorEq
    (fun x => f_equal R.(fobj) (e.(objEq) x)) _).
  intros x y f. cbn. rewrite <- (mapCastArrow R). now rewrite (e.(homEq) x y f).
Defined.

Definition feqAssoc {G H K L: Category}
  (F: Functor G H) (R: Functor H K) (S: Functor K L):
  (F ⨟ᶠ R) ⨟ᶠ S ≐ F ⨟ᶠ (R ⨟ᶠ S).
Proof. unshelve econstructor; now intros. Defined.

Definition composeSquares {A B C D E F: Category}
  (u: Functor A B) (v: Functor B C) (w: Functor C F)
  (r: Functor A D) (s: Functor D E) (t: Functor E F) (k: Functor B E)
  (h: u ⨟ᶠ k ≐ r ⨟ᶠ s) (j: v ⨟ᶠ w ≐ k ⨟ᶠ t):
  (u ⨟ᶠ v) ⨟ᶠ w ≐ r ⨟ᶠ (s ⨟ᶠ t) :=
  feqAssoc u v w •ᶠ
    (feqWhiskerL u j •ᶠ
      (feqSym (feqAssoc u k t) •ᶠ
        (feqWhiskerR h t •ᶠ feqAssoc r s t))).

(** Cancellation needs uniqueness of paths between observed objects. *)
Definition cancelObservation {G H K: Category} (O: Functor H K)
  (objectUIP: forall (x y: K.(CObj)) (p q: x = y), p = q)
  (oi: forall x y, O.(fobj) x = O.(fobj) y -> x = y)
  (mi: forall x y (f g: H.(CHom) x y), O.(fhom) f = O.(fhom) g -> f = g)
  (F L: Functor G H) (h: F ⨟ᶠ O ≐ L ⨟ᶠ O): F ≐ L.
Proof.
  refine (Build_FunctorEq (fun x => oi _ _ (h.(objEq) x)) _).
  intros x y f. apply mi. rewrite (mapCastArrow O).
  rewrite (objectUIP _ _ (f_equal O.(fobj) (oi _ _ (h.(objEq) x))) (h.(objEq) x)).
  rewrite (objectUIP _ _ (f_equal O.(fobj) (oi _ _ (h.(objEq) y))) (h.(objEq) y)).
  now exact (h.(homEq) x y f).
Defined.
