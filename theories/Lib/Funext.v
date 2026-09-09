Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT Notation.

(** Functional extensionality for functions out of a strict proposition.

    The standard library axiom does not cover this case:

      Axiom functional_extensionality_dep:
        forall (A: Type) (B: A -> Type) (f g: forall x: A, B x), ...

    is stated at [A: Type], and [SProp] is a separate sort with no coercion into
    [Type], so [functional_extensionality_dep (A := S)] is rejected outright for
    [S: SProp].

    [sBox] removes it by giving [S] a [Type]-level carrier: a one-field
    inductive holding a proof of [S]. Ordinary funext does apply at the boxed
    domain [forall b: sBox S, T (unbox b)], and the boxed and unboxed function
    spaces transfer into each other definitionally, because [SProp] proof
    irrelevance is: any [s s': S] are convertible, hence so are [T s] and [T
    s'], and in particular [T (unbox (sbox s))] is [T s]. So [spropFunext]
    boxes, applies funext, and pulls the result back along [sbox].

    This trick is needed for *empty* [S]. Were [S] inhabited by some [s0],
    irrelevance and eta would already settle it with no axiom at all: [u] is
    convertible with [fun s => u s0], so [f_equal (fun (t: T s0) (s: S) => t) (h s0)]
    proves [u = v]. For empty [S], there is no such [s0], and the general
    statement does rest on funext. *)

Inductive sBox (S: SProp): Type := sbox: S -> sBox S.
Arguments sbox {S} _.

Definition unbox {S: SProp} (b: sBox S): S :=
  match b with sbox s => s end.

Lemma spropFunext {S: SProp} {T: S -> Type} (u v: forall s, T s)
  (h: forall s, u s = v s): u = v.
Proof.
  (* [r w] is [w] transposed to the boxed domain; the [match] typechecks
     because [T (unbox (sbox s))] is convertible with [T s]. *)
  pose (r := fun (w: forall s, T s) (b: sBox S) =>
    match b as b0 return T (unbox b0) with sbox s => w s end).
  assert (R: r u = r v).
  { apply functional_extensionality_dep_good; intros [s]. now exact (h s). }
  (* Pull back along [sbox]: [fun s => r w (sbox s)] is convertible with [w]. *)
  now exact (f_equal
    (fun (w: forall b: sBox S, T (unbox b)) (s: S) => w (sbox s)) R).
Qed.

(** Functional extensionality as an induction principle

    To prove [P g h] for every function [g] and pointwise homotopy
    [h: forall i, f i = g i], it suffices to prove [P f (fun i => eq_refl)].
    This allows both a function and the homotopy identifying it to vary in
    the motive, including when later data depend on them.

    The type of pairs [(g, h)] is contractible: send a pair to the family
    [(g i; h i)] in the singleton types [{u &T f i = u}]. Functional
    extensionality identifies this family with [(f i; eq_refl)]. Taking
    the two projections reconstructs the original pair definitionally by
    function eta and primitive-record eta for [sigT].

    The variants with several arguments accept homotopies pointwise in all
    arguments. *)

(** Evaluating an equality of functions at a point *)

Definition happly {I: Type} {B: I -> Type} {f g: forall i, B i} (p: f = g)
  (i: I): f i = g i := f_equal (fun k => k i) p.

(** The standard library's computational form of functional extensionality
    is a left inverse of [happly], so [happly] is injective. *)

Lemma funextHapply {I: Type} {B: I -> Type} {f g: forall i, B i} (p: f = g):
  functional_extensionality_dep_good f g (happly p) = p.
Proof.
  destruct p. now apply functional_extensionality_dep_good_refl.
Qed.

Lemma happlyInj {I: Type} {B: I -> Type} {f g: forall i, B i} (p q: f = g)
  (h: forall i, happly p i = happly q i): p = q.
Proof.
  rewrite <- (funextHapply p), <- (funextHapply q). f_equal.
  now apply functional_extensionality_dep.
Qed.

(** The one-argument principle applies to a dependent tuple of arguments.
    The curried variants below recover their functions and homotopies by
    evaluation at tuples. A strict-proposition argument is boxed in the
    tuple; strict proof irrelevance identifies its unboxing with the original
    argument. *)

Section HomInd1.
Context {I1: Type} {B: I1 -> Type}.

Abbreviation T1 := (forall i1, B i1).
Abbreviation H1 f u := (forall i1, f i1 = u i1).

Lemma homContr1 (f g: T1) (h: H1 f g):
  existT (fun u: T1 => H1 f u) f (fun i1 => eq_refl)
  = existT (fun u: T1 => H1 f u) g h.
Proof.
  assert (K: (fun i1 => existT (fun u: B i1 => f i1 = u) (f i1) eq_refl)
           = (fun i1 => existT (fun u: B i1 => f i1 = u) (g i1) (h i1))).
  { apply functional_extensionality_dep; intro i1. now destruct (h i1). }
  now exact (f_equal (fun k: forall i1, {u: B i1 &T f i1 = u} =>
    existT (fun u: T1 => H1 f u)
      (fun i1 => (k i1).1) (fun i1 => (k i1).2)) K).
Defined.

Definition homInd1 (f: T1) (P: forall g: T1, H1 f g -> Type)
  (d: P f (fun i1 => eq_refl)) (g: T1) (h: H1 f g): P g h :=
  eq_rect (existT (fun u: T1 => H1 f u) f (fun i1 => eq_refl))
    (fun z: {u: T1 &T H1 f u} => P z.1 z.2) d
    (existT (fun u: T1 => H1 f u) g h) (homContr1 f g h).

End HomInd1.

Section HomInd2.
Context {I1: Type} {I2: I1 -> Type} {B: forall i1, I2 i1 -> Type}.

Abbreviation T2 := (forall i1 i2, B i1 i2).
Abbreviation H2 f u := (forall i1 i2, f i1 i2 = u i1 i2).

Definition homInd2 (f: T2) (P: forall g: T2, H2 f g -> Type)
  (d: P f (fun i1 i2 => eq_refl)) (g: T2) (h: H2 f g): P g h :=
  homInd1 (fun z: {i1: I1 &T I2 i1} => f z.1 z.2)
    (fun g h => P (fun i1 i2 => g (i1; i2))
                  (fun i1 i2 => h (i1; i2)))
    d (fun z => g z.1 z.2)
      (fun z => h z.1 z.2).

End HomInd2.

Section Hom4.
Context {I1: Type} {I2: I1 -> Type} {I3: forall i1, I2 i1 -> Type}
        {I4: forall i1 i2, I3 i1 i2 -> Type}
        {B: forall i1 i2 i3, I4 i1 i2 i3 -> Type}.

Abbreviation T4 := (forall i1 i2 i3 i4, B i1 i2 i3 i4).
Abbreviation H4 f u := (forall i1 i2 i3 i4, f i1 i2 i3 i4 = u i1 i2 i3 i4).

Definition homInd4 (f: T4) (P: forall g: T4, H4 f g -> Type)
  (d: P f (fun i1 i2 i3 i4 => eq_refl)) (g: T4) (h: H4 f g): P g h :=
  homInd1
    (fun z: {i1: I1 &T {i2: I2 i1 &T {i3: I3 i1 i2 &T I4 i1 i2 i3}}} =>
       f z.1 z.2.1 z.2.2.1 z.2.2.2)
    (fun g h => P (fun i1 i2 i3 i4 => g (i1; (i2; (i3; i4))))
                  (fun i1 i2 i3 i4 => h (i1; (i2; (i3; i4)))))
    d (fun z => g z.1 z.2.1 z.2.2.1 z.2.2.2)
      (fun z => h z.1 z.2.1 z.2.2.1 z.2.2.2).

End Hom4.

Section HomInd5.
Context {I1: Type} {I2: I1 -> Type} {I3: forall i1, I2 i1 -> Type}
        {I4: forall i1 i2, I3 i1 i2 -> Type}
        {I5: forall i1 i2 i3, I4 i1 i2 i3 -> Type}
        {B: forall i1 i2 i3 i4, I5 i1 i2 i3 i4 -> Type}.

Abbreviation T5 := (forall i1 i2 i3 i4 i5, B i1 i2 i3 i4 i5).
Abbreviation H5 f u :=
  (forall i1 i2 i3 i4 i5, f i1 i2 i3 i4 i5 = u i1 i2 i3 i4 i5).

Definition homInd5 (f: T5) (P: forall g: T5, H5 f g -> Type)
  (d: P f (fun i1 i2 i3 i4 i5 => eq_refl)) (g: T5) (h: H5 f g): P g h :=
  homInd1
    (fun z: {i1: I1 &T {i2: I2 i1 &T {i3: I3 i1 i2 &T
              {i4: I4 i1 i2 i3 &T I5 i1 i2 i3 i4}}}} =>
       f z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
    (fun g h => P (fun i1 i2 i3 i4 i5 => g (i1; (i2; (i3; (i4; i5)))))
                  (fun i1 i2 i3 i4 i5 => h (i1; (i2; (i3; (i4; i5))))))
    d (fun z => g z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
      (fun z => h z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).

End HomInd5.

Section Hom5S.
Context {I1: Type} {I2: I1 -> Type} {I3: forall i1, I2 i1 -> SProp}
        {I4: forall i1 i2, I3 i1 i2 -> Type}
        {I5: forall i1 i2 i3, I4 i1 i2 i3 -> Type}
        {B: forall i1 i2 i3 i4, I5 i1 i2 i3 i4 -> Type}.

Abbreviation T5S := (forall i1 i2 i3 i4 i5, B i1 i2 i3 i4 i5).
Abbreviation H5S f u :=
  (forall i1 i2 i3 i4 i5, f i1 i2 i3 i4 i5 = u i1 i2 i3 i4 i5).

Definition homInd5S (f: T5S) (P: forall g: T5S, H5S f g -> Type)
  (d: P f (fun i1 i2 i3 i4 i5 => eq_refl)) (g: T5S) (h: H5S f g): P g h :=
  homInd1
    (fun z: {i1: I1 &T {i2: I2 i1 &T {i3: sBox (I3 i1 i2) &T
              {i4: I4 i1 i2 (unbox i3) &T I5 i1 i2 (unbox i3) i4}}}} =>
       f z.1 z.2.1 (unbox z.2.2.1) z.2.2.2.1 z.2.2.2.2)
    (fun g h => P (fun i1 i2 i3 i4 i5 => g (i1; (i2; (sbox i3; (i4; i5)))))
                  (fun i1 i2 i3 i4 i5 => h (i1; (i2; (sbox i3; (i4; i5))))))
    d (fun z => g z.1 z.2.1 (unbox z.2.2.1) z.2.2.2.1 z.2.2.2.2)
      (fun z => h z.1 z.2.1 (unbox z.2.2.1) z.2.2.2.1 z.2.2.2.2).

End Hom5S.

(** Evaluating extensional equality of a two-argument family. *)

Polymorphic Lemma funextGoodAt2 {A: Type} {B: A -> A -> Type} (f g: forall x y, B x y)
  (H: forall x y, f x y = g x y) (a b: A):
  f_equal (fun k: forall x y, B x y => k a b)
    (functional_extensionality_dep_good f g
      (fun x => functional_extensionality_dep_good (f x) (g x) (H x)))
  = H a b.
Proof.
  rewrite <- (f_equal_compose (fun k: forall x y, B x y => k a)
    (fun k: forall y, B a y => k b)).
  rewrite (f_equal__functional_extensionality_dep_good
    (f := f) (g := g) _ a).
  now apply (f_equal__functional_extensionality_dep_good (H a) b).
Qed.
