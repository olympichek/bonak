(** This file defines HGpd and provides unit, sigT and forall on HGpd. *)

Set Warnings "-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Vec.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** [HGpd] is the next truncation level: its identity types are [HSet]s. *)

Record HGpd := {
  GDom:> Type;
  GUIP {x y: GDom} {h g: x = y} {p q: h = g}: p = q;
}.

Definition hpaths {A: HGpd} (x y: A): HSet := {|
  Dom := x = y;
  UIP := @GUIP A x y;
|}.

Lemma retract_eq {A B: Type} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) {x y: A} (p: x = y):
  p = eq_trans (eq_sym (H x)) (eq_trans (f_equal g (f_equal f p)) (H y)).
Proof.
  destruct p; simpl. destruct (H x). reflexivity.
Defined.

Lemma retract_UIP {A: Type} {B: HSet} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) (x y: A) (p q: x = y): p = q.
Proof.
  rewrite (retract_eq f g H p).
  rewrite (retract_eq f g H q).
  now rewrite (@UIP B (f x) (f y) (f_equal f p) (f_equal f q)).
Defined.

(** A transparent copy of Stdlib's [Eqdep_dec.UIP_dec] (Hedberg's
    theorem): the stdlib proof chain is [Qed]-opaque, which would leave
    normal forms of groupoid-level coherences stuck on it. *)

Section EqdepDec.

Variable A: Type.

Let comp {x y y': A} (eq1: x = y) (eq2: x = y'): y = y' :=
  eq_ind _ (fun a => a = y') eq2 _ eq1.

Remark trans_sym_eq {x y: A} (u: x = y): comp u u = eq_refl y.
Proof.
  case u; trivial.
Defined.

Variable x: A.
Variable eq_dec: forall y: A, x = y \/ x <> y.

Let nu {y: A} (u: x = y): x = y :=
  match eq_dec y with
  | or_introl eqxy => eqxy
  | or_intror neqxy => False_ind _ (neqxy u)
  end.

#[local]
Lemma nu_constant {y: A} (u v: x = y): nu u = nu v.
Proof.
  unfold nu.
  destruct (eq_dec y) as [Heq|Hneq].
  - reflexivity.
  - case Hneq; trivial.
Defined.

Let nu_inv {y: A} (v: x = y): x = y := comp (nu (eq_refl x)) v.

Remark nu_left_inv_on {y: A} (u: x = y): nu_inv (nu u) = u.
Proof.
  case u; unfold nu_inv.
  apply trans_sym_eq.
Defined.

Theorem eq_proofs_unicity_on (y: A) (p1 p2: x = y): p1 = p2.
Proof.
  elim (nu_left_inv_on p1).
  elim (nu_left_inv_on p2).
  elim (nu_constant p1 p2).
  reflexivity.
Defined.

End EqdepDec.

Theorem UIP_dec (A: Type) (eq_dec: forall x y: A, {x = y} + {x <> y})
  (x y: A) (p1 p2: x = y): p1 = p2.
Proof.
  apply eq_proofs_unicity_on.
  intros y'; destruct (eq_dec x y'); [now left | now right].
Defined.

Lemma unit_GUIP (x y: unit) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply unit_UIP.
Defined.

Lemma bool_GUIP (x y: bool) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply bool_UIP.
Defined.

Definition gunit@{m}: HGpd@{m} := {|
  GDom := unit;
  GUIP := unit_GUIP;
|}.

Definition gbool@{m}: HGpd@{m} := {|
  GDom := bool;
  GUIP := bool_GUIP;
|}.

(** [sigT] seen as a type constructor on [HGpd] *)

Definition sigT_path_code {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a}):
  HSet :=
  hsigT (A := hpaths x.1 y.1)
    (fun p => hpaths (rew [B] p in x.2) y.2).

Definition sigT_path_encode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_code x y :=
  (projT1_eq p; projT2_eq p).

Definition sigT_path_decode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: sigT_path_code x y): x = y :=
  (= p.1; p.2).

Lemma sigT_path_decode_encode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_decode (sigT_path_encode p) = p.
Proof.
  symmetry. apply sigT_decompose_eq.
Defined.

Lemma sigT_GUIP {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a})
  (h g: x = y) (p q: h = g): p = q.
Proof.
  eapply retract_UIP with
    (f := @sigT_path_encode A B x y)
    (g := @sigT_path_decode A B x y).
  exact sigT_path_decode_encode.
Defined.

Definition gsigT {A: HGpd} (B: A -> HGpd): HGpd := {|
  GDom := {a: A &T B a};
  GUIP := sigT_GUIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (gsigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (gsigT (A := A) (fun x => P%type)): type_scope.

Unset Universe Polymorphism.

Module HGpdProduct <: FiniteProductSig.
  Definition Obj := HGpd.
  Definition El (A: Obj) : Type := A.
  Coercion El : Obj >-> Sortclass.

  Definition unit_obj := gunit.
  Definition unit_intro : unit_obj := tt.
  Definition unit_ext (x y: unit_obj): x = y.
  Proof.
    now destruct x, y.
  Defined.

  Definition prod_obj (A B: Obj): Obj := gsigT (fun _ : A => B).
  Definition pair {A B: Obj} (x: A) (y: B): prod_obj A B := (x; y).
  Definition fst {A B: Obj} (x: prod_obj A B): A := x.1.
  Definition snd {A B: Obj} (x: prod_obj A B): B := x.2.

  Definition fst_pair {A B: Obj} (x: A) (y: B): fst (pair x y) = x :=
    eq_refl.
  Definition snd_pair {A B: Obj} (x: A) (y: B): snd (pair x y) = y :=
    eq_refl.

  Definition prod_ext {A B: Obj} (x y: prod_obj A B)
    (H1: fst x = fst y) (H2: snd x = snd y): x = y.
  Proof.
    destruct x as [x1 x2], y as [y1 y2].
    simpl in H1, H2. now destruct H1, H2.
  Defined.
End HGpdProduct.

Module HGpdVec := FiniteVector(HGpdProduct).

Lemma HGpdVec_path_ext {n: nat} {B: Fin.t n -> HGpd}
  {xs ys: HGpdVec.vec n B} (p q: xs = ys):
  (forall i,
    f_equal (fun z => HGpdVec.vec_nth z i) p =
    f_equal (fun z => HGpdVec.vec_nth z i) q) ->
  p = q.
Proof.
  revert B xs ys p q.
  induction n as [|n IH].
  - intros B xs ys p q _. now apply unit_UIP.
  - intros B xs ys p q H. cbn in xs, ys, p, q, H |- *.
    unshelve eapply sigT_const_path_ext.
    + exact (H Fin.F1).
    + apply IH. intro i. rewrite !f_equal_compose.
      exact (H (Fin.FS i)).
Defined.

Set Universe Polymorphism.

(** [forall] defined over an [HGpd] codomain *)

Lemma gpiT_decompose {A: Type} (B: A -> HGpd)
  (f g: forall a: A, B a) (p: f = g):
  functional_extensionality_dep_good _ _
    (fun x => f_equal (fun H => H x) p) = p.
Proof.
  destruct p; now apply functional_extensionality_dep_good_refl.
Qed.

Definition piT_path_code {A: Type} (B: A -> HGpd)
  (f g: forall a: A, B a): HSet :=
  hpiT (fun a => hpaths (f a) (g a)).

Definition piT_path_encode {A: Type} {B: A -> HGpd}
  {f g: forall a: A, B a} (p: f = g): piT_path_code B f g :=
  fun a => f_equal (fun H => H a) p.

Definition piT_path_decode {A: Type} {B: A -> HGpd}
  {f g: forall a: A, B a} (p: piT_path_code B f g): f = g :=
  functional_extensionality_dep_good _ _ p.

Definition gpiT_GUIP {A: Type} (B: A -> HGpd) (f g: forall a: A, B a)
  (h i: f = g) (p q: h = i): p = q.
Proof.
  eapply retract_UIP with
    (f := @piT_path_encode A B f g)
    (g := @piT_path_decode A B f g).
  exact (gpiT_decompose B f g).
Qed.

Definition gpiT {A: Type} (B: A -> HGpd): HGpd.
Proof.
  exists (forall a: A, B a). now apply gpiT_GUIP.
Defined.

Notation "'gforall' x .. y , P" :=
  (gpiT (fun x => .. (gpiT (fun y => P%type)) ..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' 'gforall'  x  ..  y ']' ,  '/' P ']'"): type_scope.
