(** The set-valued Yoneda embedding and its explicit inverse on hom-types. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Category Require Import FullyFaithful.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

Definition representable (C: Category) (a: C.(CObj)): Functor (Op C) HSetCat.
Proof.
  refine {| fobj x := C.(CHom) x a;
    fhom x y f h := @ccomp C y x a f h; fid := _; fcomp := _ |}.
  - intro x. apply functional_extensionality_dep; intro h. now exact (C.(cidl) h).
  - intros x y z f g. apply functional_extensionality_dep; intro h. now exact (C.(cassoc) g f h).
Defined.

Definition yonedaArrow {C: Category} {a b: C.(CObj)} (f: C.(CHom) a b):
  NatTrans (representable C a) (representable C b).
Proof.
  refine {| ncomp x h := h ⨟ f; nnat := _ |}.
  intros x y g. apply functional_extensionality_dep; intro h. now exact (C.(cassoc) g h f).
Defined.

Definition yoneda (C: Category): Functor C (functorCategory (Op C) HSetCat).
Proof.
  refine {| fobj := representable C;
    fhom a b f := yonedaArrow f; fid := _; fcomp := _ |}.
  - intro a. apply natTransEq; intro x.
    apply functional_extensionality_dep; intro h. now apply cidr.
  - intros a b c f g. apply natTransEq; intro x.
    apply functional_extensionality_dep; intro h. now apply eq_sym, cassoc.
Defined.

Definition yonedaEvaluate {C: Category} {a b: C.(CObj)}
  (α: NatTrans (representable C a) (representable C b)): C.(CHom) a b :=
  α.(ncomp) a (cid a).

Lemma yonedaEvaluateRet {C: Category} {a b: C.(CObj)} (f: C.(CHom) a b):
  yonedaEvaluate (yonedaArrow f) = f.
Proof. now apply cidl. Qed.

Lemma yonedaEvaluateSec {C: Category} {a b: C.(CObj)}
  (α: NatTrans (representable C a) (representable C b)):
  yonedaArrow (yonedaEvaluate α) = α.
Proof.
  apply natTransEq; intro x. apply functional_extensionality_dep; intro h.
  pose proof (f_equal (fun k => k (cid a)) (α.(nnat) h)) as e.
  change (α.(ncomp) x (h ⨟ cid a) = h ⨟ α.(ncomp) a (cid a)) in e.
  rewrite cidr in e. now exact (eq_sym e).
Qed.

Definition yonedaHomEquiv (C: Category) (a b: C.(CObj)):
  Equiv (C.(CHom) a b) (NatTrans (representable C a) (representable C b)) :=
  qinvEquiv yonedaArrow yonedaEvaluate yonedaEvaluateRet yonedaEvaluateSec.

Definition yonedaFullyFaithful (C: Category): FullyFaithful (yoneda C) :=
  fun a b => (yonedaHomEquiv C a b).(eqvIsEquiv).
