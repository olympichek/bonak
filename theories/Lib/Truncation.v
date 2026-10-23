(** Propositional truncation: a universe-polymorphic interface, derived
    elimination rules, and an implementation using impredicative [Prop]. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Export HSet.
From Bonak.Lib Require Import SigT Equiv Univalence.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

(** Universe-polymorphic equality eliminators. The derived Corelib equality
    operations have fixed universe bounds in this toolchain. *)
Local Definition transport@{u v} {A: Type@{u}} (P: A -> Type@{v})
  {x y: A} (e: x = y) (a: P x): P y :=
  match e with eq_refl => a end.

Local Definition cast@{u} {A B: Type@{u}} (e: A = B) (a: A): B :=
  match e with eq_refl => a end.

Local Definition sym@{u} {A: Type@{u}} {x y: A} (e: x = y): y = x :=
  match e with eq_refl => eq_refl end.

Local Definition concat@{u} {A: Type@{u}} {x y z: A} (p: x = y) (q: y = z): x = z :=
  match q with eq_refl => p end.

Local Definition ap@{u v} {A: Type@{u}} {B: Type@{v}} (f: A -> B)
  {x y: A} (e: x = y): f x = f y :=
  match e with eq_refl => eq_refl end.

Module Type PropositionalTruncation.
  Polymorphic Parameter merely@{u}: Type@{u} -> Type@{u}.
  Polymorphic Parameter merelyProp@{u +}: forall A: Type@{u}, IsHProp (merely@{u} A).
  Polymorphic Parameter tr@{u}: forall {A: Type@{u}}, A -> merely@{u} A.
  Polymorphic Parameter trRec@{u v +}: forall {A: Type@{u}} {B: Type@{v}},
    IsHProp B -> (A -> B) -> merely@{u} A -> B.

End PropositionalTruncation.

Module TruncationFacts (T: PropositionalTruncation).
  Import T.
  Set Universe Polymorphism.

  Lemma trRecBeta {A B: Type} (h: IsHProp B) (f: A -> B) (a: A):
    trRec h f (tr a) = f a.
  Proof. now apply h. Qed.

  Definition trInd {A: Type} (P: merely A -> Type)
    (h: forall x, IsHProp (P x)) (f: forall a, P (tr a)) (x: merely A): P x :=
    trRec (h x)
      (fun a => transport P (merelyProp A (tr a) x) (f a)) x.

  Lemma trIndBeta {A: Type} (P: merely A -> Type)
    (h: forall x, IsHProp (P x)) (f: forall a, P (tr a)) (a: A):
    trInd P h f (tr a) = f a.
  Proof. now apply h. Qed.

  Definition trMap {A B: Type} (f: A -> B): merely A -> merely B :=
    trRec (merelyProp B) (fun a => tr (f a)).

  Definition IsSurjective {A B: Type} (f: A -> B): Type :=
    forall b, merely {a: A &T f a = b}.

End TruncationFacts.

(** A set cover is a map from an h-set with merely inhabited fibers. *)
Module SetCovers (T: PropositionalTruncation).
  Module TF := TruncationFacts T.

  Definition SetCover (X: Type): Type :=
    {S: HSet &T {p: S -> X &T TF.IsSurjective p}}.
End SetCovers.

(** Univalence represents a proposition [B] in any [Type] universe by
    [unit = B] in [Prop]. Equality elimination decodes this representation
    without a separate resizing assumption. *)
Local Definition equivInjective {A B: Type} (e: Equiv A B)
  {x y: A} (p: e x = e y): x = y :=
  concat (sym (retEq e x)) (concat (ap (invEq e) p) (retEq e y)).

Local Definition unitEquiv@{u}: Equiv@{u u} unit unit :=
  qinvEquiv (fun x => x) (fun x => x) (fun _ => eq_refl) (fun _ => eq_refl).

Local Lemma unitEquivUnique@{u} (e: Equiv@{u u} unit unit): unitEquiv@{u} = e.
Proof.
  destruct e as [f [l hl r hr]].
  assert ((fun x: unit => x) = f) as ef.
  { apply functional_extensionality; intro x. now destruct (f x), x. }
  destruct ef.
  assert ((fun x: unit => x) = l) as el.
  { apply functional_extensionality; intro x. now destruct (l x), x. }
  destruct el.
  assert ((fun x: unit => x) = r) as er.
  { apply functional_extensionality; intro x. now destruct (r x), x. }
  destruct er.
  assert ((fun a: unit => eq_refl) = hl) as eh.
  { apply functional_extensionality_dep; intro x. now apply unit_UIP. }
  destruct eh.
  assert ((fun a: unit => eq_refl) = hr) as eh.
  { apply functional_extensionality_dep; intro x. now apply unit_UIP. }
  now destruct eh.
Defined.

Local Definition unitPathProp (B: Type): IsHProp (@eq Type unit B).
Proof.
  intros p q. destruct p.
  apply (equivInjective (uaEquiv unit unit)).
  now exact (concat (sym (unitEquivUnique (uaEquiv unit unit eq_refl)))
    (unitEquivUnique (uaEquiv unit unit q))).
Defined.

Local Definition unitPathFrom {B: Type} (h: IsHProp B) (b: B): @eq Type unit B :=
  ua (qinvEquiv (fun _: unit => b) (fun _: B => tt)
    (fun x => match x with tt => eq_refl end) (fun x => h b x)).

(** The quantified propositions carry explicit proof-irrelevance witnesses;
    proof irrelevance of arbitrary inhabitants of Rocq's [Prop] is not used.
    The recursor computes propositionally, as expressed by [trRecBeta]. *)
Module ImpredicativeTruncation <: PropositionalTruncation.
  Set Universe Minimization ToSet.
  Polymorphic Definition merely@{u} (A: Type@{u}): Type@{u} :=
    forall P: Prop, IsHProp@{Set Set} P -> (A -> P) -> P.

  Polymorphic Definition merelyProp@{u +} (A: Type@{u}): IsHProp (merely@{u} A).
  Proof.
    intros x y. apply functional_extensionality_dep; intro P.
    apply functional_extensionality_dep; intro h.
    apply functional_extensionality_dep; intro f. now apply h.
  Defined.

  Polymorphic Definition tr@{u} {A: Type@{u}} (a: A): merely@{u} A :=
    fun P h f => f a.

  Polymorphic Definition trRec@{u v +} {A: Type@{u}} {B: Type@{v}}
    (h: IsHProp B) (f: A -> B) (x: merely@{u} A): B :=
    cast (x (@eq Type@{v} unit B) (unitPathProp B)
      (fun a => unitPathFrom h (f a))) tt.
End ImpredicativeTruncation.
