(** Functor categories into a univalent category are univalent. The proof
    contracts the total space of natural isomorphisms by first contracting
    their objectwise isomorphisms, then their forced action on arrows. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation Equiv Contractible.
From Bonak.Category Require Import Category CategoryEq UnivalenceFacts.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Universe Polymorphism.

Section FunctorIdentity.
Context {C D: Category} (u: IsUnivalentCategory D) (F: Functor C D).

Local Definition ObjectIsoFamily :=
  forall x: C.(CObj), {y: D.(CObj) &T Iso D (F.(fobj) x) y}.
Local Definition Code :=
  {v: ObjectIsoFamily &T
    {d: @FunctorOn C D (fun x => (v x).1) &T
     forall a b (f: C.(CHom) a b),
       F.(fhom) f ⨟ (v b).2.(isoHom) = (v a).2.(isoHom) ⨟ d.1 a b f}}.

Local Definition encode (z: {G: Functor C D &T Iso (functorCategory C D) F G}): Code :=
  (fun x => (z.1.(fobj) x; natIsoComponent z.2 x);
    (toFunctorOn z.1; fun a b f => z.2.(isoHom).(nnat) f)).

Local Definition decode (z: Code):
  {G: Functor C D &T Iso (functorCategory C D) F G} :=
  (ofFunctorOn z.2.1; @natIsoFromComponents C D F (ofFunctorOn z.2.1)
    (fun x => (z.1 x).2) z.2.2).

Local Lemma decodeEncode (z: {G: Functor C D &T Iso (functorCategory C D) F G}):
  decode (encode z) = z.
Proof.
  destruct z as [G i]. refine (eq_existT_curried eq_refl _).
  apply isoEq. apply natTransEq; intro x. now reflexivity.
Qed.

Local Definition codeContr: Contr Code.
Proof.
  exists ((fun x => (F.(fobj) x; @idToIso D _ _ eq_refl));
    (toFunctorOn F; fun a b f => D.(cidr) (F.(fhom) f)
      • eq_sym (D.(cidl) (F.(fhom) f)))).
  intros [v [d n]].
  pose (c := piContr (fun x => categoryIsoTotal u (F.(fobj) x))).
  assert (e: (fun x => (F.(fobj) x; @idToIso D _ _ eq_refl)) = v).
  { now exact (c.2 v). }
  destruct e.
  assert (q: toFunctorOn F = d).
  { apply functorOnEq. intros a b f.
    specialize (n a b f). cbn in n.
    now rewrite cidl, cidr in n. }
  destruct q. refine (eq_existT_curried eq_refl _).
  refine (eq_existT_curried eq_refl _).
  repeat (apply functional_extensionality_dep; intro). now apply UIP.
Defined.

Definition functorIsoTotal:
  Contr {G: Functor C D &T Iso (functorCategory C D) F G} :=
  retractContr encode decode decodeEncode codeContr.
End FunctorIdentity.

Definition functorCategoryUnivalence {C D: Category} (u: IsUnivalentCategory D):
  IsUnivalentCategory (functorCategory C D) :=
  categoryUnivalenceFromTotal (functorCategory C D) (functorIsoTotal u).
