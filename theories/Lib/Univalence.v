(** Univalence, and the equality of HSets it induces.

    Univalence is stated as [idToEquiv] being an equivalence; [ua] is its
    inverse, universe polymorphic so it applies both at the [Dom] level of HSets
    and one level up on ordinary types. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import Notation HSet RewLemmas.
From Bonak.Lib Require Import Equiv SigT.

Polymorphic Definition idToEquiv {A B: Type} (e: A = B): Equiv A B :=
  match e with
  | eq_refl => qinvEquiv (fun x: A => x) (fun x: A => x) (fun _ => eq_refl) (fun _ => eq_refl)
  end.

Polymorphic Axiom univalence: forall A B: Type, IsEquiv (@idToEquiv A B).

Polymorphic Definition uaEquiv (A B: Type): Equiv (A = B) (Equiv A B) :=
  {| eqvFun := @idToEquiv A B; eqvIsEquiv := univalence A B |}.

Polymorphic Definition ua {A B: Type} (e: Equiv A B): A = B := invEq (uaEquiv A B) e.

Polymorphic Lemma idToEquivRew {A B: Type} (e: A = B) (a: A):
  idToEquiv e a = rew [fun T: Type => T] e in a.
Proof.
  now destruct e.
Qed.

Polymorphic Lemma uaRew {A B: Type} (e: Equiv A B) (a: A):
  rew [fun T: Type => T] (ua e) in a = e a.
Proof.
  rewrite <- idToEquivRew.
  now exact (f_equal (fun E: Equiv A B => E a) (secEq (uaEquiv A B) e)).
Qed.

(** Equality of HSets from equivalence of their carriers.

    From univalence, [hsetEq] turns an equivalence of the carriers of two HSets
    into an equality of the HSets: the [Dom] path comes from univalence, and the
    [UIP] field is proof-irrelevant ([eq_hprop_UIP]); functional
    extensionality proves equality of the transported fields. *)

Polymorphic Definition hsetEqIntro (h1 h2: HSet)
  (p: h1.(Dom) = h2.(Dom)): h1 = h2.
Proof.
  destruct h1 as [d1 u1], h2 as [d2 u2]; cbn in p; destruct p.
  apply (f_equal (fun u => {| Dom := d1; UIP := u |})).
  apply functional_extensionality_dep_good; intro x.
  apply functional_extensionality_dep_good; intro y.
  apply functional_extensionality_dep_good; intro a.
  apply functional_extensionality_dep_good; intro b.
  now apply (eq_hprop_UIP (u1 x y)).
Defined.

Polymorphic Lemma hsetEqIntroEta {A B: HSet} (p: A = B):
  hsetEqIntro A B (f_equal Dom p) = p.
Proof.
  destruct p. destruct A as [A h]. unfold hsetEqIntro; cbn.
  match goal with |- f_equal _ ?q = _ =>
    assert (q = eq_refl) by (now apply (eq_hprop_UIP (@uipProp A)));
    now rewrite H
  end.
Qed.

Polymorphic Definition hsetEq {h1 h2: HSet} (e: Equiv h1 h2): h1 = h2 :=
  hsetEqIntro h1 h2 (ua e).

Polymorphic Lemma hsetEqIntroRew (h1 h2: HSet) (p: h1.(Dom) = h2.(Dom)) (x: h1):
  rew [Dom] (hsetEqIntro h1 h2 p) in x = rew [fun T: Type => T] p in x.
Proof.
  destruct h1 as [d1 u1], h2 as [d2 u2]; cbn in p; destruct p; cbn.
  rewrite <- (rew_map Dom (fun u => {| Dom := d1; UIP := u |})).
  now apply rew_const.
Qed.

Polymorphic Lemma hsetEqRew {h1 h2: HSet} (e: Equiv h1 h2) (x: h1):
  rew [Dom] (hsetEq e) in x = e x.
Proof.
  unfold hsetEq. rewrite hsetEqIntroRew. now apply uaRew.
Qed.

Polymorphic Lemma hsetEqRewSym {h1 h2: HSet} (e: Equiv h1 h2) (x: h2):
  rew [Dom] (eq_sym (hsetEq e)) in x = invEq e x.
Proof.
  apply (eqvInj e).
  now exact (eq_sym (hsetEqRew e _)
    • (rew_sym_cancel_r (P := Dom) (hsetEq e) x • eq_sym (secEq e x))).
Qed.

(** Univalence as induction on equivalences of types and h-set families. *)

Polymorphic Definition equivInd {A: Type}
  (P: forall B: Type, Equiv A B -> Type) (h: P A idEquiv)
  {B: Type} (e: Equiv A B): P B e.
Proof.
  refine (rew [P B] (secEq (uaEquiv A B) e) in _).
  change (P B (idToEquiv (ua e))).
  generalize (ua e). intros p. destruct p. now exact h.
Defined.

Polymorphic Definition hsetEquivInd (A: HSet)
  (P: forall B: HSet, Equiv A B -> Type) (h: P A idEquiv)
  (B: HSet) (e: Equiv A B): P B e.
Proof.
  destruct A as [A u], B as [B v]. cbn in e.
  revert v.
  refine (equivInd (fun B e => forall v, P {| Dom := B; UIP := v |} e) _ e).
  intro v.
  assert (q: u = v).
  { repeat (apply functional_extensionality_dep; intro).
    now apply (eq_hprop_UIP (u _ _)). }
  destruct q. now exact h.
Defined.

Polymorphic Definition hsetEquivContr (A B: HSet) (e: Equiv A B):
  existT (fun C: HSet => Equiv A C) A idEquiv = (B; e) :=
  hsetEquivInd A (fun B e =>
    existT (fun C: HSet => Equiv A C) A idEquiv = (B; e)) eq_refl B e.

Polymorphic Definition hsetFamilyEquivInd {I: Type} (H: I -> HSet)
  (P: forall K: I -> HSet, (forall i, Equiv (H i) (K i)) -> Type)
  (h: P H (fun _ => idEquiv)) (K: I -> HSet)
  (e: forall i, Equiv (H i) (K i)): P K e.
Proof.
  assert (q: (fun i => existT (fun C: HSet => Equiv (H i) C) (H i) idEquiv)
    = (fun i => (K i; e i))).
  { apply functional_extensionality_dep. intro i. now apply hsetEquivContr. }
  pose (r := f_equal (fun z: forall i, {C: HSet &T Equiv (H i) C} =>
    existT (fun L: I -> HSet => forall i, Equiv (H i) (L i))
      (fun i => (z i).1) (fun i => (z i).2)) q).
  now exact (@eq_rect {L: I -> HSet &T forall i, Equiv (H i) (L i)}
    (H; fun _ => idEquiv) (fun z => P z.1 z.2) h (K; e) r).
Defined.

Polymorphic Definition hsetFamilyEquivInd2 {I: Type} {J: I -> Type}
  (H: forall i, J i -> HSet)
  (P: forall K: forall i, J i -> HSet,
    (forall i j, Equiv (H i j) (K i j)) -> Type)
  (h: P H (fun _ _ => idEquiv)) (K: forall i, J i -> HSet)
  (e: forall i j, Equiv (H i j) (K i j)): P K e :=
  hsetFamilyEquivInd (fun z: {i: I &T J i} => H z.1 z.2)
    (fun K e => P (fun i j => K (i; j)) (fun i j => e (i; j))) h
    (fun z => K z.1 z.2) (fun z => e z.1 z.2).

Polymorphic Definition hsetFamilyEquivInd4 {I: Type} {J: I -> Type}
  {K: forall i, J i -> Type} {L: forall i j, K i j -> Type}
  (H: forall i j k, L i j k -> HSet)
  (P: forall R: forall i j k, L i j k -> HSet,
    (forall i j k l, Equiv (H i j k l) (R i j k l)) -> Type)
  (h: P H (fun _ _ _ _ => idEquiv)) (R: forall i j k, L i j k -> HSet)
  (e: forall i j k l, Equiv (H i j k l) (R i j k l)): P R e :=
  hsetFamilyEquivInd (fun z: {i: I &T {j: J i &T {k: K i j &T L i j k}}} =>
      H z.1 z.2.1 z.2.2.1 z.2.2.2)
    (fun R e => P (fun i j k l => R (i; (j; (k; l))))
      (fun i j k l => e (i; (j; (k; l))))) h
    (fun z => R z.1 z.2.1 z.2.2.1 z.2.2.2)
    (fun z => e z.1 z.2.1 z.2.2.1 z.2.2.2).
