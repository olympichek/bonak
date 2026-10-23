(** Structure identity for displayed groupoids over a fixed base. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Univalence.
From Bonak.Category.Groupoid Require Export Family StructureIdentity.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record FamilyIso {G: HSetGroupoid} {E P: Family G} := {
  fisoObj: forall x, Equiv (E.(dobj) x) (P.(dobj) x);
  fisoHom: forall x y (a: E.(dobj) x) (b: E.(dobj) y),
    Equiv (E.(dhom) a b) (P.(dhom) (fisoObj x a) (fisoObj y b));
  fisoBase: forall x y (a: E.(dobj) x) (b: E.(dobj) y) (f: E.(dhom) a b),
    P.(dbase) (fisoHom x y a b f) = E.(dbase) f;
  fisoId: forall x (a: E.(dobj) x),
    fisoHom x x a a (E.(did) a) = P.(did) (fisoObj x a);
  fisoComp: forall x y z (a: E.(dobj) x) (b: E.(dobj) y) (c: E.(dobj) z)
    (f: E.(dhom) a b) (g: E.(dhom) b c),
    fisoHom x z a c (E.(dcomp) f g) =
      P.(dcomp) (fisoHom x y a b f) (fisoHom y z b c g);
}.
Arguments FamilyIso {G} E P.

Definition familyIsoTotal {G: HSetGroupoid} {E P: Family G} (e: FamilyIso E P):
  HSetGroupoidIso (total E) (total P) :=
  @Build_HSetGroupoidIso (total E) (total P) (sigTEquivSnd e.(fisoObj))
    (fun a b => e.(fisoHom) a.1 b.1 a.2 b.2)
    (fun a => e.(fisoId) a.1 a.2)
    (fun a b c f g => e.(fisoComp) a.1 b.1 c.1 a.2 b.2 c.2 f g).

Definition idFamilyIso {G: HSetGroupoid} (E: Family G): FamilyIso E E :=
  @Build_FamilyIso G E E (fun _ => idEquiv) (fun _ _ _ _ => idEquiv)
    (fun _ _ _ _ _ => eq_refl) (fun _ _ => eq_refl)
    (fun _ _ _ _ _ _ _ _ => eq_refl).

Definition familyIsoInd {G: HSetGroupoid} (E: Family G)
  (Q: forall P: Family G, FamilyIso E P -> Type)
  (q: Q E (idFamilyIso E)) (P: Family G) (e: FamilyIso E P): Q P e.
Proof.
  destruct E as [O H b i c v l r s vl vr bi bc bv].
  destruct P as [O' H' b' i' c' v' l' r' s' vl' vr' bi' bc' bv'].
  destruct e as [eo eh eb ei ec]. cbn in eo, eh, eb, ei, ec.
  revert H' b' i' c' v' l' r' s' vl' vr' bi' bc' bv' eh eb ei ec.
  pattern O', eo. apply hsetFamilyEquivInd.
  intros H' b' i' c' v' l' r' s' vl' vr' bi' bc' bv' eh eb ei ec.
  cbn in eh, eb, ei, ec.
  revert b' i' c' v' l' r' s' vl' vr' bi' bc' bv' eb ei ec.
  pattern H', eh.
  match goal with |- ?Q _ _ => refine (hsetFamilyEquivInd4 _ Q _ _ _) end.
  intros b' i' c' v' l' r' s' vl' vr' bi' bc' bv' eb ei ec.
  cbn in eb, ei, ec.
  assert (qb: b' = b).
  { repeat (apply functional_extensionality_dep; intro). now apply eb. }
  destruct qb.
  assert (qi: i = i').
  { repeat (apply functional_extensionality_dep; intro). now apply ei. }
  destruct qi.
  assert (qc: c = c').
  { repeat (apply functional_extensionality_dep; intro). now apply ec. }
  destruct qc.
  assert (qv: v = v').
  { apply functional_extensionality_dep; intro x.
    apply functional_extensionality_dep; intro y.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b0.
    apply functional_extensionality_dep; intro f.
    rewrite <- (r y x b0 a (v x y a b0 f)), <- (vr' x y a b0 f).
    rewrite <- s, vl. now apply l. }
  destruct qv.
  assert (ql: l = l').
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  destruct ql.
  assert (qr: r = r').
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  destruct qr.
  assert (qs: s = s').
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  destruct qs.
  assert (qvl: vl = vl').
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  destruct qvl.
  assert (qvr: vr = vr').
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  destruct qvr.
  assert (qbi: bi = bi').
  { repeat (apply functional_extensionality_dep; intro). now apply (G.(CHom) _ _).(UIP). }
  destruct qbi.
  assert (qbc: bc = bc').
  { repeat (apply functional_extensionality_dep; intro). now apply (G.(CHom) _ _).(UIP). }
  destruct qbc.
  assert (qbv: bv = bv').
  { repeat (apply functional_extensionality_dep; intro). now apply (G.(CHom) _ _).(UIP). }
  destruct qbv.
  assert (qeb: eb = (fun _ _ _ _ _ => eq_refl)).
  { repeat (apply functional_extensionality_dep; intro). now apply (G.(CHom) _ _).(UIP). }
  assert (qei: ei = (fun _ _ => eq_refl)).
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  assert (qec: ec = (fun _ _ _ _ _ _ _ _ => eq_refl)).
  { repeat (apply functional_extensionality_dep; intro). now apply (H _ _ _ _).(UIP). }
  rewrite qeb, qei, qec. now exact q.
Defined.

Definition familyIsoContr {G: HSetGroupoid} (E P: Family G) (e: FamilyIso E P):
  existT (fun R => FamilyIso E R) E (idFamilyIso E) = (P; e) :=
  familyIsoInd E (fun P e =>
    existT (fun R => FamilyIso E R) E (idFamilyIso E) = (P; e)) eq_refl P e.

Definition familyEq {G: HSetGroupoid} {E P: Family G} (e: FamilyIso E P): E = P :=
  projT1_eq (familyIsoContr E P e).

Lemma familyEqIso {G: HSetGroupoid} {E P: Family G} (e: FamilyIso E P):
  rew [FamilyIso E] (familyEq e) in idFamilyIso E = e.
Proof. now exact (projT2_eq (familyIsoContr E P e)). Qed.

Definition familyPathTotal {G: HSetGroupoid} {E P: Family G} (p: E = P):
  Functor (total E) (total P) :=
  rew [fun R => Functor (total E) (total R)] p in idFunctor (total E).

Lemma totalFamilyPath {G: HSetGroupoid} {E P: Family G} (q: E = P):
  transportGroupoidFunctor (f_equal total q) = familyPathTotal q.
Proof. now destruct q. Defined.

Local Lemma familyIsoRewTotal {G: HSetGroupoid} {E P: Family G} (p: E = P):
  familyPathTotal p =
    hsetGroupoidIsoFunctor (familyIsoTotal (rew [FamilyIso E] p in idFamilyIso E)).
Proof. now destruct p. Qed.

Lemma familyEqTotalFunctor {G: HSetGroupoid} {E P: Family G} (e: FamilyIso E P):
  familyPathTotal (familyEq e) = hsetGroupoidIsoFunctor (familyIsoTotal e).
Proof. rewrite familyIsoRewTotal. now rewrite familyEqIso. Qed.
