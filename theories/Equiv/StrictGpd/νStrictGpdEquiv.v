(** Levelwise structure isomorphisms of indexed strict groupoids.

    A prefix relation identifies the preceding prefix and its displayed
    groupoid. Structure identity turns these isomorphisms into compatible
    prefix paths, which determine equality of the telescope limits. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT RewLemmas HSet LeSProp Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category.Groupoid Require Import FamilyIdentity.
From Bonak.Equiv.StrictGpd Require Import Tower.
Import Logic.EqNotations.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νStrictGpdEquivOn (A: LayerSig) (S: νStrictGpdSig A).
Import A.
Module Export Tower := TowerOn A S.

Definition νFillerEqvType {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA) (EB: νFillerType XB): Type :=
  FamilyIso (rew [νFillerType] e in EA) EB.

Definition νFillerEq {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (iso: νFillerEqvType e EA EB): rew [νFillerType] e in EA = EB := familyEq iso.

Definition νStrictGpdBisim: Bisimulation νStrictGpdTel :=
  Build_Bisimulation νStrictGpdTel
    (fun x y => hunit_ext x y)
    (fun n XA XB e EA EB => νFillerEqvType e EA EB)
    (fun n XA XB e EA EB iso => νFillerEq e iso).

Definition PrefixRel n: (νStrictGpdAt n).(prefix) -> (νStrictGpdAt n).(prefix) -> Type :=
  Rel νStrictGpdBisim n.

Definition prefixEq {n} {XA XB: (νStrictGpdAt n).(prefix)}
  (r: PrefixRel n XA XB): XA = XB := relEq νStrictGpdBisim r.

Definition relStep {n} {XA XB: (νStrictGpdAt n).(prefix)} (r: PrefixRel n XA XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (iso: νFillerEqvType (prefixEq r) EA EB):
  PrefixRel n.+1 (XA; EA) (XB; EB) := (r; iso).

Definition rel0: PrefixRel 0 tt tt := tt.

Definition eqvTel (XA XB: νStrictGpds): Telescope := {|
  stage m := PrefixRel m (νStrictGpdPack m XA).1 (νStrictGpdPack m XB).1;
  datum m r := νFillerEqvType (prefixEq r)
    (this ((νStrictGpdPack m XA).2)) (this ((νStrictGpdPack m XB).2));
  extend m r E := ((r; E): PrefixRel m.+1
    (νStrictGpdPack m.+1 XA).1 (νStrictGpdPack m.+1 XB).1);
  bond m r := r.1;
  head m r := r.2;
  bondExtend m r E := eq_refl;
  extendHead m r := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

Definition νStrictGpdsEquiv (XA XB: νStrictGpds): Type := Limit (eqvTel XA XB) 0 tt.

Definition packPath (m: nat) (X: νStrictGpds):
  (νStrictGpdPack m X).1 = X.(approx) m leR_O := limitPackPath m X.

Lemma packPathS (m: nat) (X: νStrictGpds):
  f_equal (fun Y: (νStrictGpdAt m.+1).(prefix) => Y.1) (packPath m.+1 X)
    • X.(approxS) m leR_O leR_O = packPath m X.
Proof.
  pose proof (limitPackPathS m X) as H.
  now rewrite eq_trans_refl_l in H.
Defined.

Lemma νStrictGpdsEqFromPaths {XA XB: νStrictGpds}
  (p: forall m, (νStrictGpdPack m XA).1 = (νStrictGpdPack m XB).1)
  (ps: forall m,
    f_equal (fun Xp: (νStrictGpdAt m.+1).(prefix) => Xp.1) (p m.+1) = p m):
  XA = XB.
Proof.
  unshelve eapply limitEqIntro.
  - now exact (fun l => eq_sym (packPath l XA) • (p l • packPath l XB)).
  - now apply unit_UIP.
  - intro l; cbv beta.
    rewrite 2 eq_trans_map_distr, <- eq_sym_map_distr.
    rewrite (ps l).
    rewrite <- (packPathS l XA), <- (packPathS l XB).
    now apply eq_trans_conj_comp.
Defined.

Lemma extendCongFst {n} {XA XB: (νStrictGpdAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB):
  f_equal (fun Xp: (νStrictGpdAt n.+1).(prefix) => Xp.1)
    (extendCong (T := νStrictGpdTel) e h) = e.
Proof. now destruct e, h. Defined.

Lemma prefixEqFst {m} {XA XB: (νStrictGpdAt m.+1).(prefix)}
  (r: PrefixRel m.+1 XA XB):
  f_equal (fun Xp: (νStrictGpdAt m.+1).(prefix) => Xp.1) (prefixEq r) = prefixEq r.1.
Proof. now exact (extendCongFst (prefixEq r.1) (νFillerEq (prefixEq r.1) r.2)). Defined.

Definition νStrictGpdsEquivEq {XA XB: νStrictGpds} (iso: νStrictGpdsEquiv XA XB): XA = XB :=
  νStrictGpdsEqFromPaths
    (fun m => prefixEq (iso.(approx) m leR_O))
    (fun m => prefixEqFst (iso.(approx) m.+1 leR_O)
      • f_equal (@prefixEq m (νStrictGpdPack m XA).1 (νStrictGpdPack m XB).1)
          (iso.(approxS) m leR_O leR_O)).

End νStrictGpdEquivOn.

Module νStrictGpdEquiv (A: LayerSig).
Module Base := νStrictGpd.νStrictGpd A.
Include νStrictGpdEquivOn A Base.
End νStrictGpdEquiv.

Module νStrictGpdEquivSimplicial := νStrictGpdEquivOn SimplicialLayer νStrictGpdSimplicial.
Module νStrictGpdEquivCubical := νStrictGpdEquivOn CubicalLayer νStrictGpdCubical.
