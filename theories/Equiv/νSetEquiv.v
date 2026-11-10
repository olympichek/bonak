(** Equality of νSets from levelwise filler equivalences.

    A family of equivalences between the filler families of two prefixes,
    over a path between those prefixes, gives a path between the extended
    prefixes: univalence and functional extensionality collapse the
    equivalences into a filler path ([νFillerEq]). All restriction and
    coherence data of the construction is computed from the prefix, so
    transport along that path supplies its compatibility.
    [rewTotalνFillerEq] computes that transport on a total-space element:
    the frame component moves along the lower prefix path, the filler
    component through the inverse of the equivalence. This is the one place
    where the computation rules of [ua] enter.

    An equality of towers then follows from [limitEqIntro], which asks for a
    family of paths between the stored prefixes commuting with the bonding
    map. The paths are indexed by [νSetPack], the unfolding whose stage at
    [m.+1] is definitionally a Σ-type over its stage at [m], whereas a
    tower stores [approx], for which that holds only up to [approxS].
    [packPath] identifies the two and [packPathS] shows the identification
    commutes with the bonding maps, so the paths transfer. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Univalence
  νSet.Layer νSet Limit.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νSetEquivOn (A: LayerSig) (S: νSetSig A).
Import A.

Module Export νSet := S.

Definition νDataAt {m} (Xpre: (νSetAt m).(prefix)): νSetData m :=
  (νSetAt m).(data) Xpre.

Definition νTowerDeps {n} (Xpre: (νSetAt n).(prefix)): DepsRestr n 0 :=
  toDepsRestr (νDataAt Xpre).(restrFrames).

(** The full frame at a prefix, and the filler-family type over it. The
    [this] field of [νSetFrom n Xpre] has type [νFillerType Xpre], and the
    prefix one level up is [{Xpre &T νFillerType Xpre}], both definitionally.
    [νFrameDom] is the [Type]-valued version used as a transport motive. *)

Definition νFrame {n} (Xpre: (νSetAt n).(prefix)): HSet :=
  mkFrame (νTowerDeps Xpre).

Definition νFrameDom {n} (Xpre: (νSetAt n).(prefix)): Type := νFrame Xpre.

Definition νFillerType {n} (Xpre: (νSetAt n).(prefix)): Type :=
  νFrame Xpre -> HSet.

(** The construction data assembled from a prefix one level up. At a tower
    position, the pair of the prefix with the current filler assembles the
    [DepsCohs] that the face operations consume. [νFrame Xp] at level
    [n.+1] is [mkFrame (mkDepsRestr (depsCohs := prefixDepsCohs Xp))],
    definitionally. *)

Definition prefixDepsCohs {n} (Xp: (νSetAt n.+1).(prefix)): DepsCohs n 0 := {|
  _deps := νTowerDeps Xp.1;
  _extraDeps := TopRestrDep Xp.2;
  _restrPaintings := (νDataAt Xp.1).(restrPaintings) Xp.2;
  _cohs := (νDataAt Xp.1).(cohFrames) Xp.2;
|}.

(** The total space of cells at a prefix one level up — the result type of
    [νFace] at [prefixDepsCohs], as a functor of the prefix *)

Definition νTotalType {n} (Xp: (νSetAt n.+1).(prefix)): Type :=
  {d: νFrame Xp.1 &T Xp.2 d}.

(** Equivalences of filler families over a prefix path *)

Definition νFillerEqvType {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA) (EB: νFillerType XB): Type :=
  forall d: νFrame XB, Equiv (EA (rew <- [νFrameDom] e in d)) (EB d).

(** Transporting a filler family along a prefix equality precomposes with
    the backward frame transport. The definition is transparent so that
    the equality reduces when the prefix equality is [eq_refl]. *)

Definition rewνFillerType {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA):
  rew [νFillerType] e in EA = fun d => EA (rew <- [νFrameDom] e in d).
Proof.
  now destruct e.
Defined.

(** The filler-family equality induced by an equivalence family: funext of
    the levelwise HSet equalities from univalence *)

Definition νFillerEq {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType e EA EB): rew [νFillerType] e in EA = EB :=
  rewνFillerType e EA
  • functional_extensionality_dep_good _ _ (fun d => hsetEq (eqvs d)).

(** Computing transport along a prefix equality

    Three steps: backward transport of a total-space pair along a sigma
    equality with a reflexive base moves only the filler component
    ([rewTotalFamily]); backward transport of the filler component along the
    funext-assembled family equality computes pointwise
    ([rewνFillerFunext]); and pointwise backward transport along [hsetEq]
    is the inverse of the equivalence ([hsetEqRewSym]).
    [rewTotalνFillerEq] assembles them after destructing the lower prefix
    equality. *)

Lemma rewTotalFamily {n} {X1: (νSetAt n).(prefix)}
  {EA EB: νFillerType X1} (q: EA = EB)
  (t: νTotalType ((X1; EB): (νSetAt n.+1).(prefix))):
  rew <- [νTotalType]
    (extendCong (T := νSetTel) (eq_refl X1) q
     : ((X1; EA): (νSetAt n.+1).(prefix)) = (X1; EB)) in t =
  (t.1; rew <- [fun E: νFillerType X1 => E t.1: Type] q in t.2).
Proof.
  now destruct q.
Qed.

Lemma rewνFillerFunext {n} {X1: (νSetAt n).(prefix)}
  {EA EB: νFillerType X1} (H: forall d, EA d = EB d)
  (d0: νFrame X1) (c: EB d0):
  rew <- [fun E: νFillerType X1 => E d0: Type]
    (functional_extensionality_dep_good EA EB H) in c =
  rew <- [Dom] (H d0) in c.
Proof.
  unfold eq_rect_r.
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun E: νFillerType X1 => E d0)).
  rewrite <- eq_sym_f_equal.
  now rewrite (f_equal__functional_extensionality_dep_good H d0).
Qed.

(** The three steps assembled, for an arbitrary lower equality: path
    induction on it turns [νFillerEq] into the funext equality of the
    filler families, which the two lemmas above compute. *)

Lemma rewTotalνFillerEq {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType e EA EB)
  (t: νTotalType ((XB; EB): (νSetAt n.+1).(prefix))):
  rew <- [νTotalType]
    (extendCong (T := νSetTel) e (νFillerEq e eqvs)
     : ((XA; EA): (νSetAt n.+1).(prefix)) = (XB; EB)) in t =
  (rew <- [νFrameDom] e in t.1; invEq (eqvs t.1) t.2).
Proof.
  destruct e.
  unfold νFillerEq; cbn [rewνFillerType].
  rewrite eq_trans_refl_l.
  rewrite (rewTotalFamily
    (functional_extensionality_dep_good _ _ (fun d => hsetEq (eqvs d))) t).
  apply (f_equal (fun c: EA t.1 =>
    ((t.1; c): νTotalType ((XA; EA): (νSetAt n.+1).(prefix))))).
  rewrite (rewνFillerFunext (fun d => hsetEq (eqvs d)) t.1 t.2).
  now apply hsetEqRewSym.
Qed.

(** Finite unfoldings of a tower

    The [m]-step unfolding of a νSet: the reached prefix, packed with the
    remaining tower so the recursion needs no arithmetic. *)

Definition νSetPack (m: nat) (S: νSets):
  {Xp: (νSetAt m).(prefix) &T νSetFrom m Xp} := limitPack m S.

(** Reading the finite unfoldings off the chain

    [νSetPack] rebuilds the level-[m] prefix by iterating the
    destructors. [packPath] identifies that prefix with level [m] of the
    tower's stored chain. *)

Definition packPath (m: nat) (S: νSets):
  (νSetPack m S).1 = S.(approx) m leR_O := limitPackPath m S.

Lemma packPathS (m: nat) (S: νSets):
  f_equal (fun Y: (νSetAt m.+1).(prefix) => Y.1) (packPath m.+1 S)
    • S.(approxS) m leR_O leR_O = packPath m S.
Proof.
  pose proof (limitPackPathS m S) as H.
  now rewrite eq_trans_refl_l in H.
Qed.

(** From coherent prefix paths to tower equality

    Conjugating the given paths by [packPath] gives paths between the
    stored prefixes, and [packPathS] turns their coherence into the square
    [limitEqIntro] asks for. The base coherence lives in the [unit] prefix
    of level 0, hence is free. *)

Lemma νSetsEqFromPaths {SA SB: νSets}
  (p: forall m, (νSetPack m SA).1 = (νSetPack m SB).1)
  (ps: forall m,
    f_equal (fun Xp: (νSetAt m.+1).(prefix) => Xp.1) (p m.+1) = p m):
  SA = SB.
Proof.
  unshelve eapply limitEqIntro.
  - exact (fun l => eq_sym (packPath l SA) • (p l • packPath l SB)).
  - now apply unit_UIP.
  - intro l; cbv beta.
    rewrite eq_trans_map_distr, eq_trans_map_distr, <- eq_sym_map_distr.
    rewrite (ps l).
    rewrite <- (packPathS l SA), <- (packPathS l SB).
    apply eq_trans_conj_comp.
Qed.

(** The first projection of an extended prefix path is the lower prefix
    path. [extendCong] takes the two components of a stage as independent
    variables, which is what lets both paths be inducted on. *)

Lemma extendCongFst {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB):
  f_equal (fun Xp: (νSetAt n.+1).(prefix) => Xp.1)
    (extendCong (T := νSetTel) e h) = e.
Proof.
  now destruct e, h.
Qed.

End νSetEquivOn.

Module νSetEquiv (A: LayerSig).
Module Base := νSet.νSet A.
Include νSetEquivOn A Base.
End νSetEquiv.

Module νSetEquivSimplicial := νSetEquiv SimplicialLayer.
Module νSetEquivCubical := νSetEquiv CubicalLayer.
