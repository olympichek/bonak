(** The equivalence theory of SSSets: the levelwise equivalence
    [SSSetsEquiv] and its conversion into an equality of towers.

    Two towers are levelwise equivalent when their finite prefixes
    correspond level by level and their filler families correspond over that
    identification. A correspondence of prefixes is turned into an equality
    as soon as it is formed ([prefixEq]), univalence and functional
    extensionality collapsing the filler equivalences. All restriction and
    coherence data of the construction is computed from the prefix, so
    transport along that equality supplies its compatibility.
    [prefixEqRewTotal] computes that transport on a total-space element: the
    frame component moves along the lower prefix equality, the filler
    component through the inverse of the stored equivalence. This is the one
    place where the computation rules of [ua] enter.

    An equality of towers then follows from [limitEqIntro], which asks for a
    family of paths between the stored prefixes commuting with the bonding
    map. The relations are indexed by [SSSetPack], the unfolding whose stage
    at [m.+1] is definitionally a Σ-type over its stage at [m], whereas a
    tower stores [approx], for which that holds only up to [approxS].
    [packPath] identifies the two and [packPathS] shows the identification
    commutes with the bonding maps, so the paths transfer. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Univalence
  SSSet.SSSet Limit.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module SSSetEquiv.

Module Export SSSet := Bonak.SSSet.SSSet.SSSet.

Definition ssDataAt {m} (Xpre: (SSSetAt m).(prefix)): SSSetData m :=
  (SSSetAt m).(data) Xpre.

Definition ssTowerDeps {n} (Xpre: (SSSetAt n).(prefix)): DepsRestr n 0 :=
  toDepsRestr (ssDataAt Xpre).(restrFrames).

(** The full frame at a prefix, and the filler-family type over it. The
    [this] field of [SSSetFrom n Xpre] has type [ssFillerType Xpre], and the
    prefix one level up is [{Xpre &T ssFillerType Xpre}], both definitionally.
    [ssFrameDom] is the [Type]-valued version used as a transport motive. *)

Definition ssFrame {n} (Xpre: (SSSetAt n).(prefix)): HSet :=
  mkFrame (ssTowerDeps Xpre).

Definition ssFrameDom {n} (Xpre: (SSSetAt n).(prefix)): Type := ssFrame Xpre.

Definition ssFillerType {n} (Xpre: (SSSetAt n).(prefix)): Type :=
  ssFrame Xpre -> HSet.

(** The construction data assembled from a prefix one level up. At a tower
    position, the pair of the prefix with the current filler determines
    [DepsCohs]. [ssFrame Xp] at level
    [n.+1] is [mkFrame (mkDepsRestr (depsCohs := prefixDepsCohs Xp))],
    definitionally. *)

Definition prefixDepsCohs {n} (Xp: (SSSetAt n.+1).(prefix)): DepsCohs n 0 := {|
  _deps := ssTowerDeps Xp.1;
  _extraDeps := TopRestrDep Xp.2;
  _restrPaintings := (ssDataAt Xp.1).(restrPaintings) Xp.2;
  _cohs := (ssDataAt Xp.1).(cohFrames) Xp.2;
|}.

(** The total space of cells at a prefix one level up as a type family
    over that prefix *)

Definition ssTotalType {n} (Xp: (SSSetAt n.+1).(prefix)): Type :=
  {d: ssFrame Xp.1 &T Xp.2 d}.

(** The levelwise prefix relation, mutually with its conversion to equality

    The relation at level [n.+1] pairs a relation on the lower prefixes
    with an equivalence of the filler families over the transport along the
    lower equality; converting it to an equality collapses those
    equivalences through univalence and functional extensionality
    ([ssFillerEq]). Relation and conversion are mutually recursive on the
    level, which [Rel] and [relEq] build together from a [Bisimulation]. *)

Definition ssFillerEqvType {n} {XA XB: (SSSetAt n).(prefix)} (e: XA = XB)
  (EA: ssFillerType XA) (EB: ssFillerType XB): Type :=
  forall d: ssFrame XB, Equiv (EA (rew <- [ssFrameDom] e in d)) (EB d).

(** Transporting a filler family along a prefix equality precomposes with
    the backward frame transport. The definition is transparent so that
    the equality reduces when the prefix equality is [eq_refl]. *)

Definition rewSSFillerType {n} {XA XB: (SSSetAt n).(prefix)} (e: XA = XB)
  (EA: ssFillerType XA):
  rew [ssFillerType] e in EA = fun d => EA (rew <- [ssFrameDom] e in d).
Proof.
  now destruct e.
Defined.

(** The filler-family equality induced by an equivalence family: funext of
    the levelwise HSet equalities from univalence *)

Definition ssFillerEq {n} {XA XB: (SSSetAt n).(prefix)} (e: XA = XB)
  {EA: ssFillerType XA} {EB: ssFillerType XB}
  (eqvs: ssFillerEqvType e EA EB): rew [ssFillerType] e in EA = EB :=
  rewSSFillerType e EA
  • functional_extensionality_dep_good _ _ (fun d => hsetEq (eqvs d)).

(** The levelwise relation is the bisimulation of the SSSet telescope:
    correspondence of data over a prefix path is a family of filler
    equivalences, and [ssFillerEq] converts it into a path. Prefixes at
    level [0] are [unit], which supplies the base irrelevance. *)

Definition SSSetBisim: Bisimulation SSSetTel :=
  Build_Bisimulation SSSetTel
    (fun x y => hunit_ext x y)
    (fun n XA XB e EA EB => ssFillerEqvType e EA EB)
    (fun n XA XB e EA EB eqvs => ssFillerEq e eqvs).

Definition PrefixRel n: (SSSetAt n).(prefix) -> (SSSetAt n).(prefix) -> Type :=
  Rel SSSetBisim n.

Definition prefixEq {n} {XA XB: (SSSetAt n).(prefix)}
  (r: PrefixRel n XA XB): XA = XB := relEq SSSetBisim r.

(** The relation one level up, from filler equivalences over the current
    equality — definitionally a pair, named for the corecursion *)

Definition relStep {n} {XA XB: (SSSetAt n).(prefix)} (r: PrefixRel n XA XB)
  {EA: ssFillerType XA} {EB: ssFillerType XB}
  (eqvs: ssFillerEqvType (prefixEq r) EA EB):
  PrefixRel n.+1 (XA; EA) (XB; EB) := (r; eqvs).

Definition rel0: PrefixRel 0 tt tt := tt.

(** Computing transport along a prefix equality

    Three steps: backward transport of a total-space pair along a sigma
    equality with a reflexive base moves only the filler component
    ([rewTotalFamily]); backward transport of the filler component along the
    funext-assembled family equality computes pointwise
    ([rewSSFillerFunext]); and pointwise backward transport along [hsetEq]
    is the inverse of the equivalence ([hsetEqRewSym]).
    [prefixEqRewTotal] assembles them after destructing the lower prefix
    equality. *)

Lemma rewTotalFamily {n} {X1: (SSSetAt n).(prefix)}
  {EA EB: ssFillerType X1} (q: EA = EB)
  (t: ssTotalType ((X1; EB): (SSSetAt n.+1).(prefix))):
  rew <- [ssTotalType]
    (extendCong (T := SSSetTel) (eq_refl X1) q
     : ((X1; EA): (SSSetAt n.+1).(prefix)) = (X1; EB)) in t =
  (t.1; rew <- [fun E: ssFillerType X1 => E t.1: Type] q in t.2).
Proof.
  now destruct q.
Qed.

Lemma rewSSFillerFunext {n} {X1: (SSSetAt n).(prefix)}
  {EA EB: ssFillerType X1} (H: forall d, EA d = EB d)
  (d0: ssFrame X1) (c: EB d0):
  rew <- [fun E: ssFillerType X1 => E d0: Type]
    (functional_extensionality_dep_good EA EB H) in c =
  rew <- [Dom] (H d0) in c.
Proof.
  unfold eq_rect_r.
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun E: ssFillerType X1 => E d0)).
  rewrite <- eq_sym_f_equal.
  now rewrite (f_equal__functional_extensionality_dep_good H d0).
Qed.

(** The three steps assembled, for an arbitrary lower equality: path
    induction on it turns [ssFillerEq] into the funext equality of the
    filler families, which the two lemmas above compute. *)

Lemma rewTotalSSFillerEq {n} {XA XB: (SSSetAt n).(prefix)} (e: XA = XB)
  {EA: ssFillerType XA} {EB: ssFillerType XB}
  (eqvs: ssFillerEqvType e EA EB)
  (t: ssTotalType ((XB; EB): (SSSetAt n.+1).(prefix))):
  rew <- [ssTotalType]
    (extendCong (T := SSSetTel) e (ssFillerEq e eqvs)
     : ((XA; EA): (SSSetAt n.+1).(prefix)) = (XB; EB)) in t =
  (rew <- [ssFrameDom] e in t.1; invEq (eqvs t.1) t.2).
Proof.
  destruct e.
  unfold ssFillerEq; cbn [rewSSFillerType].
  rewrite eq_trans_refl_l.
  rewrite (rewTotalFamily
    (functional_extensionality_dep_good _ _ (fun d => hsetEq (eqvs d))) t).
  apply (f_equal (fun c: EA t.1 =>
    ((t.1; c): ssTotalType ((XA; EA): (SSSetAt n.+1).(prefix))))).
  rewrite (rewSSFillerFunext (fun d => hsetEq (eqvs d)) t.1 t.2).
  now apply hsetEqRewSym.
Qed.

Lemma prefixEqRewTotal {n} {XA XB: (SSSetAt n.+1).(prefix)}
  (r: PrefixRel n.+1 XA XB) (t: ssTotalType XB):
  rew <- [ssTotalType] (prefixEq r) in t =
  (rew <- [ssFrameDom] (prefixEq r.1) in t.1; invEq (r.2 t.1) t.2).
Proof.
  now exact (rewTotalSSFillerEq (prefixEq r.1) r.2 t).
Qed.

(** Finite unfoldings of a tower

    The [m]-step unfolding of a SSSet: the reached prefix, packed with the
    remaining tower so the recursion needs no arithmetic. *)

Definition SSSetPack (m: nat) (S: SSSets):
  {Xp: (SSSetAt m).(prefix) &T SSSetFrom m Xp} := limitPack m S.

(** The levelwise equivalence

    The prefix relations form a telescope of their own: [PrefixRel] is
    indexed by the level and definitionally a Σ-type over the level below,
    whose second component is the filler equivalence at that level. So a
    levelwise equivalence of two towers is a limit of that telescope, in
    the same form as the towers it relates. The restriction and coherence
    data at each level is computed from the prefix, so transport along
    [prefixEq] supplies its compatibility. *)

Definition eqvTel (SA SB: SSSets): Telescope := {|
  stage m := PrefixRel m (SSSetPack m SA).1 (SSSetPack m SB).1;
  datum m r := ssFillerEqvType (prefixEq r)
    (this ((SSSetPack m SA).2)) (this ((SSSetPack m SB).2));
  extend m r E := ((r; E): PrefixRel m.+1
    (SSSetPack m.+1 SA).1 (SSSetPack m.+1 SB).1);
  bond m r := r.1;
  head m r := r.2;
  bondExtend m r E := eq_refl;
  extendHead m r := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

Definition SSSetsEquiv (SA SB: SSSets): Type := Limit (eqvTel SA SB) 0 tt.

(** Reading the finite unfoldings off the chain

    [SSSetPack] rebuilds the level-[m] prefix by iterating the
    destructors. [packPath] identifies that prefix with level [m] of the
    tower's stored chain. *)

Definition packPath (m: nat) (S: SSSets):
  (SSSetPack m S).1 = S.(approx) m leR_O := limitPackPath m S.

Lemma packPathS (m: nat) (S: SSSets):
  f_equal (fun Y: (SSSetAt m.+1).(prefix) => Y.1) (packPath m.+1 S)
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

Lemma SSSetsEqFromPaths {SA SB: SSSets}
  (p: forall m, (SSSetPack m SA).1 = (SSSetPack m SB).1)
  (ps: forall m,
    f_equal (fun Xp: (SSSetAt m.+1).(prefix) => Xp.1) (p m.+1) = p m):
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

(** The chain of prefix paths generated by a levelwise equivalence

    [prefixEq] at a positive level is built by [eq_existT_curried], so its
    first projection is [prefixEq] of the relation's own first projection,
    which the bonding equation identifies with the relation one level
    down. *)

(** [extendCong] abstracts the two components of a stage as independent
    variables, which is what lets both paths be inducted on; at [prefixEq]
    they are projections of one prefix and no longer independent. *)

Lemma extendCongFst {n} {XA XB: (SSSetAt n).(prefix)} (e: XA = XB)
  {EA: ssFillerType XA} {EB: ssFillerType XB}
  (h: rew [ssFillerType] e in EA = EB):
  f_equal (fun Xp: (SSSetAt n.+1).(prefix) => Xp.1)
    (extendCong (T := SSSetTel) e h) = e.
Proof.
  now destruct e, h.
Qed.

Lemma prefixEqFst {m} {XA XB: (SSSetAt m.+1).(prefix)}
  (r: PrefixRel m.+1 XA XB):
  f_equal (fun Xp: (SSSetAt m.+1).(prefix) => Xp.1) (prefixEq r) =
  prefixEq r.1.
Proof.
  now exact (extendCongFst (prefixEq r.1) (ssFillerEq (prefixEq r.1) r.2)).
Qed.

(** Convert a levelwise equivalence of towers into an equality through the
    prefix paths its stored relations generate. *)

Definition SSSetsEquivEq {SA SB: SSSets} (E: SSSetsEquiv SA SB): SA = SB :=
  SSSetsEqFromPaths
    (fun m => prefixEq (E.(approx) m leR_O))
    (fun m => prefixEqFst (E.(approx) m.+1 leR_O)
      • f_equal (@prefixEq m (SSSetPack m SA).1 (SSSetPack m SB).1)
          (E.(approxS) m leR_O leR_O)).

End SSSetEquiv.
