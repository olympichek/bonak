(** The indexed side of the backward round trip [f ∘ g] of the
    correspondence: [fg: SSSetsEquiv (f (g X)) X].

    The levelwise equivalence is built level by level. At each level the
    cells of the presheaf [g X] in the ambient dimension are identified with
    the total space of the position reached in [X] (the descent witness
    [Desc]), and the candidate fillers of [f (g X)] over a frame transported
    along the prefix equality contract onto the fillers of [X]
    ([fillerEquivOf]). The frame identification carried along the chain
    states that the candidate frame of a transported cell is the transport
    of its frame; it steps by [ssFaceEq], every face of the two frames
    agreeing. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation Limit Equiv.
From Bonak.SSSet Require Import SSSet.
From Bonak.Presheaf Require Import Presentation.
From Bonak.Equiv Require Import Face SSSetOfPresheaf PresheafOfSSSet.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module SSSetRoundtrip.

Module Export PresheafOfSSSet := Bonak.Equiv.PresheafOfSSSet.PresheafOfSSSet.

(** Lifting arbitrary chains to equipped chains

    [ssFaceEq]'s hypothesis quantifies over *arbitrary* [DepsCohsChain]s
    from the shared top. On the presheaf side the equipped chains
    ([PshCohsChain]) step by [proj1DepsCohs] on their [DepsCohs] images, so
    every chain is the image of an equipped one; the identification is
    carried as a sigma-package equality (the result type of [ssFace] does
    not depend on the endpoint, so packages can be rewritten wholesale). *)

Lemma cohsChainStage {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): p + cohsChainLen c = P.
Proof.
  induction c as [|p k dc c IH]; cbn [cohsChainLen].
  - now symmetry; apply plus_n_O.
  - rewrite <- plus_n_Sm. now exact IH.
Qed.

Lemma pshChainLift (psh: SSSetPresentation) {M P K} (PCTop: PshDepsCohs psh M P K)
  {p k} {dc: DepsCohs p k}
  (c0: DepsCohsChain (pshDepsCohs psh PCTop) dc):
  {PC: PshDepsCohs psh M p k &T {C: PshCohsChain psh PCTop PC &T
    ((dc; c0): {dc0: DepsCohs p k &T
       DepsCohsChain (pshDepsCohs psh PCTop) dc0}) =
    (pshDepsCohs psh PC; pshCohsChainCohs psh C)}}.
Proof.
  induction c0 as [|p k dc' c0' IH].
  - now exact (PCTop; (PshCohsChainNil; eq_refl)).
  - destruct IH as (PC', (C', e')).
    refine (proj1PshDepsCohs psh PC'; (PshCohsChainCons C'; _)).
    now exact (f_equal (fun s: {dc0: DepsCohs p.+1 k &T
        DepsCohsChain (pshDepsCohs psh PCTop) dc0} =>
      ((proj1DepsCohs s.1; DepsCohsChainCons s.2):
        {dc0: DepsCohs p k.+1 &T
          DepsCohsChain (pshDepsCohs psh PCTop) dc0})) e').
Qed.

(** Normal forms of chain packages

    The original-tower side of the round trip compares [g]'s
    fuel-synthesized chains with arbitrary chains from the position's top;
    both are iterated [dcStep]s of the nil package, reconnected through
    length/stage arithmetic alone. *)

Fixpoint dcStepIter {P K} {dcTop: DepsCohs P K} (j: nat)
  (s: DCPack dcTop): DCPack dcTop :=
  match j with
  | 0 => s
  | S j => dcStep (dcStepIter j s)
  end.

Lemma chain2DownIter {P K} (T2: DepsCohs2 P K) (j: nat):
  dc2PackDeps (chain2Down T2 j) =
  dcStepIter j (P; (K; (T2.(_depsCohs); DepsCohsChainNil))).
Proof.
  induction j; cbn [chain2Down dcStepIter].
  - now reflexivity.
  - now rewrite dc2PackDepsStep, IHj.
Qed.

Lemma chainPackNF {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  ((p; (k; (dc; c))): DCPack dcTop) =
  dcStepIter (cohsChainLen c) (P; (K; (dcTop; DepsCohsChainNil))).
Proof.
  induction c as [|p k dc c IH]; cbn [cohsChainLen dcStepIter].
  - now reflexivity.
  - now rewrite <- IH.
Qed.

(** The face maps commute with prefix transport

    At a prefix [Xp] one level up, the input frame of [ssFace] is [ssFrame Xp]
    and its output is the total space [ssTotalType Xp]; both are functors of
    the prefix, and the chains from [prefixDepsCohs Xp] to a fixed endpoint
    form a third one. So [ssFace] commutes with wholesale transport along an
    equality of prefixes, by path induction. The [Nil] case is stated
    separately: transporting the empty chain lands on the empty chain of the
    other prefix. *)

Lemma ssFaceRewPrefix {n} {XpA XpB: (SSSetAt n.+1).(prefix)} (e: XpA = XpB)
  {p k} {dc: DepsCohs p k} (cA: DepsCohsChain (prefixDepsCohs XpA) dc)
  (d: ssFrameDom XpB):
  ssFace cA (rew <- [ssFrameDom] e in d) =
  rew <- [ssTotalType] e in
    ssFace (rew [fun Xp => DepsCohsChain (prefixDepsCohs Xp) dc] e in cA) d.
Proof.
  now destruct e.
Qed.

Lemma ssFaceRewPrefixNil {n} {XpA XpB: (SSSetAt n.+1).(prefix)} (e: XpA = XpB)
  (d: ssFrameDom XpB):
  ssFace (dcTop := prefixDepsCohs XpA) DepsCohsChainNil
    (rew <- [ssFrameDom] e in d) =
  rew <- [ssTotalType] e in
    ssFace (dcTop := prefixDepsCohs XpB) DepsCohsChainNil d.
Proof.
  now destruct e.
Qed.

(** The candidate-filler contraction: given a frame
    translation [tr], an identification [HF] of the cells with the total
    space, and the frame identification [FRT] ([pshF] of a cell is the
    translation of its frame), the candidate filler over a translated
    frame is equivalent to the original filler. The construction composes
    existing equivalences, and [UIP] identifies their path components. *)

Definition fillerEquivOf {FrB FrA CellH: HSet} (tr: Equiv FrB FrA)
  {E: FrB -> HSet} (HF: CellH = {D: FrB & E D})
  (pshF: CellH -> FrA)
  (FRT: forall (D: FrB) (c: E D),
    pshF (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)))
      = tr D)
  (D: FrB):
  Equiv {cell: CellH &T tr D = pshF cell} (E D) :=
  compEquiv
    (sigTEquivSnd (fun cell => pathEquiv (A := FrA)
      (fun q => q • f_equal pshF (eq_sym (rew_sym_cancel (P := Dom) HF cell)))
      (fun q => q • f_equal pshF (rew_sym_cancel (P := Dom) HF cell))))
  (compEquiv
    (sigTEquivFst (rewEquiv (fun h: HSet => h.(Dom)) HF))
  (compEquiv
    (sigTEquivSnd (fun t => pathEquiv (A := FrA)
      (fun q => q • FRT t.1 t.2)
      (fun q => q • eq_sym (FRT t.1 t.2))))
  (compEquiv
    (sigTEquivSnd (fun t => pathEquiv2 (eqvInj tr)
      (fun q => f_equal tr q)))
    (baseContract E D)))).

(** The inverse of the contraction, whole: the pair of the candidate frame
    of a transported cell with its tautological filler is the translated
    pair — the single equation the [FRT] step consumes. *)

Lemma fillerEquivOfWhole {FrB FrA CellH: HSet} (tr: Equiv FrB FrA)
  {E: FrB -> HSet} (HF: CellH = {D: FrB & E D})
  (pshF: CellH -> FrA)
  (FRT: forall (D: FrB) (c: E D),
    pshF (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)))
      = tr D)
  (D: FrB) (c: E D):
  ((pshF (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)));
    (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)); eq_refl))
   : {D0: FrA &T {cell: CellH &T D0 = pshF cell}})
  = (tr D; symEquiv (fillerEquivOf tr HF pshF FRT D) c).
Proof.
  refine (eq_existT_curried (FRT D c) _).
  cbn.
  etransitivity.
  { now exact (rew_sigT_fst_const (FRT D c) _ eq_refl). }
  apply f_equal.
  now apply FrA.(UIP).
Qed.

Lemma gFaceLevelEq {m0} {Xpre0: (SSSetAt m0).(prefix)} (X0: SSSetFrom m0 Xpre0)
  {n1 n2: nat} (e: n1 = n2) (dim: nat)
  (H1: dim <= n1 + m0) (H2: dim <= n2 + m0) (d: gF0 X0 n1.+1):
  gFace X0 n2 dim H2 (rew [fun l => (gF0 X0 l.+1).(Dom)] e in d) =
  rew [fun l => (gF0 X0 l).(Dom)] e in gFace X0 n1 dim H1 d.
Proof.
  now destruct e.
Qed.

(** The descent identification

    The level step of [fg] must, at an abstract level, identify the
    cells of [g X] with the total spaces of the carried [X]-position.
    Induction on [Desc] proves this identification, with [plus_n_Sm]-style
    equalities on the relative index at each successor step. *)

Section FG.

Variable X: SSSets.

Inductive Desc: forall {n} {Xpre: (SSSetAt n).(prefix)},
  SSSetFrom n Xpre -> Type :=
| DescZ: Desc X
| DescS {n} {Xpre: (SSSetAt n).(prefix)} {S0: SSSetFrom n Xpre}:
    Desc S0 -> Desc (next S0).

(** Indexing by [k + n] makes the use sites instantiate [k := 0]. The
    branches supply the required [plus_n_O] and [plus_n_Sm] equalities. *)

Fixpoint descF0 {n} {Xpre: (SSSetAt n).(prefix)} {S0: SSSetFrom n Xpre}
  (D: Desc S0) (k: nat) {struct D}: gF0 X (k + n) = gF0 S0 k :=
  match D in @Desc n0 _ S1 return gF0 X (k + n0) = gF0 S1 k with
  | DescZ => f_equal (gF0 X) (eq_sym (plus_n_O k))
  | @DescS n1 _ S1 D' =>
      f_equal (gF0 X) (eq_sym (plus_n_Sm k n1)) • descF0 D' k.+1
  end.

(** At [k := 0], the cells of [g X] at the position's level are the
    total space of the position — the level state's cell
    identification. *)

Definition descTotal {n} {Xpre: (SSSetAt n).(prefix)} {S0: SSSetFrom n Xpre}
  (D: Desc S0): gF0 X n = ssTotal S0 := descF0 D 0.

(** The faces of [g X] along a descent are the faces of the position:
    the face-compatibility of the cell identification, by induction on
    the witness with index equalities normalized by [natUIP]. *)

Lemma descFace {n} {Xpre: (SSSetAt n).(prefix)} {S0: SSSetFrom n Xpre}
  (D: Desc S0) (k dim: nat) (HdX: dim <= k + n) (HdS: dim <= k + n)
  (t: gF0 S0 k.+1):
  (g X).(Face) (k + n) dim HdX
    (rew [Dom] (eq_sym (descF0 D k.+1)) in t) =
  rew [Dom] (eq_sym (descF0 D k)) in (gFace S0 k dim HdS t).
Proof.
  revert k dim HdX HdS t; induction D; intros k dim HdX HdS t.
  - cbn [descF0].
    rewrite 2 eq_sym_f_equal.
    rewrite (natUIP (eq_sym (eq_sym (plus_n_O k))) (plus_n_O k)).
    rewrite (natUIP (eq_sym (eq_sym (plus_n_O k.+1)))
      (f_equal S (plus_n_O k))).
    rewrite <- 2 (rew_map (fun h: HSet => h.(Dom)) (gF0 X)).
    rewrite <- (rew_map (fun l => (gF0 X l).(Dom)) S).
    now exact (gFaceLevelEq X (plus_n_O k) dim HdS
      (leR_eq_r (plus_n_O (k + 0)) HdX) t).
  - cbn [descF0].
    rewrite 2 eq_trans_sym_distr.
    rewrite 2 eq_sym_f_equal.
    rewrite (natUIP (eq_sym (eq_sym (plus_n_Sm k n))) (plus_n_Sm k n)).
    rewrite (natUIP (eq_sym (eq_sym (plus_n_Sm k.+1 n)))
      (f_equal S (plus_n_Sm k n))).
    rewrite <- 2 rew_compose.
    rewrite <- 2 (rew_map (fun h: HSet => h.(Dom)) (gF0 X)).
    rewrite <- (rew_map (fun l => (gF0 X l).(Dom)) S).
    refine (gFaceLevelEq X (plus_n_Sm k n) dim
      (leR_eq_r (eq_sym (plus_n_Sm k n) • plus_n_O (k + n).+1) HdS)
      (leR_eq_r (plus_n_O (k + n.+1)) HdX) _ • _).
    now exact (f_equal
      (fun w => rew [fun l => (gF0 X l).(Dom)] plus_n_Sm k n in w)
      (IHD k.+1 dim (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS)
        (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS) t)).
Qed.

(** Aligning the two presentations of the next-level cell identification:
    stepping the witness, then identifying at relative index 0, is
    identifying at relative index 1. [natUIP] identifies the resulting
    [plus_n_Sm] equality with the required index equality. *)

Lemma descTotalS {n} {Xpre: (SSSetAt n).(prefix)} {S0: SSSetFrom n Xpre}
  (HD: Desc S0): descTotal (DescS HD) = descF0 HD 1.
Proof.
  unfold descTotal; cbn [descF0].
  rewrite (natUIP (eq_sym (plus_n_Sm 0 n)) eq_refl).
  now apply eq_trans_refl_l.
Qed.

(** The carried frame identification: the candidate
    frame of a cell transported from the position's total space is the
    backward transport of its frame along the prefix equality. Stated in
    the exact shape [fillerEquivOf] consumes. *)

Definition FrtInv {m} {XpA XpB: (SSSetAt m.+1).(prefix)}
  (r: PrefixRel m.+1 XpA XpB)
  (T: PshTower (g X) m XpA) (SB: SSSetFrom m.+1 XpB) (HD: Desc SB): Type :=
  forall (D: mkFrame (ssTowerDeps XpB)) (c: this SB D),
  mkPshFrame (g X) (towerPshDeps (g X) T)
    (rew [Dom] (eq_sym (descTotal HD)) in
      ((D; c): ({D0: mkFrame (ssTowerDeps XpB) & this SB D0}: HSet)))
  = rew <- [ssFrameDom] (prefixEq r) in D.

(** The filler equivalence of the round trip at a level: the
    candidate-filler contraction over the frame identification, in the
    direction the prefix relation stores it — from the candidate fillers
    over the transported frame to the fillers of the position. *)

Definition fgThis {m} {XpA XpB: (SSSetAt m.+1).(prefix)}
  (r: PrefixRel m.+1 XpA XpB)
  (T: PshTower (g X) m XpA) (SB: SSSetFrom m.+1 XpB) (HD: Desc SB)
  (FRT: FrtInv r T SB HD):
  ssFillerEqvType (prefixEq r)
    (mkPshFiller (g X) (towerPshDeps (g X) T)) (this SB) :=
  fun D => fillerEquivOf (rewEquiv ssFrameDom (eq_sym (prefixEq r)))
    (descTotal HD) (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT D.

(** The bottom face of [g X] at the position, as [ssFace] along an
    arbitrary chain from the position's top: the fuel-synthesized package
    and the chain's own package are both [dcStep]-iterations of the nil
    package, of the same length by the stage equation. *)

Lemma fgFaceB {m} {Xpre: (SSSetAt m.+1).(prefix)} (SB: SSSetFrom m.+1 Xpre)
  {p k} {dc: DepsCohs p k} (cB: DepsCohsChain (ssDepsCohsAt SB) dc)
  (Hp: p <= m.+1) (t: ssTotal (next SB)):
  gFace SB 0 p Hp t = ssFace cB t.1.
Proof.
  change (ssFaceFuel SB (m.+1 - p) t = ssFace cB t.1).
  unfold ssFaceFuel.
  rewrite (f_equal (fun z => z - p) (eq_sym (cohsChainStage cB))
    • addSubCancelL p (cohsChainLen cB)).
  now exact (f_equal
    (fun s: DCPack (ssDepsCohsAt SB) => ssFace s.2.2.2 t.1)
    (chain2DownIter (ssDepsCohs2At SB) (cohsChainLen cB)
      • eq_sym (chainPackNF cB))).
Qed.

(** The step of the frame identification, by [ssFaceEq]: every face of the
    two frames agrees. Lift the arbitrary chain to the presheaf side and
    rewrite [ssFace] with [pshSSFace]; on the original-tower side push the
    prefix transport through [ssFace] ([ssFaceRewPrefix]) and compute it on
    the resulting cell ([prefixEqRewTotal]); identify the two faces with the
    face at the position using [descFace] and [fgFaceB]; and apply the
    current identification through [fillerEquivOfWhole].

    The top of the arbitrary chain is retyped as [prefixDepsCohs] of the
    stepped prefix before the transport is pushed through: the two forms
    are convertible, but only the [prefixDepsCohs] one exposes the prefix
    as an argument for the transport motive to abstract. *)

Lemma fgFrameStep {m} {XpA XpB: (SSSetAt m.+1).(prefix)}
  (r: PrefixRel m.+1 XpA XpB)
  (T: PshTower (g X) m XpA) (rpPsh: PshTowerRestrPaintings (g X) T)
  (SB: SSSetFrom m.+1 XpB) (HD: Desc SB) (FRT: FrtInv r T SB HD):
  FrtInv (relStep r (fgThis r T SB HD FRT))
    (towerStep (g X) T rpPsh) (next SB) (DescS HD).
Proof.
  intros D c.
  refine (ssFaceEq
    (dcTop := pshDepsCohs (g X) (towerPshDepsCohs (g X) T rpPsh)) _ _ _).
  intros p k dc c0.
  destruct (pshChainLift (g X) (towerPshDepsCohs (g X) T rpPsh) c0)
    as (PC, (Cpsh, ePsh)).
  pose (Hp := leR_eq_r (cohsChainStage c0) (leR_add_r p (cohsChainLen c0))).
  refine (f_equal (fun s: {dc0: DepsCohs p k &T
      DepsCohsChain (pshDepsCohs (g X) (towerPshDepsCohs (g X) T rpPsh)) dc0}
    => ssFace s.2 _) ePsh • _).
  rewrite (pshSSFace (g X) Cpsh Hp).
  change (DepsCohsChain (prefixDepsCohs
    ((XpA; mkPshFiller (g X) (towerPshDeps (g X) T)):
      (SSSetAt m.+2).(prefix))) dc) in (type of c0).
  rewrite (ssFaceRewPrefix
    (prefixEq (relStep r (fgThis r T SB HD FRT))) c0 D).
  set (cB0 := rew [fun Xp => DepsCohsChain (prefixDepsCohs Xp) dc]
    (prefixEq (relStep r (fgThis r T SB HD FRT))) in c0).
  rewrite (prefixEqRewTotal (relStep r (fgThis r T SB HD FRT))
    (ssFace cB0 D)).
  rewrite (descTotalS HD).
  rewrite (descFace HD 0 p Hp Hp (D; c)).
  rewrite (fgFaceB SB cB0 Hp (D; c)).
  now exact (fillerEquivOfWhole (rewEquiv ssFrameDom (eq_sym (prefixEq r)))
    (descTotal HD) (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT
    (ssFace cB0 D).1 (ssFace cB0 D).2).
Qed.

(** Base case of the frame identification. At level 0, the frame is
    [unit], the candidate frame map is constant, and [hunit_ext] proves
    the required identification. *)

Definition pshF0A: gF0 X 0 ->
  mkFrame (ssTowerDeps (tt: (SSSetAt 0).(prefix))) := fun _ => tt.

Definition frt0 (D: mkFrame (ssTowerDeps (tt: (SSSetAt 0).(prefix))))
  (c: this X D):
  pshF0A (rew [Dom] (eq_sym (descTotal DescZ)) in
    ((D; c): ({D0: mkFrame (ssTowerDeps (tt: (SSSetAt 0).(prefix))) &
       this X D0}: HSet)))
  = rew <- [ssFrameDom] (prefixEq rel0) in D :=
  hunit_ext tt (rew <- [ssFrameDom] (prefixEq rel0) in D).

Definition fgThis0:
  ssFillerEqvType (prefixEq rel0) (pshFiller0 (g X)) (this X) :=
  fun D => fillerEquivOf (rewEquiv ssFrameDom (eq_sym (prefixEq rel0)))
    (descTotal DescZ) pshF0A frt0 D.

(** The level-1 base case of [fgFrameStep]. The only chain from stage 0 is
    empty, so both applications of [ssFace] reduce by conversion. *)

Lemma fgFrameStep0:
  FrtInv (relStep rel0 fgThis0) (tower1 (g X)) (next X) (DescS DescZ).
Proof.
  intros D c.
  refine (ssFaceEq (dcTop := prefixDepsCohs
    ((tt; pshFiller0 (g X)): (SSSetAt 1).(prefix))) _ _ _).
  intros p k dc c0.
  destruct c0 as [|p k dc' c0'].
  2: { pose proof (cohsChainStage c0') as HS. now discriminate HS. }
  rewrite (ssFaceRewPrefixNil (prefixEq (relStep rel0 fgThis0)) D).
  rewrite (prefixEqRewTotal (relStep rel0 fgThis0)
    (ssFace (dcTop := ssDepsCohsAt X) DepsCohsChainNil D)).
  unfold ssFace.
  cbn -[descTotal descF0 g].
  rewrite (descTotalS DescZ).
  rewrite (descFace DescZ 0 0 leR_O leR_O (D; c)).
  now exact (fillerEquivOfWhole (rewEquiv ssFrameDom (eq_sym (prefixEq rel0)))
    (descTotal DescZ) pshF0A frt0
    (ssFace (dcTop := ssDepsCohsAt X) DepsCohsChainNil D).1
    (ssFace (dcTop := ssDepsCohsAt X) DepsCohsChainNil D).2).
Qed.

(** The round trip as a levelwise equivalence

    [SSSetsEquiv] asks for a chain of prefix relations bonded by first
    projection. The relations are produced level by level by a chain
    fixpoint whose state carries what the next level needs: the frame
    identification, and the identification of the presheaf-side
    approximation with the one [SSSetPack] reaches.

    [SSSetPack m (f (g X))] and [(pshApprox (g X) m; pshFrom (g X) m)] are
    two recursions on [m] that agree, but neither reduces at a variable
    level, so the state also carries their identification. It is [eq_refl]
    at every level: once the two agree at [m], the [SSSetPack] step is the
    presheaf step by conversion, because [pshApprox] bonds by [eq_refl].
    The presheaf-side state steps definitionally in the same way,
    [pshTw (g X) m.+1] being
    [towerStep (g X) (pshTw (g X) m) (pshTwRp (g X) m)]. *)

Fixpoint descAt (m: nat): Desc ((SSSetPack m X).2) :=
  match m with
  | 0 => DescZ
  | S m => DescS (descAt m)
  end.

Definition FgState (m: nat)
  (P: {Xp: (SSSetAt m.+1).(prefix) &T SSSetFrom m.+1 Xp})
  (r: PrefixRel m.+1 P.1 ((SSSetPack m.+1 X).1)): Type :=
  { HP: (pshApprox (g X) m.+1; pshFrom (g X) m.+1) = P &T
    FrtInv (rew <- [fun Q: {Xp: (SSSetAt m.+1).(prefix) &T SSSetFrom m.+1 Xp}
                      => PrefixRel m.+1 Q.1 ((SSSetPack m.+1 X).1)] HP in r)
      (pshTw (g X) m) ((SSSetPack m.+1 X).2) (descAt m.+1) }.

Definition FgChainState (m: nat):
  PrefixRel m (SSSetPack m (f (g X))).1 ((SSSetPack m X).1) -> Type :=
  match m return PrefixRel m (SSSetPack m (f (g X))).1 ((SSSetPack m X).1) ->
    Type with
  | 0 => fun _ => unit
  | S m => fun r => FgState m (SSSetPack m.+1 (f (g X))) r
  end.

(** The level step at a positive level: it emits the level's filler
    equivalence and rebuilds the state one level up, with the
    identification of the two approximations consumed first so that the
    filler equivalence is the presheaf-side one. *)

Lemma fgStep (m: nat)
  (P: {Xp: (SSSetAt m.+1).(prefix) &T SSSetFrom m.+1 Xp})
  (r: PrefixRel m.+1 P.1 ((SSSetPack m.+1 X).1)) (s: FgState m P r):
  { E: ssFillerEqvType (prefixEq r) (this P.2) (this ((SSSetPack m.+1 X).2)) &T
    FgState m.+1 ((P.1; this P.2); next P.2) (relStep r E) }.
Proof.
  destruct s as (HP, s); revert r s; destruct HP; intros r s; cbn in s |- *.
  now exact
    (fgThis r (pshTw (g X) m) ((SSSetPack m.+1 X).2) (descAt m.+1) s;
     (eq_refl;
      fgFrameStep r (pshTw (g X) m) (pshTwRp (g X) m)
        ((SSSetPack m.+1 X).2) (descAt m.+1) s)).
Defined.

(** The level step at level 0: the prefix relation there is [unit], so it
    is the canonical one and the level data is the base case. *)

Lemma fgStep0
  (r: PrefixRel 0 (SSSetPack 0 (f (g X))).1 ((SSSetPack 0 X).1))
  (s: FgChainState 0 r):
  { E: ssFillerEqvType (prefixEq r)
         (this ((SSSetPack 0 (f (g X))).2)) (this ((SSSetPack 0 X).2)) &T
    FgChainState 1 (relStep r E) }.
Proof.
  destruct r.
  now exact (fgThis0; (eq_refl; fgFrameStep0)).
Defined.

Definition fgExtend (m: nat):
  forall r: PrefixRel m (SSSetPack m (f (g X))).1 ((SSSetPack m X).1),
  FgChainState m r ->
  { E: ssFillerEqvType (prefixEq r)
         (this ((SSSetPack m (f (g X))).2)) (this ((SSSetPack m X).2)) &T
    FgChainState m.+1 (relStep r E) } :=
  match m return forall r: PrefixRel m (SSSetPack m (f (g X))).1
      ((SSSetPack m X).1), FgChainState m r ->
    { E: ssFillerEqvType (prefixEq r)
           (this ((SSSetPack m (f (g X))).2)) (this ((SSSetPack m X).2)) &T
      FgChainState m.+1 (relStep r E) } with
  | 0 => fgStep0
  | S m => fun r s => fgStep m (SSSetPack m.+1 (f (g X))) r s
  end.

Fixpoint fgChain (m: nat):
  {r: PrefixRel m (SSSetPack m (f (g X))).1 ((SSSetPack m X).1) &T
   FgChainState m r} :=
  match m with
  | 0 => (tt; tt)
  | S m =>
    let s := fgChain m in
    let e := fgExtend m s.1 s.2 in
    ((s.1; e.1); e.2)
  end.

(** The chain is bonded by conversion: the relation at [m.+1] is the
    relation at [m] paired with the emitted filler equivalence. *)

Definition fg: SSSetsEquiv (f (g X)) X :=
  limit (eqvTel (f (g X)) X) 0 tt
    (fun m _ => (fgChain m).1) eq_refl (fun m _ _ => eq_refl).
End FG.

End SSSetRoundtrip.
