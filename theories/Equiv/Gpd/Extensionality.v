(** A levelwise equivalence [νGpdsEquiv SA SB] determines compatible
    paths between finite prefixes. [νGpdsEqFromPaths] turns these into
    tower equality through [Limit.limitEqIntro].

    Univalence and function extensionality identify filler families.
    The invariant below compares transport along each prefix path with
    the frame and painting translations, including their restriction
    coherences. These coherences are proved along the recursion; [GUIP]
    identifies parallel 2-cells where their particular proofs do not matter.

    The step lemmas abstract over the prefix and filler paths so that
    path induction exposes the transports. Their comparison data are
    parameters rather than projections of a term matching on those paths. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Limit Univalence
  νGpd.HGpd νGpd.HGpdEq νGpd.Layer νGpd.Lemmas νGpd.Pasting νGpd.
From Bonak.Lib Require Import Equiv.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Equiv.Gpd Require νGpdEquiv.

From Bonak.Lib Require Import NatLemmas.
From Bonak.Equiv.Gpd Require Import PathAlgebra.

Set Primitive Projections.
Set Keyed Unification.

Module Extensionality (A: LayerGpdSig) (Base: PresheafOfνGpd.ConstructionsSig A)
  (Translations: νGpdEquiv.TranslationSig A Base).
Import A.
Module Export Tr := Translations.

(** Equivalences of filler families over a prefix path. *)

Definition νFillerEqvType {n} {XA XB: (νGpdAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA) (EB: νFillerType XB): Type :=
  forall d: νFrame XB, Equiv (EA (rew <- [νFrameDom] e in d)) (EB d).

(** Transporting a filler family along a prefix equality precomposes with
    the backward frame transport. The definition is transparent so that
    the equality reduces when the prefix equality is [eq_refl]. *)

Definition rewνFillerType {n} {XA XB: (νGpdAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA):
  rew [νFillerType] e in EA = fun d => EA (rew <- [νFrameDom] e in d).
Proof.
  now destruct e.
Defined.

(** The filler-family equality induced by an equivalence family: funext of
    the levelwise HGpd equalities from univalence *)

Definition νFillerEq {n} {XA XB: (νGpdAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType e EA EB): rew [νFillerType] e in EA = EB :=
  rewνFillerType e EA
  • functional_extensionality_dep_good _ _ (fun d => hgpdEq (eqvs d)).

(** Transport along a pointwise equality of filler families. *)

Lemma rewνFillerFunext {n} {X1: (νGpdAt n).(prefix)}
  {EA EB: νFillerType X1} (H: forall d, EA d = EB d)
  (d0: νFrame X1) (c: EB d0):
  rew <- [fun E: νFillerType X1 => E d0: Type]
    (functional_extensionality_dep_good EA EB H) in c =
  rew <- [GDom] (H d0) in c.
Proof.
  unfold eq_rect_r.
  rewrite (rew_map (fun h: HGpd => h.(GDom)) (fun E: νFillerType X1 => E d0)).
  rewrite <- eq_sym_f_equal.
  now rewrite (f_equal__functional_extensionality_dep_good H d0).
Qed.

(** Reading the finite unfoldings off the chain

    [νGpdPack] rebuilds the level-[m] prefix by iterating the
    destructors. [packPath] identifies that prefix with level [m] of the
    tower's stored chain. *)

Fixpoint packApprox (m: nat) (S: νGpds) (l: nat) {struct m}:
  forall Hl: m <= l, ((νGpdPack m S).2).(approx) l Hl = S.(approx) l leR_O :=
  match m return forall Hl: m <= l,
    ((νGpdPack m S).2).(approx) l Hl = S.(approx) l leR_O with
  | 0 => fun _ => eq_refl
  | m.+1 => fun Hl => packApprox m S l (↓ Hl)
  end.

Definition packPath (m: nat) (S: νGpds):
  (νGpdPack m S).1 = S.(approx) m leR_O :=
  eq_sym ((νGpdPack m S).2).(approxO)
  • packApprox m S m leR_refl.

(** Reading it off is compatible with the bonding equations:
    [νGpdPack]'s own bonding equation is [eq_refl] (its prefix at [m.+1]
    is literally a pair over its prefix at [m]), the tower's is
    [approxS]. *)

Lemma packApproxS (m: nat) (S: νGpds) (l: nat) (Hl: m <= l) (HSl: m <= l.+1):
  f_equal (fun Y: (νGpdAt l.+1).(prefix) => Y.1) (packApprox m S l.+1 HSl)
    • S.(approxS) l leR_O leR_O
  = ((νGpdPack m S).2).(approxS) l Hl HSl • packApprox m S l Hl.
Proof.
  revert l Hl HSl; induction m as [|m IH]; intros l Hl HSl.
  - cbn. now rewrite eq_trans_refl_l.
  - now exact (IH l (↓ Hl) (↓ HSl)).
Qed.

(** The generic truncation law at this telescope: its [bondExtend] is
    [eq_refl], so the trailing composite disappears and [bondApproxEta]
    reads as the first projection of the Σ-equality [approxEta] is built
    from. *)

Definition approxEtaProj {n} {X: (νGpdAt n).(prefix)} (ν: νGpdFrom n X):
  f_equal (fun Y: (νGpdAt n.+1).(prefix) => Y.1) (approxEta ν)
  = ν.(approxS) n leR_refl (↑ leR_refl) • ν.(approxO) :=
  bondApproxEta ν.

Lemma packPathS (m: nat) (S: νGpds):
  f_equal (fun Y: (νGpdAt m.+1).(prefix) => Y.1) (packPath m.+1 S)
    • S.(approxS) m leR_O leR_O = packPath m S.
Proof.
  unfold packPath.
  change ((νGpdPack m.+1 S).2).(approxO)
    with (approxEta ((νGpdPack m S).2)).
  change (packApprox m.+1 S m.+1 leR_refl)
    with (packApprox m S m.+1 (↓ leR_refl)).
  rewrite eq_trans_map_distr, <- eq_sym_map_distr.
  rewrite (approxEtaProj ((νGpdPack m S).2)).
  rewrite <- eq_trans_assoc.
  rewrite (packApproxS m S m leR_refl (↓ leR_refl)).
  now apply eq_trans_sym_cancel_common.
Qed.

(** From coherent prefix paths to tower equality

    Conjugating the given paths by [packPath] gives paths between the
    stored prefixes, and [packPathS] turns their coherence into the square
    [limitEqIntro] asks for. The base coherence lives in the [unit] prefix
    of level 0, hence is free. *)

Lemma νGpdsEqFromPaths {SA SB: νGpds}
  (p: forall m, (νGpdPack m SA).1 = (νGpdPack m SB).1)
  (ps: forall m,
    f_equal (fun Xp: (νGpdAt m.+1).(prefix) => Xp.1) (p m.+1) = p m):
  SA = SB.
Proof.
  unshelve eapply limitEqIntro.
  - now exact (fun l => eq_sym (packPath l SA) • (p l • packPath l SB)).
  - now apply unit_UIP.
  - intro l; cbv beta.
    rewrite eq_trans_map_distr, eq_trans_map_distr, <- eq_sym_map_distr.
    rewrite (ps l).
    rewrite <- (packPathS l SA), <- (packPathS l SB).
    now apply eq_trans_conj_comp.
Qed.

(** The first component of an extended prefix path. *)

Lemma extendCongFst {n} {XA XB: (νGpdAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB):
  f_equal (fun Xp: (νGpdAt n.+1).(prefix) => Xp.1)
    (extendCong (T := νGpdTel) e h) = e.
Proof.
  now destruct e, h.
Qed.

(** Transport along a prefix path

    The dependencies of a level as a function of the prefix, and
    transport of frames and paintings along a prefix path; its naturality
    in the restrictions holds by path induction. One level up, the
    paintings depend on the fillers too, so their transport is along the
    prefix path and the filler path. *)

Section Transport.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB).

Definition rewFr {p k} (F: (νGpdAt m).(prefix) -> mkFrameTypes p.+1 k)
  (d: (F XB).2): (F XA).2 :=
  rew <- [fun X => GDom (F X).2] e in d.

Definition rewPt {p k} (F: (νGpdAt m).(prefix) -> mkFrameTypes p.+1 k)
  (PT: forall X, mkPaintingTypes p.+1 k (F X))
  (d: (F XB).2) (c: (PT XB).2 d): (PT XA).2 (rewFr F d) :=
  match e as e0 in (_ = XB0)
    return forall d: (F XB0).2, (PT XB0).2 d ->
      (PT XA).2 (rew <- [fun X => GDom (F X).2] e0 in d)
  with eq_refl => fun d c => c end d c.

Definition nextFr {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (X: (νGpdAt m).(prefix)): mkFrameTypes p.+1 k := mkFrames (DR X).

(** Transport commutes with the restrictions computed from the prefix. *)
Definition natRestr {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  q (Hq: q <= k) (ε: arity) (d: (nextFr DR XB).1.2):
  rewFr (fun X => (DR X).(_frames)) ((DR XB).(_restrFrames).2 q Hq ε d)
  = (DR XA).(_restrFrames).2 q Hq ε (rewFr (fun X => (nextFr DR X).1) d) :=
  match e as e0 in (_ = XB0)
    return forall d: (nextFr DR XB0).1.2,
      rew <- [fun X => GDom (DR X).(_frames).2] e0 in
        (DR XB0).(_restrFrames).2 q Hq ε d
      = (DR XA).(_restrFrames).2 q Hq ε
          (rew <- [fun X => GDom (nextFr DR X).1.2] e0 in d)
  with eq_refl => fun d => eq_refl end d.

Context {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB).

Definition rewPtN {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (d: (nextFr DR XB).2) (c: (mkPaintings (XT XB EB)).2 d):
  (mkPaintings (XT XA EA)).2 (rewFr (nextFr DR) d) :=
  match e as e0 in (_ = XB0)
    return forall (EB0: νFillerType XB0)
      (h0: rew [νFillerType] e0 in EA = EB0) (d: (nextFr DR XB0).2),
      (mkPaintings (XT XB0 EB0)).2 d ->
      (mkPaintings (XT XA EA)).2 (rew <- [fun X => GDom (nextFr DR X).2] e0 in d)
  with eq_refl => fun EB0 h0 =>
    match h0 in (_ = EB1)
      return forall d: (nextFr DR XA).2,
        (mkPaintings (XT XA EB1)).2 d -> (mkPaintings (XT XA EA)).2 d
    with eq_refl => fun d c => c end
  end EB h d c.

End Transport.

(** Transport commutes with the restriction paintings. *)
Definition natRestrPt {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  q (Hq: q <= k) (ε: arity) (d: (nextFr DR XB).1.2)
  (c: (mkPaintings (XT XB EB)).1.2 d):
  rew [fun x => GDom ((DR XA).(_paintings).2 x)] natRestr e DR q Hq ε d in
    rewPt e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      ((DR XB).(_restrFrames).2 q Hq ε d) ((RP XB EB).2 q Hq ε d c)
  = (RP XA EA).2 q Hq ε (rewFr e (fun X => (nextFr DR X).1) d)
      (rewPtN e h (fun X => proj1DepsRestr (DR X))
        (fun X E => (DR X; XT X E)%extradepsrestr) d c).
Proof.
  destruct e. cbn in h. destruct h. now reflexivity.
Defined.

(** The invariant

    [RhoTypes]: at every stage, transport of a frame along the path is the
    translation tower's frame equivalence; [PiTypes]: transported paintings, read at
    the frame equivalence through [ρ], are the painting equivalences
    ([PiTypesN] is its form for the paintings one level up, transported
    along the filler path too); [SigmaTypes]: the translation tower's restriction
    commutations are the naturality of transport, conjugated by [ρ] at
    both ends, [ρ] for the next level's frames included; [TauTypes]: the
    same for the restriction-painting commutations over [σ]. *)

Section Invariant.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB).

Fixpoint RhoTypes {p k}:
  forall (F: (νGpdAt m).(prefix) -> mkFrameTypes p k),
  mkFrameEqvTypes (F XA) (F XB) -> Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p => fun F eqvs =>
      { _: RhoTypes (fun X => (F X).1) eqvs.1 &T
        forall d: (F XB).2, rewFr e F d = eqvs.2 d }
  end.

Fixpoint PiTypes {p k}:
  forall (F: (νGpdAt m).(prefix) -> mkFrameTypes p k)
    (PT: forall X, mkPaintingTypes p k (F X))
    (eqvs: mkFrameEqvTypes (F XA) (F XB)) (rho: RhoTypes F eqvs),
  mkPaintingEqvTypes eqvs (PT XA) (PT XB) -> Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p => fun F PT eqvs rho pEqvs =>
      { _: PiTypes (fun X => (F X).1) (fun X => (PT X).1) eqvs.1 rho.1 pEqvs.1 &T
        forall (d: (F XB).2) (c: (PT XB).2 d),
          rew [fun x => GDom ((PT XA).2 x)] (rho.2 d) in rewPt e F PT d c
          = pEqvs.2 d c }
  end.

Fixpoint SigmaTypes {p k}:
  forall (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (rho: RhoTypes (fun X => (DR X).(_frames)) eqvs)
    (rho'1: RhoTypes (fun X => (nextFr DR X).1)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).1), Type :=
  match p with
  | 0 => fun _ _ _ _ _ _ => unit
  | S p => fun DR eqvs pEqvs trRestrs rho rho'1 =>
      { _: SigmaTypes (fun X => proj1DepsRestr (DR X)) eqvs.1 pEqvs.1 trRestrs.1 rho.1 rho'1.1 &T
        forall q (Hq: q <= k) (ε: arity) (d: (nextFr DR XB).1.2),
          rho.2 ((DR XB).(_restrFrames).2 q Hq ε d) • trRestrs.2 q Hq ε d
          = path_reindex_source (natRestr e DR q Hq ε d)
              (f_equal ((DR XA).(_restrFrames).2 q Hq ε) (rho'1.2 d)) }
  end.

Context {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB).

Definition PiTop {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (eqvs': mkFrameEqvTypes (nextFr DR XA) (nextFr DR XB))
  (rho': RhoTypes (nextFr DR) eqvs')
  (pEqvs': mkPaintingEqvTypes eqvs' (mkPaintings (XT XA EA))
    (mkPaintings (XT XB EB))): Type :=
  forall (d: (nextFr DR XB).2) (c: (mkPaintings (XT XB EB)).2 d),
    rew [fun x => GDom ((mkPaintings (XT XA EA)).2 x)] (rho'.2 d) in
      rewPtN e h DR XT d c
    = pEqvs'.2 d c.

Fixpoint PiTypesNPrefix {p k}:
  forall (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (eqvs': mkFrameEqvTypes (nextFr DR XA) (nextFr DR XB))
    (rho': RhoTypes (nextFr DR) eqvs'),
  mkPaintingEqvTypes eqvs' (mkPaintings (XT XA EA)) (mkPaintings (XT XB EB))
  -> Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p => fun DR XT eqvs' rho' pEqvs' =>
      { _: PiTypesNPrefix (fun X => proj1DepsRestr (DR X))
             (fun X E => (DR X; XT X E)%extradepsrestr) eqvs'.1 rho'.1 pEqvs'.1 &T
        PiTop (fun X => proj1DepsRestr (DR X))
          (fun X E => (DR X; XT X E)%extradepsrestr) eqvs'.1 rho'.1 pEqvs'.1 }
  end.

Definition PiTypesN {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (eqvs': mkFrameEqvTypes (nextFr DR XA) (nextFr DR XB))
  (rho': RhoTypes (nextFr DR) eqvs')
  (pEqvs': mkPaintingEqvTypes eqvs' (mkPaintings (XT XA EA))
    (mkPaintings (XT XB EB))): Type :=
  { _: PiTypesNPrefix DR XT eqvs' rho' pEqvs' &T PiTop DR XT eqvs' rho' pEqvs' }.

(** The clause of [TauTypes] at one stage: the translation tower's
    restriction-painting commutation, conjugated by [σ], is transport
    naturality against [π] at the face and the next level's [π]. *)
Definition TauClauseAt {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension {| _depsA := DR XA; _depsB := DR XB;
    _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
    (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes {| _depsA := DR XA; _depsB := DR XB;
    _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
    TX (RP XA EA) (RP XB EB))
  (rho: RhoTypes (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes DR eqvs pEqvs trRestrs rho rho'.1)
  (pi': PiTypesN DR XT _ rho' (mkPaintingEqvs TX)) (q: nat) (Hq: q <= k): Type :=
      forall (ε: arity) (d: (nextFr DR XB).1.2)
        (c: (mkPaintings (XT XB EB)).1.2 d),
      rew [fun r: rewFr e (fun X => (DR X).(_frames))
                    ((DR XB).(_restrFrames).2 q Hq ε d)
                  = (DR XA).(_restrFrames).2 q Hq ε
                      (((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef)
                          trRestrs).1.2 d) =>
           rew [fun x => GDom ((DR XA).(_paintings).2 x)] r in
             rewPt e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
               ((DR XB).(_restrFrames).2 q Hq ε d) ((RP XB EB).2 q Hq ε d c)
           = (RP XA EA).2 q Hq ε
               (((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).1.2 d)
               ((mkPaintingEqvs TX).1.2 d c)]
        sigma.2 q Hq ε d in
      (pi.2 ((DR XB).(_restrFrames).2 q Hq ε d) ((RP XB EB).2 q Hq ε d c)
       ⊙[fun x => GDom ((DR XA).(_paintings).2 x)] rp.2 q Hq ε d c)
      = path_reindex_source_comp (fun x => GDom ((DR XA).(_paintings).2 x))
          (natRestr e DR q Hq ε d)
          (f_equal ((DR XA).(_restrFrames).2 q Hq ε) (rho'.1.2 d))
          (natRestrPt e h DR XT RP q Hq ε d c)
          (sigT_map_eq (Q := fun x => GDom ((DR XA).(_paintings).2 x))
            (fun y c0 => (RP XA EA).2 q Hq ε y c0) (pi'.1.2 d c)).

(** The clause at all offsets *)
Definition TauClause {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension {| _depsA := DR XA; _depsB := DR XB;
    _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
    (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes {| _depsA := DR XA; _depsB := DR XB;
    _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
    TX (RP XA EA) (RP XB EB))
  (rho: RhoTypes (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes DR eqvs pEqvs trRestrs rho rho'.1)
  (pi': PiTypesN DR XT _ rho' (mkPaintingEqvs TX)): Type :=
  forall q (Hq: q <= k),
  TauClauseAt DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma pi' q Hq.

Fixpoint TauTypes {p k}:
  forall (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension {| _depsA := DR XA; _depsB := DR XB;
      _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
      (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes {| _depsA := DR XA; _depsB := DR XB;
      _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
      TX (RP XA EA) (RP XB EB))
    (rho: RhoTypes (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes DR eqvs pEqvs trRestrs rho rho'.1)
    (pi': PiTypesN DR XT _ rho' (mkPaintingEqvs TX)), Type :=
  match p with
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ _ => unit
  | S p => fun DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma pi' =>
      { _: TauTypes (fun X => proj1DepsRestr (DR X)) (fun X E => (DR X; XT X E)%extradepsrestr)
             (fun X E => (RP X E).1) eqvs.1 pEqvs.1 trRestrs.1
             (AddTrDep _ TX) rp.1 rho.1 pi.1 rho'.1 sigma.1 pi'.1 &T
        TauClause DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma pi' }
  end.

End Invariant.

(** The filler path of a filler equivalence, and the extended prefix path

    The translation tower states its filler equivalence over its frame equivalence;
    [ρ] for the next level's frames reads it over transport, which is what
    [νFillerEq] turns into a path. *)

Section FillerPath.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  (eqvs': mkFrameEqvTypes (nextFr νTowerDeps XA) (nextFr νTowerDeps XB))
  (rho': RhoTypes e (nextFr νTowerDeps) eqvs')
  {EA: νFillerType XA} {EB: νFillerType XB}
  (fEqv: forall d: νFrame XB, Equiv (EB d) (EA (eqvs'.2 d))).

Definition eqvsOf: νFillerEqvType e EA EB :=
  fun d => compEquiv (rewEquiv (fun x => GDom (EA x)) (rho'.2 d))
    (symEquiv (fEqv d)).

Definition hOf: rew [νFillerType] e in EA = EB := νFillerEq e eqvsOf.

Definition extOf: ((XA; EA): (νGpdAt m.+1).(prefix)) = (XB; EB) :=
  extendCong (T := νGpdTel) e hOf.

End FillerPath.

(** Transport lemmas by path induction *)

(** Transport along the extended path in a family of the truncation is
    transport along the path. *)
Lemma rewFrExt {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB) {p k}
  (F: (νGpdAt m).(prefix) -> mkFrameTypes p.+1 k)
  (d: (F XB).2):
  rewFr (extendCong (T := νGpdTel) e h) (fun X' => F X'.1) d = rewFr e F d.
Proof.
  destruct e. cbn in h. destruct h. now reflexivity.
Defined.

(** Transport of a layer along the path, and of the pair frame it sits in *)
Definition rewLayer {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (d: (nextFr DR XB).1.2)
  (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d):
  mkLayer (DR XA).(_restrFrames).2 (painting := (DR XA).(_paintings).2)
    (rewFr e (fun X => (nextFr DR X).1) d) :=
  match e as e0 in (_ = XB0)
    return forall (d: (nextFr DR XB0).1.2)
      (l: mkLayer (DR XB0).(_restrFrames).2 (painting := (DR XB0).(_paintings).2) d),
      mkLayer (DR XA).(_restrFrames).2 (painting := (DR XA).(_paintings).2)
        (rew <- [fun X => GDom (nextFr DR X).1.2] e0 in d)
  with eq_refl => fun d l => l end d l.

Lemma rewFrPair {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (d: (nextFr DR XB).1.2)
  (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d):
  rewFr e (nextFr DR) ((d; l): (nextFr DR XB).2)
  = ((rewFr e (fun X => (nextFr DR X).1) d; rewLayer e DR d l): (nextFr DR XA).2).
Proof.
  destruct e. now reflexivity.
Defined.

(** The components of a transported layer are the transported components,
    at the transported face. *)
Lemma nthRewLayer {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (d: (nextFr DR XB).1.2)
  (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d)
  (ε: arity):
  nth (rewLayer e DR d l) ε
  = rew [fun x => GDom ((DR XA).(_paintings).2 x)] natRestr e DR 0 leR_O ε d in
      rewPt e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
        ((DR XB).(_restrFrames).2 0 leR_O ε d) (nth l ε).
Proof.
  destruct e. now reflexivity.
Defined.

Section LayerStep.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho'1: RhoTypes (p := p.+1) (k := k.+1) e (fun X => (nextFr DR X).1)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).1)
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'1).

(** Over [ρ] for the next level's frames, the transported layer is the
    translation tower's layer equivalence: componentwise, [π] at the face and the
    transport square of [σ] at index [0]. *)
Definition rhoLayerNth (d: (nextFr DR XB).1.2)
  (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d)
  (ε: arity):
  nth (rew [fun x => mkLayer (DR XA).(_restrFrames).2 (painting := (DR XA).(_paintings).2) x]
    rho'1.2 d in rewLayer e DR d l) ε
  = nth (mkTrLayerEquiv pEqvs trRestrs d l) ε.
Proof.
  refine (nth_rew (B := fun x ε => (DR XA).(_paintings).2 ((DR XA).(_restrFrames).2 0 leR_O ε x))
    (rho'1.2 d) (rewLayer e DR d l) ε • _).
  refine (f_equal (fun c => rew [fun x => GDom ((DR XA).(_paintings).2 ((DR XA).(_restrFrames).2 0 leR_O ε x))]
    rho'1.2 d in c) (nthRewLayer e DR d l ε) • _).
  now exact (source_triangle_fill
    (fun x => GDom ((DR XA).(_paintings).2 x))
    ((DR XA).(_restrFrames).2 0 leR_O ε)
    (natRestr e DR 0 leR_O ε d) (rho'1.2 d) (sigma.2 0 leR_O ε d)
    (pi.2 ((DR XB).(_restrFrames).2 0 leR_O ε d) (nth l ε))
    (eq_sym (trLayerEqvNth pEqvs trRestrs d l ε))).
Defined.

Definition mkRhoLayer (d: (nextFr DR XB).1.2)
  (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d):
  rew [fun x => mkLayer (DR XA).(_restrFrames).2 (painting := (DR XA).(_paintings).2) x]
    rho'1.2 d in rewLayer e DR d l
  = mkTrLayerEquiv pEqvs trRestrs d l :=
  ext _ _ (rhoLayerNth d l).

End LayerStep.

(** The top stage of [ρ] for the next level's frames: on a pair frame it
    is the pair of [ρ] on the base with the layer step, which is what
    [RhoPairTypes] records. Both the stage recursion [rhoSigmaNext] and
    the level step build their top stage with it. *)
Definition rhoTop {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho'1: RhoTypes (p := p.+1) (k := k.+1) e (fun X => (nextFr DR X).1)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).1)
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'1)
  (d: (nextFr DR XB).2):
  rewFr e (nextFr DR) d
  = ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).2 d :=
  path_reindex_source (rewFrPair e DR d.1 d.2)
    (= rho'1.2 d.1;
       mkRhoLayer e DR eqvs pEqvs trRestrs rho pi rho'1 sigma d.1 d.2).

(** The next-level painting invariant

    Transport of a next-level painting along a reflexive prefix path is
    transport along the filler path; at the top, along the filler path
    univalence builds, it is the inverse of the filler equivalence. On a
    pair painting it decomposes into the transported layer and the
    transported painting over the transported pair frame. *)

Lemma rewPtNRefl {m: nat} {XA: (νGpdAt m).(prefix)}
  {EA EB: νFillerType XA} (h: EA = EB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (d: (nextFr DR XA).2) (c: (mkPaintings (XT XA EB)).2 d):
  rewPtN eq_refl h DR XT d c
  = rew <- [fun E => GDom ((mkPaintings (XT XA E)).2 d)] h in c.
Proof.
  destruct h. now reflexivity.
Defined.

Lemma rewPtNTop {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB} (eqvs: νFillerEqvType e EA EB)
  (d: νFrame XB) (c: EB d):
  rewPtN e (νFillerEq e eqvs) νTowerDeps (fun X E => TopRestrDep E) d c
  = invEq (eqvs d) c.
Proof.
  destruct e.
  unfold νFillerEq; cbn [rewνFillerType]; rewrite eq_trans_refl_l.
  rewrite rewPtNRefl.
  rewrite (rewνFillerFunext (fun d => hgpdEq (eqvs d)) d c).
  now apply hgpdEqRewSym.
Qed.

Lemma rewPtNPair {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (d: (nextFr DR XB).1.2)
  (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d)
  (c: (mkPaintings (XT XB EB)).2 ((d; l): (nextFr DR XB).2)):
  rewPtN e h (fun X => proj1DepsRestr (DR X)) (fun X E => (DR X; XT X E)%extradepsrestr)
    d ((l; c): (mkPaintings (DR XB; XT XB EB)%extradepsrestr).2 d)
  = ((rewLayer e DR d l;
      rew [fun z: (nextFr DR XA).2 => GDom ((mkPaintings (XT XA EA)).2 z)]
        rewFrPair e DR d l in rewPtN e h DR XT (d; l) c)
     : (mkPaintings (DR XA; XT XA EA)%extradepsrestr).2
         (rewFr e (nextFr (fun X => proj1DepsRestr (DR X))) d)).
Proof.
  destruct e. cbn in h. destruct h. now reflexivity.
Defined.

(** [ρ] for the next level's frames is built stage by stage: on a pair
    frame it is the pair of [ρ] on the base with the layer step. *)
Section RhoPair.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB).

Fixpoint RhoPairTypes {p k}:
  forall (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1), Type :=
  match p with
  | 0 => fun _ _ _ _ _ _ _ _ => unit
  | S p => fun DR eqvs pEqvs trRestrs rho pi rho' sigma =>
      { _: RhoPairTypes (fun X => proj1DepsRestr (DR X)) eqvs.1 pEqvs.1
             trRestrs.1 rho.1 pi.1 rho'.1 sigma.1 &T
        forall (d: (nextFr DR XB).1.2)
          (l: mkLayer (DR XB).(_restrFrames).2 (painting := (DR XB).(_paintings).2) d),
        rho'.2 ((d; l): (nextFr DR XB).2)
        = rhoTop e DR eqvs pEqvs trRestrs rho pi rho'.1 sigma (d; l) }
  end.

End RhoPair.

Section PiStep.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
  {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension {| _depsA := DR XA; _depsB := DR XB;
      _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
    (XT XA EA) (XT XB EB))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes e (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
  (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma).

(** The pair case: the component one stage down from the component above,
    at the pair frame. *)
Definition piStep
  (above: PiTop e h DR XT _ rho' (mkPaintingEqvs TX)):
  PiTop e h (fun X => proj1DepsRestr (DR X)) (fun X E => (DR X; XT X E)%extradepsrestr)
    _ rho'.1 (mkPaintingEqvs TX).1.
Proof.
  intros d [l c].
  rewrite (rewPtNPair e h DR XT d l c).
  unshelve eapply (eq_existT_curried_dep
    (Q := fun z: (nextFr DR XA).2 => GDom ((mkPaintings (XT XA EA)).2 z))).
  - now exact (mkRhoLayer e DR eqvs pEqvs trRestrs rho pi rho'.1 sigma d l).
  - now exact (path_reindex_source_unlift_along
      (fun z: (nextFr DR XA).2 => GDom ((mkPaintings (XT XA EA)).2 z))
      (rewFrPair e DR d l) _ _ (rhoPair.2 d l) _ _ (above (d; l) c)).
Defined.

End PiStep.

Section PiN.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB).

Fixpoint mkPiNPrefix {p k}:
  forall (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension {| _depsA := DR XA; _depsB := DR XB;
        _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
      (XT XA EA) (XT XB EB))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (above: PiTop e h DR XT _ rho' (mkPaintingEqvs TX)),
  PiTypesNPrefix e h DR XT _ rho' (mkPaintingEqvs TX) :=
  match p with
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ => tt
  | S p => fun DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair above =>
      (mkPiNPrefix (fun X => proj1DepsRestr (DR X))
         (fun X E => (DR X; XT X E)%extradepsrestr)
         eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rho.1 pi.1 rho'.1 sigma.1
         rhoPair.1
         (piStep e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair above);
       piStep e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair above)
  end.

Definition mkPiN {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension {| _depsA := DR XA; _depsB := DR XB;
      _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}
    (XT XA EA) (XT XB EB))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes e (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
  (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
  (above: PiTop e h DR XT _ rho' (mkPaintingEqvs TX)):
  PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX) :=
  (mkPiNPrefix DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair above; above).

End PiN.

(** The top component at a level of the tower: the univalence computation
    rule, [rewPtNTop], read through [ρ]. *)
Definition piTopCase {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  (eqvs: mkFrameEqvTypes (νTowerDeps XA).(_frames) (νTowerDeps XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (νTowerDeps XA).(_paintings)
    (νTowerDeps XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (νTowerDeps XA).(_restrFrames) (νTowerDeps XB).(_restrFrames))
  (rho': RhoTypes e (nextFr νTowerDeps)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  {EA: νFillerType XA} {EB: νFillerType XB}
  (fEqv: forall d: νFrame XB, Equiv (EB d)
    (EA (((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).2 d))):
  PiTop e (hOf e _ rho' fEqv) νTowerDeps (fun X E => TopRestrDep E) _ rho'
    (mkPaintingEqvs (TopTrDep (T := {| _depsA := νTowerDeps XA;
      _depsB := νTowerDeps XB; _frameEqvs := eqvs; _paintingEqvs := pEqvs;
      _trRestrs := trRestrs |}) fEqv)).
Proof.
  intros d c. unfold hOf.
  refine (f_equal (fun z => rew [fun x => GDom ((mkPaintings
      (TopRestrDep (deps := νTowerDeps XA) EA)).2 x)] rho'.2 d in z)
    (rewPtNTop e (eqvsOf e ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef)
      trRestrs) rho' fEqv) d c) • _).
  unfold eqvsOf. cbn [compEquiv symEquiv rewEquiv qinvEquiv invEq eqvIsEquiv linv].
  now exact (rew_sym_cancel_r (P := fun x: νFrame XA => GDom (EA x)) (rho'.2 d)
    (fEqv d c)).
Defined.

(** Lifting to the next level

    The next level's frames and its paintings are families of the
    truncated prefix and of the prefix, so [ρ] for the next level's frames
    and [πN] lift to the level above along the extended path. *)

Section Lift.
Context {m: nat} {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB).

Fixpoint rhoLift {p k}:
  forall (G: (νGpdAt m).(prefix) -> mkFrameTypes p k)
    (eqvs: mkFrameEqvTypes (G XA) (G XB)),
  RhoTypes e G eqvs
  -> RhoTypes (extendCong (T := νGpdTel) e h) (fun X' => G X'.1) eqvs :=
  match p with
  | 0 => fun _ _ _ => tt
  | S p => fun G eqvs rho =>
      (rhoLift (fun X => (G X).1) eqvs.1 rho.1;
       fun d => path_reindex_source (rewFrExt e h G d) (rho.2 d))
  end.

Lemma rewPtExt {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (d: (nextFr DR XB).2) (c: (mkPaintings (XT XB EB)).2 d):
  rewPt (extendCong (T := νGpdTel) e h) (fun X' => nextFr DR X'.1)
    (fun X' => mkPaintings (XT X'.1 X'.2)) d c
  = rew <- [fun x => GDom ((mkPaintings (XT XA EA)).2 x)]
      rewFrExt e h (nextFr DR) d in rewPtN e h DR XT d c.
Proof.
  destruct e. cbn in h. destruct h. now reflexivity.
Defined.

Definition piLiftTop {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (eqvs': mkFrameEqvTypes (nextFr DR XA) (nextFr DR XB))
  (rho': RhoTypes e (nextFr DR) eqvs')
  (pEqvs': mkPaintingEqvTypes eqvs' (mkPaintings (XT XA EA))
    (mkPaintings (XT XB EB)))
  (top: PiTop e h DR XT eqvs' rho' pEqvs')
  (d: (nextFr DR XB).2) (c: (mkPaintings (XT XB EB)).2 d):
  rew [fun x => GDom ((mkPaintings (XT XA EA)).2 x)]
    (path_reindex_source (rewFrExt e h (nextFr DR) d) (rho'.2 d)) in
    rewPt (extendCong (T := νGpdTel) e h) (fun X' => nextFr DR X'.1)
      (fun X' => mkPaintings (XT X'.1 X'.2)) d c
  = pEqvs'.2 d c :=
  path_reindex_source_dep (fun x => GDom ((mkPaintings (XT XA EA)).2 x))
    (rewFrExt e h (nextFr DR) d) (rho'.2 d)
    (rewPtN e h DR XT d c)
    (rewPt (extendCong (T := νGpdTel) e h) (fun X' => nextFr DR X'.1)
      (fun X' => mkPaintings (XT X'.1 X'.2)) d c)
    (pEqvs'.2 d c) (rewPtExt DR XT d c) (top d c).

Fixpoint piLiftPrefix {p k}:
  forall (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (eqvs': mkFrameEqvTypes (nextFr DR XA) (nextFr DR XB))
    (rho': RhoTypes e (nextFr DR) eqvs')
    (pEqvs': mkPaintingEqvTypes eqvs' (mkPaintings (XT XA EA))
      (mkPaintings (XT XB EB))),
  PiTypesNPrefix e h DR XT eqvs' rho' pEqvs'
  -> PiTypes (extendCong (T := νGpdTel) e h)
       (fun X' => (nextFr DR X'.1).1)
       (fun X' => (mkPaintings (XT X'.1 X'.2)).1) eqvs'.1
       (rhoLift (fun X => (nextFr DR X).1) eqvs'.1 rho'.1) pEqvs'.1 :=
  match p with
  | 0 => fun DR XT eqvs' rho' pEqvs' piN => tt
  | S p => fun DR XT eqvs' rho' pEqvs' piN =>
      (piLiftPrefix (fun X => proj1DepsRestr (DR X))
         (fun X E => (DR X; XT X E)%extradepsrestr) eqvs'.1 rho'.1 pEqvs'.1 piN.1;
       piLiftTop (fun X => proj1DepsRestr (DR X))
         (fun X E => (DR X; XT X E)%extradepsrestr) eqvs'.1 rho'.1 pEqvs'.1 piN.2)
  end.

Definition piLift {p k}
  (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (eqvs': mkFrameEqvTypes (nextFr DR XA) (nextFr DR XB))
  (rho': RhoTypes e (nextFr DR) eqvs')
  (pEqvs': mkPaintingEqvTypes eqvs' (mkPaintings (XT XA EA))
    (mkPaintings (XT XB EB)))
  (piN: PiTypesN e h DR XT eqvs' rho' pEqvs'):
  PiTypes (extendCong (T := νGpdTel) e h) (fun X' => nextFr DR X'.1)
    (fun X' => mkPaintings (XT X'.1 X'.2)) eqvs'
    (rhoLift (nextFr DR) eqvs' rho') pEqvs' :=
  (piLiftPrefix DR XT eqvs' rho' pEqvs' piN.1;
   piLiftTop DR XT eqvs' rho' pEqvs' piN.2).

End Lift.

(** The level step: the next-frames ρ and σ one level up *)

Section StepDefs.
Context {m: nat}.

Definition DCof {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (X: (νGpdAt m).(prefix)) (E: νFillerType X): DepsCohs p k := {|
  _deps := DR X; _extraDeps := XT X E; _restrPaintings := RP X E; _cohs := CF X E |}.

Definition DRof {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (X': (νGpdAt m.+1).(prefix)): DepsRestr p.+1 k :=
  mkDepsRestr (depsCohs := DCof DR XT RP CF X'.1 X'.2).

Context {XA XB: (νGpdAt m).(prefix)}.

Definition Tof {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames)): TrDepsRestr p k :=
  {| _depsA := DR XA; _depsB := DR XB;
     _frameEqvs := eqvs; _paintingEqvs := pEqvs; _trRestrs := trRestrs |}.

Context {EA: νFillerType XA} {EB: νFillerType XB}.

Definition baseOf {p k} (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA) (RP XB EB)):
  TrDepsCohsBase p k := {|
  _trDeps := Tof DR eqvs pEqvs trRestrs;
  _tExtA := XT XA EA; _tExtB := XT XB EB; _trExt := TX;
  _tRpA := RP XA EA; _tRpB := RP XB EB; _trRestrPaintings := rp;
  _tCohsA := CF XA EA; _tCohsB := CF XB EB |}.

End StepDefs.

(** The layer clause of the level step

    At a stage, the pair frame's layer component of [σ] one level up: the
    level-[m] transport of the restricted layer, followed by the translation tower's
    restriction commutation at the layer, is the restriction map applied
    to the level-[m+1] transport of the layer. The base 2-cell [κ] is
    arbitrary: any two parallel 2-cells of frames agree by [GUIP], and the
    clause is needed again, at the layer component of a pair painting, by
    the construction of [τ] one level up. *)



Definition sigmaComponentFamily {T: Type} {Bd: T -> arity -> HGpd}
  {d1 d2: T} {e1 e2: d1 = d2} {kappa: e1 = e2}
  {l: Layer (Bd d1)} {l': Layer (Bd d2)}
  (u: rew [fun d => Layer (Bd d)] e1 in l = l')
  (v: rew [fun d => Layer (Bd d)] e2 in l = l'): Type :=
  forall omega,
    rew [fun e => rew [fun d => Bd d omega] e in nth l omega = nth l' omega]
      kappa in nth_dpath u omega = nth_dpath v omega.

Section SigmaClause.
Context {m: nat} {XA: (νGpdAt m).(prefix)} {EA: νFillerType XA}.
Context {p k: nat}
  (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XA).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XA).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XA).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XA EA))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
    (RP XA EA))
  (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
  (rho: RhoTypes eq_refl (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes eq_refl (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes eq_refl (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes eq_refl DR eqvs pEqvs trRestrs rho rho'.1)
  (piN: PiTypesN eq_refl eq_refl DR XT _ rho' (mkPaintingEqvs TX))
  (tau: TauTypes eq_refl eq_refl DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho'
    sigma piN).

Let TC := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp.
Let Q := mkTrRestrFrames {| _trBase := TC; _trCohs := cohs |}.
Let DR1 := fun X => proj1DepsRestr (DR X).
Let XT1 := fun X (E: νFillerType X) => (DR X; XT X E)%extradepsrestr.
Let RP1 := fun X (E: νFillerType X) => (RP X E).1.
Let CF1 := fun X (E: νFillerType X) => (CF X E).1.
Let TC1 := baseOf DR1 XT1 RP1 CF1 eqvs.1 pEqvs.1 trRestrs.1
  (AddTrDep (Tof DR eqvs pEqvs trRestrs) TX) rp.1.
Let Q1 := mkTrRestrFrames {| _trBase := TC1; _trCohs := cohs.1 |}.
Let E2 := mkFrameEqvs (mkTrDepsRestr {| _trBase := TC1; _trCohs := cohs.1 |}).
Let XA' := νGpdTel.(extend) XA EA.

Context
  (prevRho: RhoTypes (p := p.+1) (k := k.+2)
    (extendCong (T := νGpdTel) eq_refl eq_refl)
    (fun X' => (nextFr (DRof DR1 XT1 RP1 CF1) X').1) E2.1)
  (prevSigma: SigmaTypes (p := p.+1) (k := k.+1)
    (extendCong (T := νGpdTel) eq_refl eq_refl)
    (DRof DR1 XT1 RP1 CF1) (mkFrameEqvs (Tof DR1 eqvs.1 pEqvs.1 trRestrs.1))
    (mkPaintingEqvs (AddTrDep (Tof DR eqvs pEqvs trRestrs) TX)) Q1
    (rhoLift eq_refl eq_refl (nextFr DR1) _ rho'.1) prevRho).

Definition sigmaLayerComponent (q: nat) (Hq: q <= k) (ε: arity)
  (d: (nextFr (DRof DR XT RP CF) XA').1.2)
  (κ: rho'.1.2 ((DRof DR1 XT1 RP1 CF1 XA').(_restrFrames).2 q.+1 (⇑ Hq) ε d.1)
      • Q1.2 q.+1 (⇑ Hq) ε d.1
      = f_equal ((DRof DR1 XT1 RP1 CF1 XA').(_restrFrames).2 q.+1 (⇑ Hq) ε)
          (prevRho.2 d.1)):
  sigmaComponentFamily (Bd := fun a omega => (DR XA).(_paintings).2 ((DR XA).(_restrFrames).2 0 leR_O omega a)) (kappa := κ)
    (mkRhoLayer eq_refl DR eqvs pEqvs trRestrs rho pi rho'.1 sigma
     ((mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1 (⇑ Hq) ε d.1)
     (mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq ε d.1 d.2)
   ⊙[fun a => GDom (mkLayer (DR XA).(_restrFrames).2
                      (painting := (DR XA).(_paintings).2) a)]
     mkTrRestrLayer TC Q.1 cohs.2 q Hq ε d)
    (sigT_map_eq
      (Q := fun a => GDom (mkLayer (DR XA).(_restrFrames).2
                             (painting := (DR XA).(_paintings).2) a))
      (f := (mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1
              (⇑ Hq) ε)
      (mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq ε)
      (mkRhoLayer (m := m.+1) (XA := XA') (XB := XA') eq_refl
         (fun X' => (DRof DR XT RP CF X').(1)%depsrestr)
         (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)).1 (mkPaintingEqvs TX).1 Q.1
         (rhoLift eq_refl eq_refl (fun X => (nextFr DR X).1.1)
            ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).1.1
            rho'.1.1;
          fun d0 => rho'.1.2 d0)
         (piLift eq_refl eq_refl DR XT _ rho' (mkPaintingEqvs TX) piN).1
         prevRho prevSigma d.1 d.2)).
Proof.
  unfold sigmaComponentFamily; intro ω.
  rewrite nth_dpath_trans.
  unfold mkRhoLayer, mkTrRestrLayer.
  rewrite nth_dpath_lmap2_chain.
  unfold mkRestrLayer at 1.
  rewrite (nth_dpath_map_chain (Bd := fun a ε0 => (DRof DR XT RP CF XA').(_paintings).1.2 ((DRof DR XT RP CF XA').(_restrFrames).1.2 0 leR_O ε0 a)) (Bd' := fun x ε0 => (DR XA).(_paintings).2 ((DR XA).(_restrFrames).2 0 leR_O ε0 x)) (f := fun a => (mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1 (⇑ Hq) ε a) (G := fun a ω0 c => rew [fun x => (DR XA).(_paintings).2 x] (CF XA EA).2 q Hq 0 leR_O ε ω0 a in (RP XA EA).2 q Hq ε ((mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 0 (leR_O ↕ ↑ Hq) ω0 a) c)).
  unfold nth_dpath.
  rewrite 2 ap_nth_ext.
  unfold rhoLayerNth.
  cbn [rewLayer natRestr rewPt nthRewLayer].
  rewrite 2 eq_trans_sym_cancel_l.
  cbn [f_equal].
  rewrite 2 eq_trans_refl_l.
  unshelve refine (sigmaLayerKernelSelected
    (P := fun x => (DR XA).(_paintings).2 x)
    (P' := fun x => (DRof DR XT RP CF XA').(_paintings).1.2 x)
    (fun a => (mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1 (⇑ Hq) ε a)
    (fun t => (DR XA).(_restrFrames).2 0 leR_O ω t)
    (fun a => (DRof DR XT RP CF XA').(_restrFrames).1.2 0 leR_O ω a)
    eqvs.2
    ((DR XA).(_restrFrames).2 q Hq ε)
    pEqvs.2
    ((RP XA EA).2 q Hq ε)
    (fun a => (CF XA EA).2 q Hq 0 leR_O ε ω a)
    rho.2 pi.2
    d.1 (E2.1.2 d.1) (prevRho.2 d.1)
    _ _ _ (nth d.2 ω) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ κ _).
  now exact (rho'.1.2 _).
  now exact eq_refl.
  now exact (piN.1.2 _ (nth d.2 ω)).
  now exact (sigma.2 q Hq ε _).
  now exact eq_refl.
  now exact (tau.2 q Hq ε _ (nth d.2 ω)).
  (** The selected scalar recipe fixes this final frame 3-cell before
      the dependent transfer consumes it. *)
  unfold SigmaFrameCoherence.
  now apply ((DR XA).(_frames).2.(GUIP)).
Defined.

Definition sigmaLayerClause (q: nat) (Hq: q <= k) (ε: arity)
  (d: (nextFr (DRof DR XT RP CF) XA').1.2)
  (κ: rho'.1.2 ((DRof DR1 XT1 RP1 CF1 XA').(_restrFrames).2 q.+1 (⇑ Hq) ε d.1)
      • Q1.2 q.+1 (⇑ Hq) ε d.1
      = f_equal ((DRof DR1 XT1 RP1 CF1 XA').(_restrFrames).2 q.+1 (⇑ Hq) ε)
          (prevRho.2 d.1)):
  rew [fun r: (mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1
                (⇑ Hq) ε d.1
              = (mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1
                  (⇑ Hq) ε (E2.1.2 d.1) =>
       rew [fun a => mkLayer (DR XA).(_restrFrames).2
                       (painting := (DR XA).(_paintings).2) a] r in
       mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq ε d.1 d.2
       = mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq ε (E2.1.2 d.1)
           (sigTEquivSnd
              (fun d0 => mkTrLayerEquiv (mkPaintingEqvs TX).1 Q.1 d0) d).2]
    κ in
  (mkRhoLayer eq_refl DR eqvs pEqvs trRestrs rho pi rho'.1 sigma
     ((mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1 (⇑ Hq) ε d.1)
     (mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq ε d.1 d.2)
   ⊙[fun a => GDom (mkLayer (DR XA).(_restrFrames).2
                      (painting := (DR XA).(_paintings).2) a)]
     mkTrRestrLayer TC Q.1 cohs.2 q Hq ε d)
  = sigT_map_eq
      (Q := fun a => GDom (mkLayer (DR XA).(_restrFrames).2
                             (painting := (DR XA).(_paintings).2) a))
      (f := (mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2 q.+1
              (⇑ Hq) ε)
      (mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq ε)
      (mkRhoLayer (m := m.+1) (XA := XA') (XB := XA') eq_refl
         (fun X' => (DRof DR XT RP CF X').(1)%depsrestr)
         (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)).1 (mkPaintingEqvs TX).1 Q.1
         (rhoLift eq_refl eq_refl (fun X => (nextFr DR X).1.1)
            ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs).1.1
            rho'.1.1;
          fun d0 => rho'.1.2 d0)
         (piLift eq_refl eq_refl DR XT _ rho' (mkPaintingEqvs TX) piN).1
         prevRho prevSigma d.1 d.2).
Proof.
  now exact (layer_dpath2_eq _ _ (sigmaLayerComponent q Hq ε d κ)).
Defined.

End SigmaClause.

Section SigmaPairCell.
Context {m: nat} {XA: (νGpdAt m).(prefix)} {EA: νFillerType XA}.
Context {p k: nat}
  (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XA).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XA).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XA).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XA EA))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
    (RP XA EA))
  (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
  (rho: RhoTypes eq_refl (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes eq_refl (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes eq_refl (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes eq_refl DR eqvs pEqvs trRestrs rho rho'.1)
  (piN: PiTypesN eq_refl eq_refl DR XT _ rho' (mkPaintingEqvs TX))
  (tau: TauTypes eq_refl eq_refl DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho'
    sigma piN).

Let TC := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp.
Let Q := mkTrRestrFrames {| _trBase := TC; _trCohs := cohs |}.
Let DR1 := fun X => proj1DepsRestr (DR X).
Let XT1 := fun X (E: νFillerType X) => (DR X; XT X E)%extradepsrestr.
Let RP1 := fun X (E: νFillerType X) => (RP X E).1.
Let CF1 := fun X (E: νFillerType X) => (CF X E).1.
Let TC1 := baseOf DR1 XT1 RP1 CF1 eqvs.1 pEqvs.1 trRestrs.1
  (AddTrDep (Tof DR eqvs pEqvs trRestrs) TX) rp.1.
Let Q1 := mkTrRestrFrames {| _trBase := TC1; _trCohs := cohs.1 |}.
Let E2 := mkFrameEqvs (mkTrDepsRestr {| _trBase := TC1; _trCohs := cohs.1 |}).
Let XA' := νGpdTel.(extend) XA EA.

Context
  (prevRho: RhoTypes (p := p.+1) (k := k.+2)
    (extendCong (T := νGpdTel) eq_refl eq_refl)
    (fun X' => (nextFr (DRof DR1 XT1 RP1 CF1) X').1) E2.1)
  (prevSigma: SigmaTypes (p := p.+1) (k := k.+1)
    (extendCong (T := νGpdTel) eq_refl eq_refl)
    (DRof DR1 XT1 RP1 CF1) (mkFrameEqvs (Tof DR1 eqvs.1 pEqvs.1 trRestrs.1))
    (mkPaintingEqvs (AddTrDep (Tof DR eqvs pEqvs trRestrs) TX)) Q1
    (rhoLift eq_refl eq_refl (nextFr DR1) _ rho'.1) prevRho).


Context
  (rhoPair: RhoPairTypes eq_refl DR eqvs pEqvs trRestrs rho pi rho' sigma)
  (nextTop: forall d: (nextFr (DRof DR XT RP CF) XA').1.2,
    d = E2.2 d)
  (nextTopPair: forall d,
    nextTop d = rhoTop (m := m.+1) (XA := XA') (XB := XA')
      (p := p) (k := k.+1) eq_refl
      (fun X' => proj1DepsRestr (DRof DR XT RP CF X'))
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)).1 (mkPaintingEqvs TX).1 Q.1
      (rhoLift eq_refl eq_refl (nextFr DR) _ rho').1
      (piLift eq_refl eq_refl DR XT _ rho' (mkPaintingEqvs TX) piN).1
      prevRho prevSigma d).

Definition sigmaPairCell q (Hq: q <= k) (epsilon: arity)
  (d: (nextFr (DRof DR XT RP CF) XA').1.2):
  rho'.2 ((DRof DR XT RP CF XA').(_restrFrames).2 q Hq epsilon d)
    • Q.2 q Hq epsilon d =
  f_equal ((DRof DR XT RP CF XA').(_restrFrames).2 q Hq epsilon)
    (nextTop d).
Proof.
  change (Q.2 q Hq epsilon d) with
    (mkTrRestrFrameStep TC Q.1 cohs.2 q Hq epsilon d).
  unfold mkTrRestrFrameStep.
  unshelve refine (sigT_triangle_reindex _ _
    (rhoPair.2
      ((mkRestrFrames (depsCohs := DCof DR XT RP CF XA EA)).1.2
        q.+1 (⇑ Hq) epsilon d.1)
      (mkRestrLayer (RP XA EA).2 (CF XA EA).2 q Hq epsilon d.1 d.2))
    (nextTopPair d) (prevSigma.2 q.+1 (⇑ Hq) epsilon d.1) _).
  now exact (sigmaLayerClause DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
    rho pi rho' sigma piN tau prevRho prevSigma q Hq epsilon d _).
Defined.

End SigmaPairCell.


Section Step.
Context {m: nat}.

Fixpoint rhoSigmaNext {p k}:
  forall {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
    {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
    (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA) (RP XB EB))
    (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (piN: PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX))
    (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma piN),
  { rho'': RhoTypes (p := p.+1) (k := k.+1) (extendCong (T := νGpdTel) e h)
      (fun X' => (nextFr (DRof DR XT RP CF) X').1)
      (mkFrameEqvs (mkTrDepsRestr {| _trBase := baseOf DR XT RP CF eqvs pEqvs
        trRestrs TX rp; _trCohs := cohs |})).1 &T
    SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
      (mkTrRestrFrames {| _trBase := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp;
        _trCohs := cohs |})
      (rhoLift e h (nextFr DR) _ rho') rho'' }.
Proof.
  destruct p.
  2: {
    intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair piN tau.
    destruct e, h.
    pose (prev := rhoSigmaNext p k.+1 _ _ eq_refl _ _ eq_refl (fun X => proj1DepsRestr (DR X))
        (fun X E => (DR X; XT X E)%extradepsrestr) (fun X E => (RP X E).1) (fun X E => (CF X E).1)
        eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rp.1 cohs.1 rho.1 pi.1 rho'.1 sigma.1 rhoPair.1
        piN.1 tau.1).
    unshelve esplit.
    -
    unshelve esplit.
    +
    now exact prev.1.
    +
    now exact (rhoTop (extendCong (T := νGpdTel) eq_refl eq_refl)
            (fun X' => proj1DepsRestr (DRof DR XT RP CF X'))
            (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)).1 (mkPaintingEqvs TX).1
            (mkTrRestrFrames {| _trBase := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp;
              _trCohs := cohs |}).1
            (rhoLift eq_refl eq_refl (nextFr DR) _ rho').1
            (piLift eq_refl eq_refl DR XT _ rho' (mkPaintingEqvs TX) piN).1
            prev.1 prev.2).
    -
    unshelve esplit.
    +
    now exact prev.2.
    +
    intros q Hq ε d.
    now exact (sigmaPairCell DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
      rho pi rho' sigma piN tau prev.1 prev.2 rhoPair _
      (fun _ => eq_refl) q Hq ε d).
  }
  intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair piN tau.
  destruct e, h.
  unshelve esplit.
  unshelve esplit.
  now exact tt.
  intro d.
  now reflexivity.
  unshelve esplit.
  now exact tt.
  intros q Hq ε d.
  now apply unit_UIP.
Defined.

End Step.

Section StepPair.
Context {m: nat}.

Fixpoint rhoPairNext {p k}:
  forall {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
    {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
    (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA) (RP XB EB))
    (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (piN: PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX))
    (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma piN),
  RhoPairTypes (extendCong (T := νGpdTel) e h)
    (fun X' => proj1DepsRestr (DRof DR XT RP CF X'))
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)).1 (mkPaintingEqvs TX).1
    (mkTrRestrFrames {| _trBase := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp;
      _trCohs := cohs |}).1
    (rhoLift e h (nextFr DR) _ rho').1
    (piLift e h DR XT _ rho' (mkPaintingEqvs TX) piN).1
    (rhoSigmaNext e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho'
      sigma rhoPair piN tau).1
    (rhoSigmaNext e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho'
      sigma rhoPair piN tau).2.1.
Proof.
  destruct p.
  - now intros; now exact tt.
  - intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi
      rho' sigma rhoPair piN tau.
    destruct e, h.
    unshelve esplit.
    + now exact (rhoPairNext p k.+1 _ _ eq_refl _ _ eq_refl
        (fun X => proj1DepsRestr (DR X))
        (fun X E => (DR X; XT X E)%extradepsrestr) (fun X E => (RP X E).1)
        (fun X E => (CF X E).1) eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rp.1
        cohs.1 rho.1 pi.1 rho'.1 sigma.1 rhoPair.1 piN.1 tau.1).
    + now intros d l; now reflexivity.
Defined.

End StepPair.


Section SigmaPair.
Context {m: nat}.

(** The chosen restriction comparison at each stage is the total
    triangle selected from its previous-stage cell and layer witness. *)
Fixpoint SigmaPairTypes {p k}:
  forall {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
    {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
    (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA) (RP XB EB))
    (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (piN: PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX))
    (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma piN),
  forall (nextRho: RhoTypes (p := p.+1) (k := k.+1) (extendCong (T := νGpdTel) e h)
      (fun X' => (nextFr (DRof DR XT RP CF) X').1)
      (mkFrameEqvs (mkTrDepsRestr {| _trBase := baseOf DR XT RP CF eqvs pEqvs
        trRestrs TX rp; _trCohs := cohs |})).1)
    (nextSigma: SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
      (mkTrRestrFrames {| _trBase := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp;
        _trCohs := cohs |})
      (rhoLift e h (nextFr DR) _ rho') nextRho)
    (nextPair: RhoPairTypes (extendCong (T := νGpdTel) e h)
    (fun X' => proj1DepsRestr (DRof DR XT RP CF X'))
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)).1 (mkPaintingEqvs TX).1
    (mkTrRestrFrames {| _trBase := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp;
      _trCohs := cohs |}).1
    (rhoLift e h (nextFr DR) _ rho').1
    (piLift e h DR XT _ rho' (mkPaintingEqvs TX) piN).1
    nextRho
    nextSigma.1), Type.
Proof.
  destruct p.
  - now intros; now exact unit.
  - intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
      rho pi rho' sigma rhoPair piN tau nextRho nextSigma nextPair.
    destruct e, h.
    now exact { _: SigmaPairTypes p k.+1 _ _ eq_refl _ _ eq_refl
      (fun X => proj1DepsRestr (DR X))
      (fun X E => (DR X; XT X E)%extradepsrestr)
      (fun X E => (RP X E).1) (fun X E => (CF X E).1)
      eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rp.1 cohs.1
      rho.1 pi.1 rho'.1 sigma.1 rhoPair.1 piN.1 tau.1
      nextRho.1 nextSigma.1 nextPair.1 &T
      forall q (Hq: q <= k) (epsilon: arity)
        (d: (nextFr (DRof DR XT RP CF) (νGpdTel.(extend) XA EA)).1.2),
      nextSigma.2 q Hq epsilon d =
        sigmaPairCell DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
          rho pi rho' sigma piN tau nextRho.1 nextSigma.1 rhoPair
          nextRho.2 (fun d => nextPair.2 d.1 d.2) q Hq epsilon d }.
Defined.

Fixpoint sigmaPairNext {p k}:
  forall {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
    {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
    (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA) (RP XB EB))
    (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (piN: PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX))
    (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma piN),
  SigmaPairTypes e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair piN tau
    (rhoSigmaNext e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair piN tau).1
    (rhoSigmaNext e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair piN tau).2
    (rhoPairNext e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair piN tau).
Proof.
  destruct p.
  - now intros; now exact tt.
  - intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
      rho pi rho' sigma rhoPair piN tau.
    destruct e, h.
    unshelve esplit.
    + now exact (sigmaPairNext p k.+1 _ _ eq_refl _ _ eq_refl
      (fun X => proj1DepsRestr (DR X))
      (fun X E => (DR X; XT X E)%extradepsrestr)
      (fun X E => (RP X E).1) (fun X E => (CF X E).1)
      eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rp.1 cohs.1
      rho.1 pi.1 rho'.1 sigma.1 rhoPair.1 piN.1 tau.1).
    + now intros q Hq epsilon d; now reflexivity.
Defined.

End SigmaPair.


Section StepData.
Context {m: nat} {p k: nat}.
Context {XA XB: (νGpdAt m).(prefix)} (e: XA = XB).
Context {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB).
Context (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
    (RP XB EB))
  (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes e (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
  (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
  (piN: PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX))
  (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma piN).
Definition trCohsOf: TrDepsCohs p k :=
  {| _trBase := baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp; _trCohs := cohs |}.
Definition rhoOne := rhoLift e h (nextFr DR) _ rho'.
Definition piOne := piLift e h DR XT _ rho' (mkPaintingEqvs TX) piN.

End StepData.

Section TauLevel.
Context {m: nat} {p k: nat}.
Context {XA XB: (νGpdAt m).(prefix)} (e: XA = XB).
Context {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB).
Context (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
    (RP XB EB))
  (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes e (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
  (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
  (aboveM: PiTop e h DR XT _ rho' (mkPaintingEqvs TX)).
Definition piMid: PiTypesN e h DR XT _ rho' (mkPaintingEqvs TX) :=
  mkPiN e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM.
Context (XC: forall (X': (νGpdAt m.+1).(prefix)) (E': νFillerType X'),
  DepsCohsExtension p k (DCof DR XT RP CF X'.1 X'.2)).
Context {EA'': νFillerType ((XA; EA): (νGpdAt m.+1).(prefix))}
  {EB'': νFillerType ((XB; EB): (νGpdAt m.+1).(prefix))}
  (TCX: TrDepsCohsExtension
    (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs)
    (XC _ EA'') (XC _ EB''))
  (h': rew [νFillerType] (extendCong (T := νGpdTel) e h) in EA'' = EB'')
  (rho'': RhoTypes (extendCong (T := νGpdTel) e h)
    (nextFr (DRof DR XT RP CF))
    (mkFrameEqvs (mkTrDepsRestr
      (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))))
  (sigma': SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (rhoOne e h DR eqvs pEqvs trRestrs rho') rho''.1)
  (rhoPair'': RhoPairTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho' piMid) rho'' sigma')
  (above': PiTop (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E')) _ rho''
    (mkPaintingEqvs (mkTrExtraDeps TCX))).
Definition piNextOf: PiTypesN (extendCong (T := νGpdTel) e h) h'
    (DRof DR XT RP CF) (fun X' E' => mkExtraDeps (XC X' E')) _ rho''
    (mkPaintingEqvs (mkTrExtraDeps TCX)) :=
  mkPiN (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E'))
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (mkTrExtraDeps TCX) (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho' piMid) rho'' sigma'
    rhoPair'' above'.
Definition TauClauseHereAt (q: nat) (Hq: q <= k): Type :=
  TauClauseAt (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E'))
    (fun X' E' => mkRestrPaintings (XC X' E'))
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (mkTrExtraDeps TCX) (mkTrRestrPaintings TCX)
    (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho' piMid) rho'' sigma'
    piNextOf q Hq.
Definition TauClauseHere: Type :=
  TauClause (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E'))
    (fun X' E' => mkRestrPaintings (XC X' E'))
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (mkTrExtraDeps TCX) (mkTrRestrPaintings TCX)
    (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho' piMid) rho'' sigma'
    piNextOf.
End TauLevel.
Lemma tauBase {m: nat} {p k: nat}
  {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB)
  (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
    (RP XB EB))
  (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes e (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
  (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
  (aboveM: PiTop e h DR XT _ rho' (mkPaintingEqvs TX))
  (XC: forall (X': (νGpdAt m.+1).(prefix)) (E': νFillerType X'),
  DepsCohsExtension p k (DCof DR XT RP CF X'.1 X'.2))
  {EA'': νFillerType ((XA; EA): (νGpdAt m.+1).(prefix))}
  {EB'': νFillerType ((XB; EB): (νGpdAt m.+1).(prefix))}
  (TCX: TrDepsCohsExtension
    (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs)
    (XC _ EA'') (XC _ EB''))
  (h': rew [νFillerType] (extendCong (T := νGpdTel) e h) in EA'' = EB'')
  (rho'': RhoTypes (extendCong (T := νGpdTel) e h)
    (nextFr (DRof DR XT RP CF))
    (mkFrameEqvs (mkTrDepsRestr
      (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))))
  (sigma': SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (rhoOne e h DR eqvs pEqvs trRestrs rho') rho''.1)
  (rhoPair'': RhoPairTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho' (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi
       rho' sigma rhoPair aboveM)) rho'' sigma')
  (above': PiTop (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E')) _ rho''
    (mkPaintingEqvs (mkTrExtraDeps TCX)))
  (Hq: 0 <= k):
  TauClauseHereAt e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma rhoPair aboveM XC TCX h' rho'' sigma' rhoPair'' above' 0 Hq.
Proof.
  destruct e, h.
  cbn in h'.
  destruct h'.
  unfold TauClauseHereAt, TauClauseAt.
  intros ε d c.
  cbn [path_reindex_source_comp path_reindex_source extendCong natRestrPt rewPt rewFr f_equal] in *.
  unfold piNextOf, mkPiN.
  cbn [mkPiNPrefix projT1 projT2].
  cbn [mkTrRestrPaintings mkTrRestrPainting projT1 projT2].
  cbn [mkRestrPaintings mkRestrPainting projT1 projT2].
  destruct c as [l cc].
  unfold piStep.
  cbn [path_reindex_source_unlift_along path_reindex_source_unlift rhoTop path_reindex_source rewPtNPair eq_rect_r eq_rect eq_sym f_equal eq_ind_r eq_ind extendCong] in *.
  rewrite nth_dpath_sigT_fst.
  unfold nth_dpath, mkRhoLayer.
  rewrite ap_nth_ext.
  unfold rhoLayerNth.
  cbn [rewLayer natRestr rewPt nthRewLayer f_equal].
  rewrite eq_trans_refl_l.
  rewrite eq_trans_sym_cancel_l.
  cbn [f_equal].
  lazymatch goal with
  | |- context [source_triangle_fill ?P ?f ?c ?r ?K ?hp ?hq] =>
      now exact (source_triangle_fill_boundary_conv P f c r K hp hq)
  end.
Defined.

(** [τ'] at offset [q+1], from the clause of the stage above. Offset [0]
    is [tauBase]; at [q+1] both sides are [eq_existT_curried_dep] terms of
    a layer and a painting component. [SigmaPairTypes] identifies the
    chosen first-rung triangle, so its dependent lift consumes the clause
    of the stage above directly. The layer witness is the one selected
    by [sigmaPairCell]. *)

Lemma tauStep {m: nat} {p k: nat}
  {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB)
  (DR: (νGpdAt m).(prefix) -> DepsRestr p.+1 k)
  (XT: forall X (E: νFillerType X), DepsRestrExtension p.+1 k (DR X))
  (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
  (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
  (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
  (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
  (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
    (DR XA).(_restrFrames) (DR XB).(_restrFrames))
  (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
  (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
    (RP XB EB))
  (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
  (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
  (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
    eqvs rho pEqvs)
  (rho': RhoTypes e (nextFr DR)
    ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
  (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
  (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
  (aboveM: PiTop e h DR XT _ rho' (mkPaintingEqvs TX))
  (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma
    (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM))
  (XC: forall (X': (νGpdAt m.+1).(prefix)) (E': νFillerType X'),
  DepsCohsExtension p.+1 k (DCof DR XT RP CF X'.1 X'.2))
  {EA'': νFillerType ((XA; EA): (νGpdAt m.+1).(prefix))}
  {EB'': νFillerType ((XB; EB): (νGpdAt m.+1).(prefix))}
  (TCX: TrDepsCohsExtension
    (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs)
    (XC _ EA'') (XC _ EB''))
  (h': rew [νFillerType] (extendCong (T := νGpdTel) e h) in EA'' = EB'')
  (rho'': RhoTypes (extendCong (T := νGpdTel) e h)
    (nextFr (DRof DR XT RP CF))
    (mkFrameEqvs (mkTrDepsRestr
      (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))))
  (sigma': SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (rhoOne e h DR eqvs pEqvs trRestrs rho') rho''.1)
  (rhoPair'': RhoPairTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho' (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi
       rho' sigma rhoPair aboveM)) rho'' sigma')
  (above': PiTop (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E')) _ rho''
    (mkPaintingEqvs (mkTrExtraDeps TCX)))
  (above: TauClauseHere e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi
    rho' sigma rhoPair aboveM XC TCX h' rho'' sigma' rhoPair'' above')
  (sigmaPair': SigmaPairTypes e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
    rho pi rho' sigma rhoPair
    (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM)
    tau rho''.1 sigma' rhoPair''.1):
  TauClauseHere e h (fun X => proj1DepsRestr (DR X))
    (fun X E => (DR X; XT X E)%extradepsrestr) (fun X E => (RP X E).1)
    (fun X E => (CF X E).1) eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rp.1
    cohs.1 rho.1 pi.1 rho'.1 sigma.1 rhoPair.1
    (piStep e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM)
    (fun X' E' => AddCohDep _ (XC X' E'))
    (AddTrCohDep (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs) TCX) h'
    rho''.1 sigma'.1 rhoPair''.1
    (piStep (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
       (fun X' E' => mkExtraDeps (XC X' E'))
       (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
       (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
       (mkTrExtraDeps TCX) (rhoOne e h DR eqvs pEqvs trRestrs rho')
       (piOne e h DR XT eqvs pEqvs trRestrs TX rho'
          (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair
             aboveM)) rho'' sigma' rhoPair'' above').
Proof.
  unfold TauClauseHere, TauClause.
  intros q Hq.
  destruct q.
  {
    now exact (tauBase e h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h' _ _ _ _ Hq).
  }
  destruct e, h.
  cbn in h'.
  destruct h'.
  unfold TauClauseAt.
  intros ε d c.
  cbn [path_reindex_source_comp path_reindex_source extendCong natRestrPt rewPt rewFr f_equal] in *.
  destruct c as [l cc].
  cbn [mkTrRestrPaintings mkTrRestrPainting projT1 projT2].
  cbn [mkRestrPaintings mkRestrPainting projT1 projT2].
  unfold piOne.
  cbn [piLift piLiftTop path_reindex_source path_reindex_source_dep rewFrExt rewPtExt].
  unfold piNextOf, mkPiN.
  cbn [mkPiNPrefix projT1 projT2].
  unfold piMid, mkPiN.
  cbn [mkPiNPrefix projT1 projT2].
  unfold piStep.
  cbn [path_reindex_source_unlift_along path_reindex_source_unlift rhoTop path_reindex_source rewPtNPair eq_ind_r eq_ind eq_rect eq_sym f_equal extendCong] in *.
  pose proof (above q (⇓ Hq) ε (d; l) cc) as HAB.
  cbn [path_reindex_source_comp path_reindex_source extendCong natRestrPt rewPt rewFr f_equal] in HAB.
  unfold piOne in HAB.
  cbn [piLift piLiftTop path_reindex_source path_reindex_source_dep rewFrExt rewPtExt] in HAB.
  unfold piNextOf, mkPiN in HAB.
  cbn [mkPiNPrefix projT1 projT2] in HAB.
  unfold piMid, mkPiN in HAB.
  cbn [mkPiNPrefix projT1 projT2] in HAB.
  unfold piStep in HAB.
  cbn [path_reindex_source_unlift_along path_reindex_source_unlift rhoTop path_reindex_source rewPtNPair eq_ind_r eq_ind eq_rect eq_sym f_equal extendCong] in HAB.
  rewrite (sigmaPair'.2 q (⇓ Hq) ε (d; l)) in HAB.
  unfold sigmaPairCell in HAB.
  cbn [path_reindex_source_comp natRestr] in HAB.
  lazymatch type of HAB with
  | _ = ?rhs =>
    lazymatch rhs with
    | context [sigT_map_eq ?G _] => pose (gPm := G)
    end
  end.
  lazymatch type of HAB with
  | context [sigT_triangle_reindex ?f ?g ?D1 ?D3 ?K ?H] =>
      now exact (sigT_triangle_reindex_dep f g gPm D1 D3 K H _ _ _ HAB)
  end.

Defined.

(** At the top stage of a tower the offset is bounded by [0], so the whole
    clause there is [tauBase]. *)

Lemma tauTop {m: nat} {p: nat}
  {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
    {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
    (DR: (νGpdAt m).(prefix) -> DepsRestr p 0)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p 0 (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
      (RP XB EB))
    (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (aboveM: PiTop e h DR XT _ rho' (mkPaintingEqvs TX))
    (XC: forall (X': (νGpdAt m.+1).(prefix)) (E': νFillerType X'),
      DepsCohsExtension p 0 (DCof DR XT RP CF X'.1 X'.2))
    {EA'': νFillerType ((XA; EA): (νGpdAt m.+1).(prefix))}
    {EB'': νFillerType ((XB; EB): (νGpdAt m.+1).(prefix))}
    (TCX: TrDepsCohsExtension
      (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs)
      (XC _ EA'') (XC _ EB''))
    (h': rew [νFillerType] (extendCong (T := νGpdTel) e h) in EA'' = EB'')
    (rho'': RhoTypes (extendCong (T := νGpdTel) e h)
      (nextFr (DRof DR XT RP CF))
      (mkFrameEqvs (mkTrDepsRestr
        (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))))
    (sigma': SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
      (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
      (rhoOne e h DR eqvs pEqvs trRestrs rho') rho''.1)
    (rhoPair'': RhoPairTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
      (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
      (rhoOne e h DR eqvs pEqvs trRestrs rho')
      (piOne e h DR XT eqvs pEqvs trRestrs TX rho'
        (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair
          aboveM)) rho'' sigma')
    (above': PiTop (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
      (fun X' E' => mkExtraDeps (XC X' E')) _ rho''
      (mkPaintingEqvs (mkTrExtraDeps TCX))):
  TauClauseHere e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho'
    sigma rhoPair aboveM XC TCX h' rho'' sigma' rhoPair'' above'.
Proof.
  unfold TauClauseHere, TauClause.
  intros q Hq.
  destruct q.
  - now exact (tauBase e h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h' _ _ _ _ Hq).
  - now destruct (leR_O_contra Hq).
Defined.

(** The stage recursion of [τ']: the clause of the top stage is given, and
    [tauStep] threads it down the stages. *)

Section TauNext.
Context {m: nat}.

Fixpoint tauNext {p k}:
  forall {XA XB: (νGpdAt m).(prefix)} (e: XA = XB)
    {EA: νFillerType XA} {EB: νFillerType XB} (h: rew [νFillerType] e in EA = EB)
    (DR: (νGpdAt m).(prefix) -> DepsRestr p k)
    (XT: forall X (E: νFillerType X), DepsRestrExtension p k (DR X))
    (RP: forall X (E: νFillerType X), mkRestrPaintingTypes (XT X E))
    (CF: forall X (E: νFillerType X), mkCohFrameTypes (RP X E))
    (eqvs: mkFrameEqvTypes (DR XA).(_frames) (DR XB).(_frames))
    (pEqvs: mkPaintingEqvTypes eqvs (DR XA).(_paintings) (DR XB).(_paintings))
    (trRestrs: (mkTrRestrTypesAndFrames eqvs pEqvs).(TrRestrTypesDef)
      (DR XA).(_restrFrames) (DR XB).(_restrFrames))
    (TX: TrDepsExtension (Tof DR eqvs pEqvs trRestrs) (XT XA EA) (XT XB EB))
    (rp: mkTrRestrPaintingTypes (Tof DR eqvs pEqvs trRestrs) TX (RP XA EA)
      (RP XB EB))
    (cohs: mkTrCohTypes (baseOf DR XT RP CF eqvs pEqvs trRestrs TX rp))
    (rho: RhoTypes e (fun X => (DR X).(_frames)) eqvs)
    (pi: PiTypes e (fun X => (DR X).(_frames)) (fun X => (DR X).(_paintings))
      eqvs rho pEqvs)
    (rho': RhoTypes e (nextFr DR)
      ((mkTrRestrTypesAndFrames eqvs pEqvs).(FrameEqvDef) trRestrs))
    (sigma: SigmaTypes e DR eqvs pEqvs trRestrs rho rho'.1)
    (rhoPair: RhoPairTypes e DR eqvs pEqvs trRestrs rho pi rho' sigma)
    (aboveM: PiTop e h DR XT _ rho' (mkPaintingEqvs TX))
    (tau: TauTypes e h DR XT RP eqvs pEqvs trRestrs TX rp rho pi rho' sigma
      (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM))
    (XC: forall (X': (νGpdAt m.+1).(prefix)) (E': νFillerType X'),
      DepsCohsExtension p k (DCof DR XT RP CF X'.1 X'.2))
    {EA'': νFillerType ((XA; EA): (νGpdAt m.+1).(prefix))}
    {EB'': νFillerType ((XB; EB): (νGpdAt m.+1).(prefix))}
    (TCX: TrDepsCohsExtension
      (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs)
      (XC _ EA'') (XC _ EB''))
    (h': rew [νFillerType] (extendCong (T := νGpdTel) e h) in EA'' = EB'')
    (rho'': RhoTypes (extendCong (T := νGpdTel) e h)
      (nextFr (DRof DR XT RP CF))
      (mkFrameEqvs (mkTrDepsRestr
        (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))))
    (sigma': SigmaTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
      (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
      (rhoOne e h DR eqvs pEqvs trRestrs rho') rho''.1)
    (rhoPair'': RhoPairTypes (extendCong (T := νGpdTel) e h) (DRof DR XT RP CF)
      (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
      (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
      (rhoOne e h DR eqvs pEqvs trRestrs rho')
      (piOne e h DR XT eqvs pEqvs trRestrs TX rho'
        (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair
          aboveM)) rho'' sigma')
    (above': PiTop (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
      (fun X' E' => mkExtraDeps (XC X' E')) _ rho''
      (mkPaintingEqvs (mkTrExtraDeps TCX)))
    (aboveC: TauClauseHere e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho
      pi rho' sigma rhoPair aboveM XC TCX h' rho'' sigma' rhoPair'' above')
  (sigmaPair': SigmaPairTypes e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs
    rho pi rho' sigma rhoPair
    (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM)
    tau rho''.1 sigma' rhoPair''.1),
  TauTypes (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
    (fun X' E' => mkExtraDeps (XC X' E'))
    (fun X' E' => mkRestrPaintings (XC X' E'))
    (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
    (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
    (mkTrExtraDeps TCX) (mkTrRestrPaintings TCX)
    (rhoOne e h DR eqvs pEqvs trRestrs rho')
    (piOne e h DR XT eqvs pEqvs trRestrs TX rho'
      (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair aboveM))
    rho'' sigma'
    (piNextOf e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho' sigma
      rhoPair aboveM XC TCX h' rho'' sigma' rhoPair'' above').
Proof.
  destruct p.
  - intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi
      rho' sigma rhoPair aboveM tau XC EA'' EB'' TCX h' rho'' sigma' rhoPair''
      above' aboveC sigmaPair'.
    now exact (tt; aboveC).
  - intros XA XB e EA EB h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi
      rho' sigma rhoPair aboveM tau XC EA'' EB'' TCX h' rho'' sigma' rhoPair''
      above' aboveC sigmaPair'.
    unshelve esplit.
    + unshelve refine (tauNext p k.+1 XA XB e EA EB h
        (fun X => proj1DepsRestr (DR X))
        (fun X E => (DR X; XT X E)%extradepsrestr) (fun X E => (RP X E).1)
        (fun X E => (CF X E).1) eqvs.1 pEqvs.1 trRestrs.1 (AddTrDep _ TX) rp.1
        cohs.1 rho.1 pi.1 rho'.1 sigma.1 rhoPair.1
        (piStep e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair
          aboveM) tau.1 (fun X' E' => AddCohDep _ (XC X' E')) EA'' EB''
        (AddTrCohDep (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs) TCX)
        h' rho''.1 sigma'.1 rhoPair''.1
        (piStep (extendCong (T := νGpdTel) e h) h' (DRof DR XT RP CF)
          (fun X' E' => mkExtraDeps (XC X' E'))
          (mkFrameEqvs (Tof DR eqvs pEqvs trRestrs)) (mkPaintingEqvs TX)
          (mkTrRestrFrames (trCohsOf DR XT RP CF eqvs pEqvs trRestrs TX rp cohs))
          (mkTrExtraDeps TCX) (rhoOne e h DR eqvs pEqvs trRestrs rho')
          (piOne e h DR XT eqvs pEqvs trRestrs TX rho'
            (piMid e h DR XT eqvs pEqvs trRestrs TX rho pi rho' sigma rhoPair
              aboveM)) rho'' sigma' rhoPair'' above')
        (tauStep e h DR XT RP CF eqvs pEqvs trRestrs TX rp cohs rho pi rho'
          sigma rhoPair aboveM tau XC TCX h' rho'' sigma' rhoPair'' above'
          aboveC sigmaPair') _).
      destruct e, h.
      now exact sigmaPair'.1.
    + now exact aboveC.
Defined.

End TauNext.

(** The invariant at a level of a tower of translation data, and the
    conversion

    The state carried up the levels: the prefix path and the four
    invariant families for the translation tower's data at the level, with [τ] for
    every filler equivalence the level may be extended by. *)

Record Inv {m: nat} {XA XB: (νGpdAt m).(prefix)} (W: TrTower m XA XB) := {
  invEq: XA = XB;
  invRho: RhoTypes invEq (fun X => (νTowerDeps X).(_frames)) W.(_twFrameEqvs);
  invPi: PiTypes invEq (fun X => (νTowerDeps X).(_frames))
    (fun X => (νTowerDeps X).(_paintings)) W.(_twFrameEqvs) invRho
    W.(_twPaintingEqvs);
  invRho': RhoTypes invEq (nextFr νTowerDeps) (mkFrameEqvs (towerTrDeps W));
  invSigma: SigmaTypes invEq νTowerDeps W.(_twFrameEqvs) W.(_twPaintingEqvs)
    W.(_twTrRestrs) invRho invRho'.1;
  invRhoPair: RhoPairTypes invEq νTowerDeps W.(_twFrameEqvs) W.(_twPaintingEqvs)
    W.(_twTrRestrs) invRho invPi invRho' invSigma;
  invTau: forall (EA: νFillerType XA) (EB: νFillerType XB)
    (fEqv: towerFillerEqv W EA EB),
    TauTypes invEq (hOf invEq _ invRho' fEqv) νTowerDeps
      (fun X E => TopRestrDep E) (fun X E => (νDataAt X).(restrPaintings) E)
      W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
      (TopTrDep (T := towerTrDeps W) fEqv) (W.(_twTrRestrPaintings) EA EB fEqv)
      invRho invPi invRho' invSigma
      (mkPiN invEq (hOf invEq _ invRho' fEqv) νTowerDeps
        (fun X E => TopRestrDep E) W.(_twFrameEqvs) W.(_twPaintingEqvs)
        W.(_twTrRestrs) (TopTrDep (T := towerTrDeps W) fEqv)
        invRho invPi invRho' invSigma invRhoPair
        (piTopCase invEq W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
          invRho' fEqv));
}.

Arguments invEq {m XA XB W} _.

(** Level [0]: the prefixes are units, the invariant families are units,
    and [ρ] for the level-[1] frames is the transport of the point of the
    unit frame along the unit path. *)
Definition inv0 (XA XB: (νGpdAt 0).(prefix)): Inv (trTower0 XA XB).
Proof.
  unshelve refine (Build_Inv 0 XA XB (trTower0 XA XB) (hunit_ext XA XB: XA = XB)
    _ _ _ _ _ _).
  - now exact tt.
  - now exact tt.
  - unshelve esplit.
    + now exact tt.
    + intro d. now apply hunit_ext.
  - now exact tt.
  - now exact tt.
  - intros EA EB fEqv. now exact tt.
Defined.

(** The level step

    The invariant one level up: the prefix path is [extOf], [ρ] and [π]
    are the lifts of the ones below, [ρ''] and [σ'] come from
    [rhoSigmaNext] with [rhoTop] at the top stage, and [τ'] is [tauNext]
    over [tauTop]. The prefix path of the new invariant is [extOf] by
    construction, which is the compatibility the conversion needs between
    consecutive levels. *)

Definition invStepA {m: nat} {XA XB: (νGpdAt m).(prefix)}
  {W: TrTower m XA XB} (I: Inv W)
  {EA: νFillerType XA} {EB: νFillerType XB} (fEqv: towerFillerEqv W EA EB):
  Inv (trTowerStep W fEqv).
Proof.
  unshelve refine (Build_Inv m.+1 (XA; EA) (XB; EB) (trTowerStep W fEqv)
    (extOf (invEq I) _ (invRho' _ I) fEqv) _ _ _ _ _ _).
  all: pose (hh := hOf (invEq I) _ (invRho' _ I) fEqv).
  all: pose (pN := mkPiN (invEq I) hh νTowerDeps (fun X E => TopRestrDep E)
    W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
    (TopTrDep (T := towerTrDeps W) fEqv) (invRho _ I) (invPi _ I) (invRho' _ I)
    (invSigma _ I) (invRhoPair _ I)
    (piTopCase (invEq I) W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
      (invRho' _ I) fEqv)).
  all: pose (RS := rhoSigmaNext (invEq I) hh νTowerDeps (fun X E => TopRestrDep E)
    (fun X E => (νDataAt X).(restrPaintings) E) (fun X E => (νDataAt X).(cohFrames) E)
    W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
    (TopTrDep (T := towerTrDeps W) fEqv) (W.(_twTrRestrPaintings) EA EB fEqv)
    (W.(_twTrCohs) EA EB fEqv) (invRho _ I) (invPi _ I) (invRho' _ I)
    (invSigma _ I) (invRhoPair _ I) pN (invTau _ I EA EB fEqv)).
  all: pose (rho1 := rhoLift (invEq I) hh (nextFr νTowerDeps) _ (invRho' _ I)).
  all: pose (pi1 := piLift (invEq I) hh νTowerDeps (fun X E => TopRestrDep E) _
    (invRho' _ I) _ pN).
  1: now exact rho1.
  1: now exact pi1.
  1: now exact (RS.1; rhoTop (extOf (invEq I) _ (invRho' _ I) fEqv) νTowerDeps
    _ _ _ rho1 pi1 RS.1 RS.2).
  1: now exact RS.2.
  1: now exact (rhoPairNext (invEq I) hh νTowerDeps (fun X E => TopRestrDep E)
    (fun X E => (νDataAt X).(restrPaintings) E) (fun X E => (νDataAt X).(cohFrames) E)
    W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
    (TopTrDep (T := towerTrDeps W) fEqv) (W.(_twTrRestrPaintings) EA EB fEqv)
    (W.(_twTrCohs) EA EB fEqv) (invRho _ I) (invPi _ I) (invRho' _ I)
    (invSigma _ I) (invRhoPair _ I) pN (invTau _ I EA EB fEqv);
    fun d l => eq_refl).
  intros EA2 EB2 fEqv2.
  unshelve refine (tauNext (invEq I) hh νTowerDeps (fun X E => TopRestrDep E)
    (fun X E => (νDataAt X).(restrPaintings) E) (fun X E => (νDataAt X).(cohFrames) E)
    W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
    (TopTrDep (T := towerTrDeps W) fEqv) (W.(_twTrRestrPaintings) EA EB fEqv)
    (W.(_twTrCohs) EA EB fEqv) (invRho _ I) (invPi _ I) (invRho' _ I)
    (invSigma _ I) (invRhoPair _ I)
    (piTopCase (invEq I) W.(_twFrameEqvs) W.(_twPaintingEqvs) W.(_twTrRestrs)
      (invRho' _ I) fEqv)
    (invTau _ I EA EB fEqv) (fun X' E' => TopCohDep E') (TopTrCohDep (TC := trCohsOf νTowerDeps
       (fun X E => TopRestrDep E) (fun X E => (νDataAt X).(restrPaintings) E)
       (fun X E => (νDataAt X).(cohFrames) E) W.(_twFrameEqvs) W.(_twPaintingEqvs)
       W.(_twTrRestrs) (TopTrDep (T := towerTrDeps W) fEqv)
       (W.(_twTrRestrPaintings) EA EB fEqv) (W.(_twTrCohs) EA EB fEqv)) fEqv2)
    _ _ _ _ _ _ _).
  - now apply tauTop.
  - now apply sigmaPairNext.
Defined.

Definition invStep {m: nat} {XA XB: (νGpdAt m).(prefix)}
  {W: TrTower m XA XB} (I: Inv W)
  {EA: νFillerType XA} {EB: νFillerType XB} (fEqv: towerFillerEqv W EA EB):
  { I': Inv (trTowerStep W fEqv) &T
    invEq I' = extOf (invEq I) _ (invRho' _ I) fEqv } :=
  (invStepA I fEqv; eq_refl).

Section Conversion.

Lemma invEqRew {m: nat} {XA XB: (νGpdAt m).(prefix)}
  {P P': (trAt m XA XB).(trPrefix)} (q: P = P')
  (I: Inv ((trAt m XA XB).(trData) P)):
  invEq (rew [fun P0 => Inv ((trAt m XA XB).(trData) P0)] q in I) = invEq I.
Proof.
  now destruct q.
Qed.

Context {SA SB: νGpds} (L: νGpdsEquiv SA SB).

Fixpoint invAt (m: nat):
  Inv ((trAt m (νGpdPack m SA).1 (νGpdPack m SB).1).(trData) (L.(approx) m leR_O)) :=
  match m with
  | 0 => inv0 _ _
  | S m => (invStep
      (rew <- [fun P => Inv ((trAt m _ _).(trData) P)] L.(approxS) m leR_O leR_O in
        invAt m)
      (L.(approx) m.+1 leR_O).2).1
  end.

Lemma invAtS (m: nat):
  f_equal (fun Xp: (νGpdAt m.+1).(prefix) => Xp.1) (invEq (invAt m.+1))
  = invEq (invAt m).
Proof.
  cbn [invAt].
  rewrite (invStep _ _).2.
  unfold extOf. rewrite extendCongFst.
  now apply invEqRew.
Qed.

Definition νGpdsEquivEq: SA = SB :=
  νGpdsEqFromPaths (fun m => invEq (invAt m)) invAtS.

End Conversion.

End Extensionality.
