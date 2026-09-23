Import Logic.EqNotations.
Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation
  νGpd.HGpd νGpd.Layer νGpd.Lemmas νGpd.Pasting νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf PresheafOfνGpd νGpdEquiv PathAlgebra.
From Bonak.Equiv.Gpd.νGpdRoundtrip Require Import Translation Canonical.
From Bonak.Lib Require Import Equiv.
From Bonak Require Import Limit.
Set Primitive Projections.
Set Keyed Unification.
Local Lemma restriction_index_cell_dep {U V W: Type} {S: V -> Type} {P: W -> Type}
  (d: U -> V) (tr: V -> W) (G: forall v, S v -> P (tr v))
  {u0 u1: U} (e: u0 = u1) {z: V}
  (c0: d u0 = z) (c1: d u1 = z)
  (C: c0 = f_equal d e • c1)
  {v0: S (d u0)} {v1: S (d u1)} {vz: S z}
  (hc0: rew [S] c0 in v0 = vz)
  (hm: rew [S] f_equal d e in v0 = v1)
  (hc1: rew [S] c1 in v1 = vz)
  (HC: rew [fun c: d u0 = z => rew [S] c in v0 = vz] C in hc0 = hm ⊙ hc1):
  rew [fun c: tr (d u0) = tr z => rew [P] c in G (d u0) v0 = G z vz]
    restriction_index_cell d tr e c0 c1 C in sigT_map_eq G hc0 =
  sigT_map_eq G hm ⊙ sigT_map_eq G hc1.
Proof.
  now exact
    (sigT_map_eq
      (P := fun c: d u0 = z => rew [S] c in v0 = vz)
      (Q := fun c: tr (d u0) = tr z => rew [P] c in G (d u0) v0 = G z vz)
      (f := fun c => f_equal tr c) (fun c h => sigT_map_eq G h) HC
    ⊙[fun c: tr (d u0) = tr z => rew [P] c in G (d u0) v0 = G z vz]
      sigT_map_eq_comp G hm hc1).
Defined.

(** Recover a displayed prefix from a composite and its terminal edge. *)
Local Definition displayed_cancel_right {A: Type} (P: A -> Type)
  {x y z: A} (p: x = y) (q: y = z)
  {u: P x} {v: P y} {w: P z}
  (h: rew [P] (p • q) in u = w) (k: rew [P] q in v = w):
  rew [P] p in u = v :=
  eq_sym (rew_opp_l P q (rew [P] p in u)) •
    (f_equal (fun value => rew [P] eq_sym q in value)
      (rew_compose P p q u • (h • eq_sym k)) • rew_opp_l P q v).

Local Lemma square_compose_dep_inv_right {X: Type} (P: X -> Type)
  {x0 x1 x2 y0 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = y0} {q: x1 = y1} {r: x2 = y2}
  (H: p • c = a • q) (K: q • d = b • r)
  {u0: P x0} {u1: P x1} {u2: P x2}
  {v0: P y0} {v1: P y1} {v2: P y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [P] c in v0 = v1) (hd: rew [P] d in v1 = v2)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in u2 = v2)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (ALL: rew [fun e => rew [P] e in u0 = v2] square_compose H K in
    (hp ⊙ (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr):
  rew [fun e => rew [P] e in u1 = v2] K in (hq ⊙ hd) = hb ⊙ hr.
Proof.
  pose (D := fun e: x0 = y2 => rew [P] e in u0 = v2).
  pose proof (sigT_trans_eq_inv_l (P := D)
    (displayed_assoc_forward P hp hc hd) ALL) as E1.
  pose proof (sigT_trans_eq_inv_l (P := D)
    (displayed_whisker_r P H d hd HH) E1) as E2.
  pose proof (sigT_trans_eq_inv_l (P := D)
    (sigT_trans_eq_assoc ha hq hd) E2) as E3.
  pose proof (displayed_cancel_right D (whisker_l a K)
    (eq_trans_assoc a b r) E3 (displayed_assoc_forward P ha hb hr)) as E4.
  pose (F := fun e: x1 = y2 => rew [P] e in u1 = v2).
  assert (E5: ha ⊙ (rew [F] K in (hq ⊙ hd)) = ha ⊙ (hb ⊙ hr)).
  { refine (eq_sym (rew_sigT_trans_eq_r K ha (hq ⊙ hd)) • _).
    refine (rew_map D (fun e => a • e) K (ha ⊙ (hq ⊙ hd)) • _).
    now exact E4. }
  refine (eq_sym (sigT_trans_eq_inv_l_recover ha (rew [F] K in (hq ⊙ hd))) • _).
  refine (f_equal (fun h: rew [P] (a • (b • r)) in u0 = v2 =>
    sigT_trans_eq_inv_l ha h) E5 • _).
  now exact (sigT_trans_eq_inv_l_recover ha (hb ⊙ hr)).
Defined.


Local Lemma restriction_step_cell_dep_inv_previous {U V W: Type} (P: W -> Type)
  (f: U -> W) (d: U -> V) (tr: V -> W)
  (alpha: forall u, f u = tr (d u))
  {u0 u1: U} (e: u0 = u1) {z: V}
  (c0: d u0 = z) (c1: d u1 = z)
  (C: c0 = f_equal d e • c1)
  {a b: W} (a0: tr z = b) (b0: f u1 = a) (r: a = b)
  (Qprev: (alpha u1 • f_equal tr c1) • a0 = b0 • r)
  {u0p: P (f u0)} {u1p: P (f u1)}
  {v0p: P (tr (d u0))} {v1p: P (tr (d u1))}
  {zp: P (tr z)} {ap: P a} {bp: P b}
  (ha0: rew [P] alpha u0 in u0p = v0p)
  (ha1: rew [P] alpha u1 in u1p = v1p)
  (he: rew [P] f_equal f e in u0p = u1p)
  (hm: rew [P] f_equal tr (f_equal d e) in v0p = v1p)
  (hc0: rew [P] f_equal tr c0 in v0p = zp)
  (hc1: rew [P] f_equal tr c1 in v1p = zp)
  (ha: rew [P] a0 in zp = bp) (hb: rew [P] b0 in u1p = ap)
  (hr: rew [P] r in ap = bp)
  (HC: rew [fun q => rew [P] q in v0p = zp]
    restriction_index_cell d tr e c0 c1 C in hc0 = hm ⊙ hc1)
  (HN: rew [fun q => rew [P] q in u0p = v1p]
    restriction_naturality_cell f d tr alpha e in (ha0 ⊙ hm) = he ⊙ ha1)
  (ALL: rew [fun q => rew [P] q in u0p = bp]
    restriction_step_cell f d tr alpha e c0 c1 C a0 b0 r Qprev in
    ((ha0 ⊙ hc0) ⊙ ha) = (he ⊙ hb) ⊙ hr):
rew [fun q => rew [P] q in u1p = bp] Qprev in
    ((ha1 ⊙ hc1) ⊙ ha) = hb ⊙ hr.
Proof.
  pose (m := f_equal tr (f_equal d e)).
  pose (n := f_equal tr c1).
  pose (MC := restriction_index_cell d tr e c0 c1 C).
  pose (N := restriction_naturality_cell f d tr alpha e).
  pose (liftMC := sigT_map_eq
    (P := fun q: tr (d u0) = tr z => rew [P] q in v0p = zp)
    (Q := fun q: f u0 = b => rew [P] q in u0p = bp)
    (f := fun q => (alpha u0 • q) • a0)
    (fun q hq => (ha0 ⊙ hq) ⊙ ha) HC).
  pose (liftOuter := sigT_trans_eq_assoc ha0 (hm ⊙ hc1) ha).
  pose (liftMiddle := sigT_map_eq
    (P := fun q: tr (d u0) = b => rew [P] q in v0p = bp)
    (Q := fun q: f u0 = b => rew [P] q in u0p = bp)
    (f := fun q => alpha u0 • q)
    (fun q hq => ha0 ⊙ hq) (sigT_trans_eq_assoc hm hc1 ha)).

  pose (DP := fun q: f u0 = b => rew [P] q in u0p = bp).
  pose proof (sigT_trans_eq_inv_l (P := DP) liftMC ALL) as E1.
  pose proof (sigT_trans_eq_inv_l (P := DP) liftOuter E1) as E2.
  pose proof (sigT_trans_eq_inv_l (P := DP) liftMiddle E2) as E3.
  pose (ar := eq_trans_assoc (alpha u1) n a0).
  pose (liftRightAssoc := f_equal
    (fun z => rew [fun q: f u1 = b => rew [P] q in u1p = bp] ar in z)
    (eq_sym (sigT_trans_eq_assoc ha1 hc1 ha))
    • rew_sym_cancel_r (P := fun q: f u1 = b => rew [P] q in u1p = bp)
        ar ((ha1 ⊙ hc1) ⊙ ha)).

  pose proof (square_compose_dep_inv_right P N (ar • Qprev)
    he hb hm (hc1 ⊙ ha) ha0 ha1 hr HN E3) as Previous.
  now exact (sigT_trans_eq_inv_l
    (P := fun q: f u1 = b => rew [P] q in u1p = bp)
    liftRightAssoc Previous).
Defined.


(** Mapping a selected pair encoding carries its displayed path through
    the same encoding cell. *)
Local Lemma sigT_selected_map_cell_dep {A B: Type} {P: A -> Type} {Q: B -> Type}
  {R: {a: A &T P a} -> Type} {S: {b: B &T Q b} -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  (h: forall z: {a: A &T P a}, R z -> S (f z.1; g z.1 z.2))
  {x y: A} {u: P x} {v: P y}
  (p: (x; u) = (y; v)) (r: x = y) (hr: rew [P] r in u = v)
  (H: p = (=r; hr)) {cu: R (x; u)} {cv: R (y; v)}
  (hp: rew [R] p in cu = cv):
  eq_existT_curried_dep (P := Q) (Q := S)
    (H := f_equal f r) (Hu := sigT_map_eq (P := P) (Q := Q) (f := f) g hr)
    (Hv := rew [fun e => rew [S] e in h (x; u) cu = h (y; v) cv]
      (f_equal (fun e => f_equal
         (fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) e) H
       • f_equal_eq_existT_curried (P := P) (Q := Q) f g r hr) in
      sigT_map_eq (P := R) (Q := S)
        (f := fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) h hp) =
  sigT_map_eq
    (P := fun a => {u: P a &T R (a; u)})
    (Q := fun b => {v: Q b &T S (b; v)}) (f := f)
    (fun a uv => (g a uv.1; h (a; uv.1) uv.2))
    (eq_existT_curried_dep (P := P) (Q := R) (H := r) (Hu := hr)
      (Hv := rew [fun e => rew [R] e in cu = cv] H in hp)).
Proof.
  subst p.
  cbn [f_equal].
  rewrite eq_trans_refl_l.
  now exact (eq_sym (sigT_map_eq_existT_curried_dep_curried
    (P := P) (R := fun a u => R (a; u))
    (P' := Q) (R' := fun b v => S (b; v))
    f g (fun a u c => h (a; u) c) r hr hp)).
Defined.

(** The projection encoding used by [sigT_total_map_cell] has the same
    displayed companion, with no comparison between separately chosen cells. *)
Local Lemma sigT_total_map_cell_dep {A B: Type} {P: A -> Type} {Q: B -> Type}
  {R: {a: A &T P a} -> Type} {S: {b: B &T Q b} -> Type}
  (f: A -> B) (g: forall a, P a -> Q (f a))
  (h: forall z: {a: A &T P a}, R z -> S (f z.1; g z.1 z.2))
  {u v: {a: A &T P a}} (p: u = v)
  {cu: R u} {cv: R v} (hp: rew [R] p in cu = cv):
  eq_existT_curried_dep (P := Q) (Q := S)
    (H := f_equal f (projT1_eq p))
    (Hu := sigT_map_eq (P := P) (Q := Q) (f := f) g (projT2_eq p))
    (Hv := rew [fun e => rew [S] e in h u cu = h v cv]
      sigT_total_map_cell (P := P) (Q := Q) f g p in
      sigT_map_eq (P := R) (Q := S)
        (f := fun z: {a: A &T P a} => (f z.1; g z.1 z.2)) h hp) =
  sigT_map_eq
    (P := fun a => {u: P a &T R (a; u)})
    (Q := fun b => {v: Q b &T S (b; v)}) (f := f)
    (fun a uv => (g a uv.1; h (a; uv.1) uv.2))
    (eq_existT_curried_dep (P := P) (Q := R)
      (H := projT1_eq p) (Hu := projT2_eq p)
      (Hv := rew [fun e => rew [R] e in cu = cv]
        (eq_sym (totalPathReencode p)) in hp)).
Proof.
  destruct u as [x u], v as [y v].
  now exact (sigT_selected_map_cell_dep f g h p (projT1_eq p)
    (projT2_eq p) (eq_sym (totalPathReencode p)) hp).
Defined.


(** Mapping the chosen zero-painting endpoint correction leaves the
    frame path unchanged. *)
Local Lemma sigT_map_eq_target_adjust {A B: Type} {P: A -> Type} {Q: B -> Type}
  {f: A -> B} (g: forall a, P a -> Q (f a))
  {x y: A} {u: P x} {v v': P y} {p: x = y}
  (h: rew [P] p in u = v) (E: v' = v):
  sigT_map_eq (P := P) (Q := Q) (f := f) g (h • eq_sym E) =
  sigT_map_eq (P := P) (Q := Q) (f := f) g h • eq_sym (f_equal (g y) E).
Proof.
  subst v'. cbn [eq_sym f_equal].
  now rewrite 2 eq_trans_refl_r.
Defined.


Module SelectedNaturality (A: LayerGpdSig)
  (Base: PresheafOfνGpd.ConstructionsSig A) (Translations: νGpdEquiv.TranslationSig A Base).
Import A.
Module Export C := Canonical.Canonical A Base Translations.
#[local] Arguments Desc {X} {n} {Xpre} _.
#[local] Arguments DescS {X} {n} {Xpre} {S0} _.
#[local] Arguments FgFrp {X} m W frt.
#[local] Arguments FgFrt {X} m W.
#[local] Arguments FgLevel {X} m.
#[local] Arguments FgRestrData {X} m W frt frp.
#[local] Arguments FgTower {X} m.
#[local] Arguments FrtDeps {X} M {XpB0} {S0} HD {p} {k} {dcB} cB.
#[local] Arguments FrtDepsCohs {X} M {XpB0} {S0} HD {p} {k} {dcB} cB.
#[local] Arguments FrtFramesNextType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB'.
#[local] Arguments FrtFramesType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtPaintingTopType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F {XA} {XB} TX PX top val H.
#[local] Arguments FrtPaintingsNextType {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' frames.
#[local] Arguments FrtPairLawAt {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top.
#[local] Arguments FrtRestr0At {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair.
#[local] Arguments FrtRestrDataDef {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {F} {FrtRestrBlock}.
#[local] Arguments FrtRestrFramesDef {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {F} {FrtRestrBlock} _.
#[local] Arguments FrtRestrLayerStepAtChosen {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev.
#[local] Arguments FrtRestrPaintingCellSelected {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t HP {a} {b} vl vr.
#[local] Arguments FrtRestrPrevData {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings.
#[local] Arguments FrtRpZeroType {p} {k} {DR} Xe rp.
#[local] Arguments FrtSplitDataAt {X} M {XpB0} {S0} HD p {k} {dcB} cB F top frames.
#[local] Arguments FrtSplitStep {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top frames.
#[local] Arguments PshRpZeroType {X} {m} {p} {k} P {Xe} PX {rp} pshRp Hrp.
#[local] Arguments RestrNext {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} B sp.
#[local] Arguments StepInput {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f.
#[local] Arguments StepLayer {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f sp q Hq Hqp epsilon t.
#[local] Arguments StepPrevious {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FC} {cB'} {Hlen'} {frames} {paintings} {SD} f _.
#[local] Arguments TrRpZeroType {p} {k} T {XA} {XB} TX {rpA} {rpB} trRp HrpA HrpB.
#[local] Arguments _fcCohsA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcF {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPX {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPshCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcPshRp {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcRpA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcTX {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcTrRp {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcXA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _fcXB {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDepsCohs}.
#[local] Arguments _frBound {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frDepsA {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frFrameEqvs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPaintingEqvs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPaintings {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frPshRestrs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments _frTrRestrs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} {FrtDeps}.
#[local] Arguments descAt {X} m.
#[local] Arguments descCanonicalPaintingConsCell_dep {X} {M} {XpB0} {S0} HD {p} {k} {dc3} a Hlen q Hq Hdim epsilon t.
#[local] Arguments descCanonicalPaintingPaired {X} {M} {XpB0} {S0} HD q {p} {k} {dc3} a Hlen Hq Hdim epsilon t.
#[local] Arguments descCanonicalZeroRpChoice {p} {k} dc3 Hq ζ d c.
#[local] Arguments descCell {X} {m} {XpB} {SB} HD t.
#[local] Arguments descCellPairRestrAt {X} {n} {XpB0} {S0} HD {pB} {kB} {dcB} cB dim Hdim Hlen ε t.
#[local] Arguments descCells {X} {m} {XpB} {SB} HD t.
#[local] Arguments descChain {X} {n} {Xpre} {S0} D.
#[local] Arguments descChainLen {X} {n} {Xpre} {S0} D.
#[local] Arguments descQcells {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} cB Hlen q Hq Hqp ε t.
#[local] Arguments descQcellsCons {X} {n} {XpB0} {S0} HD {P} {k} {dcB} cB Hlen q Hq Hqp Hq' Hqp' ε t.
#[local] Arguments descTop {X} {M} {XpB0} {S0} HD {p} {k} {dcB} cB _.
#[local] Arguments fgDeps {X} m W frt frp.
#[local] Arguments fgFrpNextOf {X} m s.
#[local] Arguments fgFrtNextOf {X} m s.
#[local] Arguments fgFrtOf {X} m W frt frp Q.
#[local] Arguments fgPrefixNext {X} m s.
#[local] Arguments fgQNext {X} m s.
#[local] Arguments fgSplitOf {X} m P frt frp Q.
#[local] Arguments fgTowerAt {X} m P.
#[local] Arguments frTr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments frtDcB {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtPairLawPrev {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings ε t.
#[local] Arguments frtPshCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtPshCohsOf {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F XA PX rpA pshRp cohsA.
#[local] Arguments frtPshDeps {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments frtRestrBaseCell {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp epsilon t.
#[local] Arguments frtRestrCell {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t HP.
#[local] Arguments frtRestrLeftNorm {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev q Hq Hqp epsilon t.
#[local] Arguments frtRestrPaintingStepSelectedOf {X} M XpB0 S0 HD p k dcB cB F XA XB TX PX rpA rpB trRp pshRp HrpA HrpB HtrRp HpshRp top val prev Hpair HR E ε t.
#[local] Arguments frtRestrPrevBlock {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings.
#[local] Arguments frtRestrPrevClause {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp ε t.
#[local] Arguments frtRestrPrevFrames {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Qprev.
#[local] Arguments frtRestrPrevPair {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev t.
#[local] Arguments frtRestrPrevZero {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev ε t.
#[local] Arguments frtRestrRightNorm {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' Hlen' frames paintings Hpair HR Qprev q Hq Hqp epsilon t.
#[local] Arguments frtSplitHead {X} {M} {XpB0} {S0} HD p {k} {dcB} cB F top frames SD.
#[local] Arguments frtSplitOfQ {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F Q.
#[local] Arguments frtTopNext {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' _.
#[local] Arguments frtTrBase {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments frtTrCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments lvFrp {X} {m} f.
#[local] Arguments lvFrt {X} {m} f.
#[local] Arguments lvP {X} {m} f.
#[local] Arguments lvQ {X} {m} f.
#[local] Arguments lvSP {X} {m} f.
#[local] Arguments lvW {X} {m} s.
#[local] Arguments mkCellFramesOf {X} M {P} {K} {depsTop} {p} {k} {deps} c top.
#[local] Arguments mkCellValues {X} M {p} {k} deps extraDeps top val.
#[local] Arguments mkCellValuesOf {X} M {P} {K} {depsTop} {extTop} {p} {k} {deps} {ext} c top val.
#[local] Arguments mkFrtDepsOf {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC cB' frames paintings.
#[local] Arguments mkFrtFrameStep {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev lay.
#[local] Arguments mkFrtLayerOfRestr {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F top prev Hpair HR t.
#[local] Arguments mkFrtPaintingStepDown {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F XA XB TX PX top val prev lay E t.
#[local] Arguments mkFrtPaintingTypes {X} M {p} {k} {framesA} {framesB} {eqvs} {pshFrames} {cells} frt {paintingsA} {paintingsB} pEqvs pshPaintings cellValues.
#[local] Arguments mkFrtPaintingsOfRestr {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F XA XB TX PX val Q E.
#[local] Arguments mkFrtRestrTypeStep {X} {M} {p} {k} {framesA} {framesB} {eqvs} {pshFrames} {cells} frt {prevA} {prevB} {prevPsh} {prevTr} {RA} {RB} Qpsh Qtr cellsNext frtNext Qcells.
#[local] Arguments mkFrtRestrTypesAndFrames {X} M {XpB0} {S0} HD p {k} {dcB} cB Hlen F.
#[local] Arguments mkFrtStepTypesAndRestrNext {X} M {XpB0} {S0} HD p {k} {dcB} cB FC cB' Hlen' frames paintings SD.
#[local] Arguments proj1FrtDeps {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} F.
#[local] Arguments proj1FrtDepsCohs {X} {M} {XpB0} {S0} {HD} {p} {k} {dcB} {cB} FC.
#[local] Arguments pshRc {X} m.
#[local] Arguments pshRp {X} m.
#[local] Arguments pshRpZeroChainOf {X} p {m} {k} {PC2} {XC} PCX.
#[local] Arguments pshTw {X} m.
#[local] Arguments rpZeroChainOf p {k} {depsCohs} XC.
#[local] Arguments towerFrtDepsCohs {X} m s.
#[local] Arguments towerFrtDepsCohsOf {X} m W frt frp Q.
#[local] Arguments trRpZeroChainOf p {k} {TC} {XCA} {XCB} TCX.




Section FG.
Variable X: νGpds.
Local Lemma displayed_unit_right {A: Type} {P: A -> Type}
  {x y: A} {p: x = y} {u: P x} {v: P y} (h: rew [P] p in u = v):
  h ⊙[P] (eq_refl: rew [P] eq_refl in v = v) = h.
Proof. now destruct p, h. Defined.

Section CarriedPaintingNaturality.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames).

Let frameA := (mkPshFrames (g X) (frtPshDeps FC.(_fcF))).1.2.
Let frameB := (mkCellFramesOf M.+1 (extChainDeps (cohsChainExt cB'))
  (descCells (DescS HD))).1.2.
Let frameMap := (mkFrameEqvs (frTr FC.(_fcF))).1.2.
Let PA := fun a => GDom ((mkPaintings FC.(_fcXA)).1.2 a).
Let PB := fun a => GDom ((mkPaintings FC.(_fcXB)).1.2 a).
Let paintingMap := fun a b => (mkPaintingEqvs FC.(_fcTX)).1.2 a b.
Let valueA := (mkPshPaintings (g X) FC.(_fcPX)).1.2.
Let valueB := (mkCellValuesOf M.+1 (cohsChainExt cB')
  (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).1.2.

(** The carried painting comparison supplies the naturality witness over
    the exact frame naturality cell selected by the restriction step. *)
Lemma frtPaintingIndexNaturality {u v: (g X).(G0) M.+1} (e: u = v):
  rew [fun p => rew [PA] p in valueA u = paintingMap (frameB v) (valueB v)]
    restriction_naturality_cell frameA frameB frameMap frames.1.2 e in
    (paintings.1.2 u ⊙[PA]
      sigT_map_eq (P := PB) (Q := PA) (f := frameMap) paintingMap
        (f_equal_dep_sigT (Q := PB) frameB valueB e)) =
  f_equal_dep_sigT (Q := PA) frameA valueA e ⊙[PA] paintings.1.2 v.
Proof.
  destruct e.
  cbn [restriction_naturality_cell f_equal_naturality f_equal
    f_equal_dep_sigT f_equal_id sigT_map_eq eq_sym eq_trans].
  rewrite (displayed_unit_right (P := PA) (paintings.1.2 u)).
  now exact (eq_sym (sigT_trans_eq_refl_l (P := PA) (frames.1.2 u) (paintings.1.2 u))).
Defined.
End CarriedPaintingNaturality.

Section NativeRestrictionPaintingConsumers.
Context {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2
          = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair).

Context (Hsplit: forall t, frames.2 t =
  (=frames.1.2 t;
    mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR t)).
Section RestrictionPaintingEdges.
Context (Qprev: (FrtRestrPrevData FC cB' Hlen' frames paintings))
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1) (ε: arity)
  (t: (g X).(G0) M.+2).
Let prev := (frtRestrPrevFrames FC cB' Hlen' frames paintings) Qprev.
Let HRPrev := (frtRestrPrevZero FC cB' Hlen' frames paintings Hpair HR) Qprev.
Let LA := fun x => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
  (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).(GDom).
Let LB := fun x => (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
  (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x).(GDom).
Let ha := mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR
       ((g X).(GFace) M.+1 (q + p.+1) Hqp ε t).

Let hd := sigT_map_eq
         (P := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 x0)
         (fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
            (frTr FC.(_fcF)).(_trRestrs) a l)
         (projT2_eq (descQcells cB' Hlen' q Hq Hqp ε t)).

Let ht := mkTrRestrLayer (frtTrCohs FC).(_trBase)
         (mkTrRestrFrames (proj1TrDepsCohs (frtTrCohs FC)))
         (frtTrCohs FC).(_trCohs).2 q Hq ε (descTop (DescS HD) cB' t).1.

Let kp := mkPshRestrLayerMerged (g X) (frtPshCohs FC)
       (mkPshRestrFrames (g X)
          (proj1PshDepsCohs (g X)
             (frtPshCohsOf FC.(_fcF) FC.(_fcXA) FC.(_fcPX) FC.(_fcRpA)
                FC.(_fcPshRp) FC.(_fcCohsA)))
          FC.(_fcPshCohs).1)
       FC.(_fcPshCohs).2 q Hq Hqp ε t.

Let kn := sigT_map_eq
         (P := fun x0 => (mkLayer
            (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
            (painting := (mkDepsRestr (depsCohs :=
               trDepsCohsA (frtTrBase FC))).(1).(_paintings).2) x0).(GDom))
         (Q := fun x0 => (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
            (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x0).(GDom))
         (f := fun x0 => (mkRestrFrames (depsCohs :=
            proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2 q.+1 (⇑ Hq) ε x0)
         (fun a l => mkRestrLayer
            (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2
            (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq ε a l)
         (mkFrtLayerOfRestr
            (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
            (descTop (DescS HD) (DepsCohsChainCons cB')) prev
            (frtPairLawPrev FC cB' Hlen' frames paintings) HRPrev t).

Let ND := sigT_total_map_cell (P := LB) (Q := LA)
  (fun x => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 x)
  (fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
    (frTr FC.(_fcF)).(_trRestrs) a l) (descQcells cB' Hlen' q Hq Hqp ε t).
Let NN :=
  f_equal (fun e => f_equal
    ((mkRestrFrames (depsCohs := trDepsCohsA (frtTrBase FC))).2 q Hq ε) e)
    ((frtRestrPrevPair FC cB' Hlen' frames paintings Hpair HR) Qprev t)
  • f_equal_eq_existT_curried
    (P := fun x => (mkLayer
      (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).(1).(_restrFrames).2
      (painting := (mkDepsRestr (depsCohs := trDepsCohsA (frtTrBase FC))).(1).(_paintings).2)
      x).(GDom)) (Q := LA)
    ((mkRestrFrames (depsCohs := proj1DepsCohs (trDepsCohsA (frtTrBase FC)))).2
      q.+1 (⇑ Hq) ε)
    (fun a l => mkRestrLayer (trDepsCohsA (frtTrBase FC)).(_restrPaintings).2
      (trDepsCohsA (frtTrBase FC)).(_cohs).2 q Hq ε a l)
    (((frtRestrPrevFrames FC cB' Hlen' frames paintings) Qprev).2 t)
    (mkFrtLayerOfRestr (proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings))
      (descTop (DescS HD) (DepsCohsChainCons cB')) ((frtRestrPrevFrames FC cB' Hlen' frames paintings) Qprev)
      (frtPairLawPrev FC cB' Hlen' frames paintings) ((frtRestrPrevZero FC cB' Hlen' frames paintings Hpair HR) Qprev) t).

Context (HP: DPathCellOver (ha ⊙[LA] hd ⊙[LA] ht) (kp ⊙[LA] kn)
  ((frtRestrBaseCell FC cB' Hlen' frames paintings Hpair HR) Qprev q Hq Hqp ε t))
  (R: mkFrame (frTr FC.(_fcF)).(_depsA) -> Type) {a0 a1 a2 a3 b1}
  (va: rew [R] frames.2 ((g X).(GFace) M.+1 (q + p.+1) Hqp ε t) in a0 = a1)
  (vd: rew [R] f_equal (mkFrameEqv (frTr FC.(_fcF)))
    (descQcells cB' Hlen' q Hq Hqp ε t) in a1 = a2)
  (vt: rew [R] (mkTrRestrFrames (frtTrCohs FC)).2 q Hq ε
    (descTop (DescS HD) cB' t).1 in a2 = a3)
  (wp: rew [R] (mkPshRestrFrames (g X) (frtPshCohs FC) FC.(_fcPshCohs)).2
    q Hq Hqp ε t in a0 = b1)
  (wn: rew [R] f_equal ((mkRestrFrames (depsCohs := trDepsCohsA (frtTrBase FC))).2
    q Hq ε) (((frtRestrPrevBlock FC cB' Hlen' frames paintings).(FrtRestrFramesDef) Qprev).2 t) in b1 = a3)
  (Hparent: rew [fun e => rew [R] e in a0 = a3]
    (frtRestrCell FC cB' Hlen' frames paintings Hpair HR Hsplit) Qprev q Hq Hqp ε t HP in
    (va ⊙[R] vd ⊙[R] vt) = wp ⊙[R] wn).

Definition frtRestrPaintingEdgeA :=
  eq_existT_curried_dep (P := LA) (Q := R) (Hu := ha)
    (Hv := rew [fun e => rew [R] e in a0 = a1]
      Hsplit ((g X).(GFace) M.+1 (q + p.+1) Hqp ε t) in va).
Definition frtRestrPaintingEdgeD :=
  eq_existT_curried_dep (P := LA) (Q := R) (Hu := hd)
    (Hv := rew [fun e => rew [R] e in a1 = a2] ND in vd).
Definition frtRestrPaintingEdgeT :=
  eq_existT_curried_dep (P := LA) (Q := R) (Hu := ht) (Hv := vt).
Definition frtRestrPaintingEdgeP :=
  eq_existT_curried_dep (P := LA) (Q := R) (Hu := kp) (Hv := wp).
Definition frtRestrPaintingEdgeN :=
  eq_existT_curried_dep (P := LA) (Q := R) (Hu := kn)
    (Hv := rew [fun e => rew [R] e in b1 = a3] NN in wn).

(** The parent certificate produces the actual pair-valued route used
    to recover the positive previous-stage painting clause. *)
Lemma frtRestrCell_dep_edges:
  DPathCellOver
    (P := fun x => {u: LA x &T R (x; u)})
    ((frtRestrPaintingEdgeA ⊙ frtRestrPaintingEdgeD) ⊙ frtRestrPaintingEdgeT)
    (frtRestrPaintingEdgeP ⊙ frtRestrPaintingEdgeN)
    ((frtRestrBaseCell FC cB' Hlen' frames paintings Hpair HR) Qprev q Hq Hqp ε t).
Proof.
  unfold DPathCellOver, frtRestrPaintingEdgeA, frtRestrPaintingEdgeD,
    frtRestrPaintingEdgeT, frtRestrPaintingEdgeP, frtRestrPaintingEdgeN.
  rewrite 3 (sigT_trans_eq_existT_curried_dep (P := LA) (Q := R)).
  apply (eq_existT_curried_dep_eq (P := LA) (Q := R)
    ((frtRestrBaseCell FC cB' Hlen' frames paintings Hpair HR) Qprev q Hq Hqp ε t) HP).
  pose proof (rew_conjugate (fun e => rew [R] e in a0 = a3)
    ((frtRestrLeftNorm FC cB' Hlen' frames paintings Hpair HR Hsplit) Qprev q Hq Hqp ε t)
    (eq_existT_curried_eq (P := LA) ((frtRestrBaseCell FC cB' Hlen' frames paintings Hpair HR) Qprev q Hq Hqp ε t) HP)
    ((frtRestrRightNorm FC cB' Hlen' frames paintings Hpair HR) Qprev q Hq Hqp ε t)
    (va ⊙[R] vd ⊙[R] vt) (wp ⊙[R] wn) Hparent) as H.
  unfold frtRestrLeftNorm, frtRestrRightNorm in H.
  rewrite 3 (sigT_path_paste_dep R) in H.
  now exact H.
Defined.
End RestrictionPaintingEdges.

Section RestrictionCarriedPaintingInverse.
Context (Qprev: (FrtRestrPrevData FC cB' Hlen' frames paintings))
  (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (epsilon: arity) (t: (g X).(G0) M.+2).

Let Fprev := proj1FrtDeps (mkFrtDepsOf FC cB' frames paintings).
Let frameA := (mkPshFrames (g X) (frtPshDeps FC.(_fcF))).1.2.
Let frameB := fun u => (getFrame (extChainDeps (cohsChainExt cB'))
  (descCells (DescS HD) u)).1.
Let frameMap := fun z => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 z.
Let PA := fun a => GDom ((mkPaintings FC.(_fcXA)).1.2 a).
Let PB := fun a => GDom ((mkPaintings FC.(_fcXB)).1.2 a).
Let paintingMap := fun a b => (mkPaintingEqvs FC.(_fcTX)).1.2 a b.
Let valueA := (mkPshPaintings (g X) FC.(_fcPX)).1.2.
Let valueB := (mkCellValuesOf M.+1 (cohsChainExt cB')
  (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).1.2.
Let u0 := (g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t.
Let u1 := (g X).(GFace) M.+1 (q.+1 + p) (leR_add_shift Hqp) epsilon t.
Let e := pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
  (Hq := Hqp) (Hq' := leR_add_shift Hqp) epsilon t.
Let topB := (descTop (DescS HD) (DepsCohsChainCons cB') t).1.
Let z := (mkDepsRestr (depsCohs := proj1DepsCohs (frtDcB FC))).(_restrFrames).2
  q.+1 (⇑ Hq) epsilon topB.
Let c0 := projT1_eq (descQcells cB' Hlen' q Hq Hqp epsilon t).
Let c1 := descQcells (DepsCohsChainCons cB')
  (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p))
  q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t.
Let indexCell :=
  descQcellsCons (DescS HD) cB' Hlen' q Hq Hqp (⇑ Hq)
    (leR_add_shift Hqp) epsilon t •
  f_equal (fun c => c • c1)
    (f_equal_compose
      (fun u => getFrame (extChainDeps (cohsChainExt cB'))
        (descCells (DescS HD) u))
      (fun z: mkFrame (frtDcB FC).(_deps) => z.1) e).
Let a0 := Fprev.(_frTrRestrs).2 q.+1 (⇑ Hq) epsilon topB.
Let b0 := Fprev.(_frPshRestrs).2 q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t.
Let r := f_equal (Fprev.(_frDepsA).(_restrFrames).2 q.+1 (⇑ Hq) epsilon)
  (((frtRestrPrevFrames FC cB' Hlen' frames paintings) Qprev).2 t).
Let previousCell := (frtRestrPrevClause FC cB' Hlen' frames paintings Hpair HR) Qprev q.+1 (⇑ Hq)
  (leR_add_shift Hqp) epsilon t.

Context {vb: PB z}
  (bc0: rew [PB] c0 in valueB u0 = vb)
  (bc1: rew [PB] c1 in valueB u1 = vb)
  (BC: rew [fun c => rew [PB] c in valueB u0 = vb] indexCell in bc0 =
    f_equal_dep_sigT (Q := PB) frameB valueB e ⊙[PB] bc1)
  {ap bp}
  (ht: rew [PA] a0 in paintingMap z vb = bp)
  (hp: rew [PA] b0 in valueA u1 = ap)
  (hn: rew [PA] r in ap = bp).

Let mc0 := sigT_map_eq (P := PB) (Q := PA) (f := frameMap) paintingMap bc0.
Let mc1 := sigT_map_eq (P := PB) (Q := PA) (f := frameMap) paintingMap bc1.
Let he := f_equal_dep_sigT (Q := PA) frameA valueA e.
Let hm := sigT_map_eq (P := PB) (Q := PA) (f := frameMap) paintingMap
  (f_equal_dep_sigT (Q := PB) frameB valueB e).

(** The positive clause is recovered over the exact previous cell.
    The index witness retains the canonical B painting, and the
    naturality witness is generated from the carried painting list. *)
Lemma frtRestrCarriedPaintingPrevious
  (Hparent: DPathCellOver (P := PA)
    ((paintings.1.2 u0 ⊙[PA] mc0) ⊙[PA] ht)
    ((he ⊙[PA] hp) ⊙[PA] hn)
    ((frtRestrBaseCell FC cB' Hlen' frames paintings Hpair HR) Qprev q Hq Hqp epsilon t)):
  DPathCellOver (P := PA)
    ((paintings.1.2 u1 ⊙[PA] mc1) ⊙[PA] ht) (hp ⊙[PA] hn) previousCell.
Proof.
  pose (HC := restriction_index_cell_dep (S := PB) (P := PA)
    frameB frameMap paintingMap e c0 c1 indexCell bc0
    (f_equal_dep_sigT (Q := PB) frameB valueB e) bc1 BC).
  pose (HN := frtPaintingIndexNaturality FC cB' frames paintings e).
  now exact (restriction_step_cell_dep_inv_previous PA
    frameA frameB frameMap frames.1.2 e c0 c1 indexCell a0 b0 r previousCell
    (paintings.1.2 u0) (paintings.1.2 u1) he hm mc0 mc1 ht hp hn HC HN Hparent).
Defined.
End RestrictionCarriedPaintingInverse.

End NativeRestrictionPaintingConsumers.

(** The lower painting entry is assembled over the same pair equation
    as the frame split. *)
Definition FrtPaintingSplitAt {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall u, mkPainting XB (top u))
  (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
    (mkPshPaintings (g X) PX)
    (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
  (SD: FrtSplitStep F top frames): Type :=
  forall t: (g X).(G0) M.+1,
  paintings.1.2 t =
  eq_existT_curried_dep
    (P := fun x => GDom (mkLayer F.(_frDepsA).(_restrFrames).2
      (painting := F.(_frDepsA).(_paintings).2) x))
    (Q := fun d => GDom (mkPainting XA d))
    (H := frames.1.2 t)
    (Hu := mkFrtLayerOfRestr F top frames.1 SD.1 SD.2.1 t)
    (Hv := rew [fun e => rew [fun d => GDom (mkPainting XA d)] e in
        mkPshPainting (g X) PX t = mkPaintingEqv TX (top t) (val t)]
      SD.2.2 t in paintings.2 t).

Lemma frtPaintingSplitOfRestr (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
  (F: FrtDeps M HD cB)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall u, mkPainting XB (descTop HD cB u))
  (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cB) val
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)):
  FrtPaintingSplitAt F XA XB TX PX (descTop HD cB) val
    ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD p cB Hlen F XA XB TX PX val Q E)
    (frtSplitHead HD p cB F (descTop HD cB)
      ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q)
      (frtSplitOfQ M HD p cB Hlen F Q)).
Proof.
  unfold FrtPaintingSplitAt.
  intro t. destruct p; now reflexivity.
Defined.

Section GeneratedPositivePainting.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB)
  (cB': DepsCohsChain (νDepsCohsAt (next S0)) (frtDcB FC))
  (Hlen': cohs3ChainLen (descChain (DescS HD)).2 = (cohsChainLen cB' + p.+1)%nat)
  (frames: FrtFramesNextType FC cB') (paintings: FrtPaintingsNextType FC cB' frames)
  (Hpair: FrtPairLawAt FC.(_fcF) (frtTopNext FC cB'))
  (HR: FrtRestr0At FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair)
  (Hsplit: forall t, frames.2 t =
    (=frames.1.2 t; mkFrtLayerOfRestr FC.(_fcF) (frtTopNext FC cB') frames.1 Hpair HR t))
  (Qprev: FrtRestrPrevData FC cB' Hlen' frames paintings)
  (HP: FrtRestrLayerStepAtChosen FC cB' Hlen' frames paintings Hpair HR Qprev).

Let F1 := mkFrtDepsOf FC cB' frames paintings.
Let top1 := descTop (DescS HD) cB'.
Let prev1 := (frtRestrPrevBlock FC cB' Hlen' frames paintings).(FrtRestrFramesDef) Qprev.
Let pair1: FrtPairLawAt F1 top1 := fun epsilon t =>
  descCellPairRestrAt (DescS HD) cB' p.+1 (⇓ F1.(_frBound)) Hlen' epsilon t.
Let hr1: FrtRestr0At F1 top1 prev1 pair1 := fun epsilon t =>
  frtRestrCell FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev
    0 leR_O (⇓ F1.(_frBound)) epsilon t
    (HP 0 leR_O (⇓ F1.(_frBound)) epsilon t).

Context
  (XCA1: DepsCohsExtension p.+1 k (trDepsCohsA (frtTrBase FC)))
  (XCB1: DepsCohsExtension p.+1 k (frtDcB FC))
  (TCX1: TrDepsCohsExtension (frtTrCohs FC) XCA1 XCB1)
  (EPA0: DepsCohsExtension p.+1 k (pshDepsCohs (g X) (frtPshCohs FC)))
  (CPA0: mkCohPaintingTypes EPA0) (C2A0: mkCoh2FrameTypes CPA0).
Let PC2: PshDepsCohs2 (g X) M p.+1 k :=
  {| _pshDepsCohs := frtPshCohs FC; _pExtraDepsCohs := EPA0;
     _pCohPaintings := CPA0; _pCoh2Frames := C2A0;
     _pshRestrCohs := FC.(_fcPshCohs) |}.
Context (PCX1: PshDepsCohsExtension (g X) M PC2 XCA1).
Let XA1 := mkExtraDeps XCA1.
Let XB1 := mkExtraDeps XCB1.
Let TX1 := mkTrExtraDeps TCX1.
Let PX1 := mkPshExtraDeps (g X) PCX1.
Let rpA1 := mkRestrPaintings XCA1.
Let rpB1 := mkRestrPaintings XCB1.
Let trRp1 := mkTrRestrPaintings TCX1.
Let pshRp1 := mkPshRestrPaintings (g X) PCX1.
Context
  (val1: forall t, mkPainting XB1 (top1 t))
  (E1: FrtPaintingTopType F1 TX1 PX1 top1 val1
    (mkFrtFrameStep F1 top1 prev1
      (fun t => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 t))).

Context
  (PS: FrtPaintingSplitAt FC.(_fcF) FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX)
    (frtTopNext FC cB')
    ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
      (fun u => (descCell (DescS HD) u).2)).2)
    frames paintings (Hpair; (HR; Hsplit))).
Context (q: nat) (Hq: q <= k) (Hqp: q + p.+1 <= M.+1)
  (epsilon: arity) (t: (g X).(G0) M.+2).
Let R := fun d => GDom (mkPainting FC.(_fcXA) d).
Let RB := fun d => GDom (mkPainting FC.(_fcXB) d).
Let face := (g X).(GFace) M.+1 (q + p.+1) Hqp epsilon t.
Let BQ := descQcells cB' Hlen' q Hq Hqp epsilon t.
Context (BPainting: rew [RB] BQ in
  (mkCellValuesOf M.+1 (cohsChainExt cB')
    (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).2 face =
  rpB1.2 q Hq epsilon (top1 t).1 ((top1 t).2; val1 t)).

Definition frtPositivePaintingEdgeA := F1.(_frPaintings).2 face.
Definition frtPositivePaintingEdgeD :=
  sigT_map_eq (P := RB) (Q := R) (f := fun d => F1.(_frFrameEqvs).2 d)
    (fun d c => F1.(_frPaintingEqvs).2 d c) BPainting.
Definition frtPositivePaintingEdgeT :=
  trRp1.2 q Hq epsilon (top1 t).1 ((top1 t).2; val1 t).
Definition frtPositivePaintingEdgeP := pshRp1.2 q Hq Hqp epsilon t.
Definition frtPositivePaintingEdgeN :=
  sigT_map_eq
    (P := fun d => GDom (mkPainting (F1.(_frDepsA); XA1)%extradepsrestr d))
    (Q := R) (f := fun d => F1.(_frDepsA).(_restrFrames).2 q Hq epsilon d)
    (fun d c => rpA1.2 q Hq epsilon d c)
    (mkFrtPaintingStepDown F1 XA1 XB1 TX1 PX1 top1 val1 prev1
      (fun u => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 u) E1 t).

Definition frtPositivePaintingRouteLeft :=
  (frtPositivePaintingEdgeA ⊙[R] frtPositivePaintingEdgeD)
    ⊙[R] frtPositivePaintingEdgeT.
Definition frtPositivePaintingRouteRight :=
  frtPositivePaintingEdgeP ⊙[R] frtPositivePaintingEdgeN.

(** Restriction-painting data supplies all five edges. The higher input
    is indexed by the frame cell emitted by the preceding block. *)
Definition frtPositivePaintingRoute
  (Hparent: FrtRestrPaintingCellSelected FC cB' Hlen' frames paintings
    Hpair HR Hsplit Qprev q Hq Hqp epsilon t (HP q Hq Hqp epsilon t)
    frtPositivePaintingRouteLeft frtPositivePaintingRouteRight) :=
  frtRestrCell_dep_edges FC cB' Hlen' frames paintings Hpair HR Hsplit
    Qprev q Hq Hqp epsilon t (HP q Hq Hqp epsilon t) R
    frtPositivePaintingEdgeA frtPositivePaintingEdgeD frtPositivePaintingEdgeT
    frtPositivePaintingEdgeP frtPositivePaintingEdgeN Hparent.
Let Fprev := proj1FrtDeps F1.
Let lowerTop := descTop (DescS HD) (DepsCohsChainCons cB').
Let previousPainting := fun u =>
  mkFrtPaintingStepDown F1 XA1 XB1 TX1 PX1 top1 val1 prev1
    (fun v => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 v) E1 u.
Let lowerPaintings := mkFrtPaintingsOfRestr M.+1 (DescS HD) p
  (DepsCohsChainCons cB') (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p)) Fprev
  (F1.(_frDepsA); XA1)%extradepsrestr
  (mkDepsRestr (depsCohs := frtDcB FC); XB1)%extradepsrestr
  (AddTrDep (frTr F1) TX1) (AddPshDep (g X) M.+1 (frtPshDeps F1) PX1)
  (fun u => ((top1 u).2; val1 u)) Qprev previousPainting.
Let LA := fun x => GDom (mkLayer (frTr FC.(_fcF)).(_depsA).(_restrFrames).2
  (painting := (frTr FC.(_fcF)).(_depsA).(_paintings).2) x).
Let LB := fun x => GDom (mkLayer (frTr FC.(_fcF)).(_depsB).(_restrFrames).2
  (painting := (frTr FC.(_fcF)).(_depsB).(_paintings).2) x).
Let lowerFrameMap := fun a => (mkFrameEqvs (proj1TrDepsRestr (frTr FC.(_fcF)))).2 a.
Let layerMap := fun a l => mkTrLayerEquiv (frTr FC.(_fcF)).(_paintingEqvs)
  (frTr FC.(_fcF)).(_trRestrs) a l.

(** The previous painting prefix uses precisely the frame encoding in
    the selected restriction route. *)
Lemma frtPositivePaintingPreviousSplit (u: (g X).(G0) M.+2):
  lowerPaintings.1.2 u =
  eq_existT_curried_dep
    (P := fun x => GDom (mkLayer Fprev.(_frDepsA).(_restrFrames).2
      (painting := Fprev.(_frDepsA).(_paintings).2) x))
    (Q := fun d => GDom (mkPainting (F1.(_frDepsA); XA1)%extradepsrestr d))
    (H := (frtRestrPrevFrames FC cB' Hlen' frames paintings Qprev).2 u)
    (Hu := mkFrtLayerOfRestr Fprev lowerTop
      (frtRestrPrevFrames FC cB' Hlen' frames paintings Qprev)
      (frtPairLawPrev FC cB' Hlen' frames paintings)
      (frtRestrPrevZero FC cB' Hlen' frames paintings Hpair HR Qprev) u)
    (Hv := rew [fun e => rew [fun d =>
        GDom (mkPainting (F1.(_frDepsA); XA1)%extradepsrestr d)] e in
      mkPshPainting (g X) (AddPshDep (g X) M.+1 (frtPshDeps F1) PX1) u =
      mkPaintingEqv (AddTrDep (frTr F1) TX1) (top1 u).1 ((top1 u).2; val1 u)]
      (frtRestrPrevPair FC cB' Hlen' frames paintings Hpair HR Qprev u) in previousPainting u).
Proof.
  unfold lowerPaintings, previousPainting, Fprev, lowerTop, F1, prev1.
  unfold FrtRestrPrevData, frtRestrPrevPair, frtRestrPrevZero, frtRestrPrevClause,
    frtRestrPrevFrames, frtRestrPrevBlock in *.
  destruct p; now reflexivity.
Defined.

Definition frtPositivePaintingBPair :=
  eq_existT_curried_dep (P := LB) (Q := RB)
    (H := projT1_eq BQ) (Hu := projT2_eq BQ)
    (Hv := rew [fun e => rew [RB] e in
      (mkCellValuesOf M.+1 (cohsChainExt cB')
        (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).2 face =
      rpB1.2 q Hq epsilon (top1 t).1 ((top1 t).2; val1 t)]
      (eq_sym (totalPathReencode BQ)) in BPainting).

(** The D edge is the mapped combined canonical painting, with the
    displayed path moved along exactly [sigT_total_map_cell]. *)
Lemma frtPositivePaintingMappedB:
  eq_existT_curried_dep (P := LA) (Q := R)
    (H := f_equal lowerFrameMap (projT1_eq BQ))
    (Hu := sigT_map_eq (P := LB) (Q := LA) (f := lowerFrameMap)
      layerMap (projT2_eq BQ))
    (Hv := rew [fun e => rew [R] e in
      F1.(_frPaintingEqvs).2
        ((mkCellFramesOf M.+1 (extChainDeps (cohsChainExt cB'))
          (descCells (DescS HD))).2 face)
        ((mkCellValuesOf M.+1 (cohsChainExt cB')
          (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).2 face) =
      F1.(_frPaintingEqvs).2
        ((mkDepsRestr (depsCohs := frtDcB FC)).(_restrFrames).2 q Hq epsilon (top1 t).1)
        (rpB1.2 q Hq epsilon (top1 t).1 ((top1 t).2; val1 t))]
      (sigT_total_map_cell (P := LB) (Q := LA) lowerFrameMap layerMap BQ) in
      frtPositivePaintingEdgeD) =
  sigT_map_eq
    (P := fun a => GDom ((mkPaintings FC.(_fcXB)).1.2 a))
    (Q := fun a => GDom ((mkPaintings FC.(_fcXA)).1.2 a))
    (f := lowerFrameMap) (fun a c => (mkPaintingEqvs FC.(_fcTX)).1.2 a c)
    frtPositivePaintingBPair.
Proof.
  now exact (sigT_total_map_cell_dep (P := LB) (Q := LA) (R := RB) (S := R)
    lowerFrameMap layerMap (fun d c => F1.(_frPaintingEqvs).2 d c) BQ BPainting).
Defined.

Let PA := fun a => GDom ((mkPaintings FC.(_fcXA)).1.2 a).
Let PB := fun a => GDom ((mkPaintings FC.(_fcXB)).1.2 a).
Let valueA := (mkPshPaintings (g X) FC.(_fcPX)).1.2.
Let valueB := (mkCellValuesOf M.+1 (cohsChainExt cB')
  (descCells (DescS HD)) (fun u => (descCell (DescS HD) u).2)).1.2.
Let frameA := (mkPshFrames (g X) (frtPshDeps FC.(_fcF))).1.2.
Let frameB := fun u => (getFrame (extChainDeps (cohsChainExt cB'))
  (descCells (DescS HD) u)).1.
Let index := pshFaceDimIrr (g X) (eq_sym (plus_n_Sm q p))
  (Hq := Hqp) (Hq' := leR_add_shift Hqp) epsilon t.
Let childFace := (g X).(GFace) M.+1 (q.+1 + p) (leR_add_shift Hqp) epsilon t.
Let childQ := descQcells (DepsCohsChainCons cB')
  (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p))
  q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t.
Let childValueB := rpB1.1.2 q.+1 (⇑ Hq) epsilon (top1 t).1.1
  ((top1 t).1.2; ((top1 t).2; val1 t)).
Let indexCell := descQcellsCons (DescS HD) cB' Hlen' q Hq Hqp
  (⇑ Hq) (leR_add_shift Hqp) epsilon t •
  f_equal (fun c => c • childQ)
    (f_equal_compose
      (fun u => getFrame (extChainDeps (cohsChainExt cB')) (descCells (DescS HD) u))
      (fun z: mkFrame (frtDcB FC).(_deps) => z.1) index).
Context (BChild: rew [PB] childQ in valueB childFace = childValueB)
  (BC: DPathCellOver (P := PB) frtPositivePaintingBPair
    (f_equal_dep_sigT (Q := PB) frameB valueB index ⊙[PB] BChild) indexCell).
Let childD := sigT_map_eq (P := PB) (Q := PA) (f := lowerFrameMap)
  (fun a c => (mkPaintingEqvs FC.(_fcTX)).1.2 a c) BChild.
Let childT := trRp1.1.2 q.+1 (⇑ Hq) epsilon (top1 t).1.1
  ((top1 t).1.2; ((top1 t).2; val1 t)).
Let childP := pshRp1.1.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t.
Let childN := sigT_map_eq
  (P := fun a => GDom ((mkPaintings (F1.(_frDepsA); XA1)%extradepsrestr).1.2 a))
  (Q := PA) (f := Fprev.(_frDepsA).(_restrFrames).2 q.+1 (⇑ Hq) epsilon)
  (fun a c => rpA1.1.2 q.+1 (⇑ Hq) epsilon a c) (lowerPaintings.1.2 t).

(** The actual generated restriction-painting constructors turn the
    selected parent certificate into the positive previous-stage clause. *)
Lemma frtPositivePaintingPrevious
  (Hparent: FrtRestrPaintingCellSelected FC cB' Hlen' frames paintings
    Hpair HR Hsplit Qprev q Hq Hqp epsilon t (HP q Hq Hqp epsilon t)
    frtPositivePaintingRouteLeft frtPositivePaintingRouteRight):
  DPathCellOver (P := PA)
    ((paintings.1.2 childFace ⊙[PA] childD) ⊙[PA] childT)
    (childP ⊙[PA] childN)
    (frtRestrPrevClause FC cB' Hlen' frames paintings Hpair HR Qprev
      q.+1 (⇑ Hq) (leR_add_shift Hqp) epsilon t).
Proof.
  pose proof (frtPositivePaintingRoute Hparent) as ALL.
  unfold frtRestrPaintingEdgeA, frtRestrPaintingEdgeD, frtRestrPaintingEdgeT,
    frtRestrPaintingEdgeP, frtRestrPaintingEdgeN in ALL.
  rewrite <- (PS face), frtPositivePaintingMappedB in ALL.
  pose proof (mkPshRestrPaintingMerged_comp (g X) PC2 PCX1
    q Hq Hqp epsilon t) as EP.
  rewrite EP in ALL.
  rewrite sigT_selected_map_cell_dep in ALL.
  rewrite <- (frtPositivePaintingPreviousSplit t) in ALL.
  now exact (frtRestrCarriedPaintingPrevious FC cB' Hlen' frames paintings
    Hpair HR Qprev q Hq Hqp epsilon t frtPositivePaintingBPair BChild BC
    childT childP childN ALL).
Defined.

End GeneratedPositivePainting.



(** Each painting split names the corresponding stored frame split. *)
Fixpoint FrtPaintingSplitChainAt (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dcB: DepsCohs p k} (cb: DepsCohsChain (νDepsCohsAt S0) dcB)
    (F: FrtDeps M HD cb)
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
    (TX: TrDepsExtension (frTr F) XA XB)
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
    (val: forall t, mkPainting XB (top t))
    (frames: FrtFramesType F top)
    (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
      (mkPshPaintings (g X) PX)
      (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
    (SD: FrtSplitDataAt M HD p cb F top frames), Type.
Proof.
  destruct p as [|p]; intros k dcB cb F XA XB TX PX top val frames paintings SD.
  - now exact (FrtPaintingSplitAt F XA XB TX PX top val frames paintings SD).
  - now exact ({_: FrtPaintingSplitChainAt M XpB0 S0 HD p k.+1 _
        (DepsCohsChainCons cb) (proj1FrtDeps F)
        (F.(_frDepsA); XA)%extradepsrestr
        (mkDepsRestr (depsCohs := dcB); XB)%extradepsrestr
        (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
        (fun t => (top t).1) (fun t => ((top t).2; val t))
        frames.1 paintings.1 SD.1 &T
      FrtPaintingSplitAt F XA XB TX PX top val frames paintings SD.2}).
Defined.

Lemma frtPaintingSplitChainOfRestr (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cb: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (val: forall t, mkPainting XB (descTop HD cb t))
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef))
  (E: FrtPaintingTopType F TX PX (descTop HD cb) val
    ((mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q)):
  FrtPaintingSplitChainAt M HD p cb F XA XB TX PX (descTop HD cb) val
    ((mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q)
    (mkFrtPaintingsOfRestr M HD p cb Hlen F XA XB TX PX val Q E)
    (frtSplitOfQ M HD p cb Hlen F Q).
Proof.
  revert k dcB cb Hlen F XA XB TX PX val Q E.
  induction p as [|p IH]; intros k dcB cb Hlen F XA XB TX PX val Q E.
  - now exact (frtPaintingSplitOfRestr M HD 0 cb Hlen F XA XB TX PX val Q E).
  - split.
    + now apply IH.
    + now exact (frtPaintingSplitOfRestr M HD p.+1 cb Hlen F XA XB TX PX val Q E).
Defined.

Definition frtPaintingSplitChainHead (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cb: DepsCohsChain (νDepsCohsAt S0) dcB) (F: FrtDeps M HD cb)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
  (XB: DepsRestrExtension p.+1 k (mkDepsRestr (depsCohs := dcB)))
  (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (top: (g X).(G0) M.+1 -> mkFrame (mkDepsRestr (depsCohs := dcB)))
  (val: forall t, mkPainting XB (top t)) (frames: FrtFramesType F top)
  (paintings: mkFrtPaintingTypes M.+1 frames (mkPaintingEqvs TX)
    (mkPshPaintings (g X) PX)
    (mkCellValues M.+1 (mkDepsRestr (depsCohs := dcB)) XB top val))
  (SD: FrtSplitDataAt M HD p cb F top frames)
  (PS: FrtPaintingSplitChainAt M HD p cb F XA XB TX PX top val frames paintings SD):
  FrtPaintingSplitAt F XA XB TX PX top val frames paintings
    (frtSplitHead HD p cb F top frames SD).
Proof. destruct p; [now exact PS | now exact PS.2]. Defined.

(** Read the clause from existing restriction data. This accessor chooses
    no new path; the successor case is its stored second projection. *)
Definition frtRestrictionClauseOf {M} {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {k} {dcB: DepsCohs p k}
  (cB: DepsCohsChain (νDepsCohsAt S0) dcB)
  (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cB + p)%nat)
  (F: FrtDeps M HD cB)
  (Q: (mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrDataDef)):
  mkFrtRestrTypeStep F.(_frFrames) F.(_frPshRestrs) F.(_frTrRestrs)
    (fun t => (descTop HD cB t).1)
    (fun t => ((mkFrtRestrTypesAndFrames M HD p cB Hlen F).(FrtRestrFramesDef) Q).1.2 t)
    (descQcells cB Hlen).
Proof. destruct p; [now exact Q | now exact Q.2]. Defined.

Section ExistingRestrictionPainting.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Let rpB := (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings).
Context (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let top := descTop HD cb.
Let val: forall t, mkPainting XB (top t) := fun t =>
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2.
Let nextFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Context (E: FrtPaintingTopType F TX PX top val nextFrames).
Let nextPaintings := mkFrtPaintingsOfRestr M HD p cb Hlen F XA XB TX PX val Q E.
Let PA := fun d => GDom (F.(_frDepsA).(_paintings).2 d).
Let PB := fun d => GDom ((mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(_paintings).2 d).
Context (q: nat) (Hq: q <= k) (Hdim: q + p <= M)
  (epsilon: arity) (t: (g X).(G0) M.+1).
Let face := (g X).(GFace) M (q + p) Hdim epsilon t.
Let bPainting := descCanonicalPaintingPaired HD q a Hlen Hq Hdim epsilon t.

Definition frtRestrictionPaintingLeft :=
  (F.(_frPaintings).2 face ⊙[PA]
    sigT_map_eq (P := PB) (Q := PA) (f := fun d => F.(_frFrameEqvs).2 d)
      (fun d c => F.(_frPaintingEqvs).2 d c) bPainting)
    ⊙[PA] trRp.2 q Hq epsilon (top t).1 ((top t).2; val t).
Definition frtRestrictionPaintingRight :=
  pshRp.2 q Hq Hdim epsilon t ⊙[PA]
    sigT_map_eq (P := fun d => GDom (mkPainting (F.(_frDepsA); XA)%extradepsrestr d))
      (Q := PA) (f := F.(_frDepsA).(_restrFrames).2 q Hq epsilon)
      (fun d c => rpA.2 q Hq epsilon d c) (nextPaintings.1.2 t).

(** Painting naturality is indexed by the clause already stored in Q.
    It can be generated after Q, without choosing or replacing that clause. *)
Definition FrtRestrictionPaintingSelected: Type :=
  DPathCellOver (P := PA) frtRestrictionPaintingLeft frtRestrictionPaintingRight
    (frtRestrictionClauseOf HD p cb Hlen F Q q Hq Hdim epsilon t).
End ExistingRestrictionPainting.

(** The selected certificates follow the existing restriction-data prefix.
    The next painting entry is the same dependent-pair constructor as the
    painting factory. *)
Fixpoint FrtRestrictionPaintingSelectedChain (M: nat) {XpB0: (νGpdAt M).(prefix)}
  {S0: νGpdFrom M XpB0} (HD: Desc (X := X) S0) (p: nat) {struct p}:
  forall {k} {dc3: DepsCohs3 p k}
    (a: DepsCohs3Chain (νDepsCohs3At S0) dc3)
    (Hlen: cohs3ChainLen (descChain HD).2
      = (cohsChainLen (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) + p)%nat)
    (F: FrtDeps M HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
    (XA: DepsRestrExtension p.+1 k F.(_frDepsA))
    (TX: TrDepsExtension (frTr F) XA (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps))
    (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
    (rpA: mkRestrPaintingTypes XA)
    (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA
      (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings))
    (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
    (Q: (mkFrtRestrTypesAndFrames M HD p
      (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrDataDef))
    (E: FrtPaintingTopType F TX PX
      (descTop HD (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)))
      (fun t => (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2)
      ((mkFrtRestrTypesAndFrames M HD p
        (cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)) Hlen F).(FrtRestrFramesDef) Q)), Type.
Proof.
  destruct p as [|p]; intros k dc3 a Hlen F XA TX PX rpA trRp pshRp Q E.
  - now exact (forall q (Hq: q <= k) (Hdim: q + 0 <= M)
      (epsilon: arity) (t: (g X).(G0) M.+1),
      FrtRestrictionPaintingSelected HD a Hlen F XA TX PX rpA trRp pshRp
        Q E q Hq Hdim epsilon t).
  - pose (cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a)).
    pose (Hchild := Hlen • eq_sym (plus_n_Sm (cohsChainLen cb) p)).
    pose (Fchild := proj1FrtDeps F).
    pose (previous := (mkFrtRestrTypesAndFrames M HD p
      (DepsCohsChainCons cb) Hchild Fchild).(FrtRestrFramesDef) Q.1).
    pose (top := descTop HD cb).
    pose (val := fun t => (deepCell (cohs3ChainDepsCohs2 a)
      (descCell (DescS HD) t)).2.2).
    pose (pair := fun epsilon t =>
      descCellPairRestrAt HD cb p.+1 (⇓ F.(_frBound)) Hlen epsilon t).
    pose (zero := fun epsilon t => Q.2 0 leR_O (⇓ F.(_frBound)) epsilon t).
    pose (Echild := fun t => mkFrtPaintingStepDown F XA
      (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps) TX PX top val previous
      (fun u => mkFrtLayerOfRestr F top previous pair zero u) E t).
    now exact ({_: FrtRestrictionPaintingSelectedChain M XpB0 S0 HD p
        k.+1 (proj1DepsCohs3 dc3) (DepsCohs3ChainCons a) Hchild Fchild
        (F.(_frDepsA); XA)%extradepsrestr
        (AddTrDep (frTr F) TX) (AddPshDep (g X) M (frtPshDeps F) PX)
        rpA.1 trRp.1 pshRp.1 Q.1 Echild &T
      forall q (Hq: q <= k) (Hdim: q + p.+1 <= M)
        (epsilon: arity) (t: (g X).(G0) M.+1),
        FrtRestrictionPaintingSelected HD a Hlen F XA TX PX rpA trRp pshRp
          Q E q Hq Hdim epsilon t}).
Defined.

Section RestrictionPaintingZeroAtExisting.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  (HD: Desc (X := X) S0) {p k} {dc3: DepsCohs3 p k}
  (a: DepsCohs3Chain (νDepsCohs3At S0) dc3).
Let cb := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a).
Context (Hlen: cohs3ChainLen (descChain HD).2 = (cohsChainLen cb + p)%nat)
  (F: FrtDeps M HD cb)
  (XA: DepsRestrExtension p.+1 k F.(_frDepsA)).
Let XB := (mkDepsCohs dc3.(_depsCohs2)).(_extraDeps).
Let rpB := (mkDepsCohs dc3.(_depsCohs2)).(_restrPaintings).
Context (TX: TrDepsExtension (frTr F) XA XB)
  (PX: PshDepsExtension (g X) M (frtPshDeps F) XA)
  (rpA: mkRestrPaintingTypes XA)
  (trRp: mkTrRestrPaintingTypes (frTr F) TX rpA rpB)
  (pshRp: mkPshRestrPaintingTypes (g X) (frtPshDeps F) PX rpA)
  (Q: (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrDataDef)).
Let top := descTop HD cb.
Let val: forall t, mkPainting XB (top t) := fun t =>
  (deepCell (cohs3ChainDepsCohs2 a) (descCell (DescS HD) t)).2.2.
Let nextFrames := (mkFrtRestrTypesAndFrames M HD p cb Hlen F).(FrtRestrFramesDef) Q.
Context (E: FrtPaintingTopType F TX PX top val nextFrames).
Let nextPaintings := mkFrtPaintingsOfRestr M HD p cb Hlen F XA XB TX PX val Q E.
Let PA := fun d => GDom (F.(_frDepsA).(_paintings).2 d).
Let PB := fun d => GDom
  ((mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(_paintings).2 d).
Let HrpB := descCanonicalZeroRpChoice dc3.
Context (HrpA: FrtRpZeroType XA rpA)
  (HtrRp: TrRpZeroType (frTr F) TX trRp HrpA HrpB)
  (HpshRp: PshRpZeroType (frtPshDeps F) PX pshRp HrpA).

(** At zero, the stored restriction clause supplies the base of the
    generated painting proof. The stage split only exposes its computed
    frame and painting entries. *)
Lemma frtRestrictionPaintingZero (epsilon: arity) (t: (g X).(G0) M.+1):
  FrtRestrictionPaintingSelected HD a Hlen F XA TX PX rpA trRp pshRp Q E
    0 leR_O (⇓ F.(_frBound)) epsilon t.
Proof.
  destruct p as [|pred_p].
  all: pose (pairLaw := fun epsilon t =>
    descCellPairRestrAt HD cb _ (⇓ F.(_frBound)) Hlen epsilon t).
  all: pose (clause := fun epsilon t =>
    frtRestrictionClauseOf HD _ cb Hlen F Q 0 leR_O
      (⇓ F.(_frBound)) epsilon t).
  all: pose proof (frtRestrPaintingStepSelectedOf M XpB0 S0 HD _ k _ cb F
    XA XB TX PX rpA rpB trRp pshRp HrpA HrpB HtrRp HpshRp
    top val nextFrames.1 pairLaw clause E epsilon t) as core.
  all: pose proof (sigT_map_eq_target_adjust
    (P := PB) (Q := PA) (f := fun d => F.(_frFrameEqvs).2 d)
    (fun d c => F.(_frPaintingEqvs).2 d c)
    (projT2_eq (pairLaw epsilon t))
    (HrpB leR_O epsilon (top t).1 ((top t).2; val t))) as HMap.
  all: now exact (rew <- [fun dh => DPathCellOver (P := PA)
      ((F.(_frPaintings).2
          ((g X).(GFace) M _ (⇓ F.(_frBound)) epsilon t)
        ⊙[PA] dh)
        ⊙[PA] trRp.2 0 leR_O epsilon (top t).1 ((top t).2; val t))
      (pshRp.2 0 leR_O (⇓ F.(_frBound)) epsilon t ⊙[PA]
        sigT_map_eq
          (P := fun d => GDom (mkPainting (F.(_frDepsA); XA)%extradepsrestr d))
          (Q := PA) (f := F.(_frDepsA).(_restrFrames).2 0 leR_O epsilon)
          (fun d c => rpA.2 0 leR_O epsilon d c) (nextPaintings.1.2 t))
      (clause epsilon t)] HMap in core).
Defined.
End RestrictionPaintingZeroAtExisting.

Section GeneratedSelectedNaturalityChild.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB).
Context (XCB1: DepsCohsExtension p.+1 k (frtDcB FC))
  (CPB1: mkCohPaintingTypes XCB1) (C2B1: mkCoh2FrameTypes CPB1).
Let dc2B1: DepsCohs2 p.+1 k :=
  {| _depsCohs := frtDcB FC; _extraDepsCohs := XCB1;
     _cohPaintings := CPB1; _coh2Frames := C2B1 |}.
Context (XCB2: DepsCohs2Extension p.+1 k dc2B1)
  (C2PB1: mkCoh2PaintingTypes XCB2).
Let dc3B1: DepsCohs3 p.+1 k :=
  {| _depsCohs2 := dc2B1; _extraDepsCohs2 := XCB2; _coh2Paintings := C2PB1 |}.
Context (a1: DepsCohs3Chain (νDepsCohs3At (next S0)) dc3B1).
Let cB' := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a1).
Context (Hlen': cohs3ChainLen (descChain (DescS HD)).2
  = (cohsChainLen cB' + p.+1)%nat).
Context (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
  (PSChain: FrtPaintingSplitChainAt M HD p cB FC.(_fcF)
    FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX) (frtTopNext FC cB')
    ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
      (fun u => (descCell (DescS HD) u).2)).2) frames paintings SD).
Let block := mkFrtStepTypesAndRestrNext M HD p cB FC cB' Hlen' frames paintings SD.
Context (sp: block.(StepInput)).
Let head := frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD.
Let Hpair := head.1.
Let HR := head.2.1.
Let Hsplit := head.2.2.
Let Qprev := block.(StepPrevious) sp.
Let HP := block.(StepLayer) sp.
Let Qnext := RestrNext block sp.

Let F1 := mkFrtDepsOf FC cB' frames paintings.
Let top1 := descTop (DescS HD) cB'.
Let prev1 := (frtRestrPrevBlock FC cB' Hlen' frames paintings).(FrtRestrFramesDef) Qprev.
Let pair1: FrtPairLawAt F1 top1 := fun epsilon t =>
  descCellPairRestrAt (DescS HD) cB' p.+1 (⇓ F1.(_frBound)) Hlen' epsilon t.
Let hr1: FrtRestr0At F1 top1 prev1 pair1 := fun epsilon t =>
  frtRestrCell FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev
    0 leR_O (⇓ F1.(_frBound)) epsilon t
    (HP 0 leR_O (⇓ F1.(_frBound)) epsilon t).

Context
  (XCA1: DepsCohsExtension p.+1 k (trDepsCohsA (frtTrBase FC)))
  (TCX1: TrDepsCohsExtension (frtTrCohs FC) XCA1 XCB1)
  (EPA0: DepsCohsExtension p.+1 k (pshDepsCohs (g X) (frtPshCohs FC)))
  (CPA0: mkCohPaintingTypes EPA0) (C2A0: mkCoh2FrameTypes CPA0).
Let PC2: PshDepsCohs2 (g X) M p.+1 k :=
  {| _pshDepsCohs := frtPshCohs FC; _pExtraDepsCohs := EPA0;
     _pCohPaintings := CPA0; _pCoh2Frames := C2A0;
     _pshRestrCohs := FC.(_fcPshCohs) |}.
Context (PCX1: PshDepsCohsExtension (g X) M PC2 XCA1).
Let XA1 := mkExtraDeps XCA1.
Let XB1 := mkExtraDeps XCB1.
Let TX1 := mkTrExtraDeps TCX1.
Let PX1 := mkPshExtraDeps (g X) PCX1.
Let rpA1 := mkRestrPaintings XCA1.
Let rpB1 := mkRestrPaintings XCB1.
Let trRp1 := mkTrRestrPaintings TCX1.
Let pshRp1 := mkPshRestrPaintings (g X) PCX1.
Let val1: forall u, mkPainting XB1 (top1 u) := fun u =>
  (deepCell (cohs3ChainDepsCohs2 a1) (descCell (DescS (DescS HD)) u)).2.2.
Context (E1: FrtPaintingTopType F1 TX1 PX1 top1 val1
    (mkFrtFrameStep F1 top1 prev1
      (fun t => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 t))).

Let PS := frtPaintingSplitChainHead M HD p cB FC.(_fcF)
  FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX) (frtTopNext FC cB')
  ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
    (fun u => (descCell (DescS HD) u).2)).2) frames paintings SD PSChain.
Let Fchild := proj1FrtDeps F1.
Let Echild := fun t => mkFrtPaintingStepDown F1 XA1 XB1 TX1 PX1 top1 val1 prev1
  (fun u => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 u) E1 t.
Context (NP: forall q (Hq: q <= k) (Hdim: q + p.+1 <= M.+1)
  (epsilon: arity) (t: (g X).(G0) M.+2),
  FrtRestrictionPaintingSelected (DescS HD) a1 Hlen' F1 XA1 TX1 PX1
    rpA1 trRp1 pshRp1 Qnext E1 q Hq Hdim epsilon t).

(** The previous block is already stored in sp. Its zero clause is
    generated directly; positive clauses consume the parent's selected
    naturality and the canonical Cons witness. *)
Lemma frtSelectedNaturalityChild:
  forall j (Hj: j <= k.+1) (Hdim: j + p <= M.+1)
    (epsilon: arity) (t: (g X).(G0) M.+2),
  FrtRestrictionPaintingSelected (DescS HD) (DepsCohs3ChainCons a1)
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p)) Fchild
    (F1.(_frDepsA); XA1)%extradepsrestr (AddTrDep (frTr F1) TX1)
    (AddPshDep (g X) M.+1 (frtPshDeps F1) PX1)
    rpA1.1 trRp1.1 pshRp1.1 Qprev Echild j Hj Hdim epsilon t.
Proof.
  generalize dependent k.
  clear - X M XpB0 S0 HD p.
  destruct p as [|pred_p]; intros k dcB cB FC XCB1 CPB1 C2B1 dc2B1 XCB2 C2PB1
    dc3B1 a1 cB' Hlen' frames paintings SD PSChain block sp head Hpair HR Hsplit
    Qprev HP Qnext F1 top1 prev1 pair1 hr1 XCA1 TCX1 EPA0 CPA0 C2A0 PC2 PCX1
    XA1 XB1 TX1 PX1 rpA1 rpB1 trRp1 pshRp1 val1 E1 PS Fchild Echild NP.
  all: intros j Hj Hdim epsilon t; destruct j as [|q].
  all: try (now exact (frtRestrictionPaintingZero (DescS HD) (DepsCohs3ChainCons a1)
    _ Fchild (F1.(_frDepsA); XA1)%extradepsrestr (AddTrDep (frTr F1) TX1)
    (AddPshDep (g X) M.+1 (frtPshDeps F1) PX1)
    rpA1.1 trRp1.1 pshRp1.1 Qprev Echild
    (rpZeroChainOf _ (AddCohDep (trDepsCohsA (frtTrBase FC)) XCA1)).2
    (trRpZeroChainOf _ (AddTrCohDep (frtTrCohs FC) TCX1)).2
    (pshRpZeroChainOf _ (AddPshCohDep (g X) M PC2 PCX1)).2 epsilon t)).
  all: pose (parentDim := leR_eq (plus_n_Sm q _) Hdim).
  all: now exact (frtPositivePaintingPrevious FC cB' Hlen' frames paintings
    Hpair HR Hsplit Qprev HP XCA1 XCB1 TCX1 EPA0 CPA0 C2A0 PCX1 val1 E1 PS
    q (⇓ Hj) parentDim epsilon t
    (descCanonicalPaintingPaired (DescS HD) q a1 Hlen' (⇓ Hj) parentDim epsilon t)
    (descCanonicalPaintingPaired (DescS HD) q.+1 (DepsCohs3ChainCons a1)
      _ Hj Hdim epsilon t)
    (descCanonicalPaintingConsCell_dep (DescS HD) a1 Hlen'
      q (⇓ Hj) parentDim epsilon t)
    (NP q (⇓ Hj) parentDim epsilon t)).
Defined.
End GeneratedSelectedNaturalityChild.

Section GeneratedSelectedNaturalityRecursion.
Context {M} {XpB0: (νGpdAt M).(prefix)} {S0: νGpdFrom M XpB0}
  {HD: Desc (X := X) S0} {p k} {dcB: DepsCohs p k}
  {cB: DepsCohsChain (νDepsCohsAt S0) dcB} (FC: FrtDepsCohs M HD cB).
Context (XCB1: DepsCohsExtension p.+1 k (frtDcB FC))
  (CPB1: mkCohPaintingTypes XCB1) (C2B1: mkCoh2FrameTypes CPB1).
Let dc2B1: DepsCohs2 p.+1 k :=
  {| _depsCohs := frtDcB FC; _extraDepsCohs := XCB1;
     _cohPaintings := CPB1; _coh2Frames := C2B1 |}.
Context (XCB2: DepsCohs2Extension p.+1 k dc2B1)
  (C2PB1: mkCoh2PaintingTypes XCB2).
Let dc3B1: DepsCohs3 p.+1 k :=
  {| _depsCohs2 := dc2B1; _extraDepsCohs2 := XCB2; _coh2Paintings := C2PB1 |}.
Context (a1: DepsCohs3Chain (νDepsCohs3At (next S0)) dc3B1).
Let cB' := cohs2ChainDepsCohs (cohs3ChainDepsCohs2 a1).
Context (Hlen': cohs3ChainLen (descChain (DescS HD)).2
  = (cohsChainLen cB' + p.+1)%nat).
Context (frames: FrtFramesNextType FC cB')
  (paintings: FrtPaintingsNextType FC cB' frames)
  (SD: FrtSplitDataAt M HD p cB FC.(_fcF) (frtTopNext FC cB') frames)
  (PSChain: FrtPaintingSplitChainAt M HD p cB FC.(_fcF)
    FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX) (frtTopNext FC cB')
    ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
      (fun u => (descCell (DescS HD) u).2)).2) frames paintings SD).
Let block := mkFrtStepTypesAndRestrNext M HD p cB FC cB' Hlen' frames paintings SD.
Context (sp: block.(StepInput)).
Let head := frtSplitHead HD p cB FC.(_fcF) (frtTopNext FC cB') frames SD.
Let Hpair := head.1.
Let HR := head.2.1.
Let Hsplit := head.2.2.
Let Qprev := block.(StepPrevious) sp.
Let HP := block.(StepLayer) sp.
Let Qnext := RestrNext block sp.

Let F1 := mkFrtDepsOf FC cB' frames paintings.
Let top1 := descTop (DescS HD) cB'.
Let prev1 := (frtRestrPrevBlock FC cB' Hlen' frames paintings).(FrtRestrFramesDef) Qprev.
Let pair1: FrtPairLawAt F1 top1 := fun epsilon t =>
  descCellPairRestrAt (DescS HD) cB' p.+1 (⇓ F1.(_frBound)) Hlen' epsilon t.
Let hr1: FrtRestr0At F1 top1 prev1 pair1 := fun epsilon t =>
  frtRestrCell FC cB' Hlen' frames paintings Hpair HR Hsplit Qprev
    0 leR_O (⇓ F1.(_frBound)) epsilon t
    (HP 0 leR_O (⇓ F1.(_frBound)) epsilon t).

Context
  (XCA1: DepsCohsExtension p.+1 k (trDepsCohsA (frtTrBase FC)))
  (TCX1: TrDepsCohsExtension (frtTrCohs FC) XCA1 XCB1)
  (EPA0: DepsCohsExtension p.+1 k (pshDepsCohs (g X) (frtPshCohs FC)))
  (CPA0: mkCohPaintingTypes EPA0) (C2A0: mkCoh2FrameTypes CPA0).
Let PC2: PshDepsCohs2 (g X) M p.+1 k :=
  {| _pshDepsCohs := frtPshCohs FC; _pExtraDepsCohs := EPA0;
     _pCohPaintings := CPA0; _pCoh2Frames := C2A0;
     _pshRestrCohs := FC.(_fcPshCohs) |}.
Context (PCX1: PshDepsCohsExtension (g X) M PC2 XCA1).
Let XA1 := mkExtraDeps XCA1.
Let XB1 := mkExtraDeps XCB1.
Let TX1 := mkTrExtraDeps TCX1.
Let PX1 := mkPshExtraDeps (g X) PCX1.
Let rpA1 := mkRestrPaintings XCA1.
Let rpB1 := mkRestrPaintings XCB1.
Let trRp1 := mkTrRestrPaintings TCX1.
Let pshRp1 := mkPshRestrPaintings (g X) PCX1.
Let val1: forall u, mkPainting XB1 (top1 u) := fun u =>
  (deepCell (cohs3ChainDepsCohs2 a1) (descCell (DescS (DescS HD)) u)).2.2.
Context (E1: FrtPaintingTopType F1 TX1 PX1 top1 val1
    (mkFrtFrameStep F1 top1 prev1
      (fun t => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 t))).

Let PS := frtPaintingSplitChainHead M HD p cB FC.(_fcF)
  FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX) (frtTopNext FC cB')
  ((mkCellValuesOf M.+1 (cohsChainExt cB') (descCells (DescS HD))
    (fun u => (descCell (DescS HD) u).2)).2) frames paintings SD PSChain.
Let Fchild := proj1FrtDeps F1.
Let Echild := fun t => mkFrtPaintingStepDown F1 XA1 XB1 TX1 PX1 top1 val1 prev1
  (fun u => mkFrtLayerOfRestr F1 top1 prev1 pair1 hr1 u) E1 t.
Lemma frtSelectedNaturalityChildChain
  (NP: forall q (Hq: q <= k) (Hdim: q + p.+1 <= M.+1)
  (epsilon: arity) (t: (g X).(G0) M.+2),
  FrtRestrictionPaintingSelected (DescS HD) a1 Hlen' F1 XA1 TX1 PX1
    rpA1 trRp1 pshRp1 Qnext E1 q Hq Hdim epsilon t):
  FrtRestrictionPaintingSelectedChain M.+1 (DescS HD) p
    (DepsCohs3ChainCons a1)
    (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') p)) Fchild
    (F1.(_frDepsA); XA1)%extradepsrestr (AddTrDep (frTr F1) TX1)
    (AddPshDep (g X) M.+1 (frtPshDeps F1) PX1)
    rpA1.1 trRp1.1 pshRp1.1 Qprev Echild.
Proof.
  generalize dependent k.
  clear - X M XpB0 S0 HD p.
  induction p as [|pred_p IH]; intros k dcB cB FC XCB1 CPB1 C2B1 dc2B1 XCB2 C2PB1
    dc3B1 a1 cB' Hlen' frames paintings SD PSChain block sp head Hpair HR Hsplit
    Qprev HP Qnext F1 top1 prev1 pair1 hr1 XCA1 TCX1 EPA0 CPA0 C2A0 PC2 PCX1
    XA1 XB1 TX1 PX1 rpA1 rpB1 trRp1 pshRp1 val1 E1 PS Fchild Echild NP.
  all: pose proof (frtSelectedNaturalityChild FC XCB1 CPB1 C2B1 XCB2 C2PB1 a1
    Hlen' frames paintings SD PSChain sp XCA1 TCX1 EPA0 CPA0 C2A0 PCX1 E1 NP) as NC.
  - now exact NC.
  - split.
    + now exact (IH k.+1 (proj1DepsCohs dcB) (DepsCohsChainCons cB)
        (proj1FrtDepsCohs FC)
        (AddCohDep (frtDcB FC) XCB1) CPB1.1 C2B1.1
        (AddCoh2Dep dc2B1 XCB2) C2PB1.1 (DepsCohs3ChainCons a1)
        (Hlen' • eq_sym (plus_n_Sm (cohsChainLen cB') pred_p.+1))
        frames.1 paintings.1 SD.1 PSChain.1 sp.1
        (AddCohDep (trDepsCohsA (frtTrBase FC)) XCA1)
        (AddTrCohDep (frtTrCohs FC) TCX1)
        (AddCohDep (pshDepsCohs (g X) (frtPshCohs FC)) EPA0) CPA0.1 C2A0.1
        (AddPshCohDep (g X) M PC2 PCX1) Echild NC).
    + now exact NC.
Defined.

(** At the top stage the offset is zero. The selected zero certificate
    supplies its head, then the previous blocks are traversed structurally. *)
Lemma frtSelectedNaturalityRootChain (Hk: k = 0):
  FrtRestrictionPaintingSelectedChain M.+1 (DescS HD) p.+1 a1 Hlen'
    F1 XA1 TX1 PX1 rpA1 trRp1 pshRp1 Qnext E1.
Proof.
  assert (root: forall q (Hq: q <= k) (Hdim: q + p.+1 <= M.+1)
      (epsilon: arity) (t: (g X).(G0) M.+2),
    FrtRestrictionPaintingSelected (DescS HD) a1 Hlen' F1 XA1 TX1 PX1
      rpA1 trRp1 pshRp1 Qnext E1 q Hq Hdim epsilon t).
  {
    intros [|q] Hq Hdim epsilon t.
    - now exact (frtRestrictionPaintingZero (DescS HD) a1 Hlen'
        F1 XA1 TX1 PX1 rpA1 trRp1 pshRp1 Qnext E1
        (rpZeroChainOf p.+1 XCA1).2 (trRpZeroChainOf p.+1 TCX1).2
        (pshRpZeroChainOf p.+1 PCX1).2 epsilon t).
    - pose proof Hq as Hbad.
      rewrite Hk in Hbad. now destruct (leR_O_contra Hbad).
  }
  split.
  - now exact (frtSelectedNaturalityChildChain root).
  - now exact root.
Defined.

End GeneratedSelectedNaturalityRecursion.

(** Name the filler-top witness directly, so later types need not infer
    it by projecting a complete painting list. *)
Definition fgPaintingTopDirect (m: nat) (W: FgTower (X := X) m)
  (frt: FgFrt (X := X) m W) (frp: FgFrp (X := X) m W frt) (Q: FgRestrData (X := X) m W frt frp):
  let FC := towerFrtDepsCohsOf (X := X) m W frt frp Q in
  FrtPaintingTopType (fgDeps (X := X) m W frt frp) FC.(_fcTX) FC.(_fcPX)
    (descCells (X := X) (descAt (X := X) m.+1)) (fun t => (descCell (X := X) (descAt (X := X) m.+1) t).2)
    (fgFrtOf (X := X) m W frt frp Q).
Proof.
  cbn zeta.
  intro t.
  now exact (fillerEquivOfTopEntry (mkFrameEqv (towerTrDeps W))
    (@descTotal X m.+1 (νGpdPack m.+1 X).1 (νGpdPack m.+1 X).2 (descAt (X := X) m.+1))
    (mkPshFrame (g X) (towerPshDeps (g X) (pshTw (X := X) m)))
    (@frtTop X m (νGpdPack m X).1 (νGpdPack m X).2 (descAt (X := X) m) m 0
      (νDepsCohsAt (νGpdPack m X).2) DepsCohsChainNil
      (fgDeps (X := X) m W frt frp) (descCells (X := X) (descAt (X := X) m.+1))
      (fgFrtOf (X := X) m W frt frp Q)) t).
Defined.

Definition fgPaintingSplitChain (m: nat) (W: FgTower (X := X) m)
  (frt: FgFrt (X := X) m W) (frp: FgFrp (X := X) m W frt) (Q: FgRestrData (X := X) m W frt frp) :=
  let FC := towerFrtDepsCohsOf (X := X) m W frt frp Q in
  frtPaintingSplitChainOfRestr m (descAt (X := X) m) m DepsCohsChainNil
    (descChainLen (X := X) (descAt (X := X) m)) (fgDeps (X := X) m W frt frp)
    FC.(_fcXA) FC.(_fcXB) FC.(_fcTX) FC.(_fcPX)
    (fun t => (descCell (X := X) (descAt (X := X) m.+1) t).2) Q (fgPaintingTopDirect m W frt frp Q).

Definition FgRestrictionPaintingSelectedChain (m: nat) (s: FgLevel (X := X) m): Type :=
  let N := m.+1 in
  let W := fgTowerAt (X := X) N (fgPrefixNext (X := X) m s) in
  let ft := fgFrtNextOf (X := X) m s in
  let fp := fgFrpNextOf (X := X) m s in
  let Q := fgQNext (X := X) m s in
  let FC := towerFrtDepsCohsOf (X := X) N W ft fp Q in
  @FrtRestrictionPaintingSelectedChain N (νGpdPack N X).1 (νGpdPack N X).2
    (descAt (X := X) N) N 0 (νDepsCohs3At (νGpdPack N X).2) DepsCohs3ChainNil
    (descChainLen (X := X) (descAt (X := X) N)) (fgDeps (X := X) N W ft fp)
    FC.(_fcXA) FC.(_fcTX) FC.(_fcPX) FC.(_fcRpA) FC.(_fcTrRp) FC.(_fcPshRp)
    Q (fgPaintingTopDirect N W ft fp Q).

(** Existing HP data determines Q at the next level. The selected
    naturality proof is then generated for that existing Q. *)
Definition fgRestrictionPaintingSelectedChain (m: nat) (s: FgLevel (X := X) m):
  FgRestrictionPaintingSelectedChain m s.
Proof.
  let N := constr:(m.+1) in
  let W := constr:(fgTowerAt (X := X) m.+1 (fgPrefixNext (X := X) m s)) in
  let ft := constr:(fgFrtNextOf (X := X) m s) in
  let fp := constr:(fgFrpNextOf (X := X) m s) in
  let Q := constr:(fgQNext (X := X) m s) in
  let FC0 := constr:(towerFrtDepsCohs (X := X) m s) in
  let FC := constr:(towerFrtDepsCohsOf (X := X) N W ft fp Q) in
  let PC0 := constr:(towerPshDepsCohs2 (g X) (pshTw (X := X) m) (pshRp (X := X) m) (pshRc (X := X) m)) in
  let DC3 := constr:(νDepsCohs3At (next ((νGpdPack m X).2))) in
  let tx := eval hnf in FC.(_fcTX) in
  lazymatch tx with @TopTrDep _ _ _ _ ?FE =>
    now exact (@frtSelectedNaturalityRootChain m _ _ (descAt (X := X) m) m 0 _
      DepsCohsChainNil FC0
      DC3.(_depsCohs2).(_extraDepsCohs)
      DC3.(_depsCohs2).(_cohPaintings) DC3.(_depsCohs2).(_coh2Frames)
      DC3.(_extraDepsCohs2) DC3.(_coh2Paintings) DepsCohs3ChainNil
      (descChainLen (X := X) (descAt (X := X) m.+1)) ft fp
      (fgSplitOf (X := X) m s.(lvP) s.(lvFrt) s.(lvFrp) s.(lvQ))
      (fgPaintingSplitChain m (lvW (X := X) s) s.(lvFrt) s.(lvFrp) s.(lvQ)) s.(lvSP)
      _ (TopTrCohDep (TC := frtTrCohs (X := X) FC0) FE)
      PC0.(_pExtraDepsCohs (g X)) PC0.(_pCohPaintings (g X)) PC0.(_pCoh2Frames (g X))
      (TopPshCohDep (g X) m) (fgPaintingTopDirect N W ft fp Q) eq_refl)
  end.
Defined.

End FG.
End SelectedNaturality.
