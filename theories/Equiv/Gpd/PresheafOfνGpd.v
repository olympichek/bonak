(** The backward direction of the correspondence between the fibred
    presentation ([νGpdPresentation]) and the indexed construction ([νGpd]):
    [g: νGpds -> νGpdPresentation arity].

    The presheaf reads off the tower directly: the total spaces of the
    ω-limit tower as [G0], and the face operations of [Face.v], run
    along the chain of dependency data a tower position carries, as the
    face maps, their exchange law and its hexagon. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp Notation νGpd.HGpd νGpd.Layer νGpd Presheaf.Gpd.Presentation.
From Bonak.Equiv.Gpd Require Import Face νGpdOfPresheaf.

From Bonak Require Import Limit.

Set Primitive Projections.
Set Keyed Unification.

Module PresheafOfνGpd (A: LayerGpdSig).
Import A.

Module Export νGpdOfPresheaf :=
  Bonak.Equiv.Gpd.νGpdOfPresheaf.νGpdOfPresheaf A.

(** The tower data at a position

    [νGpdFrom m Xpre] holds the fillers of all levels [>= m] over the prefix
    [Xpre]. The [νGpdData] at the position ([νDataAt], from [Tower.v]),
    together with the current and next fillers, assembles the
    [DepsCohs]/[DepsCohs2] that the face operations of [Face.v] consume;
    [mkDepsCohs] of the latter is definitionally the former one level up. *)

Definition νDepsCohsAt {m} {Xpre: (νGpdAt m).(prefix)}
  (X: νGpdFrom m Xpre): DepsCohs m 0 := {|
  _deps := toDepsRestr (νDataAt Xpre).(restrFrames);
  _extraDeps := TopRestrDep (this X);
  _restrPaintings := (νDataAt Xpre).(restrPaintings) (this X);
  _cohs := (νDataAt Xpre).(cohFrames) (this X);
|}.

Definition νDepsCohs2At {m} {Xpre: (νGpdAt m).(prefix)}
  (X: νGpdFrom m Xpre): DepsCohs2 m 0 := {|
  _depsCohs := νDepsCohsAt X;
  _extraDepsCohs := TopCohDep (this (next X));
  _cohPaintings := (νDataAt Xpre).(cohPaintings) (this X)
    (this (next X));
  _coh2Frames := (νDataAt Xpre).(coh2Frames) (this X)
    (this (next X));
|}.

Definition νThirdAt {m} {Xpre: (νGpdAt m).(prefix)}
  (X: νGpdFrom m Xpre):
  mkFrame (mkDepsRestr (depsCohs := mkDepsCohs (νDepsCohs2At X))) -> HGpd.
Proof.
  now exact (this (next (next X))).
Defined.

Definition νDepsCohs3At {m} {Xpre: (νGpdAt m).(prefix)}
  (X: νGpdFrom m Xpre): DepsCohs3 m 0.
Proof.
  unshelve econstructor.
  - now exact (νDepsCohs2At X).
  - now exact (TopCoh2Dep (νThirdAt X)).
  - now exact ((νDataAt Xpre).(coh2Paintings) (this X)
      (this (next X)) (νThirdAt X)).
Defined.

Definition νTotal {m} {Xpre: (νGpdAt m).(prefix)} (X: νGpdFrom m Xpre):
  HGpd :=
  {D: mkFrame (toDepsRestr (νDataAt Xpre).(restrFrames)) & (this X) D}.

(** [G0]: the total spaces down the tower *)

Fixpoint gF0 {m} {Xpre: (νGpdAt m).(prefix)} (X: νGpdFrom m Xpre)
  (n: nat): HGpd :=
  match n with
  | 0 => νTotal X
  | S n => gF0 (next X) n
  end.

(** The tower's own chain of dependency data

    A tower position carries a [DepsCohs3] and, from the three fillers
    above it, the extension that [mkCoh2Painting] needs. Extending the
    position is extending that data: [νDepsCohs3At (next X)] is
    [mkDepsCohs3 (νDepsCohs3At X) (νExt3At X)], definitionally. A chain out
    of the position therefore lifts to the next position, and the face maps
    at consecutive levels run along a chain and its lift. *)

Definition νExt3At {m} {Xpre: (νGpdAt m).(prefix)} (X: νGpdFrom m Xpre):
  DepsCohs3Extension m 0 (νDepsCohs3At X) :=
  TopCoh3Dep (depsCohs3 := νDepsCohs3At X)
    (rew [fun T: DepsCohs2 m.+1 0 =>
            mkFrame (mkDepsRestr (depsCohs := mkDepsCohs T)) -> HGpd]
       (eq_refl: νDepsCohs2At (next X) = mkDepsCohs2 (νDepsCohs3At X))
     in νThirdAt (next X)).

(** The face maps along a chain

    Erasing dimension [dim] at level [n] runs along the chain the position
    carries, at dimension [dim] rather than at dimension [0] of a shorter
    chain, so that all the face maps a coherence mentions run along one
    chain and its lifts. *)

Fixpoint gFaceC {m} {Xpre: (νGpdAt m).(prefix)} (X: νGpdFrom m Xpre)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At X) dc3)
  (n: nat) {struct n}:
  forall (dim: nat), dim <= n + k -> arity -> gF0 X n.+1 -> gF0 X n :=
  match n return
    forall (dim: nat), dim <= n + k -> arity -> gF0 X n.+1 -> gF0 X n with
  | 0 => fun dim Hdim ε d =>
      faceDeep (cohs3ChainDepsCohs2 a) dim Hdim ε d.1 d.2
  | S n => fun dim Hdim ε d =>
      gFaceC (next X) (chainUp1 (νExt3At X) a) n dim
        (leR_eq_r (plus_n_Sm n k) Hdim) ε d
  end.

(** The exchange law between two consecutive levels is the one the chain
    and its lift carry, [faceAtCohUp] at the bottom of the descent. *)

Fixpoint gFaceCohC {m} {Xpre: (νGpdAt m).(prefix)} (X: νGpdFrom m Xpre)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At X) dc3)
  (n: nat) {struct n}:
  forall (q: nat) (Hq: q <= n + k) (r: nat) (Hr: r <= q) (ε ω: arity)
    (d: gF0 X n.+2),
  gFaceC X a n q Hq ε (gFaceC X a n.+1 r (Hr ↕ (↑ Hq)) ω d) =
  gFaceC X a n r (Hr ↕ Hq) ω (gFaceC X a n.+1 q.+1 (⇑ Hq) ε d) :=
  match n return
    forall (q: nat) (Hq: q <= n + k) (r: nat) (Hr: r <= q) (ε ω: arity)
      (d: gF0 X n.+2),
    gFaceC X a n q Hq ε (gFaceC X a n.+1 r (Hr ↕ (↑ Hq)) ω d) =
    gFaceC X a n r (Hr ↕ Hq) ω (gFaceC X a n.+1 q.+1 (⇑ Hq) ε d) with
  | 0 => fun q Hq r Hr ε ω d =>
      faceAtCohUp (νExt3At X) a q Hq r Hr ε ω
        (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At X) a)) d).1
        (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At X) a)) d).2
  | S n => fun q Hq r Hr ε ω d =>
      gFaceCohC (next X) (chainUp1 (νExt3At X) a) n q
        (leR_eq_r (plus_n_Sm n k) Hq) r Hr ε ω d
  end.

(** The three exchanges on three consecutive levels paste: the hexagon is
    [faceAtCoh2Up] at the bottom of the descent. *)

Fixpoint gFaceCoh2C {m} {Xpre: (νGpdAt m).(prefix)} (X: νGpdFrom m Xpre)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain (νDepsCohs3At X) dc3)
  (n: nat) {struct n}:
  forall (q: nat) (Hq: q <= n + k) (r: nat) (Hr: r <= q) (s: nat) (Hs: s <= r)
    (ε ω θ: arity) (d: gF0 X n.+3),
  f_equal (gFaceC X a n q Hq ε)
    (gFaceCohC X a n.+1 r (Hr ↕ (↑ Hq)) s Hs ω θ d)
  • (gFaceCohC X a n q Hq s (Hs ↕ Hr) ε θ
       (gFaceC X a n.+2 r.+1 (⇑ (Hr ↕ (↑ Hq))) ω d)
     • f_equal (gFaceC X a n s (Hs ↕ (Hr ↕ Hq)) θ)
         (gFaceCohC X a n.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d))
  = gFaceCohC X a n q Hq r Hr ε ω
      (gFaceC X a n.+2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ d)
    • (f_equal (gFaceC X a n r (Hr ↕ Hq) ω)
         (gFaceCohC X a n.+1 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) ε θ d)
       • gFaceCohC X a n r (Hr ↕ Hq) s Hs ω θ
           (gFaceC X a n.+2 q.+2 (⇑ (⇑ Hq)) ε d)) :=
  match n return
    forall (q: nat) (Hq: q <= n + k) (r: nat) (Hr: r <= q) (s: nat) (Hs: s <= r)
      (ε ω θ: arity) (d: gF0 X n.+3),
    f_equal (gFaceC X a n q Hq ε)
      (gFaceCohC X a n.+1 r (Hr ↕ (↑ Hq)) s Hs ω θ d)
    • (gFaceCohC X a n q Hq s (Hs ↕ Hr) ε θ
         (gFaceC X a n.+2 r.+1 (⇑ (Hr ↕ (↑ Hq))) ω d)
       • f_equal (gFaceC X a n s (Hs ↕ (Hr ↕ Hq)) θ)
           (gFaceCohC X a n.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d))
    = gFaceCohC X a n q Hq r Hr ε ω
        (gFaceC X a n.+2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ d)
      • (f_equal (gFaceC X a n r (Hr ↕ Hq) ω)
           (gFaceCohC X a n.+1 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) ε θ d)
         • gFaceCohC X a n r (Hr ↕ Hq) s Hs ω θ
             (gFaceC X a n.+2 q.+2 (⇑ (⇑ Hq)) ε d)) with
  | 0 => fun q Hq r Hr s Hs ε ω θ d =>
      faceAtCoh2Up (νExt3At X) (νExt3At (next X)) a q Hq r Hr s Hs ε ω θ
        (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At (next X))
           (chainUp1 (νExt3At X) a))) d).1
        (deepCell (cohs3ChainDepsCohs2 (chainUp1 (νExt3At (next X))
           (chainUp1 (νExt3At X) a))) d).2
  | S n => fun q Hq r Hr s Hs ε ω θ d =>
      gFaceCoh2C (next X) (chainUp1 (νExt3At X) a) n q
        (leR_eq_r (plus_n_Sm n k) Hq) r Hr s Hs ε ω θ d
  end.

(** The presheaf a tower determines: the operations along the empty chain
    out of the tower's own dependency data, whose relative dimension bound
    [q <= n + 0] is the interface's [q <= n]. *)

Definition g (Y: νGpds): νGpdPresentation arity := {|
  G0 := gF0 Y;
  GFace n q Hq ε :=
    gFaceC Y DepsCohs3ChainNil n q (leR_eq_r (plus_n_O n) Hq) ε;
  GFaceCoh n q Hq r Hr ε ω X :=
    gFaceCohC Y DepsCohs3ChainNil n q (leR_eq_r (plus_n_O n) Hq) r Hr ε ω X;
  GFaceCoh2 n q Hq r Hr s Hs ε ω θ X :=
    gFaceCoh2C Y DepsCohs3ChainNil n q (leR_eq_r (plus_n_O n) Hq) r Hr s Hs
      ε ω θ X;
|}.

(** The lift of a chain has the length of the chain. *)

Lemma cohs3ChainUpLen {P K} {dc3Top: DepsCohs3 P K}
  (ext3: DepsCohs3Extension P K dc3Top) {p k} {dc3: DepsCohs3 p k}
  (c: DepsCohs3Chain dc3Top dc3):
  cohs3ChainLen (cohs3ChainUp ext3 c) = cohs3ChainLen c.
Proof.
  induction c; cbn [cohs3ChainUp cohs3ChainLen];
    [now reflexivity | now rewrite IHc].
Defined.

End PresheafOfνGpd.

(** The two constructions, shared by the equivalence and round-trip proofs. *)
Module Type ConstructionsSig (A: LayerGpdSig).
Include PresheafOfνGpd A.
End ConstructionsSig.
