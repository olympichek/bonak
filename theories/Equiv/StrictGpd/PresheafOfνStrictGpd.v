(** The face presentation extracted from the infinite indexed tower. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet LeSProp NatLemmas Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Equiv.StrictGpd Require Import Tower Face.
From Bonak.Presheaf.StrictGpd Require Import Presentation.
From Bonak.Category Require Import FunctorAlgebra.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafOfνStrictGpdOn (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S).
Import A.
Module Export Tower := TowerOn A S.
Module Export Faces := F.

Definition νDepsCohsAt {m} {Xpre: (νStrictGpdAt m).(prefix)}
  (X: νStrictGpdFrom m Xpre): DepsCohs m 0 := {|
  _deps := toDepsRestr (νDataAt Xpre).(restrFrames);
  _extraDeps := TopRestrDep (this X);
  _restrPaintings := (νDataAt Xpre).(restrPaintings) (this X);
  _cohs := (νDataAt Xpre).(cohFrames) (this X);
|}.

Definition νDepsCohs2At {m} {Xpre: (νStrictGpdAt m).(prefix)}
  (X: νStrictGpdFrom m Xpre): DepsCohs2 m 0 := {|
  _depsCohs := νDepsCohsAt X;
  _extraDepsCohs := TopCohDep (this (next X));
  _cohPaintings := (νDataAt Xpre).(cohPaintings) (this X)
    (this (next X));
|}.

Definition νTotal {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre):
  HSetGroupoid := total (this X).

Fixpoint gF0 {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre)
  (n: nat): HSetGroupoid :=
  match n with
  | 0 => νTotal X
  | S n => gF0 (next X) n
  end.

(** Chain synthesis

    The face operations take chains recording how many stages to descend.
    A presentation supplies a face index [q] and a bound [q <= n] in SProp;
    the bound cannot be eliminated to construct a chain in Type.
    [chain2Down] therefore descends by a natural-number argument, retaining
    the endpoint and stopping at stage 0. [gFace] uses [level - dim] as
    this argument. *)

Definition Chain2Pack {P K} (dc2Top: DepsCohs2 P K): Type :=
  {p: nat &T {k: nat &T {dc2: DepsCohs2 p k &T DepsCohs2Chain dc2Top dc2}}}.

Definition chain2Step {P K} {dc2Top: DepsCohs2 P K}
  (s: Chain2Pack dc2Top): Chain2Pack dc2Top :=
  (match s.1 as p0 return
     {k: nat &T {dc2: DepsCohs2 p0 k &T DepsCohs2Chain dc2Top dc2}} ->
     Chain2Pack dc2Top with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs2 s'.2.1;
       DepsCohs2ChainCons s'.2.2)))
   end) s.2.

Fixpoint chain2Down {P K} (dc2Top: DepsCohs2 P K) (j: nat):
  Chain2Pack dc2Top :=
  match j with
  | 0 => (P; (K; (dc2Top; DepsCohs2ChainNil)))
  | S j => chain2Step (chain2Down dc2Top j)
  end.

(** Forget the painting-coherence data at the same level, or construct
    the frame-coherence data one level higher through [mkDepsCohs]. *)

Definition DCPack {P K} (dcTop: DepsCohs P K): Type :=
  {p: nat &T {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}}}.

Definition dcStep {P K} {dcTop: DepsCohs P K} (s: DCPack dcTop):
  DCPack dcTop :=
  (match s.1 as p0 return
     {k: nat &T {dc: DepsCohs p0 k &T DepsCohsChain dcTop dc}} ->
     DCPack dcTop with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs s'.2.1;
       DepsCohsChainCons s'.2.2)))
   end) s.2.

Definition dc2PackDeps {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  DCPack T.(_depsCohs) :=
  (s.1; (s.2.1; (s.2.2.1.(_depsCohs); cohs2ChainDepsCohs s.2.2.2))).

Definition dc2PackCohs {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  DCPack (mkDepsCohs T) :=
  (s.1.+1; (s.2.1; (mkDepsCohs s.2.2.1; cohs2ChainCohs s.2.2.2))).

Definition νFaceFuel {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre)
  (j: nat) (ε: arity): Functor (νTotal (next X)) (νTotal X) :=
  proj (this (next X)) ⨟ᶠ νFace ((dc2PackDeps (chain2Down (νDepsCohs2At X) j)).2.2.2) ε.

Fixpoint gFace {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre)
  (n: nat) {struct n}:
  forall dim, dim <= n + m -> arity -> Functor (gF0 X n.+1) (gF0 X n) :=
  match n return forall dim, dim <= n + m -> arity -> Functor (gF0 X n.+1) (gF0 X n) with
  | 0 => fun dim Hdim ε => νFaceFuel X (m - dim) ε
  | S n => fun dim Hdim ε => gFace (next X) n dim (leR_eq_r (plus_n_Sm n m) Hdim) ε
  end.

Definition chain2Cat {P K} {T: DepsCohs2 P K} (s1: Chain2Pack T)
  (s2: Chain2Pack s1.2.2.1): Chain2Pack T :=
  (s2.1; (s2.2.1; (s2.2.2.1; cohs2ChainCompose s1.2.2.2 s2.2.2.2))).

Lemma chain2StepStage {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  (chain2Step s).1 = Nat.pred s.1.
Proof.
  destruct s as (p, s2). now destruct p.
Qed.

Lemma chain2DownStage {P K} (T: DepsCohs2 P K) (j: nat):
  (chain2Down T j).1 = P - j.
Proof.
  induction j.
  - now rewrite sub0r.
  - now rewrite subSuccR, chain2StepStage, IHj.
Qed.

Lemma dc2PackDepsStep {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  dc2PackDeps (chain2Step s) = dcStep (dc2PackDeps s).
Proof.
  destruct s as (p, (k, (dc2, c))). now destruct p.
Qed.

Lemma dc2PackCohsStep {P K} {T: DepsCohs2 P K} (s: Chain2Pack T)
  (p': nat) (e: s.1 = p'.+1):
  dc2PackCohs (chain2Step s) = dcStep (dc2PackCohs s).
Proof.
  destruct s as (p, (k, (dc2, c))). cbn in e. subst p. now reflexivity.
Qed.

Lemma chain2CatStep {P K} {T: DepsCohs2 P K} (s1: Chain2Pack T)
  (s2: Chain2Pack s1.2.2.1):
  chain2Cat s1 (chain2Step s2) = chain2Step (chain2Cat s1 s2).
Proof.
  destruct s2 as (p, (k, (dc2, c))). now destruct p.
Qed.

Lemma chain2DownCat {P K} (T: DepsCohs2 P K) (j1 j2: nat):
  chain2Down T (j2 + j1) =
  chain2Cat (chain2Down T j1) (chain2Down (chain2Down T j1).2.2.1 j2).
Proof.
  induction j2.
  - now reflexivity.
  - cbn. now rewrite IHj2, chain2CatStep.
Qed.

Lemma packLevelCross {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre)
  (j: nat) (Hj: j <= m):
  dc2PackDeps (chain2Down (νDepsCohs2At (next X)) j) =
  dc2PackCohs (chain2Down (νDepsCohs2At X) j).
Proof.
  revert Hj; induction j; intro Hj.
  - now reflexivity.
  - rewrite dc2PackDepsStep, (IHj (↓ Hj)).
    symmetry.
    now exact (dc2PackCohsStep (chain2Down (νDepsCohs2At X) j) (m - j.+1)
      (chain2DownStage (νDepsCohs2At X) j • subPos Hj)).
Qed.

Lemma νFaceFuelCoh {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre)
  q (Hq: q <= m) r (Hr: r <= q) ε ω:
  νFaceFuel (next X) (m.+1 - r) ω ⨟ᶠ νFaceFuel X (m - q) ε =
  νFaceFuel (next X) (m - q) ε ⨟ᶠ νFaceFuel X (m - r) ω.
Proof.
  unfold νFaceFuel.
  rewrite (subSuccL (Hr ↕ Hq)), (subSplit Hr Hq).
  rewrite (packLevelCross X (m - q) (sub_leR m q)), dc2PackDepsStep.
  rewrite (packLevelCross X ((q - r) + (m - q))
    (leR_eq (subSplit Hr Hq) (sub_leR m r))).
  rewrite (chain2DownCat (νDepsCohs2At X) (m - q) (q - r)).
  rewrite functorAssocEq, <- (functorAssocEq _ (proj (this (next X)))).
  rewrite (νFaceCoh
    ((chain2Down (νDepsCohs2At X) (m - q)).2.2.2)
    ((chain2Down (chain2Down (νDepsCohs2At X) (m - q)).2.2.1 (q - r)).2.2.2) ε ω).
  apply (functorEqPath (νTotal X).(hsetGroupoidUIP)).
  unshelve econstructor; now intros.
Defined.

Fixpoint gFaceCoh {m} {Xpre: (νStrictGpdAt m).(prefix)} (X: νStrictGpdFrom m Xpre)
  (n: nat) {struct n}:
  forall q (Hq: q <= n + m) r (Hr: r <= q) ε ω,
  gFace X n.+1 r (Hr ↕ (↑ Hq)) ω ⨟ᶠ gFace X n q Hq ε =
  gFace X n.+1 q.+1 (⇑ Hq) ε ⨟ᶠ gFace X n r (Hr ↕ Hq) ω :=
  match n return forall q (Hq: q <= n + m) r (Hr: r <= q) ε ω,
    gFace X n.+1 r (Hr ↕ (↑ Hq)) ω ⨟ᶠ gFace X n q Hq ε =
    gFace X n.+1 q.+1 (⇑ Hq) ε ⨟ᶠ gFace X n r (Hr ↕ Hq) ω with
  | 0 => fun q Hq r Hr ε ω => νFaceFuelCoh X q Hq r Hr ε ω
  | S n => fun q Hq r Hr ε ω =>
      gFaceCoh (next X) n q (leR_eq_r (plus_n_Sm n m) Hq) r Hr ε ω
  end.

Definition g (X: νStrictGpds): νStrictGpdPresentation arity := {|
  G0 := gF0 X;
  GFace := fun n q Hq ε => gFace X n q (leR_eq_r (plus_n_O n) Hq) ε;
  GFaceCoh := fun n q Hq r Hr ε ω =>
    gFaceCoh X n q (leR_eq_r (plus_n_O n) Hq) r Hr ε ω;
|}.

End PresheafOfνStrictGpdOn.

Module PresheafOfνStrictGpd (A: LayerSig).
Module Core := νStrictGpd.νStrictGpd A.
Module FaceOperations := FaceOn A Core.
Include PresheafOfνStrictGpdOn A Core FaceOperations.
End PresheafOfνStrictGpd.

Module Type ExtractionSig (A: LayerSig) (S: νStrictGpdSig A)
  (F: FaceSig A S).
Include PresheafOfνStrictGpdOn A S F.
End ExtractionSig.

Module PresheafOfνStrictGpdSimplicial :=
  PresheafOfνStrictGpdOn SimplicialLayer νStrictGpdSimplicial FaceSimplicial.
Module PresheafOfνStrictGpdCubical :=
  PresheafOfνStrictGpdOn CubicalLayer νStrictGpdCubical FaceCubical.
