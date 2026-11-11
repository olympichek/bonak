(** Faces, restrictions and descended frames of an indexed prefix depend
    only on the data below the filler that is being added. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality Logic.Eqdep_dec
  Arith.PeanoNat.
From Bonak.Lib Require Import SigT HSet HGpd Notation LeSProp NatLemmas
  RewLemmas Funext Equiv.
From Bonak.Indexed.Gpd Require Import Layer νGpd.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Face PathAlgebra.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

(** Lifted face chains and their contraction paths depend only on the
    existing coherence data, independently of the next filler family. *)

Module FaceCausalityOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Import A.
Module Export Indexed := Faces.

Definition BottomCell {p k} (dc3: DepsCohs3 p k): Type :=
  {D: mkFrame (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs))).(1) &T
   (mkPaintings (mkDepsRestr (depsCohs := dc3.(_depsCohs2).(_depsCohs));
     mkExtraDeps dc3.(_depsCohs2).(_extraDepsCohs))).2 D}.

Definition UpperChain {P K} {dc3Top: DepsCohs3 P K}
  {p k} (dc3: DepsCohs3 p k): Type :=
  DepsCohs2Chain (mkDepsCohs2 dc3Top) (proj1DepsCohs2 (mkDepsCohs2 dc3)).

Definition rebuildAt {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (c: @UpperChain P K dc3Top p k dc3) (Y: BottomCell dc3): BottomCell dc3 :=
  deepCell (cohs3ChainDepsCohs2 a)
    (getPainting (cohsChainExt (cohs2ChainDepsCohs c)) Y.1 Y.2).

(** Keeping the contraction together with its chain records how its source
    changes when the projected chain is identified with its normal form. *)
Definition RebuildData {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3): Type :=
  {c: @UpperChain P K dc3Top p k dc3 &T forall Y: BottomCell dc3, rebuildAt a c Y = Y}.

Definition rebuildData {P K} {dc3Top: DepsCohs3 P K}
  (e: DepsCohs3Extension P K dc3Top)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3): RebuildData a :=
  (cohs3ChainDepsCohs2 (chainUp1 e a); deepCellRebuildUp e a).

Definition nextRebuildData {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p.+1 k} (a: DepsCohs3Chain dc3Top dc3)
  (r: RebuildData a): RebuildData (DepsCohs3ChainCons a) :=
  (DepsCohs2ChainCons r.1;
   fun Y: BottomCell (proj1DepsCohs3 dc3) => f_equal (fun w: BottomCell dc3 =>
     ((w.1.1; (w.1.2; w.2)): BottomCell (proj1DepsCohs3 dc3)))
       (r.2 ((Y.1; Y.2.1); Y.2.2))).

Fixpoint canonicalRebuildData {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3): RebuildData a :=
  match a as a0 return RebuildData a0 with
  | DepsCohs3ChainNil => (DepsCohs2ChainCons DepsCohs2ChainNil; fun Y => eq_refl)
  | DepsCohs3ChainCons a0 => nextRebuildData a0 (canonicalRebuildData a0)
  end.

Lemma rebuildDataNormalize {P K} {dc3Top: DepsCohs3 P K}
  (e: DepsCohs3Extension P K dc3Top)
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3):
  rebuildData e a = canonicalRebuildData a.
Proof.
  induction a as [|p k dc3 a IH].
  - now reflexivity.
  - change (nextRebuildData a (rebuildData e a) =
      nextRebuildData a (canonicalRebuildData a)).
    now exact (f_equal (nextRebuildData a) IH).
Defined.

Definition UpperCell {p k} (dc3: DepsCohs3 p k): Type :=
  {D: mkFrame (mkDepsRestr (depsCohs :=
       (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1) &T
   (mkPaintings (mkDepsRestr (depsCohs :=
       (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
     mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 D}.

Definition upperRestrict {p k} {dc3: DepsCohs3 p k}
  j (Hj: j <= k.+1) a (Z: UpperCell dc3): BottomCell dc3 :=
  restrCell (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs) j Hj a Z.1 Z.2.

Definition Exchange {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (c: @UpperChain P K dc3Top p k dc3)
  q (Hq: q <= k) r (Hr: r <= q) ε ω (Z: UpperCell dc3): Type :=
  faceAt (cohs3ChainDepsCohs2 a) q Hq ε
    (rebuildAt a c (upperRestrict r (Hr ↕ ↑ Hq) ω Z)).1
    (rebuildAt a c (upperRestrict r (Hr ↕ ↑ Hq) ω Z)).2 =
  faceAt (cohs3ChainDepsCohs2 a) r (Hr ↕ Hq) ω
    (rebuildAt a c (upperRestrict q.+1 (⇑ Hq) ε Z)).1
    (rebuildAt a c (upperRestrict q.+1 (⇑ Hq) ε Z)).2.

Definition exchangeFromRebuild {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (d: RebuildData a)
  q (Hq: q <= k) r (Hr: r <= q) ε ω (Z: UpperCell dc3):
  Exchange a d.1 q Hq r Hr ε ω Z :=
  f_equal (fun w: BottomCell dc3 =>
    faceAt (cohs3ChainDepsCohs2 a) q Hq ε w.1 w.2)
      (d.2 (upperRestrict r (Hr ↕ ↑ Hq) ω Z))
  • (f_equal (faceRebuild a) (restrCellCoh dc3 q Hq r Hr ε ω Z.1 Z.2)
     • eq_sym (f_equal (fun w: BottomCell dc3 =>
       faceAt (cohs3ChainDepsCohs2 a) r (Hr ↕ Hq) ω w.1 w.2)
         (d.2 (upperRestrict q.+1 (⇑ Hq) ε Z)))).

(** The whole input cell is descended along the lifted chain before the
    exchange is evaluated. Its descent and the exchange normalize together. *)
Definition WholeUpperCell {P K} (dc3Top: DepsCohs3 P K): Type :=
  {d: mkFrame (mkDepsCohs (mkDepsCohs2 dc3Top)).(_deps) &T
   mkPainting (mkDepsCohs (mkDepsCohs2 dc3Top)).(_extraDeps) d}.

Definition WholeBottomCell {P K} (dc3Top: DepsCohs3 P K): Type :=
  {d: mkFrame dc3Top.(_depsCohs2).(_depsCohs).(_deps) &T
   mkPainting dc3Top.(_depsCohs2).(_depsCohs).(_extraDeps) d}.

Definition WholeMiddleCell {P K} (dc3Top: DepsCohs3 P K): Type :=
  {d: mkFrame (mkDepsCohs dc3Top.(_depsCohs2)).(_deps) &T
   mkPainting (mkDepsCohs dc3Top.(_depsCohs2)).(_extraDeps) d}.

(** Two adjacent face actions and their exchange paths form one observation
    of the existing prefix. The later filler affects none of this package. *)
Record LocalFaceData {P K} {dc3Top: DepsCohs3 P K} {k: nat} := {
  lowerFace q (Hq: q <= k) (ε: arity): WholeMiddleCell dc3Top -> WholeBottomCell dc3Top;
  upperFace q (Hq: q <= k.+1) (ε: arity): WholeUpperCell dc3Top -> WholeMiddleCell dc3Top;
  faceExchange q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity) (x: WholeUpperCell dc3Top):
    lowerFace q Hq ε (upperFace r (Hr ↕ ↑ Hq) ω x) =
      lowerFace r (Hr ↕ Hq) ω (upperFace q.+1 (⇑ Hq) ε x);
}.
Arguments LocalFaceData {P K} dc3Top k.

Definition localDataLowerCompare {P K} {dc3Top: DepsCohs3 P K} {k}
  {u v: LocalFaceData dc3Top k} (e: u = v) q (Hq: q <= k) a x :=
  f_equal (fun d => d.(lowerFace) q Hq a x) e.

Definition localDataUpperCompare {P K} {dc3Top: DepsCohs3 P K} {k}
  {u v: LocalFaceData dc3Top k} (e: u = v) q (Hq: q <= k.+1) a x :=
  f_equal (fun d => d.(upperFace) q Hq a x) e.

Lemma localDataPathSquareSource {P K} {dc3Top: DepsCohs3 P K} {k}
  (u v: LocalFaceData dc3Top k) (e: u = v)
  q (Hq: q <= k) r (Hr: r <= q) a b (x: WholeUpperCell dc3Top):
  (f_equal (u.(lowerFace) q Hq a) (localDataUpperCompare e r (Hr ↕ ↑ Hq) b x)
    • localDataLowerCompare e q Hq a (v.(upperFace) r (Hr ↕ ↑ Hq) b x))
    • v.(faceExchange) q Hq r Hr a b x
  = u.(faceExchange) q Hq r Hr a b x
    • (f_equal (u.(lowerFace) r (Hr ↕ Hq) b) (localDataUpperCompare e q.+1 (⇑ Hq) a x)
      • localDataLowerCompare e r (Hr ↕ Hq) b (v.(upperFace) q.+1 (⇑ Hq) a x)).
Proof.
  destruct e.
  change (eq_refl • u.(faceExchange) q Hq r Hr a b x =
    u.(faceExchange) q Hq r Hr a b x • eq_refl).
  now exact (eq_trans_refl_l _ • eq_sym (eq_trans_refl_r _)).
Defined.

Definition localFaceDataFromRebuild {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (d: RebuildData a): LocalFaceData dc3Top k := {|
  lowerFace q Hq ε x := faceDeep (cohs3ChainDepsCohs2 a) q Hq ε x.1 x.2;
  upperFace q Hq ε x := faceDeep d.1 q Hq ε x.1 x.2;
  faceExchange q Hq r Hr ε ω x :=
    exchangeFromRebuild a d q Hq r Hr ε ω (deepCell d.1 x);
|}.

Definition canonicalLocalFaceData {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3):
  LocalFaceData dc3Top k := localFaceDataFromRebuild a (canonicalRebuildData a).

Lemma chain2PackDec {P K} {dc2Top: DepsCohs2 P K} (s t: Chain2Pack dc2Top):
  {s = t} + {s <> t}.
Proof.
  destruct (natDec (chain2PackLen s) (chain2PackLen t)) as [h|h].
  - left. now exact (chain2PackEq s t h).
  - right; intro e. now exact (h (f_equal chain2PackLen e)).
Defined.

Lemma chain2PackUIP {P K} {dc2Top: DepsCohs2 P K} {s t: Chain2Pack dc2Top}
  (e f: s = t): e = f.
Proof. now exact (UIP_dec _ chain2PackDec s t e f). Defined.

Lemma chain2Stage {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  (p + cohs2ChainLen c)%nat = P.
Proof.
  induction c; cbn [cohs2ChainLen].
  - now symmetry; apply plus_n_O.
  - rewrite <- plus_n_Sm. now exact IHc.
Defined.

(** Fixing the endpoint indices fixes the chain length. Endpoint packages
    are therefore propositions even though the coherence data are not sets. *)
Lemma chain2EndpointPackEq {P K} {dc2Top: DepsCohs2 P K} {p k}
  (s t: {dc2: DepsCohs2 p k &T DepsCohs2Chain dc2Top dc2}): s = t.
Proof.
  assert (h: cohs2ChainLen s.2 = cohs2ChainLen t.2).
  { apply (Nat.add_cancel_l _ _ p).
    now exact (chain2Stage s.2 • eq_sym (chain2Stage t.2)). }
  pose (e := chain2PackEqLen s.2 t.2 h).
  pose proof (projT2_eq e) as e1.
  rewrite (natUIP (projT1_eq e) eq_refl) in e1.
  cbn in e1.
  pose proof (projT2_eq e1) as e2.
  rewrite (natUIP (projT1_eq e1) eq_refl) in e2.
  now exact e2.
Defined.

Lemma chain2EndpointPackUIP {P K} {dc2Top: DepsCohs2 P K} {p k}
  {s t: {dc2: DepsCohs2 p k &T DepsCohs2Chain dc2Top dc2}} (e f: s = t): e = f.
Proof. now exact (eq_hprop_UIP (fun s t => chain2EndpointPackEq s t) e f). Defined.

Definition LowerChainPackage {P} (dc3Top: DepsCohs3 P 0): Type :=
  {d: DepsCohs2 0 P &T DepsCohs2Chain dc3Top.(_depsCohs2) d}.

Definition UpperChainPackage {P} (dc3Top: DepsCohs3 P 0): Type :=
  {d: DepsCohs2 0 P.+1 &T DepsCohs2Chain (mkDepsCohs2 dc3Top) d}.

Definition lowerChainFace {P} {dc3Top: DepsCohs3 P 0}
  (c: LowerChainPackage dc3Top) q (Hq: q <= P) ε (x: WholeMiddleCell dc3Top):
  WholeBottomCell dc3Top := faceDeep c.2 q Hq ε x.1 x.2.

Definition upperChainFace {P} {dc3Top: DepsCohs3 P 0}
  (c: UpperChainPackage dc3Top) q (Hq: q <= P.+1) ε (x: WholeUpperCell dc3Top):
  WholeMiddleCell dc3Top := faceDeep c.2 q Hq ε x.1 x.2.

(** The chains themselves are retained alongside their exchange paths.
    Their fixed endpoint indices make comparisons of these fields unique. *)
Record ChainedFaceData {P} {dc3Top: DepsCohs3 P 0} := {
  lowerChain: LowerChainPackage dc3Top;
  upperChain: UpperChainPackage dc3Top;
  chainedExchange q (Hq: q <= P) r (Hr: r <= q) (ε ω: arity)
    (x: WholeUpperCell dc3Top):
    lowerChainFace lowerChain q Hq ε (upperChainFace upperChain r (Hr ↕ ↑ Hq) ω x) =
      lowerChainFace lowerChain r (Hr ↕ Hq) ω (upperChainFace upperChain q.+1 (⇑ Hq) ε x);
}.
Arguments ChainedFaceData {P} dc3Top.

Definition eraseChainedFaceData {P} {dc3Top: DepsCohs3 P 0}
  (d: ChainedFaceData dc3Top): LocalFaceData dc3Top P := {|
  lowerFace := lowerChainFace d.(lowerChain);
  upperFace := upperChainFace d.(upperChain);
  faceExchange := d.(chainedExchange);
|}.

Definition ChainedExchangeType {P} {dc3Top: DepsCohs3 P 0}
  (lower: LowerChainPackage dc3Top) (upper: UpperChainPackage dc3Top): Type :=
  forall q (Hq: q <= P) r (Hr: r <= q) (a b: arity) (x: WholeUpperCell dc3Top),
  lowerChainFace lower q Hq a (upperChainFace upper r (Hr ↕ ↑ Hq) b x) =
    lowerChainFace lower r (Hr ↕ Hq) b (upperChainFace upper q.+1 (⇑ Hq) a x).

Definition changeChainedData {P} {dc3Top: DepsCohs3 P 0}
  (d: ChainedFaceData dc3Top)
  (lower: LowerChainPackage dc3Top) (upper: UpperChainPackage dc3Top)
  (p: d.(lowerChain) = lower) (q: d.(upperChain) = upper):
  ChainedFaceData dc3Top :=
  @Build_ChainedFaceData P dc3Top lower upper
    (rew [fun lower => ChainedExchangeType lower upper] p in
      rew [ChainedExchangeType d.(lowerChain)] q in d.(chainedExchange)).

Lemma changeChainedDataEq {P} {dc3Top: DepsCohs3 P 0}
  (d: ChainedFaceData dc3Top)
  (lower: LowerChainPackage dc3Top) (upper: UpperChainPackage dc3Top)
  (p: d.(lowerChain) = lower) (q: d.(upperChain) = upper):
  d = changeChainedData d lower upper p q.
Proof. destruct d; cbn in p, q. now destruct p, q. Defined.

Definition FullChainPackage {P} (dc3Top: DepsCohs3 P 0): Type :=
  {d: DepsCohs3 0 P &T DepsCohs3Chain dc3Top d}.

Definition chainedFaceDataFromRebuild {P} {dc3Top: DepsCohs3 P 0}
  (a: FullChainPackage dc3Top) (d: RebuildData a.2): ChainedFaceData dc3Top := {|
  lowerChain := (a.1.(_depsCohs2); cohs3ChainDepsCohs2 a.2);
  upperChain := (proj1DepsCohs2 (mkDepsCohs2 a.1); d.1);
  chainedExchange q Hq r Hr ε ω x :=
    exchangeFromRebuild a.2 d q Hq r Hr ε ω (deepCell d.1 x);
|}.

Definition rawChainedFaceData {P} {dc3Top: DepsCohs3 P 0}
  (e: DepsCohs3Extension P 0 dc3Top) (a: FullChainPackage dc3Top):
  ChainedFaceData dc3Top := {|
  lowerChain := (a.1.(_depsCohs2); cohs3ChainDepsCohs2 a.2);
  upperChain := (proj1DepsCohs2 (mkDepsCohs2 a.1);
    cohs3ChainDepsCohs2 (chainUp1 e a.2));
  chainedExchange q Hq r Hr ε ω x :=
    faceAtCohUp e a.2 q Hq r Hr ε ω
      (deepCell (cohs3ChainDepsCohs2 (chainUp1 e a.2)) x).1
      (deepCell (cohs3ChainDepsCohs2 (chainUp1 e a.2)) x).2;
|}.

Lemma rawChainedFaceDataFromRebuild {P} {dc3Top: DepsCohs3 P 0}
  (e: DepsCohs3Extension P 0 dc3Top) (a: FullChainPackage dc3Top):
  rawChainedFaceData e a = chainedFaceDataFromRebuild a (rebuildData e a.2).
Proof.
  unfold rawChainedFaceData, chainedFaceDataFromRebuild.
  apply f_equal.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro r.
  apply spropFunext; intro Hr.
  apply functional_extensionality_dep; intro ε.
  apply functional_extensionality_dep; intro ω.
  apply functional_extensionality_dep; intro x.
  now apply faceAtCohUpConj.
Defined.

Definition canonicalChainedFaceData {P} {dc3Top: DepsCohs3 P 0}
  (a: FullChainPackage dc3Top): ChainedFaceData dc3Top :=
  chainedFaceDataFromRebuild a (canonicalRebuildData a.2).

Definition chainedFaceDataNormalize {P} {dc3Top: DepsCohs3 P 0}
  (e: DepsCohs3Extension P 0 dc3Top) (a: FullChainPackage dc3Top):
  rawChainedFaceData e a = canonicalChainedFaceData a :=
  rawChainedFaceDataFromRebuild e a
    • f_equal (chainedFaceDataFromRebuild a) (rebuildDataNormalize e a.2).

Definition chainedDataLowerCompare {P} {dc3Top: DepsCohs3 P 0}
  {u v: ChainedFaceData dc3Top} (e: u = v)
  q (Hq: q <= P) ε (x: WholeMiddleCell dc3Top):
  lowerChainFace u.(lowerChain) q Hq ε x = lowerChainFace v.(lowerChain) q Hq ε x :=
  f_equal (fun d => lowerChainFace d.(lowerChain) q Hq ε x) e.

Definition chainedDataUpperCompare {P} {dc3Top: DepsCohs3 P 0}
  {u v: ChainedFaceData dc3Top} (e: u = v)
  q (Hq: q <= P.+1) ε (x: WholeUpperCell dc3Top):
  upperChainFace u.(upperChain) q Hq ε x = upperChainFace v.(upperChain) q Hq ε x :=
  f_equal (fun d => upperChainFace d.(upperChain) q Hq ε x) e.

Lemma chainedDataPathLower {P} {dc3Top: DepsCohs3 P 0}
  {u v: ChainedFaceData dc3Top} (e: u = v)
  q (Hq: q <= P) ε (x: WholeMiddleCell dc3Top):
  chainedDataLowerCompare e q Hq ε x =
    f_equal (fun c => lowerChainFace c q Hq ε x)
      (chain2EndpointPackEq u.(lowerChain) v.(lowerChain)).
Proof.
  refine (eq_sym (f_equal_compose (@lowerChain P dc3Top)
    (fun c => lowerChainFace c q Hq ε x) e) • _).
  apply f_equal. now apply chain2EndpointPackUIP.
Defined.

Lemma chainedDataPathUpper {P} {dc3Top: DepsCohs3 P 0}
  {u v: ChainedFaceData dc3Top} (e: u = v)
  q (Hq: q <= P.+1) ε (x: WholeUpperCell dc3Top):
  chainedDataUpperCompare e q Hq ε x =
    f_equal (fun c => upperChainFace c q Hq ε x)
      (chain2EndpointPackEq u.(upperChain) v.(upperChain)).
Proof.
  refine (eq_sym (f_equal_compose (@upperChain P dc3Top)
    (fun c => upperChainFace c q Hq ε x) e) • _).
  apply f_equal. now apply chain2EndpointPackUIP.
Defined.

Lemma chainedDataPathSquareSource {P} {dc3Top: DepsCohs3 P 0}
  (u v: ChainedFaceData dc3Top) (e: u = v)
  q (Hq: q <= P) r (Hr: r <= q) ε ω (x: WholeUpperCell dc3Top):
  (f_equal (lowerChainFace u.(lowerChain) q Hq ε)
      (chainedDataUpperCompare e r (Hr ↕ ↑ Hq) ω x)
    • chainedDataLowerCompare e q Hq ε
        (upperChainFace v.(upperChain) r (Hr ↕ ↑ Hq) ω x))
    • v.(chainedExchange) q Hq r Hr ε ω x
  = u.(chainedExchange) q Hq r Hr ε ω x
    • (f_equal (lowerChainFace u.(lowerChain) r (Hr ↕ Hq) ω)
        (chainedDataUpperCompare e q.+1 (⇑ Hq) ε x)
       • chainedDataLowerCompare e r (Hr ↕ Hq) ω
           (upperChainFace v.(upperChain) q.+1 (⇑ Hq) ε x)).
Proof.
  destruct e.
  change (eq_refl • u.(chainedExchange) q Hq r Hr ε ω x =
    u.(chainedExchange) q Hq r Hr ε ω x • eq_refl).
  now exact (eq_trans_refl_l _ • eq_sym (eq_trans_refl_r _)).
Defined.

End FaceCausalityOn.


(** Changing a terminal filler preserves restrictions and their selected
    exchange paths. Maps preserve every layer in the extension spine, and
    reading a whole cell down a indexed chain commutes with them. *)

Module PaintingCausalityOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Import A.
Module Export Indexed := Faces.

Inductive CohsExtensionMap:
  forall {p k} {dc: DepsCohs p k},
    DepsCohsExtension p k dc -> DepsCohsExtension p k dc -> Type :=
| TopCohsMap {p} {dc: DepsCohs p 0}
    {E F: mkFrame (mkDepsRestr (depsCohs := dc)) -> HGpd}
    (f: forall d, E d -> F d):
    CohsExtensionMap (TopCohDep E) (TopCohDep F)
| AddCohsMap {p k} {dc: DepsCohs p.+1 k}
    {e e': DepsCohsExtension p.+1 k dc} (f: CohsExtensionMap e e'):
    CohsExtensionMap (AddCohDep dc e) (AddCohDep dc e').

Fixpoint mapExtendedPainting {p k} {dc: DepsCohs p k}
  {e e': DepsCohsExtension p k dc} (f: CohsExtensionMap e e'):
  forall d: mkFrame (mkDepsRestr (depsCohs := dc)),
    mkPainting (mkExtraDeps e) d -> mkPainting (mkExtraDeps e') d :=
  match f with
  | TopCohsMap f => fun d c => f d c
  | AddCohsMap f => fun d c => (c.1; mapExtendedPainting f (d; c.1) c.2)
  end.

Definition RestrictionSource {p k} {dc: DepsCohs p k}
  (e: DepsCohsExtension p k dc)
  (d: mkFrame (mkDepsRestr (depsCohs := dc)).(1)): HGpd :=
  mkPainting (AddRestrDep (mkDepsRestr (depsCohs := dc)) (mkExtraDeps e)) d.

Definition mapRestrictionSource {p k} {dc: DepsCohs p k}
  {e e': DepsCohsExtension p k dc} (f: CohsExtensionMap e e')
  (d: mkFrame (mkDepsRestr (depsCohs := dc)).(1))
  (c: RestrictionSource e d): RestrictionSource e' d :=
  (c.1; mapExtendedPainting f (d; c.1) c.2).

Fixpoint restrictionMap {p k} {dc: DepsCohs p k}
  {e e': DepsCohsExtension p k dc} (f: CohsExtensionMap e e')
  (q: nat) (Hq: q <= k) a
  (d: mkFrame (mkDepsRestr (depsCohs := dc)).(1))
  (c: RestrictionSource e d) {struct q}:
  mkRestrPainting e q Hq a d c =
    mkRestrPainting e' q Hq a d (mapRestrictionSource f d c).
Proof.
  destruct q as [|q].
  - now reflexivity.
  - destruct f as [p0 dc0 E F f0|p0 k0 dc0 e0 e1 f0].
    + now destruct (leR_O_contra Hq).
    + destruct c as [l c].
      cbn [mkRestrPainting mapRestrictionSource mapExtendedPainting].
      refine (eq_existT_curried eq_refl _).
      now exact (restrictionMap p0.+1 k0 dc0 e0 e1 f0 q (⇓ Hq) a (d; l) c).
Defined.

Inductive Cohs2ExtensionMap:
  forall {p k} {dc: DepsCohs2 p k},
    DepsCohs2Extension p k dc -> DepsCohs2Extension p k dc -> Type :=
| TopCohs2Map {p} {dc: DepsCohs2 p 0}
    {E F: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc)) -> HGpd}
    (f: forall d, E d -> F d):
    Cohs2ExtensionMap (TopCoh2Dep E) (TopCoh2Dep F)
| AddCohs2Map {p k} {dc: DepsCohs2 p.+1 k}
    {e e': DepsCohs2Extension p.+1 k dc} (f: Cohs2ExtensionMap e e'):
    Cohs2ExtensionMap (AddCoh2Dep dc e) (AddCoh2Dep dc e').

Fixpoint lowerExtensionMap {p k} {dc: DepsCohs2 p k}
  {e e': DepsCohs2Extension p k dc} (f: Cohs2ExtensionMap e e'):
  CohsExtensionMap (mkExtraCohs e) (mkExtraCohs e') :=
  match f with
  | TopCohs2Map f => TopCohsMap f
  | AddCohs2Map f => AddCohsMap (lowerExtensionMap f)
  end.

Definition upperExtension {p k} {dc: DepsCohs2 p k}
  (e: DepsCohs2Extension p k dc):
  DepsCohsExtension p k.+1 (proj1DepsCohs (mkDepsCohs dc)) :=
  AddCohDep (mkDepsCohs dc) (mkExtraCohs e).

Definition ExchangeFrame {p k} (dc: DepsCohs2 p k): HGpd :=
  mkFrame (mkDepsRestr (depsCohs := proj1DepsCohs (mkDepsCohs dc))).(1).

Definition ExchangeSource {p k} {dc: DepsCohs2 p k}
  (e: DepsCohs2Extension p k dc) (d: ExchangeFrame dc): HGpd :=
  RestrictionSource (upperExtension e) d.

Definition mapExchangeSource {p k} {dc: DepsCohs2 p k}
  {e e': DepsCohs2Extension p k dc} (f: Cohs2ExtensionMap e e')
  (d: ExchangeFrame dc) (c: ExchangeSource e d): ExchangeSource e' d :=
  mapRestrictionSource (AddCohsMap (lowerExtensionMap f)) d c.

Definition upperRestrictionMap {p k} {dc: DepsCohs2 p k}
  {e e': DepsCohs2Extension p k dc} (f: Cohs2ExtensionMap e e')
  q (Hq: q <= k.+1) a (d: ExchangeFrame dc) (c: ExchangeSource e d):
  restrCell (upperExtension e) q Hq a d c =
    restrCell (upperExtension e') q Hq a d (mapExchangeSource f d c).
Proof.
  refine (eq_existT_curried eq_refl _).
  now exact (restrictionMap (AddCohsMap (lowerExtensionMap f)) q Hq a d c).
Defined.

Definition generatedExchange {p k} {dc: DepsCohs2 p k}
  (e: DepsCohs2Extension p k dc)
  q (Hq: q <= k) r (Hr: r <= q) a b (d: ExchangeFrame dc) (c: ExchangeSource e d):
  restrCell dc.(_extraDepsCohs) q Hq a
      (restrCell (upperExtension e) r (Hr ↕ ↑ Hq) b d c).1
      (restrCell (upperExtension e) r (Hr ↕ ↑ Hq) b d c).2 =
    restrCell dc.(_extraDepsCohs) r (Hr ↕ Hq) b
      (restrCell (upperExtension e) q.+1 (⇑ Hq) a d c).1
      (restrCell (upperExtension e) q.+1 (⇑ Hq) a d c).2 :=
  (= (mkDepsCohs dc).(_cohs).2 q Hq r Hr a b d;
     mkCohPainting e q Hq r Hr a b d c).

Lemma generatedExchangeShift {p k} (dc: DepsCohs2 p.+1 k)
  (e: DepsCohs2Extension p.+1 k dc)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (d: ExchangeFrame (proj1DepsCohs2 dc))
  (c: ExchangeSource (AddCoh2Dep dc e) d):
  generatedExchange (AddCoh2Dep dc e) q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b d c =
    f_equal unassoc (generatedExchange e q Hq r Hr a b (d; c.1) c.2).
Proof.
  unfold generatedExchange.
  now refine (eq_sym (f_equal_unassoc_curried
    ((mkDepsCohs (proj1DepsCohs2 dc)).(_cohs).2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b d)
    (mkCohLayer dc.(_cohPaintings).2 dc.(_coh2Frames).2 q Hq r Hr a b d c.1)
    (mkCohPainting e q Hq r Hr a b (d; c.1) c.2))).
Defined.

Local Lemma unassocFixedPath {B: Type} {L: B -> Type}
  {C: {d: B &T L d} -> Type} {d: B} {l: L d} {c c': C (d; l)} (h: c = c'):
  f_equal unassoc ((= eq_refl; h): ((d; l); c) = ((d; l); c')) =
    ((= eq_refl; (= eq_refl; h)): (d; (l; c)) = (d; (l; c'))).
Proof. now destruct h. Defined.

Local Lemma pairHeadPath {B: Type} {L: B -> Type}
  {C: {d: B &T L d} -> Type} {T: Type} (F: forall d, L d -> T)
  {d: B} {l: L d} {c c': C (d; l)} (h: c = c'):
  f_equal (fun z: {d: B &T {l: L d &T C (d; l)}} => F z.1 z.2.1)
    ((= eq_refl; (= eq_refl; h)): (d; (l; c)) = (d; (l; c'))) = eq_refl.
Proof. now destruct h. Defined.

Lemma upperRestrictionMapShift {p k} {dc: DepsCohs2 p.+1 k}
  {e e': DepsCohs2Extension p.+1 k dc} (f: Cohs2ExtensionMap e e')
  q (Hq: q <= k.+1) a
  (d: ExchangeFrame (proj1DepsCohs2 dc)) (c: ExchangeSource (AddCoh2Dep dc e) d):
  upperRestrictionMap (AddCohs2Map f) q.+1 (⇑ Hq) a d c =
    f_equal unassoc (upperRestrictionMap f q Hq a (d; c.1) c.2).
Proof.
  unfold upperRestrictionMap.
  cbn [restrictionMap lowerExtensionMap].
  now exact (eq_sym (@unassocFixedPath _ _ _
    (restrCell (upperExtension e) q Hq a (d; c.1) c.2).1.1
    (restrCell (upperExtension e) q Hq a (d; c.1) c.2).1.2 _ _
    (restrictionMap (AddCohsMap (lowerExtensionMap f)) q Hq a (d; c.1) c.2))).
Defined.

Lemma lowerZeroRestrictionMap {p k} {dc: DepsCohs2 p k}
  {e e': DepsCohs2Extension p k dc} (f: Cohs2ExtensionMap e e')
  q (Hq: q <= k) a b (d: ExchangeFrame dc) (c: ExchangeSource e d):
  f_equal (fun z => restrCell dc.(_extraDepsCohs) 0 leR_O b z.1 z.2)
    (upperRestrictionMap f q.+1 (⇑ Hq) a d c) = eq_refl.
Proof.
  unfold upperRestrictionMap.
  cbn [restrictionMap].
  unfold restrCell. cbn [mkRestrPainting].
  now exact (@pairHeadPath _
    (fun d => mkLayer (mkDepsCohs dc).(_deps).(_restrFrames).2 d)
    (fun dl => mkPainting (mkDepsCohs dc).(_extraDeps) dl) _
    (fun d l => (mkRestrFrame 0 leR_O b d; nth l b))
    (restrCell (upperExtension e) q.+1 (⇑ Hq) a d c).1
    (restrCell (upperExtension e) q.+1 (⇑ Hq) a d c).2.1 _ _
    (restrictionMap (lowerExtensionMap f) q Hq a (d; c.1) c.2)).
Defined.

Fixpoint generatedExchangeMap {p k} {dc: DepsCohs2 p k}
  {e e': DepsCohs2Extension p k dc} (f: Cohs2ExtensionMap e e')
  q (Hq: q <= k) r (Hr: r <= q) a b (d: ExchangeFrame dc) (c: ExchangeSource e d)
  {struct r}:
  generatedExchange e q Hq r Hr a b d c
    • f_equal (fun z => restrCell dc.(_extraDepsCohs) r (Hr ↕ Hq) b z.1 z.2)
      (upperRestrictionMap f q.+1 (⇑ Hq) a d c) =
  f_equal (fun z => restrCell dc.(_extraDepsCohs) q Hq a z.1 z.2)
      (upperRestrictionMap f r (Hr ↕ ↑ Hq) b d c)
    • generatedExchange e' q Hq r Hr a b d (mapExchangeSource f d c).
Proof.
  destruct r as [|r].
  - rewrite lowerZeroRestrictionMap.
    cbn [upperRestrictionMap restrictionMap f_equal].
    rewrite eq_trans_refl_l, eq_trans_refl_r.
    now reflexivity.
  - destruct q as [|q]; [now destruct (leR_O_contra Hr)|].
    destruct f as [p0 dc0 E F f0|p0 k0 dc0 e0 e1 f0].
    + now destruct (leR_O_contra Hq).
    + rewrite (generatedExchangeShift dc0 e0 q (⇓ Hq) r (⇓ Hr) a b d c),
        (generatedExchangeShift dc0 e1 q (⇓ Hq) r (⇓ Hr) a b d
          (mapExchangeSource (AddCohs2Map f0) d c)),
        (upperRestrictionMapShift f0 q.+1 Hq a d c),
        (upperRestrictionMapShift f0 r (⇓ Hr ↕ ↑ (⇓ Hq)) b d c).
      pose proof (f_equal (fun h => f_equal unassoc h)
        (generatedExchangeMap p0.+1 k0 dc0 e0 e1 f0 q (⇓ Hq) r (⇓ Hr) a b (d; c.1) c.2)) as h.
      cbn beta in h.
      rewrite 2 eq_trans_map_distr in h.
      rewrite (f_equal_compose
        (fun z => restrCell dc0.(_extraDepsCohs) r (⇓ Hr ↕ ⇓ Hq) b z.1 z.2)
        unassoc (upperRestrictionMap f0 q.+1 Hq a (d; c.1) c.2)),
        (f_equal_compose
          (fun z => restrCell dc0.(_extraDepsCohs) q (⇓ Hq) a z.1 z.2)
          unassoc (upperRestrictionMap f0 r (⇓ Hr ↕ ↑ (⇓ Hq)) b (d; c.1) c.2)) in h.
      rewrite (f_equal_compose unassoc
        (fun z => restrCell dc0.(1).(_extraDepsCohs) r.+1 (Hr ↕ Hq) b z.1 z.2)
        (upperRestrictionMap f0 q.+1 Hq a (d; c.1) c.2)),
        (f_equal_compose unassoc
          (fun z => restrCell dc0.(1).(_extraDepsCohs) q.+1 Hq a z.1 z.2)
          (upperRestrictionMap f0 r (⇓ Hr ↕ ↑ (⇓ Hq)) b (d; c.1) c.2)).
      now exact h.
Defined.

(** Descent along a indexed chain. The descended frame is kept literally
    unchanged. *)

Fixpoint chain2Ext {P K} {dcTop: DepsCohs2 P K}
  (e: DepsCohs2Extension P K dcTop)
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc):
  DepsCohs2Extension p k dc :=
  match c with
  | DepsCohs2ChainNil => e
  | DepsCohs2ChainCons c => AddCoh2Dep _ (chain2Ext e c)
  end.

Fixpoint chain2Map {P K} {dcTop: DepsCohs2 P K}
  {e e': DepsCohs2Extension P K dcTop} (f: Cohs2ExtensionMap e e')
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc):
  Cohs2ExtensionMap (chain2Ext e c) (chain2Ext e' c) :=
  match c with
  | DepsCohs2ChainNil => f
  | DepsCohs2ChainCons c => AddCohs2Map (chain2Map f c)
  end.

Definition UpperFrame {P K} (dc: DepsCohs2 P K): HGpd :=
  mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc)).

Definition UpperCell {P K} {dc: DepsCohs2 P K}
  (e: DepsCohs2Extension P K dc): HGpd :=
  {d: UpperFrame dc & mkPainting (mkExtraDeps (mkExtraCohs e)) d}.

Definition ExchangeCell {p k} {dc: DepsCohs2 p k}
  (e: DepsCohs2Extension p k dc): HGpd :=
  {d: ExchangeFrame dc & ExchangeSource e d}.

Definition mapUpperCell {P K} {dc: DepsCohs2 P K}
  {e e': DepsCohs2Extension P K dc} (f: Cohs2ExtensionMap e e')
  (x: UpperCell e): UpperCell e' :=
  (x.1; mapExtendedPainting (lowerExtensionMap f) x.1 x.2).

Definition mapExchangeCell {p k} {dc: DepsCohs2 p k}
  {e e': DepsCohs2Extension p k dc} (f: Cohs2ExtensionMap e e')
  (x: ExchangeCell e): ExchangeCell e' :=
  (x.1; mapExchangeSource f x.1 x.2).

Fixpoint readUpperFrame {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc)
  (d: UpperFrame dcTop): ExchangeFrame dc :=
  match c with
  | DepsCohs2ChainNil => d.1.1
  | DepsCohs2ChainCons c => (readUpperFrame c d).1
  end.

Fixpoint readUpperPainting {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc)
  (e: DepsCohs2Extension P K dcTop) (d: UpperFrame dcTop)
  (Q: mkPainting (mkExtraDeps (mkExtraCohs e)) d):
  ExchangeSource (chain2Ext e c) (readUpperFrame c d) :=
  match c with
  | DepsCohs2ChainNil => (d.1.2; (d.2; Q))
  | DepsCohs2ChainCons c => ((readUpperFrame c d).2; readUpperPainting c e d Q)
  end.

Definition readUpper {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc)
  (e: DepsCohs2Extension P K dcTop) (x: UpperCell e): ExchangeCell (chain2Ext e c) :=
  (readUpperFrame c x.1; readUpperPainting c e x.1 x.2).

Lemma readUpperPaintingMap {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc)
  {e e': DepsCohs2Extension P K dcTop} (f: Cohs2ExtensionMap e e')
  (d: UpperFrame dcTop) (Q: mkPainting (mkExtraDeps (mkExtraCohs e)) d):
  readUpperPainting c e' d (mapExtendedPainting (lowerExtensionMap f) d Q) =
    mapExchangeSource (chain2Map f c) (readUpperFrame c d) (readUpperPainting c e d Q).
Proof.
  induction c as [|p0 k0 dc0 c IH].
  - now reflexivity.
  - cbn [readUpperPainting readUpperFrame chain2Map chain2Ext mapExchangeSource
      mapRestrictionSource mapExtendedPainting lowerExtensionMap].
    now rewrite IH.
Defined.

Lemma readUpperMap {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (c: DepsCohs2Chain dcTop dc)
  {e e': DepsCohs2Extension P K dcTop} (f: Cohs2ExtensionMap e e')
  (x: UpperCell e):
  readUpper c e' (mapUpperCell f x) = mapExchangeCell (chain2Map f c) (readUpper c e x).
Proof.
  refine (eq_existT_curried eq_refl _).
  now exact (readUpperPaintingMap c f x.1 x.2).
Defined.

Definition lowerReadCell {p k} {dc: DepsCohs2 p.+1 k}
  (e: DepsCohs2Extension p.+1 k dc) (x: ExchangeCell e):
  ExchangeCell (AddCoh2Dep dc e) := (x.1.1; (x.1.2; x.2)).

Local Lemma lowerReadCellRew {p k} {dc: DepsCohs2 p.+1 k}
  {e e': DepsCohs2Extension p.+1 k dc} (h: e = e') (x: ExchangeCell e):
  rew [ExchangeCell] f_equal (AddCoh2Dep dc) h in lowerReadCell e x =
    lowerReadCell e' (rew [ExchangeCell] h in x).
Proof. now destruct h. Defined.

(** The upper reading chain has one extra initial descent. *)
Fixpoint upperReadChain {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (c: DepsCohs3Chain dcTop dc):
  DepsCohs2Chain (mkDepsCohs2 dcTop) (proj1DepsCohs2 (mkDepsCohs2 dc)) :=
  match c with
  | DepsCohs3ChainNil => DepsCohs2ChainCons DepsCohs2ChainNil
  | DepsCohs3ChainCons c => DepsCohs2ChainCons (upperReadChain c)
  end.

Fixpoint chain2ExtOf3 {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (c: DepsCohs3Chain dcTop dc):
  chain2Ext dcTop.(_extraDepsCohs2) (cohs3ChainDepsCohs2 c) = dc.(_extraDepsCohs2) :=
  match c with
  | DepsCohs3ChainNil => eq_refl
  | DepsCohs3ChainCons c => f_equal (AddCoh2Dep _) (chain2ExtOf3 c)
  end.

Lemma readUpperIndexed {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (c: DepsCohs3Chain dcTop dc)
  (x: UpperCell dcTop.(_extraDepsCohs2)):
  rew [ExchangeCell] chain2ExtOf3 c in
    readUpper (cohs3ChainDepsCohs2 c) dcTop.(_extraDepsCohs2) x =
  deepCell (upperReadChain c) x.
Proof.
  induction c as [|p0 k0 dc0 c IH].
  - now reflexivity.
  - refine (lowerReadCellRew (chain2ExtOf3 c)
      (readUpper (cohs3ChainDepsCohs2 c) dcTop.(_extraDepsCohs2) x) • _).
    now exact (f_equal (lowerReadCell dc0.(_extraDepsCohs2)) IH).
Defined.

End PaintingCausalityOn.


(** Rebuilding a descended face depends on the existing two-level data,
    independently of the filler of the cell whose boundary is read. *)

Module FrameCausalityOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).
Import A.
Module Export Indexed := Faces.
Module Causality := FaceCausalityOn A Core Faces.
Module Painting := PaintingCausalityOn A Core Faces.

Definition RebuildCell {p k} (dc2: DepsCohs2 p k): Type :=
  {D: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))).(1) &T
   (mkPaintings (mkDepsRestr (depsCohs := dc2.(_depsCohs));
     mkExtraDeps dc2.(_extraDepsCohs))).2 D}.

Definition RebuildChain {P K} (dc2Top: DepsCohs2 P K)
  {p k} (dc2: DepsCohs2 p k): Type :=
  DepsCohsChain (mkDepsCohs dc2Top) (proj1DepsCohs (mkDepsCohs dc2)).

Definition rebuildFromChain {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2)
  (upper: RebuildChain dc2Top dc2) (Y: RebuildCell dc2): RebuildCell dc2 :=
  deepCell c (getPainting (cohsChainExt upper) Y.1 Y.2).

Definition ContractionData {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2): Type :=
  {upper: RebuildChain dc2Top dc2 &T
   forall Y: RebuildCell dc2, rebuildFromChain c upper Y = Y}.

Definition nextContractionData {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p.+1 k} (c: DepsCohs2Chain dc2Top dc2)
  (r: ContractionData c): ContractionData (DepsCohs2ChainCons c) :=
  (DepsCohsChainCons r.1;
   fun Y: RebuildCell (proj1DepsCohs2 dc2) =>
     f_equal (fun w: RebuildCell dc2 =>
       ((w.1.1; (w.1.2; w.2)): RebuildCell (proj1DepsCohs2 dc2)))
       (r.2 ((Y.1; Y.2.1); Y.2.2))).

Fixpoint canonicalContractionData {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2): ContractionData c :=
  match c as c0 return ContractionData c0 with
  | DepsCohs2ChainNil => (DepsCohsChainCons DepsCohsChainNil; fun Y => eq_refl)
  | DepsCohs2ChainCons c0 => nextContractionData c0 (canonicalContractionData c0)
  end.

(** The chain used to rebuild a face forgets the upper extension data.
    Keeping its contraction in the same pair preserves the chosen paths. *)
Definition forgetRebuildData {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3)
  (r: Causality.RebuildData a): ContractionData (cohs3ChainDepsCohs2 a) :=
  (cohs2ChainDepsCohs r.1; r.2).

Lemma forgetCanonicalRebuildData {P K} {dc3Top: DepsCohs3 P K}
  {p k} {dc3: DepsCohs3 p k} (a: DepsCohs3Chain dc3Top dc3):
  forgetRebuildData a (Causality.canonicalRebuildData a) =
    canonicalContractionData (cohs3ChainDepsCohs2 a).
Proof.
  induction a as [|p k dc3 a IH]; [now reflexivity|].
  change (nextContractionData (cohs3ChainDepsCohs2 a)
      (forgetRebuildData a (Causality.canonicalRebuildData a)) =
    nextContractionData (cohs3ChainDepsCohs2 a)
      (canonicalContractionData (cohs3ChainDepsCohs2 a))).
  now exact (f_equal (nextContractionData (cohs3ChainDepsCohs2 a)) IH).
Defined.

Definition CellAt {p k} (dc: DepsCohs p k): Type :=
  {d: mkFrame dc.(_deps) &T mkPainting dc.(_extraDeps) d}.

Definition rebuildLower {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (chain: DepsCohs2Chain dcTop dc)
  (x: CellAt dc.(_depsCohs)): CellAt dcTop.(_depsCohs) :=
  getPainting (cohsChainExt (cohs2ChainDepsCohs chain)) x.1 x.2.

Definition rebuildUpper {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (upper: RebuildChain dcTop dc)
  (x: RebuildCell dc): CellAt (mkDepsCohs dcTop) :=
  getPainting (cohsChainExt upper) x.1 x.2.

Definition rebuiltFace {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (chain: DepsCohs2Chain dcTop dc)
  (upper: RebuildChain dcTop dc) q (Hq: q <= k) a (x: RebuildCell dc):
  CellAt dcTop.(_depsCohs) :=
  faceDeep chain q Hq a (rebuildUpper upper x).1 (rebuildUpper upper x).2.

Definition rebuiltFacePath {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (chain: DepsCohs2Chain dcTop dc)
  (data: ContractionData chain) q (Hq: q <= k) a (x: RebuildCell dc):
  rebuiltFace chain data.1 q Hq a x = faceAt chain q Hq a x.1 x.2 :=
  f_equal (fun y: RebuildCell dc => faceAt chain q Hq a y.1 y.2) (data.2 x).

Definition upperReadout {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (upper: RebuildChain dcTop dc)
  (e: DepsCohs2Extension p k dc) q (Hq: q <= k.+1) a
  (d: Painting.ExchangeFrame dc) (x: Painting.ExchangeSource e d):
  CellAt (mkDepsCohs dcTop) :=
  rebuildUpper upper (restrCell (Painting.upperExtension e) q Hq a d x).

Definition upperReadoutMap {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (upper: RebuildChain dcTop dc)
  {e e': DepsCohs2Extension p k dc} (f: Painting.Cohs2ExtensionMap e e')
  q (Hq: q <= k.+1) a (d: Painting.ExchangeFrame dc) (x: Painting.ExchangeSource e d):
  upperReadout upper e q Hq a d x =
    upperReadout upper e' q Hq a d (Painting.mapExchangeSource f d x) :=
  f_equal (rebuildUpper upper) (Painting.upperRestrictionMap f q Hq a d x).

Definition reconstructedExchange {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (chain: DepsCohs2Chain dcTop dc)
  (data: ContractionData chain) (e: DepsCohs2Extension p k dc)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (d: Painting.ExchangeFrame dc) (x: Painting.ExchangeSource e d):
  faceDeep chain q Hq a
      (upperReadout data.1 e r (Hr ↕ ↑ Hq) b d x).1
      (upperReadout data.1 e r (Hr ↕ ↑ Hq) b d x).2 =
    faceDeep chain r (Hr ↕ Hq) b
      (upperReadout data.1 e q.+1 (⇑ Hq) a d x).1
      (upperReadout data.1 e q.+1 (⇑ Hq) a d x).2 :=
  rebuiltFacePath chain data q Hq a
      (restrCell (Painting.upperExtension e) r (Hr ↕ ↑ Hq) b d x)
  • (f_equal (rebuildLower chain) (Painting.generatedExchange e q Hq r Hr a b d x)
    • eq_sym (rebuiltFacePath chain data r (Hr ↕ Hq) b
        (restrCell (Painting.upperExtension e) q.+1 (⇑ Hq) a d x))).

Local Lemma conjugatedSquare {V W: Type}
  (oldL newL oldR newR: V -> W)
  (left: forall x, oldL x = newL x) (right: forall x, oldR x = newR x)
  {x x' y y': V} (u: x = x') (v: y = y')
  (c: newL x = newR y) (c': newL x' = newR y')
  (square: c • f_equal newR v = f_equal newL u • c'):
  (left x • (c • eq_sym (right y))) • f_equal oldR v =
    f_equal oldL u • (left x' • (c' • eq_sym (right y'))).
Proof.
  destruct u, v; cbn [f_equal] in square |- *.
  rewrite eq_trans_refl_l, eq_trans_refl_r in square. subst c'.
  now exact (eq_trans_refl_r _ • eq_sym (eq_trans_refl_l _)).
Defined.

(** The terminal filler map preserves the exchange after rebuilding its
    two faces, retaining the contraction paths. *)
Lemma reconstructedExchangeMap {P K} {dcTop: DepsCohs2 P K}
  {p k} {dc: DepsCohs2 p k} (chain: DepsCohs2Chain dcTop dc)
  (data: ContractionData chain)
  {e e': DepsCohs2Extension p k dc} (f: Painting.Cohs2ExtensionMap e e')
  q (Hq: q <= k) r (Hr: r <= q) a b
  (d: Painting.ExchangeFrame dc) (x: Painting.ExchangeSource e d):
  reconstructedExchange chain data e q Hq r Hr a b d x
    • f_equal (fun y: CellAt (mkDepsCohs dcTop) => faceDeep chain r (Hr ↕ Hq) b y.1 y.2)
        (upperReadoutMap data.1 f q.+1 (⇑ Hq) a d x) =
  f_equal (fun y: CellAt (mkDepsCohs dcTop) => faceDeep chain q Hq a y.1 y.2)
      (upperReadoutMap data.1 f r (Hr ↕ ↑ Hq) b d x)
    • reconstructedExchange chain data e' q Hq r Hr a b d
        (Painting.mapExchangeSource f d x).
Proof.
  pose proof (f_equal (fun h => f_equal (rebuildLower chain) h)
    (Painting.generatedExchangeMap f q Hq r Hr a b d x)) as h.
  cbn beta in h.
  rewrite 2 eq_trans_map_distr in h.
  rewrite (f_equal_compose
    (fun z => restrCell dc.(_extraDepsCohs) r (Hr ↕ Hq) b z.1 z.2)
    (rebuildLower chain) (Painting.upperRestrictionMap f q.+1 (⇑ Hq) a d x)),
    (f_equal_compose
      (fun z => restrCell dc.(_extraDepsCohs) q Hq a z.1 z.2)
      (rebuildLower chain) (Painting.upperRestrictionMap f r (Hr ↕ ↑ Hq) b d x)) in h.
  unfold upperReadoutMap.
  rewrite (f_equal_compose (rebuildUpper data.1)
    (fun y => faceDeep chain r (Hr ↕ Hq) b y.1 y.2)
    (Painting.upperRestrictionMap f q.+1 (⇑ Hq) a d x)),
    (f_equal_compose (rebuildUpper data.1)
      (fun y => faceDeep chain q Hq a y.1 y.2)
      (Painting.upperRestrictionMap f r (Hr ↕ ↑ Hq) b d x)).
  now exact (conjugatedSquare
    (rebuiltFace chain data.1 q Hq a) (fun y => faceAt chain q Hq a y.1 y.2)
    (rebuiltFace chain data.1 r (Hr ↕ Hq) b) (fun y => faceAt chain r (Hr ↕ Hq) b y.1 y.2)
    (rebuiltFacePath chain data q Hq a) (rebuiltFacePath chain data r (Hr ↕ Hq) b)
    (Painting.upperRestrictionMap f r (Hr ↕ ↑ Hq) b d x)
    (Painting.upperRestrictionMap f q.+1 (⇑ Hq) a d x)
    (f_equal (rebuildLower chain) (Painting.generatedExchange e q Hq r Hr a b d x))
    (f_equal (rebuildLower chain) (Painting.generatedExchange e' q Hq r Hr a b d
      (Painting.mapExchangeSource f d x))) h).
Defined.

(** The contraction, descended extension and whole-cell reader form one
    package, so its equality transports the actions and selected exchange
    together. *)
Definition ReadoutPackage {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc): Type :=
  {data: ContractionData (cohs3ChainDepsCohs2 a) &T
   {e: DepsCohs2Extension p k dc.(_depsCohs2) &T
    Causality.WholeUpperCell dcTop -> Painting.ExchangeCell e}}.

Definition canonicalReadoutPackage {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc): ReadoutPackage a :=
  (canonicalContractionData (cohs3ChainDepsCohs2 a);
   (Painting.chain2Ext dcTop.(_extraDepsCohs2) (cohs3ChainDepsCohs2 a);
    Painting.readUpper (cohs3ChainDepsCohs2 a) dcTop.(_extraDepsCohs2))).

Definition indexedReadoutPackage {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc): ReadoutPackage a :=
  (forgetRebuildData a (Causality.canonicalRebuildData a);
   (dc.(_extraDepsCohs2); deepCell (Causality.canonicalRebuildData a).1)).

Lemma upperReadChainCanonical {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc):
  Painting.upperReadChain a = (Causality.canonicalRebuildData a).1.
Proof.
  induction a as [|p0 k0 dc0 a IH]; [now reflexivity|].
  change (DepsCohs2ChainCons (Painting.upperReadChain a) =
    DepsCohs2ChainCons (Causality.canonicalRebuildData a).1).
  now exact (f_equal (fun c => DepsCohs2ChainCons c) IH).
Defined.

Local Lemma functionTransportPoint {I X: Type} {B: I -> Type}
  {i j: I} (e: i = j) (f: X -> B i) (x: X):
  (rew [fun i => X -> B i] e in f) x = rew [B] e in f x.
Proof. now destruct e. Defined.

Lemma readoutPackageNormalize {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc):
  canonicalReadoutPackage a = indexedReadoutPackage a.
Proof.
  unfold canonicalReadoutPackage, indexedReadoutPackage.
  refine (eq_existT_nondep (eq_sym (forgetCanonicalRebuildData a)) _).
  refine (eq_existT_curried (Painting.chain2ExtOf3 a) _).
  apply functional_extensionality_dep; intro x.
  refine (functionTransportPoint (Painting.chain2ExtOf3 a)
    (Painting.readUpper (cohs3ChainDepsCohs2 a) dcTop.(_extraDepsCohs2)) x • _).
  refine (Painting.readUpperIndexed a x • _).
  now exact (f_equal (fun c => deepCell c x) (upperReadChainCanonical a)).
Defined.

Definition readoutData {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc)
  (package: ReadoutPackage a): Causality.LocalFaceData dcTop k :=
  @Causality.Build_LocalFaceData P K dcTop k
    (fun q Hq b x => faceDeep (cohs3ChainDepsCohs2 a) q Hq b x.1 x.2)
    (fun q Hq b x => upperReadout package.1.1 package.2.1 q Hq b
      (package.2.2 x).1 (package.2.2 x).2)
    (fun q Hq r Hr b c x =>
      reconstructedExchange (cohs3ChainDepsCohs2 a) package.1 package.2.1
        q Hq r Hr b c (package.2.2 x).1 (package.2.2 x).2).

Definition canonicalReadoutDataNormalize {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc):
  readoutData a (canonicalReadoutPackage a) = Causality.canonicalLocalFaceData a :=
  f_equal (readoutData a) (readoutPackageNormalize a).

Local Lemma constantPath {X Y: Type} (y: Y) {x x': X} (e: x = x'):
  f_equal (fun _ => y) e = eq_refl.
Proof. now destruct e. Defined.

Lemma canonicalReadoutLower {P K} {dcTop: DepsCohs3 P K}
  {p k} {dc: DepsCohs3 p k} (a: DepsCohs3Chain dcTop dc):
  f_equal (fun d: Causality.LocalFaceData dcTop k => d.(Causality.lowerFace))
    (canonicalReadoutDataNormalize a) = eq_refl.
Proof.
  unfold canonicalReadoutDataNormalize.
  rewrite (f_equal_compose (readoutData a)
    (fun d => d.(Causality.lowerFace)) (readoutPackageNormalize a)).
  now apply constantPath.
Defined.

End FrameCausalityOn.
