(** The presentation round trip identifies each cell with its strict graph
    fiber. These groupoid isomorphisms commute with the extracted faces. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet LeSProp NatLemmas Notation Limit.
From Bonak.νStrictGpd Require Import Layer νStrictGpd.
From Bonak.Category.Groupoid Require Import GraphFiberRoundtrip StructureIdentity.
From Bonak.Presheaf.StrictGpd Require Import Presentation.
From Bonak.Equiv.StrictGpd Require Import
  Constructions PresheafEquiv.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafRoundtripOn (A: LayerSig) (S: νStrictGpdSig A)
  (Base: ConstructionsSig A S).
Import A.
Module Export Core := S.
Module Export Faces := Base.Faces.
Module Export Reconstruction := Base.Reconstruction.
Module Export Extraction := Base.Extraction.

Section RoundTrip.
Variable psh: νStrictGpdPresentation arity.

(** Match the synthesized extraction chains with their presentation data. *)
Definition PshPack {M P K} (PCTop: PshDepsCohs psh M P K): Type :=
  {p: nat &T {k: nat &T
    {PC: PshDepsCohs psh M p k &T PshCohsChain psh PCTop PC}}}.

Definition pshPackStep {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): PshPack PCTop :=
  (match s.1 as p0 return
     {k: nat &T {PC: PshDepsCohs psh M p0 k &T PshCohsChain psh PCTop PC}} ->
     PshPack PCTop with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1PshDepsCohs psh s'.2.1;
       PshCohsChainCons s'.2.2)))
   end) s.2.

Fixpoint pshChain2Down {M P K} (PCTop: PshDepsCohs psh M P K) (j: nat):
  PshPack PCTop :=
  match j with
  | 0 => (P; (K; (PCTop; PshCohsChainNil)))
  | S j => pshPackStep (pshChain2Down PCTop j)
  end.

Definition pshPackDC {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): DCPack (pshDepsCohs psh PCTop) :=
  (s.1; (s.2.1; (pshDepsCohs psh s.2.2.1; pshCohsChainCohs psh s.2.2.2))).

Lemma pshPackStepStage {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): (pshPackStep s).1 = Nat.pred s.1.
Proof.
  destruct s as (p, s2). now destruct p.
Defined.

Lemma pshChain2DownStage {M P K} (PCTop: PshDepsCohs psh M P K) (j: nat):
  (pshChain2Down PCTop j).1 = P - j.
Proof.
  induction j.
  - now rewrite sub0r.
  - now rewrite subSuccR, pshPackStepStage, IHj.
Defined.

Lemma pshPackDCStep {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): pshPackDC (pshPackStep s) = dcStep (pshPackDC s).
Proof.
  destruct s as (p, (k, (PC, C))). now destruct p.
Defined.

Lemma gfChainAlign (m j: nat):
  dc2PackDeps (chain2Down (νDepsCohs2At (pshFrom psh m.+1)) j) =
  pshPackDC (pshChain2Down (towerPshDepsCohs psh (pshTw psh m)
    (pshTwRp psh m)) j).
Proof.
  induction j.
  - now reflexivity.
  - now rewrite dc2PackDepsStep, IHj, pshPackDCStep.
Defined.

(** The graph-fiber isomorphisms follow the same descent as the extracted levels. *)
Fixpoint gfIso (m n: nat) {struct n}:
  forall (L: nat), L = n + m.+1 ->
  HSetGroupoidIso (psh.(G0) L) (gF0 (pshFrom psh m.+1) n) :=
  match n return forall L: nat, L = n + m.+1 ->
    HSetGroupoidIso (psh.(G0) L) (gF0 (pshFrom psh m.+1) n) with
  | 0 => fun L HL =>
      rew [fun l => HSetGroupoidIso (psh.(G0) l) (νTotal (pshFrom psh m.+1))]
        (eq_sym HL) in graphUnitIso (mkPshFrame psh (towerPshDeps psh (pshTw psh m)))
  | S n => fun L HL => gfIso m.+1 n L (HL • plus_n_Sm n m.+1)
  end.

Lemma gfIsoIrr (m n L: nat) (HL HL': L = n + m.+1):
  gfIso m n L HL = gfIso m n L HL'.
Proof. now rewrite (natUIP HL HL'). Defined.

Definition gfF0Iso (n: nat): HSetGroupoidIso (psh.(G0) n) (gF0 (f psh) n) :=
  match n with
  | 0 => graphUnitIso (terminalFunctor (psh.(G0) 0))
  | S n => gfIso 0 n n.+1 (f_equal S (plus_n_O n) • plus_n_Sm n 0)
  end.

(** Face naturality at the bottom of the descent, then at every level. *)
Lemma gfFaceBottom (m dim: nat) (Hdim: dim <= m.+1) (ε: arity):
  graphUnit (mkPshFrame psh (towerPshDeps psh (pshTw psh m.+1))) ⨟ᶠ
    νFaceFuel (pshFrom psh m.+1) (m.+1 - dim) ε ≐
  psh.(GFace) m.+1 dim Hdim ε ⨟ᶠ
    graphUnit (mkPshFrame psh (towerPshDeps psh (pshTw psh m))).
Proof.
  unfold νFaceFuel.
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  refine (feqWhiskerR (graphUnitProj _) _ •ᶠ _).
  rewrite (gfChainAlign m (m.+1 - dim)).
  assert (SE: (pshChain2Down (towerPshDepsCohs psh (pshTw psh m)
    (pshTwRp psh m)) (m.+1 - dim)).1 = dim).
  { rewrite pshChain2DownStage. now exact (subSubCancel Hdim). }
  refine (pshνFace psh
    ((pshChain2Down (towerPshDepsCohs psh (pshTw psh m) (pshTwRp psh m))
      (m.+1 - dim)).2.2.2) (leR_eq (eq_sym SE) Hdim) ε •ᶠ _).
  now apply feqWhiskerR, pshFaceDimIrr.
Defined.

Lemma gfFaceBottom0 (dim: nat) (Hdim: dim <= 0) (ε: arity):
  graphUnit (mkPshFrame psh (towerPshDeps psh (pshTw psh 0))) ⨟ᶠ
    νFaceFuel (f psh) (0 - dim) ε ≐
  psh.(GFace) 0 dim Hdim ε ⨟ᶠ graphUnit (terminalFunctor (psh.(G0) 0)).
Proof.
  destruct dim. 2: now destruct (leR_O_contra Hdim).
  unfold νFaceFuel.
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  refine (feqWhiskerR (graphUnitProj _) _ •ᶠ _).
  unfold νFace. cbn [chain2Down dc2PackDeps cohsChainNext cohsChainExt getFrame getPainting].
  refine (_ •ᶠ mkPshLayerFace psh
    (towerPshDeps psh (tower1 psh)).(_pshPaintings psh)
    (towerPshDeps psh (tower1 psh)).(_pshRestrs psh) leR_O ε).
  unshelve econstructor; now intros.
Defined.

Fixpoint gfFaceIso (m n: nat) {struct n}:
  forall (L: nat) (HL: L = n + m.+1) (HL2: L.+1 = n.+1 + m.+1)
    (dim: nat) (Hd: dim <= n + m.+1) (Hd': dim <= L) (ε: arity),
  psh.(GFace) L dim Hd' ε ⨟ᶠ hsetGroupoidIsoFunctor (gfIso m n L HL) ≐
  hsetGroupoidIsoFunctor (gfIso m n.+1 L.+1 HL2) ⨟ᶠ
    gFace (pshFrom psh m.+1) n dim Hd ε.
Proof.
  destruct n; intros.
  - set (HLs := eq_sym HL).
    rewrite (natUIP HL (eq_sym HLs)).
    clearbody HLs. clear HL. destruct HLs.
    cbn [gfIso].
    rewrite (natUIP (HL2 • plus_n_Sm 0 m.+1) eq_refl).
    now exact (feqSym (gfFaceBottom m dim Hd' ε)).
  - now exact (gfFaceIso m.+1 n L
      (HL • plus_n_Sm n m.+1) (HL2 • plus_n_Sm n.+1 m.+1)
      dim (leR_eq_r (plus_n_Sm n m.+1) Hd) Hd' ε).
Defined.

Lemma gfFaceIsoTop (n q: nat) (Hq: q <= n) (ε: arity):
  psh.(GFace) n q Hq ε ⨟ᶠ hsetGroupoidIsoFunctor (gfF0Iso n) ≐
  hsetGroupoidIsoFunctor (gfF0Iso n.+1) ⨟ᶠ (g (f psh)).(GFace) n q Hq ε.
Proof.
  destruct n.
  - unfold gfF0Iso.
    rewrite (gfIsoIrr 0 0 _
      (f_equal S (plus_n_O 0) • plus_n_Sm 0 0) eq_refl).
    now exact (feqSym (gfFaceBottom0 q Hq ε)).
  - now exact (gfFaceIso 0 n n.+1
      (f_equal S (plus_n_O n) • plus_n_Sm n 0)
      (f_equal S (plus_n_O n.+1) • plus_n_Sm n.+1 0)
      q (leR_eq_r (f_equal S (plus_n_O n) • plus_n_Sm n 0) Hq) Hq ε).
Defined.

Definition gf: PresheafIso psh (g (f psh)) :=
  @Build_PresheafIso arity psh (g (f psh)) gfF0Iso gfFaceIsoTop.

End RoundTrip.
End PresheafRoundtripOn.

Module PresheafRoundtrip (A: LayerSig).
Module Maps := Constructions A.
Include PresheafRoundtripOn A Maps.Core Maps.
End PresheafRoundtrip.
