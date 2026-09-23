(** Groupoid-valued presheaves presented by face maps and coherent
    exchange paths, with an [HGpd] of cells at each level. The arity
    parameter is an arbitrary type.

    The exchange paths are data. [GFaceCoh2] identifies their two composites
    around the hexagon for three deletions. Since identity types of an
    [HGpd] are h-sets, any two proofs of this hexagon agree by [GUIP]. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation LeSProp νGpd.HGpd.

From Bonak.Presheaf Require Import FaceStructure.

From Bonak.Lib Require Import Funext.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Primitive Projections.
Set Printing Projections.

Record νGpdPresentation (arity: Type) := {
  G0: nat -> HGpd;
  GFace n q (Hq: q <= n) (ε: arity): G0 n.+1 -> G0 n;
  GFaceCoh n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity) (X: G0 n.+2):
    GFace n q Hq ε (GFace n.+1 r (Hr ↕ (↑ Hq)) ω X) =
    GFace n r (Hr ↕ Hq) ω (GFace n.+1 q.+1 (⇑ Hq) ε X);
  GFaceCoh2 n q (Hq: q <= n) r (Hr: r <= q) s (Hs: s <= r)
    (ε ω θ: arity) (X: G0 n.+3):
    f_equal (GFace n q Hq ε) (GFaceCoh n.+1 r (Hr ↕ (↑ Hq)) s Hs ω θ X)
    • (GFaceCoh n q Hq s (Hs ↕ Hr) ε θ
        (GFace n.+2 r.+1 (⇑ (Hr ↕ (↑ Hq))) ω X)
    • f_equal (GFace n s (Hs ↕ (Hr ↕ Hq)) θ)
        (GFaceCoh n.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω X)) =
    GFaceCoh n q Hq r Hr ε ω (GFace n.+2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ X)
    • (f_equal (GFace n r (Hr ↕ Hq) ω)
        (GFaceCoh n.+1 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) ε θ X)
    • GFaceCoh n r (Hr ↕ Hq) s Hs ω θ (GFace n.+2 q.+2 (⇑ (⇑ Hq)) ε X))
}.

Arguments G0 {arity} _ _.
Arguments GFace {arity} _ _ _ _ _.
Arguments GFaceCoh {arity} _ _ _ _ _ _ _ _ _.
Arguments GFaceCoh2 {arity} _ _ _ _ _ _ _ _ _ _ _ _.

Definition AugmentedSemiSimplicialGpdPresentation := νGpdPresentation hunit.
Definition SemiCubicalGpdPresentation := νGpdPresentation hbool.

Section PresentationEq.
Context (A: HSet).

(** Equality of presentations

    Over a fixed family of levels, pointwise identifications of the face
    maps determine an equality of presentations when their squares commute
    with the exchange paths. [GUIP] identifies the transported hexagon fields. *)

Definition GFaceType (G: nat -> HGpd) :=
  forall n q (Hq: q <= n) (ε: A), G (S n) -> G n.

Definition GCohType {G: nat -> HGpd} (Fa: GFaceType G) :=
  CohOf (Build_FaceStr A G Fa).

Definition GCoh2Type {G: nat -> HGpd} {Fa: GFaceType G} (Ca: GCohType Fa) :=
  Coh2Of Ca.

(** The commuting square between two exchange laws over a pointwise
    identification of their face families. *)

Definition GSqType {G: nat -> HGpd} {Fa Fa': GFaceType G}
  (Ca: GCohType Fa) (Ca': GCohType Fa')
  (φ: forall n q (Hq: q <= n) (ε: A) x, Fa n q Hq ε x = Fa' n q Hq ε x): Type :=
  forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A) (X: G (S (S n))),
     Ca n q Hq r Hr ε ω X
     • (φ n r (Hr ↕ Hq) ω (Fa (S n) (S q) (⇑ Hq) ε X)
        • f_equal (Fa' n r (Hr ↕ Hq) ω) (φ (S n) (S q) (⇑ Hq) ε X))
     = (φ n q Hq ε (Fa (S n) r (Hr ↕ (↑ Hq)) ω X)
        • f_equal (Fa' n q Hq ε) (φ (S n) r (Hr ↕ (↑ Hq)) ω X))
       • Ca' n q Hq r Hr ε ω X.

Lemma gpdEqHom {G: nat -> HGpd} (Fa Fa': GFaceType G)
  (Ca: GCohType Fa) (Ca': GCohType Fa')
  (Da: GCoh2Type Ca) (Da': GCoh2Type Ca')
  (φ: forall n q (Hq: q <= n) (ε: A) x, Fa n q Hq ε x = Fa' n q Hq ε x)
  (Hsq: GSqType Ca Ca' φ):
  Build_νGpdPresentation A G Fa Ca Da = Build_νGpdPresentation A G Fa' Ca' Da'.
Proof.
  revert Ca' Da' Hsq.
  refine (homInd5S (I1 := nat) (I2 := fun _ => nat) (I3 := fun n q => q <= n)
            (I4 := fun _ _ _ => A) (I5 := fun n _ _ _ => G (S n))
            (B := fun n _ _ _ _ => G n) Fa
            (fun Fb φb => forall (Cb: GCohType Fb) (Db: GCoh2Type Cb),
               GSqType Ca Cb φb ->
               Build_νGpdPresentation A G Fa Ca Da = Build_νGpdPresentation A G Fb Cb Db)
            _ Fa' φ).
  intros Cb Db Hsq.
  assert (e: Ca = Cb).
  { apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro r.
    apply spropFunext; intro Hr.
    apply functional_extensionality_dep; intro ε.
    apply functional_extensionality_dep; intro ω.
    apply functional_extensionality_dep; intro X.
    now exact (Hsq n q Hq r Hr ε ω X • eq_trans_refl_l _). }
  destruct e.
  assert (e2: Da = Db).
  { apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro r.
    apply spropFunext; intro Hr.
    apply functional_extensionality_dep; intro s.
    apply spropFunext; intro Hs.
    apply functional_extensionality_dep; intro ε.
    apply functional_extensionality_dep; intro ω.
    apply functional_extensionality_dep; intro θ.
    apply functional_extensionality_dep; intro X.
    now exact ((G n).(GUIP)). }
  now destruct e2.
Qed.

End PresentationEq.
