(** P5 transport of permutahedral painting coherence to a layer. *)

Set Warnings "-notation-overridden".

From Bonak.Lib Require Import SigT Notation RewLemmas Coh2Shapes.
From Bonak.SSGpd Require Import Pasting Coh3Shapes Lemmas.
From Bonak.SS2Gpd Require Import Pasting Coh4Shapes.

Set Keyed Unification.

(** Remove a fixed prefix and a pullback map from a lifted path comparison.
    The same fiber retraction is applied at each equality level. *)
Local Lemma prefix_map_coherence_retract {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0: X} {y0 y1: Y} (p: x0 = f y0)
  {a0: P x0} {b0: P (f y0)} {b1: P (f y1)}
  (hp: rew [P] p in a0 = b0)
  {q0 q1: y0 = y1}
  {h0: rew [fun y => P (f y)] q0 in b0 = b1}
  {h1: rew [fun y => P (f y)] q1 in b0 = b1}
  {H K: q0 = q1} (C: H = K)
  (HH: rew [fun e => rew [fun y => P (f y)] e in b0 = b1] H in h0 = h1)
  (KK: rew [fun e => rew [fun y => P (f y)] e in b0 = b1] K in h0 = h1):
  let M := fun (e: y0 = y1) (h: rew [fun y => P (f y)] e in b0 = b1) =>
    sigT_map_eq (Q := P) (fun _ u => u) h in
  let W := fun (e: f y0 = f y1) (h: rew [P] e in b0 = b1) => hp ⊙ h in
  rew [fun s => rew [fun e => rew [P] e in a0 = b1] s in
      (hp ⊙ M q0 h0) = hp ⊙ M q1 h1]
    f_equal (fun H => whisker_l p (f_equal (fun e => f_equal f e) H)) C in
    sigT_map_eq W (sigT_map_eq M HH) = sigT_map_eq W (sigT_map_eq M KK) ->
  rew [fun H => rew [fun e => rew [fun y => P (f y)] e in b0 = b1] H in h0 = h1]
    C in HH = KK.
Proof.
  intros M W E.
  pose (rM := pullback_path_retraction f P b0 b1).
  pose (rW := prefix_retraction P p hp b1).
  pose (r := compose_retraction
    (path_retraction rM h0 h1)
    (path_retraction rW (M q0 h0) (M q1 h1))).
  now exact (fiber_back (path_retraction r HH KK) C E).
Defined.

(** Extend a lifted path comparison by the fixed final path. *)
Local Definition postfix_coherence_map {X: Type} (P: X -> Type)
  {x0 x1 y1: X} (q: x1 = y1)
  {a0: P x0} {a1: P x1} {b1: P y1} (hq: rew [P] q in a1 = b1)
  {p0 p1: x0 = x1}
  {h0: rew [P] p0 in a0 = a1} {h1: rew [P] p1 in a0 = a1}
  {H K: p0 = p1} {C: H = K}
  {HH: rew [fun e => rew [P] e in a0 = a1] H in h0 = h1}
  {KK: rew [fun e => rew [P] e in a0 = a1] K in h0 = h1}
  (D: rew [fun H => rew [fun e => rew [P] e in a0 = a1] H in h0 = h1] C in HH = KK):
  let W := fun (e: x0 = x1) (h: rew [P] e in a0 = a1) => h ⊙ hq in
  rew [fun H => rew [fun e => rew [P] e in a0 = b1] H in (h0 ⊙ hq) = h1 ⊙ hq]
    f_equal (fun H => whisker_r H q) C in sigT_map_eq W HH = sigT_map_eq W KK :=
  sigT_map_eq
    (fun (s: p0 = p1) (h: rew [fun e => rew [P] e in a0 = a1] s in h0 = h1) =>
      sigT_map_eq (fun (e: x0 = x1) (h: rew [P] e in a0 = a1) => h ⊙ hq) h) D.

Local Arguments square_compose_dep
  {X} P {x0 x1 x2 y0 y1 y2 a b c d p q r H K u0 u1 u2 v0 v1 v2 ha hb hc hd hp hq hr} HH KK.

Local Arguments square_stack_dep
  {X} P {x0 x1 y0 y1 z0 z1 a c d p q r s H K u0 u1 v0 v1 w0 w1 ha hc hd hp hq hr hs} HH KK.

Local Arguments square_map_dep
  {X Y P Q} f F {x0 x1 y0 y1 a b p q H u0 u1 v0 v1 ha hb hp hq} HH.

Local Arguments square_change_sides_dep
  {X} P {x0 x1 y0 y1 a b p p' q q' Hp H Hq u0 u1 v0 v1 ha hb hp hp' hq hq'} HHp HH HHq.

Local Arguments square_compose_map_coherence_dep
  {X Y} f P Q F {x0 x1 x2 y0 y1 y2 a b c d p q r H K u0 u1 u2 v0 v1 v2 ha hb hc hd hp hq hr} HH
    KK.

(** The operation labels and stage indices are those of [Coh4Shapes].
    Target painting maps are the canonical layer maps over [E]. Repeated
    comparisons with [E] at the same operation and stage share a parameter,
    so these maps agree across the adjoining facets. *)
Section Coh3Layer.

Context (X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4: Type).

Context (dA_0_0_U dB_0_0_U dC_0_0_U dD_0_0_U: X5 -> X4).

Context (dE_0_0_U: X5 -> Y4).
Context (dB_1_1_U dC_1_1_U dD_1_1_U: X4 -> X3).

Context (dE_1_1_U: X4 -> Y3).
Context (dA_1_0_U dB_1_0_U dC_1_0_U: X4 -> X3).

Context (dA_1_0_L dB_1_0_L dC_1_0_L dD_1_0_L: Y4 -> Y3).

Context (dC_2_2_U dD_2_2_U: X3 -> X2).

Context (dE_2_2_U: X3 -> Y2).
Context (dB_2_1_U dC_2_1_U: X3 -> X2).

Context (dB_2_1_L dC_2_1_L dD_2_1_L: Y3 -> Y2).

Context (dA_2_0_U: X3 -> X2).
Context (dA_2_0_L: Y3 -> Y2).
Context (dB_2_0_U: X3 -> X2).
Context (dB_2_0_L dC_2_0_L: Y3 -> Y2).

Context (dD_3_3_U: X2 -> X1).
Context (dE_3_3_U: X2 -> Y1).
Context (dC_3_2_U: X2 -> X1).
Context (dC_3_2_L dD_3_2_L: Y2 -> Y1).

Context (dB_3_1_U: X2 -> X1).
Context (dB_3_1_L dC_3_1_L: Y2 -> Y1).

Context (dA_3_0_U: X2 -> X1).
Context (dA_3_0_L dB_3_0_L: Y2 -> Y1).

Context (dE_4_4_U: X1 -> Y0).
Context (dD_4_3_L dC_4_2_L dB_4_1_L dA_4_0_L: Y1 -> Y0).

Context (cAB_nil: forall x: X5,
  dA_1_0_U (dB_0_0_U x) = dB_1_1_U (dA_0_0_U x)).

Context (cAB_C cAB_D: forall x: X4,
  dA_2_0_U (dB_1_0_U x) = dB_2_1_U (dA_1_0_U x)).

Context (cAB_E: forall x: Y4,
  dA_2_0_L (dB_1_0_L x) = dB_2_1_L (dA_1_0_L x)).

Context (cAB_CD: forall x: X3,
  dA_3_0_U (dB_2_0_U x) = dB_3_1_U (dA_2_0_U x)).

Context (cAB_CE cAB_DE: forall x: Y3,
  dA_3_0_L (dB_2_0_L x) = dB_3_1_L (dA_2_0_L x)).

Context (cAB_CDE: forall x: Y2,
  dA_4_0_L (dB_3_0_L x) = dB_4_1_L (dA_3_0_L x)).

Context (cAC_nil: forall x: X5,
  dA_1_0_U (dC_0_0_U x) = dC_1_1_U (dA_0_0_U x)).

Context (cAC_B: forall x: X4,
  dA_2_0_U (dC_1_1_U x) = dC_2_2_U (dA_1_0_U x)).

Context (cAC_D: forall x: X4,
  dA_2_0_U (dC_1_0_U x) = dC_2_1_U (dA_1_0_U x)).

Context (cAC_E: forall x: Y4,
  dA_2_0_L (dC_1_0_L x) = dC_2_1_L (dA_1_0_L x)).

Context (cAC_BD: forall x: X3,
  dA_3_0_U (dC_2_1_U x) = dC_3_2_U (dA_2_0_U x)).

Context (cAC_BE: forall x: Y3,
  dA_3_0_L (dC_2_1_L x) = dC_3_2_L (dA_2_0_L x)).

Context (cAC_DE: forall x: Y3,
  dA_3_0_L (dC_2_0_L x) = dC_3_1_L (dA_2_0_L x)).

Context (cAC_BDE: forall x: Y2,
  dA_4_0_L (dC_3_1_L x) = dC_4_2_L (dA_3_0_L x)).

Context (cAD_nil: forall x: X5,
  dA_1_0_U (dD_0_0_U x) = dD_1_1_U (dA_0_0_U x)).

Context (cAD_B cAD_C: forall x: X4,
  dA_2_0_U (dD_1_1_U x) = dD_2_2_U (dA_1_0_U x)).

Context (cAD_E: forall x: Y4,
  dA_2_0_L (dD_1_0_L x) = dD_2_1_L (dA_1_0_L x)).

Context (cAD_BC: forall x: X3,
  dA_3_0_U (dD_2_2_U x) = dD_3_3_U (dA_2_0_U x)).

Context (cAD_BE cAD_CE: forall x: Y3,
  dA_3_0_L (dD_2_1_L x) = dD_3_2_L (dA_2_0_L x)).

Context (cAD_BCE: forall x: Y2,
  dA_4_0_L (dD_3_2_L x) = dD_4_3_L (dA_3_0_L x)).

Context (cAE_nil: forall x: X5,
  dA_1_0_L (dE_0_0_U x) = dE_1_1_U (dA_0_0_U x)).

Context (cAE_B: forall x: X4,
  dA_2_0_L (dE_1_1_U x) = dE_2_2_U (dA_1_0_U x)).

Context (cAE_BC: forall x: X3,
  dA_3_0_L (dE_2_2_U x) = dE_3_3_U (dA_2_0_U x)).

Context (cAE_BCD: forall x: X2,
  dA_4_0_L (dE_3_3_U x) = dE_4_4_U (dA_3_0_U x)).

Context (cBC_nil: forall x: X5,
  dB_1_0_U (dC_0_0_U x) = dC_1_1_U (dB_0_0_U x)).

Context (cBC_A: forall x: X4,
  dB_2_1_U (dC_1_1_U x) = dC_2_2_U (dB_1_1_U x)).

Context (cBC_D: forall x: X4,
  dB_2_0_U (dC_1_0_U x) = dC_2_1_U (dB_1_0_U x)).

Context (cBC_E: forall x: Y4,
  dB_2_0_L (dC_1_0_L x) = dC_2_1_L (dB_1_0_L x)).

Context (cBC_AD: forall x: X3,
  dB_3_1_U (dC_2_1_U x) = dC_3_2_U (dB_2_1_U x)).

Context (cBC_AE: forall x: Y3,
  dB_3_1_L (dC_2_1_L x) = dC_3_2_L (dB_2_1_L x)).

Context (cBC_DE: forall x: Y3,
  dB_3_0_L (dC_2_0_L x) = dC_3_1_L (dB_2_0_L x)).

Context (cBC_ADE: forall x: Y2,
  dB_4_1_L (dC_3_1_L x) = dC_4_2_L (dB_3_1_L x)).

Context (cBD_nil: forall x: X5,
  dB_1_0_U (dD_0_0_U x) = dD_1_1_U (dB_0_0_U x)).

Context (cBD_A: forall x: X4,
  dB_2_1_U (dD_1_1_U x) = dD_2_2_U (dB_1_1_U x)).

Context (cBD_C: forall x: X4,
  dB_2_0_U (dD_1_1_U x) = dD_2_2_U (dB_1_0_U x)).

Context (cBD_E: forall x: Y4,
  dB_2_0_L (dD_1_0_L x) = dD_2_1_L (dB_1_0_L x)).

Context (cBD_AC: forall x: X3,
  dB_3_1_U (dD_2_2_U x) = dD_3_3_U (dB_2_1_U x)).

Context (cBD_AE: forall x: Y3,
  dB_3_1_L (dD_2_1_L x) = dD_3_2_L (dB_2_1_L x)).

Context (cBD_CE: forall x: Y3,
  dB_3_0_L (dD_2_1_L x) = dD_3_2_L (dB_2_0_L x)).

Context (cBD_ACE: forall x: Y2,
  dB_4_1_L (dD_3_2_L x) = dD_4_3_L (dB_3_1_L x)).

Context (cBE_nil: forall x: X5,
  dB_1_0_L (dE_0_0_U x) = dE_1_1_U (dB_0_0_U x)).

Context (cBE_A: forall x: X4,
  dB_2_1_L (dE_1_1_U x) = dE_2_2_U (dB_1_1_U x)).

Context (cBE_C: forall x: X4,
  dB_2_0_L (dE_1_1_U x) = dE_2_2_U (dB_1_0_U x)).

Context (cBE_AC: forall x: X3,
  dB_3_1_L (dE_2_2_U x) = dE_3_3_U (dB_2_1_U x)).

Context (cBE_CD: forall x: X3,
  dB_3_0_L (dE_2_2_U x) = dE_3_3_U (dB_2_0_U x)).

Context (cBE_ACD: forall x: X2,
  dB_4_1_L (dE_3_3_U x) = dE_4_4_U (dB_3_1_U x)).

Context (cCD_nil: forall x: X5,
  dC_1_0_U (dD_0_0_U x) = dD_1_1_U (dC_0_0_U x)).

Context (cCD_A cCD_B: forall x: X4,
  dC_2_1_U (dD_1_1_U x) = dD_2_2_U (dC_1_1_U x)).

Context (cCD_E: forall x: Y4,
  dC_2_0_L (dD_1_0_L x) = dD_2_1_L (dC_1_0_L x)).

Context (cCD_AB: forall x: X3,
  dC_3_2_U (dD_2_2_U x) = dD_3_3_U (dC_2_2_U x)).

Context (cCD_AE cCD_BE: forall x: Y3,
  dC_3_1_L (dD_2_1_L x) = dD_3_2_L (dC_2_1_L x)).

Context (cCD_ABE: forall x: Y2,
  dC_4_2_L (dD_3_2_L x) = dD_4_3_L (dC_3_2_L x)).

Context (cCE_nil: forall x: X5,
  dC_1_0_L (dE_0_0_U x) = dE_1_1_U (dC_0_0_U x)).

Context (cCE_A: forall x: X4,
  dC_2_1_L (dE_1_1_U x) = dE_2_2_U (dC_1_1_U x)).

Context (cCE_D: forall x: X4,
  dC_2_0_L (dE_1_1_U x) = dE_2_2_U (dC_1_0_U x)).

Context (cCE_AB: forall x: X3,
  dC_3_2_L (dE_2_2_U x) = dE_3_3_U (dC_2_2_U x)).

Context (cCE_AD: forall x: X3,
  dC_3_1_L (dE_2_2_U x) = dE_3_3_U (dC_2_1_U x)).

Context (cCE_ABD: forall x: X2,
  dC_4_2_L (dE_3_3_U x) = dE_4_4_U (dC_3_2_U x)).

Context (cDE_nil: forall x: X5,
  dD_1_0_L (dE_0_0_U x) = dE_1_1_U (dD_0_0_U x)).

Context (cDE_A: forall x: X4,
  dD_2_1_L (dE_1_1_U x) = dE_2_2_U (dD_1_1_U x)).

Context (cDE_AB: forall x: X3,
  dD_3_2_L (dE_2_2_U x) = dE_3_3_U (dD_2_2_U x)).

Context (cDE_ABC: forall x: X2,
  dD_4_3_L (dE_3_3_U x) = dE_4_4_U (dD_3_3_U x)).

Context (hABC_nil: forall x: X5,
  hexagonal_coherence
    dA_2_0_U dC_2_2_U dB_2_1_U
    (cBC_nil x) (cAB_nil x) (cAC_nil x)
    (cAC_B (dB_0_0_U x)) (cAB_C (dC_0_0_U x)) (cBC_A (dA_0_0_U x))).

Context (hABC_D: forall x: X4,
  hexagonal_coherence
    dA_3_0_U dC_3_2_U dB_3_1_U
    (cBC_D x) (cAB_D x) (cAC_D x)
    (cAC_BD (dB_1_0_U x)) (cAB_CD (dC_1_0_U x)) (cBC_AD (dA_1_0_U x))).

Context (hABC_E: forall x: Y4,
  hexagonal_coherence
    dA_3_0_L dC_3_2_L dB_3_1_L
    (cBC_E x) (cAB_E x) (cAC_E x)
    (cAC_BE (dB_1_0_L x)) (cAB_CE (dC_1_0_L x)) (cBC_AE (dA_1_0_L x))).

Context (hABC_DE: forall x: Y3,
  hexagonal_coherence
    dA_4_0_L dC_4_2_L dB_4_1_L
    (cBC_DE x) (cAB_DE x) (cAC_DE x)
    (cAC_BDE (dB_2_0_L x)) (cAB_CDE (dC_2_0_L x)) (cBC_ADE (dA_2_0_L x))).

Context (hABD_nil: forall x: X5,
  hexagonal_coherence
    dA_2_0_U dD_2_2_U dB_2_1_U
    (cBD_nil x) (cAB_nil x) (cAD_nil x)
    (cAD_B (dB_0_0_U x)) (cAB_D (dD_0_0_U x)) (cBD_A (dA_0_0_U x))).

Context (hABD_C: forall x: X4,
  hexagonal_coherence
    dA_3_0_U dD_3_3_U dB_3_1_U
    (cBD_C x) (cAB_C x) (cAD_C x)
    (cAD_BC (dB_1_0_U x)) (cAB_CD (dD_1_1_U x)) (cBD_AC (dA_1_0_U x))).

Context (hABD_E: forall x: Y4,
  hexagonal_coherence
    dA_3_0_L dD_3_2_L dB_3_1_L
    (cBD_E x) (cAB_E x) (cAD_E x)
    (cAD_BE (dB_1_0_L x)) (cAB_DE (dD_1_0_L x)) (cBD_AE (dA_1_0_L x))).

Context (hABD_CE: forall x: Y3,
  hexagonal_coherence
    dA_4_0_L dD_4_3_L dB_4_1_L
    (cBD_CE x) (cAB_CE x) (cAD_CE x)
    (cAD_BCE (dB_2_0_L x)) (cAB_CDE (dD_2_1_L x)) (cBD_ACE (dA_2_0_L x))).

Context (hABE_nil: forall x: X5,
  hexagonal_coherence
    dA_2_0_L dE_2_2_U dB_2_1_L
    (cBE_nil x) (cAB_nil x) (cAE_nil x)
    (cAE_B (dB_0_0_U x)) (cAB_E (dE_0_0_U x)) (cBE_A (dA_0_0_U x))).

Context (hABE_C: forall x: X4,
  hexagonal_coherence
    dA_3_0_L dE_3_3_U dB_3_1_L
    (cBE_C x) (cAB_C x) (cAE_B x)
    (cAE_BC (dB_1_0_U x)) (cAB_CE (dE_1_1_U x)) (cBE_AC (dA_1_0_U x))).

Context (hABE_D: forall x: X4,
  hexagonal_coherence
    dA_3_0_L dE_3_3_U dB_3_1_L
    (cBE_C x) (cAB_D x) (cAE_B x)
    (cAE_BC (dB_1_0_U x)) (cAB_DE (dE_1_1_U x)) (cBE_AC (dA_1_0_U x))).

Context (hABE_CD: forall x: X3,
  hexagonal_coherence
    dA_4_0_L dE_4_4_U dB_4_1_L
    (cBE_CD x) (cAB_CD x) (cAE_BC x)
    (cAE_BCD (dB_2_0_U x)) (cAB_CDE (dE_2_2_U x)) (cBE_ACD (dA_2_0_U x))).

Context (hACD_nil: forall x: X5,
  hexagonal_coherence
    dA_2_0_U dD_2_2_U dC_2_1_U
    (cCD_nil x) (cAC_nil x) (cAD_nil x)
    (cAD_C (dC_0_0_U x)) (cAC_D (dD_0_0_U x)) (cCD_A (dA_0_0_U x))).

Context (hACD_B: forall x: X4,
  hexagonal_coherence
    dA_3_0_U dD_3_3_U dC_3_2_U
    (cCD_B x) (cAC_B x) (cAD_B x)
    (cAD_BC (dC_1_1_U x)) (cAC_BD (dD_1_1_U x)) (cCD_AB (dA_1_0_U x))).

Context (hACD_E: forall x: Y4,
  hexagonal_coherence
    dA_3_0_L dD_3_2_L dC_3_1_L
    (cCD_E x) (cAC_E x) (cAD_E x)
    (cAD_CE (dC_1_0_L x)) (cAC_DE (dD_1_0_L x)) (cCD_AE (dA_1_0_L x))).

Context (hACD_BE: forall x: Y3,
  hexagonal_coherence
    dA_4_0_L dD_4_3_L dC_4_2_L
    (cCD_BE x) (cAC_BE x) (cAD_BE x)
    (cAD_BCE (dC_2_1_L x)) (cAC_BDE (dD_2_1_L x)) (cCD_ABE (dA_2_0_L x))).

Context (hACE_nil: forall x: X5,
  hexagonal_coherence
    dA_2_0_L dE_2_2_U dC_2_1_L
    (cCE_nil x) (cAC_nil x) (cAE_nil x)
    (cAE_B (dC_0_0_U x)) (cAC_E (dE_0_0_U x)) (cCE_A (dA_0_0_U x))).

Context (hACE_B: forall x: X4,
  hexagonal_coherence
    dA_3_0_L dE_3_3_U dC_3_2_L
    (cCE_A x) (cAC_B x) (cAE_B x)
    (cAE_BC (dC_1_1_U x)) (cAC_BE (dE_1_1_U x)) (cCE_AB (dA_1_0_U x))).

Context (hACE_D: forall x: X4,
  hexagonal_coherence
    dA_3_0_L dE_3_3_U dC_3_1_L
    (cCE_D x) (cAC_D x) (cAE_B x)
    (cAE_BC (dC_1_0_U x)) (cAC_DE (dE_1_1_U x)) (cCE_AD (dA_1_0_U x))).

Context (hACE_BD: forall x: X3,
  hexagonal_coherence
    dA_4_0_L dE_4_4_U dC_4_2_L
    (cCE_AD x) (cAC_BD x) (cAE_BC x)
    (cAE_BCD (dC_2_1_U x)) (cAC_BDE (dE_2_2_U x)) (cCE_ABD (dA_2_0_U x))).

Context (hADE_nil: forall x: X5,
  hexagonal_coherence
    dA_2_0_L dE_2_2_U dD_2_1_L
    (cDE_nil x) (cAD_nil x) (cAE_nil x)
    (cAE_B (dD_0_0_U x)) (cAD_E (dE_0_0_U x)) (cDE_A (dA_0_0_U x))).

Context (hADE_B: forall x: X4,
  hexagonal_coherence
    dA_3_0_L dE_3_3_U dD_3_2_L
    (cDE_A x) (cAD_B x) (cAE_B x)
    (cAE_BC (dD_1_1_U x)) (cAD_BE (dE_1_1_U x)) (cDE_AB (dA_1_0_U x))).

Context (hADE_C: forall x: X4,
  hexagonal_coherence
    dA_3_0_L dE_3_3_U dD_3_2_L
    (cDE_A x) (cAD_C x) (cAE_B x)
    (cAE_BC (dD_1_1_U x)) (cAD_CE (dE_1_1_U x)) (cDE_AB (dA_1_0_U x))).

Context (hADE_BC: forall x: X3,
  hexagonal_coherence
    dA_4_0_L dE_4_4_U dD_4_3_L
    (cDE_AB x) (cAD_BC x) (cAE_BC x)
    (cAE_BCD (dD_2_2_U x)) (cAD_BCE (dE_2_2_U x)) (cDE_ABC (dA_2_0_U x))).

Context (hBCD_nil: forall x: X5,
  hexagonal_coherence
    dB_2_0_U dD_2_2_U dC_2_1_U
    (cCD_nil x) (cBC_nil x) (cBD_nil x)
    (cBD_C (dC_0_0_U x)) (cBC_D (dD_0_0_U x)) (cCD_B (dB_0_0_U x))).

Context (hBCD_A: forall x: X4,
  hexagonal_coherence
    dB_3_1_U dD_3_3_U dC_3_2_U
    (cCD_A x) (cBC_A x) (cBD_A x)
    (cBD_AC (dC_1_1_U x)) (cBC_AD (dD_1_1_U x)) (cCD_AB (dB_1_1_U x))).

Context (hBCD_E: forall x: Y4,
  hexagonal_coherence
    dB_3_0_L dD_3_2_L dC_3_1_L
    (cCD_E x) (cBC_E x) (cBD_E x)
    (cBD_CE (dC_1_0_L x)) (cBC_DE (dD_1_0_L x)) (cCD_BE (dB_1_0_L x))).

Context (hBCD_AE: forall x: Y3,
  hexagonal_coherence
    dB_4_1_L dD_4_3_L dC_4_2_L
    (cCD_AE x) (cBC_AE x) (cBD_AE x)
    (cBD_ACE (dC_2_1_L x)) (cBC_ADE (dD_2_1_L x)) (cCD_ABE (dB_2_1_L x))).

Context (hBCE_nil: forall x: X5,
  hexagonal_coherence
    dB_2_0_L dE_2_2_U dC_2_1_L
    (cCE_nil x) (cBC_nil x) (cBE_nil x)
    (cBE_C (dC_0_0_U x)) (cBC_E (dE_0_0_U x)) (cCE_A (dB_0_0_U x))).

Context (hBCE_A: forall x: X4,
  hexagonal_coherence
    dB_3_1_L dE_3_3_U dC_3_2_L
    (cCE_A x) (cBC_A x) (cBE_A x)
    (cBE_AC (dC_1_1_U x)) (cBC_AE (dE_1_1_U x)) (cCE_AB (dB_1_1_U x))).

Context (hBCE_D: forall x: X4,
  hexagonal_coherence
    dB_3_0_L dE_3_3_U dC_3_1_L
    (cCE_D x) (cBC_D x) (cBE_C x)
    (cBE_CD (dC_1_0_U x)) (cBC_DE (dE_1_1_U x)) (cCE_AD (dB_1_0_U x))).

Context (hBCE_AD: forall x: X3,
  hexagonal_coherence
    dB_4_1_L dE_4_4_U dC_4_2_L
    (cCE_AD x) (cBC_AD x) (cBE_AC x)
    (cBE_ACD (dC_2_1_U x)) (cBC_ADE (dE_2_2_U x)) (cCE_ABD (dB_2_1_U x))).

Context (hBDE_nil: forall x: X5,
  hexagonal_coherence
    dB_2_0_L dE_2_2_U dD_2_1_L
    (cDE_nil x) (cBD_nil x) (cBE_nil x)
    (cBE_C (dD_0_0_U x)) (cBD_E (dE_0_0_U x)) (cDE_A (dB_0_0_U x))).

Context (hBDE_A: forall x: X4,
  hexagonal_coherence
    dB_3_1_L dE_3_3_U dD_3_2_L
    (cDE_A x) (cBD_A x) (cBE_A x)
    (cBE_AC (dD_1_1_U x)) (cBD_AE (dE_1_1_U x)) (cDE_AB (dB_1_1_U x))).

Context (hBDE_C: forall x: X4,
  hexagonal_coherence
    dB_3_0_L dE_3_3_U dD_3_2_L
    (cDE_A x) (cBD_C x) (cBE_C x)
    (cBE_CD (dD_1_1_U x)) (cBD_CE (dE_1_1_U x)) (cDE_AB (dB_1_0_U x))).

Context (hBDE_AC: forall x: X3,
  hexagonal_coherence
    dB_4_1_L dE_4_4_U dD_4_3_L
    (cDE_AB x) (cBD_AC x) (cBE_AC x)
    (cBE_ACD (dD_2_2_U x)) (cBD_ACE (dE_2_2_U x)) (cDE_ABC (dB_2_1_U x))).

Context (hCDE_nil: forall x: X5,
  hexagonal_coherence
    dC_2_0_L dE_2_2_U dD_2_1_L
    (cDE_nil x) (cCD_nil x) (cCE_nil x)
    (cCE_D (dD_0_0_U x)) (cCD_E (dE_0_0_U x)) (cDE_A (dC_0_0_U x))).

Context (hCDE_A: forall x: X4,
  hexagonal_coherence
    dC_3_1_L dE_3_3_U dD_3_2_L
    (cDE_A x) (cCD_A x) (cCE_A x)
    (cCE_AD (dD_1_1_U x)) (cCD_AE (dE_1_1_U x)) (cDE_AB (dC_1_1_U x))).

Context (hCDE_B: forall x: X4,
  hexagonal_coherence
    dC_3_1_L dE_3_3_U dD_3_2_L
    (cDE_A x) (cCD_B x) (cCE_A x)
    (cCE_AD (dD_1_1_U x)) (cCD_BE (dE_1_1_U x)) (cDE_AB (dC_1_1_U x))).

Context (hCDE_AB: forall x: X3,
  hexagonal_coherence
    dC_4_2_L dE_4_4_U dD_4_3_L
    (cDE_AB x) (cCD_AB x) (cCE_AB x)
    (cCE_ABD (dD_2_2_U x)) (cCD_ABE (dE_2_2_U x)) (cDE_ABC (dC_2_2_U x))).

Context (kABCD_nil: forall x: X5,
  @permutahedral_coherence
    X3 X2 X1
    X3 X2 dD_2_2_U
    dD_3_3_U dA_2_0_U dC_2_2_U
    dB_2_1_U dA_3_0_U dC_3_2_U
    dB_3_1_U cAD_BC cCD_AB
    cBD_AC dB_2_0_U dC_2_1_U
    dA_2_0_U dB_2_1_U cAC_BD
    cAB_CD cBC_AD (dB_1_0_U (dC_0_0_U x))
    (dC_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x)) (dB_1_1_U (dA_0_0_U x))
    (dA_1_0_U (dC_0_0_U x)) (dC_1_1_U (dA_0_0_U x)) (cBC_nil x)
    (cAB_nil x) (cAC_nil x) (cAC_B (dB_0_0_U x))
    (cAB_C (dC_0_0_U x)) (cBC_A (dA_0_0_U x)) (dC_1_0_U (dD_0_0_U x))
    (dD_1_1_U (dC_0_0_U x)) (dB_1_0_U (dD_0_0_U x)) (dD_1_1_U (dB_0_0_U x))
    (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cCD_nil x)
    (cBD_nil x) (cAD_nil x) (cBD_C (dC_0_0_U x))
    (cCD_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x)) (cBD_A (dA_0_0_U x))
    (cAD_C (dC_0_0_U x)) (cCD_A (dA_0_0_U x)) (cBC_D (dD_0_0_U x))
    (cAB_D (dD_0_0_U x)) (cAC_D (dD_0_0_U x)) (hBCD_nil x)
    (hABD_nil x) (hACD_nil x) (hABC_nil x)
    (hACD_B (dB_0_0_U x)) (hABD_C (dC_0_0_U x)) (hBCD_A (dA_0_0_U x))
    (hABC_D (dD_0_0_U x))).

Context (kABCD_E: forall x: Y4,
  @permutahedral_coherence
    Y2 Y1 Y0
    Y2 Y1 dD_3_2_L
    dD_4_3_L dA_3_0_L dC_3_2_L
    dB_3_1_L dA_4_0_L dC_4_2_L
    dB_4_1_L cAD_BCE cCD_ABE
    cBD_ACE dB_3_0_L dC_3_1_L
    dA_3_0_L dB_3_1_L cAC_BDE
    cAB_CDE cBC_ADE (dB_2_0_L (dC_1_0_L x))
    (dC_2_1_L (dB_1_0_L x)) (dA_2_0_L (dB_1_0_L x)) (dB_2_1_L (dA_1_0_L x))
    (dA_2_0_L (dC_1_0_L x)) (dC_2_1_L (dA_1_0_L x)) (cBC_E x)
    (cAB_E x) (cAC_E x) (cAC_BE (dB_1_0_L x))
    (cAB_CE (dC_1_0_L x)) (cBC_AE (dA_1_0_L x)) (dC_2_0_L (dD_1_0_L x))
    (dD_2_1_L (dC_1_0_L x)) (dB_2_0_L (dD_1_0_L x)) (dD_2_1_L (dB_1_0_L x))
    (dA_2_0_L (dD_1_0_L x)) (dD_2_1_L (dA_1_0_L x)) (cCD_E x)
    (cBD_E x) (cAD_E x) (cBD_CE (dC_1_0_L x))
    (cCD_BE (dB_1_0_L x)) (cAD_BE (dB_1_0_L x)) (cBD_AE (dA_1_0_L x))
    (cAD_CE (dC_1_0_L x)) (cCD_AE (dA_1_0_L x)) (cBC_DE (dD_1_0_L x))
    (cAB_DE (dD_1_0_L x)) (cAC_DE (dD_1_0_L x)) (hBCD_E x)
    (hABD_E x) (hACD_E x) (hABC_E x)
    (hACD_BE (dB_1_0_L x)) (hABD_CE (dC_1_0_L x)) (hBCD_AE (dA_1_0_L x))
    (hABC_DE (dD_1_0_L x))).

Context (kABCE_nil: forall x: X5,
  @permutahedral_coherence
    Y3 Y2 Y1
    X3 X2 dE_2_2_U
    dE_3_3_U dA_2_0_U dC_2_2_U
    dB_2_1_U dA_3_0_L dC_3_2_L
    dB_3_1_L cAE_BC cCE_AB
    cBE_AC dB_2_0_L dC_2_1_L
    dA_2_0_L dB_2_1_L cAC_BE
    cAB_CE cBC_AE (dB_1_0_U (dC_0_0_U x))
    (dC_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x)) (dB_1_1_U (dA_0_0_U x))
    (dA_1_0_U (dC_0_0_U x)) (dC_1_1_U (dA_0_0_U x)) (cBC_nil x)
    (cAB_nil x) (cAC_nil x) (cAC_B (dB_0_0_U x))
    (cAB_C (dC_0_0_U x)) (cBC_A (dA_0_0_U x)) (dC_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dC_0_0_U x)) (dB_1_0_L (dE_0_0_U x)) (dE_1_1_U (dB_0_0_U x))
    (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cCE_nil x)
    (cBE_nil x) (cAE_nil x) (cBE_C (dC_0_0_U x))
    (cCE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cBE_A (dA_0_0_U x))
    (cAE_B (dC_0_0_U x)) (cCE_A (dA_0_0_U x)) (cBC_E (dE_0_0_U x))
    (cAB_E (dE_0_0_U x)) (cAC_E (dE_0_0_U x)) (hBCE_nil x)
    (hABE_nil x) (hACE_nil x) (hABC_nil x)
    (hACE_B (dB_0_0_U x)) (hABE_C (dC_0_0_U x)) (hBCE_A (dA_0_0_U x))
    (hABC_E (dE_0_0_U x))).

Context (kABCE_D: forall x: X4,
  @permutahedral_coherence
    Y2 Y1 Y0
    X2 X1 dE_3_3_U
    dE_4_4_U dA_3_0_U dC_3_2_U
    dB_3_1_U dA_4_0_L dC_4_2_L
    dB_4_1_L cAE_BCD cCE_ABD
    cBE_ACD dB_3_0_L dC_3_1_L
    dA_3_0_L dB_3_1_L cAC_BDE
    cAB_CDE cBC_ADE (dB_2_0_U (dC_1_0_U x))
    (dC_2_1_U (dB_1_0_U x)) (dA_2_0_U (dB_1_0_U x)) (dB_2_1_U (dA_1_0_U x))
    (dA_2_0_U (dC_1_0_U x)) (dC_2_1_U (dA_1_0_U x)) (cBC_D x)
    (cAB_D x) (cAC_D x) (cAC_BD (dB_1_0_U x))
    (cAB_CD (dC_1_0_U x)) (cBC_AD (dA_1_0_U x)) (dC_2_0_L (dE_1_1_U x))
    (dE_2_2_U (dC_1_0_U x)) (dB_2_0_L (dE_1_1_U x)) (dE_2_2_U (dB_1_0_U x))
    (dA_2_0_L (dE_1_1_U x)) (dE_2_2_U (dA_1_0_U x)) (cCE_D x)
    (cBE_C x) (cAE_B x) (cBE_CD (dC_1_0_U x))
    (cCE_AD (dB_1_0_U x)) (cAE_BC (dB_1_0_U x)) (cBE_AC (dA_1_0_U x))
    (cAE_BC (dC_1_0_U x)) (cCE_AD (dA_1_0_U x)) (cBC_DE (dE_1_1_U x))
    (cAB_DE (dE_1_1_U x)) (cAC_DE (dE_1_1_U x)) (hBCE_D x)
    (hABE_D x) (hACE_D x) (hABC_D x)
    (hACE_BD (dB_1_0_U x)) (hABE_CD (dC_1_0_U x)) (hBCE_AD (dA_1_0_U x))
    (hABC_DE (dE_1_1_U x))).

Context (kABDE_nil: forall x: X5,
  @permutahedral_coherence
    Y3 Y2 Y1
    X3 X2 dE_2_2_U
    dE_3_3_U dA_2_0_U dD_2_2_U
    dB_2_1_U dA_3_0_L dD_3_2_L
    dB_3_1_L cAE_BC cDE_AB
    cBE_AC dB_2_0_L dD_2_1_L
    dA_2_0_L dB_2_1_L cAD_BE
    cAB_DE cBD_AE (dB_1_0_U (dD_0_0_U x))
    (dD_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x)) (dB_1_1_U (dA_0_0_U x))
    (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cBD_nil x)
    (cAB_nil x) (cAD_nil x) (cAD_B (dB_0_0_U x))
    (cAB_D (dD_0_0_U x)) (cBD_A (dA_0_0_U x)) (dD_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dD_0_0_U x)) (dB_1_0_L (dE_0_0_U x)) (dE_1_1_U (dB_0_0_U x))
    (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cDE_nil x)
    (cBE_nil x) (cAE_nil x) (cBE_C (dD_0_0_U x))
    (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cBE_A (dA_0_0_U x))
    (cAE_B (dD_0_0_U x)) (cDE_A (dA_0_0_U x)) (cBD_E (dE_0_0_U x))
    (cAB_E (dE_0_0_U x)) (cAD_E (dE_0_0_U x)) (hBDE_nil x)
    (hABE_nil x) (hADE_nil x) (hABD_nil x)
    (hADE_B (dB_0_0_U x)) (hABE_D (dD_0_0_U x)) (hBDE_A (dA_0_0_U x))
    (hABD_E (dE_0_0_U x))).

Context (kABDE_C: forall x: X4,
  @permutahedral_coherence
    Y2 Y1 Y0
    X2 X1 dE_3_3_U
    dE_4_4_U dA_3_0_U dD_3_3_U
    dB_3_1_U dA_4_0_L dD_4_3_L
    dB_4_1_L cAE_BCD cDE_ABC
    cBE_ACD dB_3_0_L dD_3_2_L
    dA_3_0_L dB_3_1_L cAD_BCE
    cAB_CDE cBD_ACE (dB_2_0_U (dD_1_1_U x))
    (dD_2_2_U (dB_1_0_U x)) (dA_2_0_U (dB_1_0_U x)) (dB_2_1_U (dA_1_0_U x))
    (dA_2_0_U (dD_1_1_U x)) (dD_2_2_U (dA_1_0_U x)) (cBD_C x)
    (cAB_C x) (cAD_C x) (cAD_BC (dB_1_0_U x))
    (cAB_CD (dD_1_1_U x)) (cBD_AC (dA_1_0_U x)) (dD_2_1_L (dE_1_1_U x))
    (dE_2_2_U (dD_1_1_U x)) (dB_2_0_L (dE_1_1_U x)) (dE_2_2_U (dB_1_0_U x))
    (dA_2_0_L (dE_1_1_U x)) (dE_2_2_U (dA_1_0_U x)) (cDE_A x)
    (cBE_C x) (cAE_B x) (cBE_CD (dD_1_1_U x))
    (cDE_AB (dB_1_0_U x)) (cAE_BC (dB_1_0_U x)) (cBE_AC (dA_1_0_U x))
    (cAE_BC (dD_1_1_U x)) (cDE_AB (dA_1_0_U x)) (cBD_CE (dE_1_1_U x))
    (cAB_CE (dE_1_1_U x)) (cAD_CE (dE_1_1_U x)) (hBDE_C x)
    (hABE_C x) (hADE_C x) (hABD_C x)
    (hADE_BC (dB_1_0_U x)) (hABE_CD (dD_1_1_U x)) (hBDE_AC (dA_1_0_U x))
    (hABD_CE (dE_1_1_U x))).

Context (kACDE_nil: forall x: X5,
  @permutahedral_coherence
    Y3 Y2 Y1
    X3 X2 dE_2_2_U
    dE_3_3_U dA_2_0_U dD_2_2_U
    dC_2_1_U dA_3_0_L dD_3_2_L
    dC_3_1_L cAE_BC cDE_AB
    cCE_AD dC_2_0_L dD_2_1_L
    dA_2_0_L dC_2_1_L cAD_CE
    cAC_DE cCD_AE (dC_1_0_U (dD_0_0_U x))
    (dD_1_1_U (dC_0_0_U x)) (dA_1_0_U (dC_0_0_U x)) (dC_1_1_U (dA_0_0_U x))
    (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cCD_nil x)
    (cAC_nil x) (cAD_nil x) (cAD_C (dC_0_0_U x))
    (cAC_D (dD_0_0_U x)) (cCD_A (dA_0_0_U x)) (dD_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dD_0_0_U x)) (dC_1_0_L (dE_0_0_U x)) (dE_1_1_U (dC_0_0_U x))
    (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cDE_nil x)
    (cCE_nil x) (cAE_nil x) (cCE_D (dD_0_0_U x))
    (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cCE_A (dA_0_0_U x))
    (cAE_B (dD_0_0_U x)) (cDE_A (dA_0_0_U x)) (cCD_E (dE_0_0_U x))
    (cAC_E (dE_0_0_U x)) (cAD_E (dE_0_0_U x)) (hCDE_nil x)
    (hACE_nil x) (hADE_nil x) (hACD_nil x)
    (hADE_C (dC_0_0_U x)) (hACE_D (dD_0_0_U x)) (hCDE_A (dA_0_0_U x))
    (hACD_E (dE_0_0_U x))).

Context (kACDE_B: forall x: X4,
  @permutahedral_coherence
    Y2 Y1 Y0
    X2 X1 dE_3_3_U
    dE_4_4_U dA_3_0_U dD_3_3_U
    dC_3_2_U dA_4_0_L dD_4_3_L
    dC_4_2_L cAE_BCD cDE_ABC
    cCE_ABD dC_3_1_L dD_3_2_L
    dA_3_0_L dC_3_2_L cAD_BCE
    cAC_BDE cCD_ABE (dC_2_1_U (dD_1_1_U x))
    (dD_2_2_U (dC_1_1_U x)) (dA_2_0_U (dC_1_1_U x)) (dC_2_2_U (dA_1_0_U x))
    (dA_2_0_U (dD_1_1_U x)) (dD_2_2_U (dA_1_0_U x)) (cCD_B x)
    (cAC_B x) (cAD_B x) (cAD_BC (dC_1_1_U x))
    (cAC_BD (dD_1_1_U x)) (cCD_AB (dA_1_0_U x)) (dD_2_1_L (dE_1_1_U x))
    (dE_2_2_U (dD_1_1_U x)) (dC_2_1_L (dE_1_1_U x)) (dE_2_2_U (dC_1_1_U x))
    (dA_2_0_L (dE_1_1_U x)) (dE_2_2_U (dA_1_0_U x)) (cDE_A x)
    (cCE_A x) (cAE_B x) (cCE_AD (dD_1_1_U x))
    (cDE_AB (dC_1_1_U x)) (cAE_BC (dC_1_1_U x)) (cCE_AB (dA_1_0_U x))
    (cAE_BC (dD_1_1_U x)) (cDE_AB (dA_1_0_U x)) (cCD_BE (dE_1_1_U x))
    (cAC_BE (dE_1_1_U x)) (cAD_BE (dE_1_1_U x)) (hCDE_B x)
    (hACE_B x) (hADE_B x) (hACD_B x)
    (hADE_BC (dC_1_1_U x)) (hACE_BD (dD_1_1_U x)) (hCDE_AB (dA_1_0_U x))
    (hACD_BE (dE_1_1_U x))).

Context (kBCDE_nil: forall x: X5,
  @permutahedral_coherence
    Y3 Y2 Y1
    X3 X2 dE_2_2_U
    dE_3_3_U dB_2_0_U dD_2_2_U
    dC_2_1_U dB_3_0_L dD_3_2_L
    dC_3_1_L cBE_CD cDE_AB
    cCE_AD dC_2_0_L dD_2_1_L
    dB_2_0_L dC_2_1_L cBD_CE
    cBC_DE cCD_BE (dC_1_0_U (dD_0_0_U x))
    (dD_1_1_U (dC_0_0_U x)) (dB_1_0_U (dC_0_0_U x)) (dC_1_1_U (dB_0_0_U x))
    (dB_1_0_U (dD_0_0_U x)) (dD_1_1_U (dB_0_0_U x)) (cCD_nil x)
    (cBC_nil x) (cBD_nil x) (cBD_C (dC_0_0_U x))
    (cBC_D (dD_0_0_U x)) (cCD_B (dB_0_0_U x)) (dD_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dD_0_0_U x)) (dC_1_0_L (dE_0_0_U x)) (dE_1_1_U (dC_0_0_U x))
    (dB_1_0_L (dE_0_0_U x)) (dE_1_1_U (dB_0_0_U x)) (cDE_nil x)
    (cCE_nil x) (cBE_nil x) (cCE_D (dD_0_0_U x))
    (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cCE_A (dB_0_0_U x))
    (cBE_C (dD_0_0_U x)) (cDE_A (dB_0_0_U x)) (cCD_E (dE_0_0_U x))
    (cBC_E (dE_0_0_U x)) (cBD_E (dE_0_0_U x)) (hCDE_nil x)
    (hBCE_nil x) (hBDE_nil x) (hBCD_nil x)
    (hBDE_C (dC_0_0_U x)) (hBCE_D (dD_0_0_U x)) (hCDE_B (dB_0_0_U x))
    (hBCD_E (dE_0_0_U x))).

Context (kBCDE_A: forall x: X4,
  @permutahedral_coherence
    Y2 Y1 Y0
    X2 X1 dE_3_3_U
    dE_4_4_U dB_3_1_U dD_3_3_U
    dC_3_2_U dB_4_1_L dD_4_3_L
    dC_4_2_L cBE_ACD cDE_ABC
    cCE_ABD dC_3_1_L dD_3_2_L
    dB_3_1_L dC_3_2_L cBD_ACE
    cBC_ADE cCD_ABE (dC_2_1_U (dD_1_1_U x))
    (dD_2_2_U (dC_1_1_U x)) (dB_2_1_U (dC_1_1_U x)) (dC_2_2_U (dB_1_1_U x))
    (dB_2_1_U (dD_1_1_U x)) (dD_2_2_U (dB_1_1_U x)) (cCD_A x)
    (cBC_A x) (cBD_A x) (cBD_AC (dC_1_1_U x))
    (cBC_AD (dD_1_1_U x)) (cCD_AB (dB_1_1_U x)) (dD_2_1_L (dE_1_1_U x))
    (dE_2_2_U (dD_1_1_U x)) (dC_2_1_L (dE_1_1_U x)) (dE_2_2_U (dC_1_1_U x))
    (dB_2_1_L (dE_1_1_U x)) (dE_2_2_U (dB_1_1_U x)) (cDE_A x)
    (cCE_A x) (cBE_A x) (cCE_AD (dD_1_1_U x))
    (cDE_AB (dC_1_1_U x)) (cBE_AC (dC_1_1_U x)) (cCE_AB (dB_1_1_U x))
    (cBE_AC (dD_1_1_U x)) (cDE_AB (dB_1_1_U x)) (cCD_AE (dE_1_1_U x))
    (cBC_AE (dE_1_1_U x)) (cBD_AE (dE_1_1_U x)) (hCDE_A x)
    (hBCE_A x) (hBDE_A x) (hBCD_A x)
    (hBDE_AC (dC_1_1_U x)) (hBCE_AD (dD_1_1_U x)) (hCDE_AB (dB_1_1_U x))
    (hBCD_AE (dE_1_1_U x))).

Context (S3: Y3 -> Type) (S2: Y2 -> Type) (S1: Y1 -> Type) (S0: Y0 -> Type).

Context (DB_2_1_L: forall z, S3 z -> S2 (dB_2_1_L z)).

Context (DC_2_1_L: forall z, S3 z -> S2 (dC_2_1_L z)).

Context (DD_2_1_L: forall z, S3 z -> S2 (dD_2_1_L z)).

Context (DA_2_0_L: forall z, S3 z -> S2 (dA_2_0_L z)).

Context (DB_2_0_L: forall z, S3 z -> S2 (dB_2_0_L z)).

Context (DC_2_0_L: forall z, S3 z -> S2 (dC_2_0_L z)).

Context (DC_3_2_L: forall z, S2 z -> S1 (dC_3_2_L z)).

Context (DD_3_2_L: forall z, S2 z -> S1 (dD_3_2_L z)).

Context (DB_3_1_L: forall z, S2 z -> S1 (dB_3_1_L z)).

Context (DC_3_1_L: forall z, S2 z -> S1 (dC_3_1_L z)).

Context (DA_3_0_L: forall z, S2 z -> S1 (dA_3_0_L z)).

Context (DB_3_0_L: forall z, S2 z -> S1 (dB_3_0_L z)).

Context (DD_4_3_L: forall z, S1 z -> S0 (dD_4_3_L z)).

Context (DC_4_2_L: forall z, S1 z -> S0 (dC_4_2_L z)).

Context (DB_4_1_L: forall z, S1 z -> S0 (dB_4_1_L z)).

Context (DA_4_0_L: forall z, S1 z -> S0 (dA_4_0_L z)).

Local Definition DA_1_0_U z (a: S3 (dE_1_1_U z)) :=
  rew [S2] cAE_B z in DA_2_0_L (dE_1_1_U z) a.

Local Definition DA_2_0_U z (a: S2 (dE_2_2_U z)) :=
  rew [S1] cAE_BC z in DA_3_0_L (dE_2_2_U z) a.

Local Definition DA_3_0_U z (a: S1 (dE_3_3_U z)) :=
  rew [S0] cAE_BCD z in DA_4_0_L (dE_3_3_U z) a.

Local Definition DB_1_1_U z (a: S3 (dE_1_1_U z)) :=
  rew [S2] cBE_A z in DB_2_1_L (dE_1_1_U z) a.

Local Definition DB_1_0_U z (a: S3 (dE_1_1_U z)) :=
  rew [S2] cBE_C z in DB_2_0_L (dE_1_1_U z) a.

Local Definition DB_2_1_U z (a: S2 (dE_2_2_U z)) :=
  rew [S1] cBE_AC z in DB_3_1_L (dE_2_2_U z) a.

Local Definition DB_2_0_U z (a: S2 (dE_2_2_U z)) :=
  rew [S1] cBE_CD z in DB_3_0_L (dE_2_2_U z) a.

Local Definition DB_3_1_U z (a: S1 (dE_3_3_U z)) :=
  rew [S0] cBE_ACD z in DB_4_1_L (dE_3_3_U z) a.

Local Definition DC_1_1_U z (a: S3 (dE_1_1_U z)) :=
  rew [S2] cCE_A z in DC_2_1_L (dE_1_1_U z) a.

Local Definition DC_1_0_U z (a: S3 (dE_1_1_U z)) :=
  rew [S2] cCE_D z in DC_2_0_L (dE_1_1_U z) a.

Local Definition DC_2_2_U z (a: S2 (dE_2_2_U z)) :=
  rew [S1] cCE_AB z in DC_3_2_L (dE_2_2_U z) a.

Local Definition DC_2_1_U z (a: S2 (dE_2_2_U z)) :=
  rew [S1] cCE_AD z in DC_3_1_L (dE_2_2_U z) a.

Local Definition DC_3_2_U z (a: S1 (dE_3_3_U z)) :=
  rew [S0] cCE_ABD z in DC_4_2_L (dE_3_3_U z) a.

Local Definition DD_1_1_U z (a: S3 (dE_1_1_U z)) :=
  rew [S2] cDE_A z in DD_2_1_L (dE_1_1_U z) a.

Local Definition DD_2_2_U z (a: S2 (dE_2_2_U z)) :=
  rew [S1] cDE_AB z in DD_3_2_L (dE_2_2_U z) a.

Local Definition DD_3_3_U z (a: S1 (dE_3_3_U z)) :=
  rew [S0] cDE_ABC z in DD_4_3_L (dE_3_3_U z) a.

Context (HcAB_CE: forall z (a: S3 z), rew [S1] cAB_CE z in DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a) =
    DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a)).

Context (HcAB_DE: forall z (a: S3 z), rew [S1] cAB_DE z in DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a) =
    DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a)).

Context (HcAB_CDE: forall z (a: S2 z), rew [S0] cAB_CDE z in DA_4_0_L (dB_3_0_L z) (DB_3_0_L z a)
     = DB_4_1_L (dA_3_0_L z) (DA_3_0_L z a)).

Context (HcAC_BE: forall z (a: S3 z), rew [S1] cAC_BE z in DA_3_0_L (dC_2_1_L z) (DC_2_1_L z a) =
    DC_3_2_L (dA_2_0_L z) (DA_2_0_L z a)).

Context (HcAC_DE: forall z (a: S3 z), rew [S1] cAC_DE z in DA_3_0_L (dC_2_0_L z) (DC_2_0_L z a) =
    DC_3_1_L (dA_2_0_L z) (DA_2_0_L z a)).

Context (HcAC_BDE: forall z (a: S2 z), rew [S0] cAC_BDE z in DA_4_0_L (dC_3_1_L z) (DC_3_1_L z a)
     = DC_4_2_L (dA_3_0_L z) (DA_3_0_L z a)).

Context (HcAD_BE: forall z (a: S3 z), rew [S1] cAD_BE z in DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a) =
    DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a)).

Context (HcAD_CE: forall z (a: S3 z), rew [S1] cAD_CE z in DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a) =
    DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a)).

Context (HcAD_BCE: forall z (a: S2 z), rew [S0] cAD_BCE z in DA_4_0_L (dD_3_2_L z) (DD_3_2_L z a)
     = DD_4_3_L (dA_3_0_L z) (DA_3_0_L z a)).

Context (HcBC_AE: forall z (a: S3 z), rew [S1] cBC_AE z in DB_3_1_L (dC_2_1_L z) (DC_2_1_L z a) =
    DC_3_2_L (dB_2_1_L z) (DB_2_1_L z a)).

Context (HcBC_DE: forall z (a: S3 z), rew [S1] cBC_DE z in DB_3_0_L (dC_2_0_L z) (DC_2_0_L z a) =
    DC_3_1_L (dB_2_0_L z) (DB_2_0_L z a)).

Context (HcBC_ADE: forall z (a: S2 z), rew [S0] cBC_ADE z in DB_4_1_L (dC_3_1_L z) (DC_3_1_L z a)
     = DC_4_2_L (dB_3_1_L z) (DB_3_1_L z a)).

Context (HcBD_AE: forall z (a: S3 z), rew [S1] cBD_AE z in DB_3_1_L (dD_2_1_L z) (DD_2_1_L z a) =
    DD_3_2_L (dB_2_1_L z) (DB_2_1_L z a)).

Context (HcBD_CE: forall z (a: S3 z), rew [S1] cBD_CE z in DB_3_0_L (dD_2_1_L z) (DD_2_1_L z a) =
    DD_3_2_L (dB_2_0_L z) (DB_2_0_L z a)).

Context (HcBD_ACE: forall z (a: S2 z), rew [S0] cBD_ACE z in DB_4_1_L (dD_3_2_L z) (DD_3_2_L z a)
     = DD_4_3_L (dB_3_1_L z) (DB_3_1_L z a)).

Context (HcCD_AE: forall z (a: S3 z), rew [S1] cCD_AE z in DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a) =
    DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a)).

Context (HcCD_BE: forall z (a: S3 z), rew [S1] cCD_BE z in DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a) =
    DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a)).

Context (HcCD_ABE: forall z (a: S2 z), rew [S0] cCD_ABE z in DC_4_2_L (dD_3_2_L z) (DD_3_2_L z a)
     = DD_4_3_L (dC_3_2_L z) (DC_3_2_L z a)).

Local Definition HcAB_C z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cAB_C z in DA_2_0_U (dB_1_0_U z) (DB_1_0_U z a) = DB_2_1_U
    (dA_1_0_U z) (DA_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAB_CE (dE_1_1_U z) a) (hABE_C z)).
Defined.

Local Definition HcAB_D z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cAB_D z in DA_2_0_U (dB_1_0_U z) (DB_1_0_U z a) = DB_2_1_U
    (dA_1_0_U z) (DA_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAB_DE (dE_1_1_U z) a) (hABE_D z)).
Defined.

Local Definition HcAB_CD z (a: S2 (dE_2_2_U z)):

  rew [fun w => S0 (dE_4_4_U w)] cAB_CD z in DA_3_0_U (dB_2_0_U z) (DB_2_0_U z a) = DB_3_1_U
    (dA_2_0_U z) (DA_2_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAB_CDE (dE_2_2_U z) a) (hABE_CD z)).
Defined.

Local Definition HcAC_B z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cAC_B z in DA_2_0_U (dC_1_1_U z) (DC_1_1_U z a) = DC_2_2_U
    (dA_1_0_U z) (DA_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAC_BE (dE_1_1_U z) a) (hACE_B z)).
Defined.

Local Definition HcAC_D z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cAC_D z in DA_2_0_U (dC_1_0_U z) (DC_1_0_U z a) = DC_2_1_U
    (dA_1_0_U z) (DA_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAC_DE (dE_1_1_U z) a) (hACE_D z)).
Defined.

Local Definition HcAC_BD z (a: S2 (dE_2_2_U z)):

  rew [fun w => S0 (dE_4_4_U w)] cAC_BD z in DA_3_0_U (dC_2_1_U z) (DC_2_1_U z a) = DC_3_2_U
    (dA_2_0_U z) (DA_2_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAC_BDE (dE_2_2_U z) a) (hACE_BD z)).
Defined.

Local Definition HcAD_B z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cAD_B z in DA_2_0_U (dD_1_1_U z) (DD_1_1_U z a) = DD_2_2_U
    (dA_1_0_U z) (DA_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAD_BE (dE_1_1_U z) a) (hADE_B z)).
Defined.

Local Definition HcAD_C z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cAD_C z in DA_2_0_U (dD_1_1_U z) (DD_1_1_U z a) = DD_2_2_U
    (dA_1_0_U z) (DA_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAD_CE (dE_1_1_U z) a) (hADE_C z)).
Defined.

Local Definition HcAD_BC z (a: S2 (dE_2_2_U z)):

  rew [fun w => S0 (dE_4_4_U w)] cAD_BC z in DA_3_0_U (dD_2_2_U z) (DD_2_2_U z a) = DD_3_3_U
    (dA_2_0_U z) (DA_2_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcAD_BCE (dE_2_2_U z) a) (hADE_BC z)).
Defined.

Local Definition HcBC_A z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cBC_A z in DB_2_1_U (dC_1_1_U z) (DC_1_1_U z a) = DC_2_2_U
    (dB_1_1_U z) (DB_1_1_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcBC_AE (dE_1_1_U z) a) (hBCE_A z)).
Defined.

Local Definition HcBC_D z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cBC_D z in DB_2_0_U (dC_1_0_U z) (DC_1_0_U z a) = DC_2_1_U
    (dB_1_0_U z) (DB_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcBC_DE (dE_1_1_U z) a) (hBCE_D z)).
Defined.

Local Definition HcBC_AD z (a: S2 (dE_2_2_U z)):

  rew [fun w => S0 (dE_4_4_U w)] cBC_AD z in DB_3_1_U (dC_2_1_U z) (DC_2_1_U z a) = DC_3_2_U
    (dB_2_1_U z) (DB_2_1_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcBC_ADE (dE_2_2_U z) a) (hBCE_AD z)).
Defined.

Local Definition HcBD_A z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cBD_A z in DB_2_1_U (dD_1_1_U z) (DD_1_1_U z a) = DD_2_2_U
    (dB_1_1_U z) (DB_1_1_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcBD_AE (dE_1_1_U z) a) (hBDE_A z)).
Defined.

Local Definition HcBD_C z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cBD_C z in DB_2_0_U (dD_1_1_U z) (DD_1_1_U z a) = DD_2_2_U
    (dB_1_0_U z) (DB_1_0_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcBD_CE (dE_1_1_U z) a) (hBDE_C z)).
Defined.

Local Definition HcBD_AC z (a: S2 (dE_2_2_U z)):

  rew [fun w => S0 (dE_4_4_U w)] cBD_AC z in DB_3_1_U (dD_2_2_U z) (DD_2_2_U z a) = DD_3_3_U
    (dB_2_1_U z) (DB_2_1_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcBD_ACE (dE_2_2_U z) a) (hBDE_AC z)).
Defined.

Local Definition HcCD_A z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cCD_A z in DC_2_1_U (dD_1_1_U z) (DD_1_1_U z a) = DD_2_2_U
    (dC_1_1_U z) (DC_1_1_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcCD_AE (dE_1_1_U z) a) (hCDE_A z)).
Defined.

Local Definition HcCD_B z (a: S3 (dE_1_1_U z)):

  rew [fun w => S1 (dE_3_3_U w)] cCD_B z in DC_2_1_U (dD_1_1_U z) (DD_1_1_U z a) = DD_2_2_U
    (dC_1_1_U z) (DC_1_1_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcCD_BE (dE_1_1_U z) a) (hCDE_B z)).
Defined.

Local Definition HcCD_AB z (a: S2 (dE_2_2_U z)):

  rew [fun w => S0 (dE_4_4_U w)] cCD_AB z in DC_3_2_U (dD_2_2_U z) (DD_2_2_U z a) = DD_3_3_U
    (dC_2_2_U z) (DC_2_2_U z a).
Proof.
  now exact (rew_cohLayer_hex (HcCD_ABE (dE_2_2_U z) a) (hCDE_AB z)).
Defined.

Context (x: X5).

Context (aA: S3 (dA_1_0_L (dE_0_0_U x))).

Local Definition aA_layer :=
  rew [S3] cAE_nil x in aA.

Context (aB: S3 (dB_1_0_L (dE_0_0_U x))).

Local Definition aB_layer :=
  rew [S3] cBE_nil x in aB.

Context (aC: S3 (dC_1_0_L (dE_0_0_U x))).

Local Definition aC_layer :=
  rew [S3] cCE_nil x in aC.

Context (aD: S3 (dD_1_0_L (dE_0_0_U x))).

Local Definition aD_layer :=
  rew [S3] cDE_nil x in aD.

Context (HcAB_E: rew [S2] cAB_E (dE_0_0_U x) in DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB = DB_2_1_L
    (dA_1_0_L (dE_0_0_U x)) aA).

Local Definition HcAB_nil: rew [fun w => S2 (dE_2_2_U w)] cAB_nil x in DA_1_0_U (dB_0_0_U x)
  aB_layer =
  DB_1_1_U (dA_0_0_U x) aA_layer.
Proof.
  now exact (rew_cohLayer_hex HcAB_E (hABE_nil x)).
Defined.

Context (HcAC_E: rew [S2] cAC_E (dE_0_0_U x) in DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC = DC_2_1_L
    (dA_1_0_L (dE_0_0_U x)) aA).

Local Definition HcAC_nil: rew [fun w => S2 (dE_2_2_U w)] cAC_nil x in DA_1_0_U (dC_0_0_U x)
  aC_layer =
  DC_1_1_U (dA_0_0_U x) aA_layer.
Proof.
  now exact (rew_cohLayer_hex HcAC_E (hACE_nil x)).
Defined.

Context (HcAD_E: rew [S2] cAD_E (dE_0_0_U x) in DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD = DD_2_1_L
    (dA_1_0_L (dE_0_0_U x)) aA).

Local Definition HcAD_nil: rew [fun w => S2 (dE_2_2_U w)] cAD_nil x in DA_1_0_U (dD_0_0_U x)
  aD_layer =
  DD_1_1_U (dA_0_0_U x) aA_layer.
Proof.
  now exact (rew_cohLayer_hex HcAD_E (hADE_nil x)).
Defined.

Context (HcBC_E: rew [S2] cBC_E (dE_0_0_U x) in DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC = DC_2_1_L
    (dB_1_0_L (dE_0_0_U x)) aB).

Local Definition HcBC_nil: rew [fun w => S2 (dE_2_2_U w)] cBC_nil x in DB_1_0_U (dC_0_0_U x)
  aC_layer =
  DC_1_1_U (dB_0_0_U x) aB_layer.
Proof.
  now exact (rew_cohLayer_hex HcBC_E (hBCE_nil x)).
Defined.

Context (HcBD_E: rew [S2] cBD_E (dE_0_0_U x) in DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD = DD_2_1_L
    (dB_1_0_L (dE_0_0_U x)) aB).

Local Definition HcBD_nil: rew [fun w => S2 (dE_2_2_U w)] cBD_nil x in DB_1_0_U (dD_0_0_U x)
  aD_layer =
  DD_1_1_U (dB_0_0_U x) aB_layer.
Proof.
  now exact (rew_cohLayer_hex HcBD_E (hBDE_nil x)).
Defined.

Context (HcCD_E: rew [S2] cCD_E (dE_0_0_U x) in DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD = DD_2_1_L
    (dC_1_0_L (dE_0_0_U x)) aC).

Local Definition HcCD_nil: rew [fun w => S2 (dE_2_2_U w)] cCD_nil x in DC_1_0_U (dD_0_0_U x)
  aD_layer =
  DD_1_1_U (dC_0_0_U x) aC_layer.
Proof.
  now exact (rew_cohLayer_hex HcCD_E (hCDE_nil x)).
Defined.

Context (HhABC_E: hexagonal_coherence_dep DA_3_0_L DC_3_2_L DB_3_1_L (hABC_E (dE_0_0_U x))
  HcBC_E HcAB_E HcAC_E (HcAC_BE (dB_1_0_L (dE_0_0_U x)) aB) (HcAB_CE (dC_1_0_L (dE_0_0_U x)) aC)
    (HcBC_AE (dA_1_0_L (dE_0_0_U x)) aA)).

Context (HhABC_DE: forall z (a: S3 z), hexagonal_coherence_dep DA_4_0_L DC_4_2_L DB_4_1_L
    (hABC_DE z)
  (HcBC_DE z a) (HcAB_DE z a) (HcAC_DE z a) (HcAC_BDE (dB_2_0_L z) (DB_2_0_L z a))
    (HcAB_CDE (dC_2_0_L z) (DC_2_0_L z a)) (HcBC_ADE (dA_2_0_L z) (DA_2_0_L z a))).

Context (HhABD_E: hexagonal_coherence_dep DA_3_0_L DD_3_2_L DB_3_1_L (hABD_E (dE_0_0_U x))
  HcBD_E HcAB_E HcAD_E (HcAD_BE (dB_1_0_L (dE_0_0_U x)) aB) (HcAB_DE (dD_1_0_L (dE_0_0_U x)) aD)
    (HcBD_AE (dA_1_0_L (dE_0_0_U x)) aA)).

Context (HhABD_CE: forall z (a: S3 z), hexagonal_coherence_dep DA_4_0_L DD_4_3_L DB_4_1_L
    (hABD_CE z)
  (HcBD_CE z a) (HcAB_CE z a) (HcAD_CE z a) (HcAD_BCE (dB_2_0_L z) (DB_2_0_L z a))
    (HcAB_CDE (dD_2_1_L z) (DD_2_1_L z a)) (HcBD_ACE (dA_2_0_L z) (DA_2_0_L z a))).

Context (HhACD_E: hexagonal_coherence_dep DA_3_0_L DD_3_2_L DC_3_1_L (hACD_E (dE_0_0_U x))
  HcCD_E HcAC_E HcAD_E (HcAD_CE (dC_1_0_L (dE_0_0_U x)) aC) (HcAC_DE (dD_1_0_L (dE_0_0_U x)) aD)
    (HcCD_AE (dA_1_0_L (dE_0_0_U x)) aA)).

Context (HhACD_BE: forall z (a: S3 z), hexagonal_coherence_dep DA_4_0_L DD_4_3_L DC_4_2_L
    (hACD_BE z)
  (HcCD_BE z a) (HcAC_BE z a) (HcAD_BE z a) (HcAD_BCE (dC_2_1_L z) (DC_2_1_L z a))
    (HcAC_BDE (dD_2_1_L z) (DD_2_1_L z a)) (HcCD_ABE (dA_2_0_L z) (DA_2_0_L z a))).

Context (HhBCD_E: hexagonal_coherence_dep DB_3_0_L DD_3_2_L DC_3_1_L (hBCD_E (dE_0_0_U x))
  HcCD_E HcBC_E HcBD_E (HcBD_CE (dC_1_0_L (dE_0_0_U x)) aC) (HcBC_DE (dD_1_0_L (dE_0_0_U x)) aD)
    (HcCD_BE (dB_1_0_L (dE_0_0_U x)) aB)).

Context (HhBCD_AE: forall z (a: S3 z), hexagonal_coherence_dep DB_4_1_L DD_4_3_L DC_4_2_L
    (hBCD_AE z)
  (HcCD_AE z a) (HcBC_AE z a) (HcBD_AE z a) (HcBD_ACE (dC_2_1_L z) (DC_2_1_L z a))
    (HcBC_ADE (dD_2_1_L z) (DD_2_1_L z a)) (HcCD_ABE (dB_2_1_L z) (DB_2_1_L z a))).

Local Definition HhABC_nil :=
  @rew_coh2Layer_perm4 Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dA_2_0_U dC_2_2_U dB_2_1_U
    dA_3_0_L dC_3_2_L dB_3_1_L DA_3_0_L DC_3_2_L DB_3_1_L cAE_BC cCE_AB cBE_AC dB_2_0_L dC_2_1_L
    dA_2_0_L dB_2_1_L DB_2_0_L DC_2_1_L DA_2_0_L DB_2_1_L cAC_BE cAB_CE cBC_AE HcAC_BE HcAB_CE
    HcBC_AE (dB_1_0_U (dC_0_0_U x)) (dC_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x))
    (dB_1_1_U (dA_0_0_U x)) (dA_1_0_U (dC_0_0_U x)) (dC_1_1_U (dA_0_0_U x)) (cBC_nil x)
    (cAB_nil x) (cAC_nil x) (cAC_B (dB_0_0_U x)) (cAB_C (dC_0_0_U x)) (cBC_A (dA_0_0_U x))
    (dC_1_0_L (dE_0_0_U x)) (dE_1_1_U (dC_0_0_U x)) (dB_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dB_0_0_U x)) (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cCE_nil x)
    (cBE_nil x) (cAE_nil x) aC aB aA (cBE_C (dC_0_0_U x)) (cCE_A (dB_0_0_U x))
    (cAE_B (dB_0_0_U x)) (cBE_A (dA_0_0_U x)) (cAE_B (dC_0_0_U x)) (cCE_A (dA_0_0_U x))
    (cBC_E (dE_0_0_U x)) (cAB_E (dE_0_0_U x)) (cAC_E (dE_0_0_U x)) HcBC_E HcAB_E HcAC_E
    (hBCE_nil x) (hABE_nil x) (hACE_nil x) (hABC_nil x) (hACE_B (dB_0_0_U x))
    (hABE_C (dC_0_0_U x)) (hBCE_A (dA_0_0_U x)) (hABC_E (dE_0_0_U x)) HhABC_E (kABCE_nil x).

Local Definition HhABC_D z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4 Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dC_3_2_U dB_3_1_U
    dA_4_0_L dC_4_2_L dB_4_1_L DA_4_0_L DC_4_2_L DB_4_1_L cAE_BCD cCE_ABD cBE_ACD dB_3_0_L
    dC_3_1_L dA_3_0_L dB_3_1_L DB_3_0_L DC_3_1_L DA_3_0_L DB_3_1_L cAC_BDE cAB_CDE cBC_ADE
    HcAC_BDE HcAB_CDE HcBC_ADE (dB_2_0_U (dC_1_0_U z)) (dC_2_1_U (dB_1_0_U z))
    (dA_2_0_U (dB_1_0_U z)) (dB_2_1_U (dA_1_0_U z)) (dA_2_0_U (dC_1_0_U z))
    (dC_2_1_U (dA_1_0_U z)) (cBC_D z) (cAB_D z) (cAC_D z) (cAC_BD (dB_1_0_U z))
    (cAB_CD (dC_1_0_U z)) (cBC_AD (dA_1_0_U z)) (dC_2_0_L (dE_1_1_U z)) (dE_2_2_U (dC_1_0_U z))
    (dB_2_0_L (dE_1_1_U z)) (dE_2_2_U (dB_1_0_U z)) (dA_2_0_L (dE_1_1_U z))
    (dE_2_2_U (dA_1_0_U z)) (cCE_D z) (cBE_C z) (cAE_B z) (DC_2_0_L (dE_1_1_U z) a)
    (DB_2_0_L (dE_1_1_U z) a) (DA_2_0_L (dE_1_1_U z) a) (cBE_CD (dC_1_0_U z))
    (cCE_AD (dB_1_0_U z)) (cAE_BC (dB_1_0_U z)) (cBE_AC (dA_1_0_U z)) (cAE_BC (dC_1_0_U z))
    (cCE_AD (dA_1_0_U z)) (cBC_DE (dE_1_1_U z)) (cAB_DE (dE_1_1_U z)) (cAC_DE (dE_1_1_U z))
    (HcBC_DE (dE_1_1_U z) a) (HcAB_DE (dE_1_1_U z) a) (HcAC_DE (dE_1_1_U z) a) (hBCE_D z)
    (hABE_D z) (hACE_D z) (hABC_D z) (hACE_BD (dB_1_0_U z)) (hABE_CD (dC_1_0_U z))
    (hBCE_AD (dA_1_0_U z)) (hABC_DE (dE_1_1_U z)) (HhABC_DE (dE_1_1_U z) a) (kABCE_D z).

Local Definition HhABD_nil :=
  @rew_coh2Layer_perm4 Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dA_2_0_U dD_2_2_U dB_2_1_U
    dA_3_0_L dD_3_2_L dB_3_1_L DA_3_0_L DD_3_2_L DB_3_1_L cAE_BC cDE_AB cBE_AC dB_2_0_L dD_2_1_L
    dA_2_0_L dB_2_1_L DB_2_0_L DD_2_1_L DA_2_0_L DB_2_1_L cAD_BE cAB_DE cBD_AE HcAD_BE HcAB_DE
    HcBD_AE (dB_1_0_U (dD_0_0_U x)) (dD_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x))
    (dB_1_1_U (dA_0_0_U x)) (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cBD_nil x)
    (cAB_nil x) (cAD_nil x) (cAD_B (dB_0_0_U x)) (cAB_D (dD_0_0_U x)) (cBD_A (dA_0_0_U x))
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (dB_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dB_0_0_U x)) (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cDE_nil x)
    (cBE_nil x) (cAE_nil x) aD aB aA (cBE_C (dD_0_0_U x)) (cDE_A (dB_0_0_U x))
    (cAE_B (dB_0_0_U x)) (cBE_A (dA_0_0_U x)) (cAE_B (dD_0_0_U x)) (cDE_A (dA_0_0_U x))
    (cBD_E (dE_0_0_U x)) (cAB_E (dE_0_0_U x)) (cAD_E (dE_0_0_U x)) HcBD_E HcAB_E HcAD_E
    (hBDE_nil x) (hABE_nil x) (hADE_nil x) (hABD_nil x) (hADE_B (dB_0_0_U x))
    (hABE_D (dD_0_0_U x)) (hBDE_A (dA_0_0_U x)) (hABD_E (dE_0_0_U x)) HhABD_E (kABDE_nil x).

Local Definition HhABD_C z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4 Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dD_3_3_U dB_3_1_U
    dA_4_0_L dD_4_3_L dB_4_1_L DA_4_0_L DD_4_3_L DB_4_1_L cAE_BCD cDE_ABC cBE_ACD dB_3_0_L
    dD_3_2_L dA_3_0_L dB_3_1_L DB_3_0_L DD_3_2_L DA_3_0_L DB_3_1_L cAD_BCE cAB_CDE cBD_ACE
    HcAD_BCE HcAB_CDE HcBD_ACE (dB_2_0_U (dD_1_1_U z)) (dD_2_2_U (dB_1_0_U z))
    (dA_2_0_U (dB_1_0_U z)) (dB_2_1_U (dA_1_0_U z)) (dA_2_0_U (dD_1_1_U z))
    (dD_2_2_U (dA_1_0_U z)) (cBD_C z) (cAB_C z) (cAD_C z) (cAD_BC (dB_1_0_U z))
    (cAB_CD (dD_1_1_U z)) (cBD_AC (dA_1_0_U z)) (dD_2_1_L (dE_1_1_U z)) (dE_2_2_U (dD_1_1_U z))
    (dB_2_0_L (dE_1_1_U z)) (dE_2_2_U (dB_1_0_U z)) (dA_2_0_L (dE_1_1_U z))
    (dE_2_2_U (dA_1_0_U z)) (cDE_A z) (cBE_C z) (cAE_B z) (DD_2_1_L (dE_1_1_U z) a)
    (DB_2_0_L (dE_1_1_U z) a) (DA_2_0_L (dE_1_1_U z) a) (cBE_CD (dD_1_1_U z))
    (cDE_AB (dB_1_0_U z)) (cAE_BC (dB_1_0_U z)) (cBE_AC (dA_1_0_U z)) (cAE_BC (dD_1_1_U z))
    (cDE_AB (dA_1_0_U z)) (cBD_CE (dE_1_1_U z)) (cAB_CE (dE_1_1_U z)) (cAD_CE (dE_1_1_U z))
    (HcBD_CE (dE_1_1_U z) a) (HcAB_CE (dE_1_1_U z) a) (HcAD_CE (dE_1_1_U z) a) (hBDE_C z)
    (hABE_C z) (hADE_C z) (hABD_C z) (hADE_BC (dB_1_0_U z)) (hABE_CD (dD_1_1_U z))
    (hBDE_AC (dA_1_0_U z)) (hABD_CE (dE_1_1_U z)) (HhABD_CE (dE_1_1_U z) a) (kABDE_C z).

Local Definition HhACD_nil :=
  @rew_coh2Layer_perm4 Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dA_2_0_U dD_2_2_U dC_2_1_U
    dA_3_0_L dD_3_2_L dC_3_1_L DA_3_0_L DD_3_2_L DC_3_1_L cAE_BC cDE_AB cCE_AD dC_2_0_L dD_2_1_L
    dA_2_0_L dC_2_1_L DC_2_0_L DD_2_1_L DA_2_0_L DC_2_1_L cAD_CE cAC_DE cCD_AE HcAD_CE HcAC_DE
    HcCD_AE (dC_1_0_U (dD_0_0_U x)) (dD_1_1_U (dC_0_0_U x)) (dA_1_0_U (dC_0_0_U x))
    (dC_1_1_U (dA_0_0_U x)) (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cCD_nil x)
    (cAC_nil x) (cAD_nil x) (cAD_C (dC_0_0_U x)) (cAC_D (dD_0_0_U x)) (cCD_A (dA_0_0_U x))
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (dC_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dC_0_0_U x)) (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cDE_nil x)
    (cCE_nil x) (cAE_nil x) aD aC aA (cCE_D (dD_0_0_U x)) (cDE_A (dC_0_0_U x))
    (cAE_B (dC_0_0_U x)) (cCE_A (dA_0_0_U x)) (cAE_B (dD_0_0_U x)) (cDE_A (dA_0_0_U x))
    (cCD_E (dE_0_0_U x)) (cAC_E (dE_0_0_U x)) (cAD_E (dE_0_0_U x)) HcCD_E HcAC_E HcAD_E
    (hCDE_nil x) (hACE_nil x) (hADE_nil x) (hACD_nil x) (hADE_C (dC_0_0_U x))
    (hACE_D (dD_0_0_U x)) (hCDE_A (dA_0_0_U x)) (hACD_E (dE_0_0_U x)) HhACD_E (kACDE_nil x).

Local Definition HhACD_B z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4 Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dD_3_3_U dC_3_2_U
    dA_4_0_L dD_4_3_L dC_4_2_L DA_4_0_L DD_4_3_L DC_4_2_L cAE_BCD cDE_ABC cCE_ABD dC_3_1_L
    dD_3_2_L dA_3_0_L dC_3_2_L DC_3_1_L DD_3_2_L DA_3_0_L DC_3_2_L cAD_BCE cAC_BDE cCD_ABE
    HcAD_BCE HcAC_BDE HcCD_ABE (dC_2_1_U (dD_1_1_U z)) (dD_2_2_U (dC_1_1_U z))
    (dA_2_0_U (dC_1_1_U z)) (dC_2_2_U (dA_1_0_U z)) (dA_2_0_U (dD_1_1_U z))
    (dD_2_2_U (dA_1_0_U z)) (cCD_B z) (cAC_B z) (cAD_B z) (cAD_BC (dC_1_1_U z))
    (cAC_BD (dD_1_1_U z)) (cCD_AB (dA_1_0_U z)) (dD_2_1_L (dE_1_1_U z)) (dE_2_2_U (dD_1_1_U z))
    (dC_2_1_L (dE_1_1_U z)) (dE_2_2_U (dC_1_1_U z)) (dA_2_0_L (dE_1_1_U z))
    (dE_2_2_U (dA_1_0_U z)) (cDE_A z) (cCE_A z) (cAE_B z) (DD_2_1_L (dE_1_1_U z) a)
    (DC_2_1_L (dE_1_1_U z) a) (DA_2_0_L (dE_1_1_U z) a) (cCE_AD (dD_1_1_U z))
    (cDE_AB (dC_1_1_U z)) (cAE_BC (dC_1_1_U z)) (cCE_AB (dA_1_0_U z)) (cAE_BC (dD_1_1_U z))
    (cDE_AB (dA_1_0_U z)) (cCD_BE (dE_1_1_U z)) (cAC_BE (dE_1_1_U z)) (cAD_BE (dE_1_1_U z))
    (HcCD_BE (dE_1_1_U z) a) (HcAC_BE (dE_1_1_U z) a) (HcAD_BE (dE_1_1_U z) a) (hCDE_B z)
    (hACE_B z) (hADE_B z) (hACD_B z) (hADE_BC (dC_1_1_U z)) (hACE_BD (dD_1_1_U z))
    (hCDE_AB (dA_1_0_U z)) (hACD_BE (dE_1_1_U z)) (HhACD_BE (dE_1_1_U z) a) (kACDE_B z).

Local Definition HhBCD_nil :=
  @rew_coh2Layer_perm4 Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dB_2_0_U dD_2_2_U dC_2_1_U
    dB_3_0_L dD_3_2_L dC_3_1_L DB_3_0_L DD_3_2_L DC_3_1_L cBE_CD cDE_AB cCE_AD dC_2_0_L dD_2_1_L
    dB_2_0_L dC_2_1_L DC_2_0_L DD_2_1_L DB_2_0_L DC_2_1_L cBD_CE cBC_DE cCD_BE HcBD_CE HcBC_DE
    HcCD_BE (dC_1_0_U (dD_0_0_U x)) (dD_1_1_U (dC_0_0_U x)) (dB_1_0_U (dC_0_0_U x))
    (dC_1_1_U (dB_0_0_U x)) (dB_1_0_U (dD_0_0_U x)) (dD_1_1_U (dB_0_0_U x)) (cCD_nil x)
    (cBC_nil x) (cBD_nil x) (cBD_C (dC_0_0_U x)) (cBC_D (dD_0_0_U x)) (cCD_B (dB_0_0_U x))
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (dC_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dC_0_0_U x)) (dB_1_0_L (dE_0_0_U x)) (dE_1_1_U (dB_0_0_U x)) (cDE_nil x)
    (cCE_nil x) (cBE_nil x) aD aC aB (cCE_D (dD_0_0_U x)) (cDE_A (dC_0_0_U x))
    (cBE_C (dC_0_0_U x)) (cCE_A (dB_0_0_U x)) (cBE_C (dD_0_0_U x)) (cDE_A (dB_0_0_U x))
    (cCD_E (dE_0_0_U x)) (cBC_E (dE_0_0_U x)) (cBD_E (dE_0_0_U x)) HcCD_E HcBC_E HcBD_E
    (hCDE_nil x) (hBCE_nil x) (hBDE_nil x) (hBCD_nil x) (hBDE_C (dC_0_0_U x))
    (hBCE_D (dD_0_0_U x)) (hCDE_B (dB_0_0_U x)) (hBCD_E (dE_0_0_U x)) HhBCD_E (kBCDE_nil x).

Local Definition HhBCD_A z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4 Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dB_3_1_U dD_3_3_U dC_3_2_U
    dB_4_1_L dD_4_3_L dC_4_2_L DB_4_1_L DD_4_3_L DC_4_2_L cBE_ACD cDE_ABC cCE_ABD dC_3_1_L
    dD_3_2_L dB_3_1_L dC_3_2_L DC_3_1_L DD_3_2_L DB_3_1_L DC_3_2_L cBD_ACE cBC_ADE cCD_ABE
    HcBD_ACE HcBC_ADE HcCD_ABE (dC_2_1_U (dD_1_1_U z)) (dD_2_2_U (dC_1_1_U z))
    (dB_2_1_U (dC_1_1_U z)) (dC_2_2_U (dB_1_1_U z)) (dB_2_1_U (dD_1_1_U z))
    (dD_2_2_U (dB_1_1_U z)) (cCD_A z) (cBC_A z) (cBD_A z) (cBD_AC (dC_1_1_U z))
    (cBC_AD (dD_1_1_U z)) (cCD_AB (dB_1_1_U z)) (dD_2_1_L (dE_1_1_U z)) (dE_2_2_U (dD_1_1_U z))
    (dC_2_1_L (dE_1_1_U z)) (dE_2_2_U (dC_1_1_U z)) (dB_2_1_L (dE_1_1_U z))
    (dE_2_2_U (dB_1_1_U z)) (cDE_A z) (cCE_A z) (cBE_A z) (DD_2_1_L (dE_1_1_U z) a)
    (DC_2_1_L (dE_1_1_U z) a) (DB_2_1_L (dE_1_1_U z) a) (cCE_AD (dD_1_1_U z))
    (cDE_AB (dC_1_1_U z)) (cBE_AC (dC_1_1_U z)) (cCE_AB (dB_1_1_U z)) (cBE_AC (dD_1_1_U z))
    (cDE_AB (dB_1_1_U z)) (cCD_AE (dE_1_1_U z)) (cBC_AE (dE_1_1_U z)) (cBD_AE (dE_1_1_U z))
    (HcCD_AE (dE_1_1_U z) a) (HcBC_AE (dE_1_1_U z) a) (HcBD_AE (dE_1_1_U z) a) (hCDE_A z)
    (hBCE_A z) (hBDE_A z) (hBCD_A z) (hBDE_AC (dC_1_1_U z)) (hBCE_AD (dD_1_1_U z))
    (hCDE_AB (dB_1_1_U z)) (hBCD_AE (dE_1_1_U z)) (HhBCD_AE (dE_1_1_U z) a) (kBCDE_A z).

(** The supplied painting coherence and the frame P5 relating its base
    permutahedron to the layer boundary. *)
Local Definition source_perm4: Prop :=
  permutahedral_coherence_dep (kABCD_E (dE_0_0_U x)) DD_3_2_L DD_4_3_L DA_3_0_L DC_3_2_L DB_3_1_L
    DA_4_0_L DC_4_2_L DB_4_1_L DB_3_0_L DC_3_1_L DA_3_0_L DB_3_1_L HcAD_BCE HcCD_ABE HcBD_ACE
    HcAC_BDE HcAB_CDE HcBC_ADE HcBC_E HcAB_E HcAC_E (HcAC_BE (dB_1_0_L (dE_0_0_U x)) aB)
    (HcAB_CE (dC_1_0_L (dE_0_0_U x)) aC) (HcBC_AE (dA_1_0_L (dE_0_0_U x)) aA) HcCD_E HcBD_E HcAD_E
    (HcBD_CE (dC_1_0_L (dE_0_0_U x)) aC) (HcCD_BE (dB_1_0_L (dE_0_0_U x)) aB)
    (HcAD_BE (dB_1_0_L (dE_0_0_U x)) aB) (HcBD_AE (dA_1_0_L (dE_0_0_U x)) aA)
    (HcAD_CE (dC_1_0_L (dE_0_0_U x)) aC) (HcCD_AE (dA_1_0_L (dE_0_0_U x)) aA)
    (HcBC_DE (dD_1_0_L (dE_0_0_U x)) aD) (HcAB_DE (dD_1_0_L (dE_0_0_U x)) aD)
    (HcAC_DE (dD_1_0_L (dE_0_0_U x)) aD) HhBCD_E HhABD_E HhACD_E HhABC_E
    (HhACD_BE (dB_1_0_L (dE_0_0_U x)) aB) (HhABD_CE (dC_1_0_L (dE_0_0_U x)) aC)
    (HhBCD_AE (dA_1_0_L (dE_0_0_U x)) aA) (HhABC_DE (dD_1_0_L (dE_0_0_U x)) aD).

Local Definition frame_perm5: Prop :=
  @perm5_coherence X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dB_0_0_U dC_0_0_U dD_0_0_U dE_0_0_U
    dB_1_1_U dC_1_1_U dD_1_1_U dE_1_1_U dA_1_0_U dB_1_0_U dC_1_0_U dA_1_0_L dB_1_0_L dC_1_0_L
    dD_1_0_L dC_2_2_U dD_2_2_U dE_2_2_U dB_2_1_U dC_2_1_U dB_2_1_L dC_2_1_L dD_2_1_L dA_2_0_U
    dA_2_0_L dB_2_0_U dB_2_0_L dC_2_0_L dD_3_3_U dE_3_3_U dC_3_2_U dC_3_2_L dD_3_2_L dB_3_1_U
    dB_3_1_L dC_3_1_L dA_3_0_U dA_3_0_L dB_3_0_L dE_4_4_U dD_4_3_L dC_4_2_L dB_4_1_L dA_4_0_L
    cAB_nil cAB_C cAB_D cAB_E cAB_CD cAB_CE cAB_DE cAB_CDE cAC_nil cAC_B cAC_D cAC_E cAC_BD cAC_BE
    cAC_DE cAC_BDE cAD_nil cAD_B cAD_C cAD_E cAD_BC cAD_BE cAD_CE cAD_BCE cAE_nil cAE_B cAE_B
    cAE_B cAE_BC cAE_BC cAE_BC cAE_BCD cBC_nil cBC_A cBC_D cBC_E cBC_AD cBC_AE cBC_DE cBC_ADE
    cBD_nil cBD_A cBD_C cBD_E cBD_AC cBD_AE cBD_CE cBD_ACE cBE_nil cBE_A cBE_C cBE_C cBE_AC cBE_AC
    cBE_CD cBE_ACD cCD_nil cCD_A cCD_B cCD_E cCD_AB cCD_AE cCD_BE cCD_ABE cCE_nil cCE_A cCE_A
    cCE_D cCE_AB cCE_AD cCE_AD cCE_ABD cDE_nil cDE_A cDE_A cDE_A cDE_AB cDE_AB cDE_AB cDE_ABC
    hABC_nil hABC_D hABC_E hABC_DE hABD_nil hABD_C hABD_E hABD_CE hABE_nil hABE_C hABE_D hABE_CD
    hACD_nil hACD_B hACD_E hACD_BE hACE_nil hACE_B hACE_D hACE_BD hADE_nil hADE_B hADE_C hADE_BC
    hBCD_nil hBCD_A hBCD_E hBCD_AE hBCE_nil hBCE_A hBCE_D hBCE_AD hBDE_nil hBDE_A hBDE_C hBDE_AC
    hCDE_nil hCDE_A hCDE_B hCDE_AB kABCD_nil kABCD_E kABCE_nil kABCE_D kABDE_nil kABDE_C kACDE_nil
    kACDE_B kBCDE_nil kBCDE_A x.

Local Abbreviation v_ABCD :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_ABCD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U dC_1_0_U
    dD_1_0_L dE_2_2_U dB_2_0_U dC_2_0_L dE_3_3_U dA_3_0_U dB_3_0_L dE_4_4_U dA_4_0_L cAE_BCD
    cBE_CD cCE_D cDE_nil x).

Local Definition Hv_ABCD: rew [S0] v_ABCD in
  (DA_4_0_L (dB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
  (DA_3_0_U (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))
    (DB_2_0_U (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer))).
Proof.
  now exact ((sigT_map_eq DA_4_0_L ((sigT_map_eq DB_3_0_L
            ((sigT_map_eq DC_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_ABDC :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_ABDC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dC_1_0_L dE_2_2_U dD_2_1_L dB_2_0_U dE_3_3_U dA_3_0_U dB_3_0_L dE_4_4_U dA_4_0_L cAE_BCD
    cBE_CD cCE_nil cDE_A x).

Local Definition Hv_ABDC: rew [S0] v_ABDC in
  (DA_4_0_L (dB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
    (DB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC))) =
  (DA_3_0_U (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))
    (DB_2_0_U (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer))).
Proof.
  now exact ((sigT_map_eq DA_4_0_L ((sigT_map_eq DB_3_0_L
            ((sigT_map_eq DD_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_ACBD :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_ACBD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U dB_1_0_U
    dD_1_0_L dE_2_2_U dC_2_1_U dB_2_0_L dE_3_3_U dC_3_1_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD cBE_C
    cCE_AD cDE_nil x).

Local Definition Hv_ACBD: rew [S0] v_ACBD in
  (DA_4_0_L (dC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
  (DA_3_0_U (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))
    (DC_2_1_U (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer))).
Proof.
  now exact ((sigT_map_eq DA_4_0_L ((sigT_map_eq DC_3_1_L
            ((sigT_map_eq DB_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_ACDB :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_ACDB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dB_1_0_L dE_2_2_U dC_2_1_U dD_2_1_L dE_3_3_U dC_3_1_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD
    cBE_nil cCE_AD cDE_A x).

Local Definition Hv_ACDB: rew [S0] v_ACDB in
  (DA_4_0_L (dC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
    (DC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
  (DA_3_0_U (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))
    (DC_2_1_U (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer))).
Proof.
  now exact ((sigT_map_eq DA_4_0_L ((sigT_map_eq DC_3_1_L
            ((sigT_map_eq DD_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_ADBC :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_ADBC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dE_1_1_U dB_1_0_U
    dC_1_0_L dD_2_2_U dE_2_2_U dB_2_0_L dE_3_3_U dD_3_2_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD cBE_C
    cCE_nil cDE_AB x).

Local Definition Hv_ADBC: rew [S0] v_ADBC in
  (DA_4_0_L (dD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
    (DD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
  (DA_3_0_U (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))
    (DD_2_2_U (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer))).
Proof.
  now exact ((sigT_map_eq DA_4_0_L ((sigT_map_eq DD_3_2_L
            ((sigT_map_eq DB_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_ADCB :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_ADCB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dC_1_1_U dE_1_1_U
    dB_1_0_L dD_2_2_U dE_2_2_U dC_2_1_L dE_3_3_U dD_3_2_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD
    cBE_nil cCE_A cDE_AB x).

Local Definition Hv_ADCB: rew [S0] v_ADCB in
  (DA_4_0_L (dD_3_2_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))))
    (DD_3_2_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))) (DC_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
  (DA_3_0_U (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))
    (DD_2_2_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer))).
Proof.
  now exact ((sigT_map_eq DA_4_0_L ((sigT_map_eq DD_3_2_L
            ((sigT_map_eq DC_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_BACD :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_BACD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U dC_1_0_U
    dD_1_0_L dE_2_2_U dA_2_0_U dC_2_0_L dE_3_3_U dB_3_1_U dA_3_0_L dE_4_4_U dB_4_1_L cAE_BC
    cBE_ACD cCE_D cDE_nil x).

Local Definition Hv_BACD: rew [S0] v_BACD in
  (DB_4_1_L (dA_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DA_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
  (DB_3_1_U (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))
    (DA_2_0_U (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer))).
Proof.
  now exact ((sigT_map_eq DB_4_1_L ((sigT_map_eq DA_3_0_L
            ((sigT_map_eq DC_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_BADC :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_BADC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dC_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dE_3_3_U dB_3_1_U dA_3_0_L dE_4_4_U dB_4_1_L cAE_BC
    cBE_ACD cCE_nil cDE_A x).

Local Definition Hv_BADC: rew [S0] v_BADC in
  (DB_4_1_L (dA_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
    (DA_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC))) =
  (DB_3_1_U (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))
    (DA_2_0_U (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer))).
Proof.
  now exact ((sigT_map_eq DB_4_1_L ((sigT_map_eq DA_3_0_L
            ((sigT_map_eq DD_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_BCAD :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_BCAD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U dA_1_0_U
    dD_1_0_L dE_2_2_U dC_2_1_U dA_2_0_L dE_3_3_U dB_3_1_U dC_3_1_L dE_4_4_U dB_4_1_L cAE_B cBE_ACD
    cCE_AD cDE_nil x).

Local Definition Hv_BCAD: rew [S0] v_BCAD in
  (DB_4_1_L (dC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
  (DB_3_1_U (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))
    (DC_2_1_U (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer))).
Proof.
  now exact ((sigT_map_eq DB_4_1_L ((sigT_map_eq DC_3_1_L
            ((sigT_map_eq DA_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_BCDA :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_BCDA X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dA_1_0_L dE_2_2_U dC_2_1_U dD_2_1_L dE_3_3_U dB_3_1_U dC_3_1_L dE_4_4_U dB_4_1_L cAE_nil
    cBE_ACD cCE_AD cDE_A x).

Local Definition Hv_BCDA: rew [S0] v_BCDA in
  (DB_4_1_L (dC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
    (DC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
  (DB_3_1_U (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))
    (DC_2_1_U (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer))).
Proof.
  now exact ((sigT_map_eq DB_4_1_L ((sigT_map_eq DC_3_1_L
            ((sigT_map_eq DD_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_BDAC :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_BDAC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dE_1_1_U dA_1_0_U
    dC_1_0_L dD_2_2_U dE_2_2_U dA_2_0_L dE_3_3_U dD_3_2_L dB_3_1_U dE_4_4_U dB_4_1_L cAE_B cBE_ACD
    cCE_nil cDE_AB x).

Local Definition Hv_BDAC: rew [S0] v_BDAC in
  (DB_4_1_L (dD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
    (DD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
  (DB_3_1_U (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))
    (DD_2_2_U (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer))).
Proof.
  now exact ((sigT_map_eq DB_4_1_L ((sigT_map_eq DD_3_2_L
            ((sigT_map_eq DA_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_BDCA :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_BDCA X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dC_1_1_U dE_1_1_U
    dA_1_0_L dD_2_2_U dE_2_2_U dC_2_1_L dE_3_3_U dD_3_2_L dB_3_1_U dE_4_4_U dB_4_1_L cAE_nil
    cBE_ACD cCE_A cDE_AB x).

Local Definition Hv_BDCA: rew [S0] v_BDCA in
  (DB_4_1_L (dD_3_2_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))))
    (DD_3_2_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))) (DC_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
  (DB_3_1_U (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))
    (DD_2_2_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer))).
Proof.
  now exact ((sigT_map_eq DB_4_1_L ((sigT_map_eq DD_3_2_L
            ((sigT_map_eq DC_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_CABD :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_CABD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U dB_1_0_U
    dD_1_0_L dE_2_2_U dA_2_0_U dB_2_0_L dE_3_3_U dC_3_2_U dA_3_0_L dE_4_4_U dC_4_2_L cAE_BC cBE_C
    cCE_ABD cDE_nil x).

Local Definition Hv_CABD: rew [S0] v_CABD in
  (DC_4_2_L (dA_3_0_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DA_3_0_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
  (DC_3_2_U (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))
    (DA_2_0_U (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer))).
Proof.
  now exact ((sigT_map_eq DC_4_2_L ((sigT_map_eq DA_3_0_L
            ((sigT_map_eq DB_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_CADB :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_CADB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dB_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dE_3_3_U dC_3_2_U dA_3_0_L dE_4_4_U dC_4_2_L cAE_BC
    cBE_nil cCE_ABD cDE_A x).

Local Definition Hv_CADB: rew [S0] v_CADB in
  (DC_4_2_L (dA_3_0_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
    (DA_3_0_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
  (DC_3_2_U (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))
    (DA_2_0_U (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer))).
Proof.
  now exact ((sigT_map_eq DC_4_2_L ((sigT_map_eq DA_3_0_L
            ((sigT_map_eq DD_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_CBAD :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_CBAD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U dA_1_0_U
    dD_1_0_L dE_2_2_U dB_2_1_U dA_2_0_L dE_3_3_U dC_3_2_U dB_3_1_L dE_4_4_U dC_4_2_L cAE_B cBE_AC
    cCE_ABD cDE_nil x).

Local Definition Hv_CBAD: rew [S0] v_CBAD in
  (DC_4_2_L (dB_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DB_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
  (DC_3_2_U (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))
    (DB_2_1_U (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer))).
Proof.
  now exact ((sigT_map_eq DC_4_2_L ((sigT_map_eq DB_3_1_L
            ((sigT_map_eq DA_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_CBDA :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_CBDA X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dA_1_0_L dE_2_2_U dB_2_1_U dD_2_1_L dE_3_3_U dC_3_2_U dB_3_1_L dE_4_4_U dC_4_2_L cAE_nil
    cBE_AC cCE_ABD cDE_A x).

Local Definition Hv_CBDA: rew [S0] v_CBDA in
  (DC_4_2_L (dB_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
    (DB_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
  (DC_3_2_U (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))
    (DB_2_1_U (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer))).
Proof.
  now exact ((sigT_map_eq DC_4_2_L ((sigT_map_eq DB_3_1_L
            ((sigT_map_eq DD_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_CDAB :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_CDAB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dE_1_1_U dA_1_0_U
    dB_1_0_L dD_2_2_U dE_2_2_U dA_2_0_L dE_3_3_U dC_3_2_U dD_3_2_L dE_4_4_U dC_4_2_L cAE_B cBE_nil
    cCE_ABD cDE_AB x).

Local Definition Hv_CDAB: rew [S0] v_CDAB in
  (DC_4_2_L (dD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
    (DD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB))) =
  (DC_3_2_U (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))
    (DD_2_2_U (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer))).
Proof.
  now exact ((sigT_map_eq DC_4_2_L ((sigT_map_eq DD_3_2_L
            ((sigT_map_eq DA_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_CDBA :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_CDBA X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dB_1_1_U dE_1_1_U
    dA_1_0_L dD_2_2_U dE_2_2_U dB_2_1_L dE_3_3_U dC_3_2_U dD_3_2_L dE_4_4_U dC_4_2_L cAE_nil cBE_A
    cCE_ABD cDE_AB x).

Local Definition Hv_CDBA: rew [S0] v_CDBA in
  (DC_4_2_L (dD_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))))
    (DD_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))) (DB_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
  (DC_3_2_U (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))
    (DD_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer))).
Proof.
  now exact ((sigT_map_eq DC_4_2_L ((sigT_map_eq DD_3_2_L
            ((sigT_map_eq DB_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_DABC :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_DABC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dE_1_1_U dB_1_0_U
    dC_1_0_L dE_2_2_U dA_2_0_U dB_2_0_L dD_3_3_U dE_3_3_U dA_3_0_L dE_4_4_U dD_4_3_L cAE_BC cBE_C
    cCE_nil cDE_ABC x).

Local Definition Hv_DABC: rew [S0] v_DABC in
  (DD_4_3_L (dA_3_0_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
    (DA_3_0_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
  (DD_3_3_U (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))
    (DA_2_0_U (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer))).
Proof.
  now exact ((sigT_map_eq DD_4_3_L ((sigT_map_eq DA_3_0_L
            ((sigT_map_eq DB_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_DACB :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_DACB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dC_1_1_U dE_1_1_U
    dB_1_0_L dE_2_2_U dC_2_1_L dA_2_0_U dD_3_3_U dE_3_3_U dA_3_0_L dE_4_4_U dD_4_3_L cAE_BC
    cBE_nil cCE_A cDE_ABC x).

Local Definition Hv_DACB: rew [S0] v_DACB in
  (DD_4_3_L (dA_3_0_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))))
    (DA_3_0_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))) (DC_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
  (DD_3_3_U (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))
    (DA_2_0_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer))).
Proof.
  now exact ((sigT_map_eq DD_4_3_L ((sigT_map_eq DA_3_0_L
            ((sigT_map_eq DC_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_DBAC :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_DBAC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dE_1_1_U dA_1_0_U
    dC_1_0_L dE_2_2_U dB_2_1_U dA_2_0_L dD_3_3_U dE_3_3_U dB_3_1_L dE_4_4_U dD_4_3_L cAE_B cBE_AC
    cCE_nil cDE_ABC x).

Local Definition Hv_DBAC: rew [S0] v_DBAC in
  (DD_4_3_L (dB_3_1_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
    (DB_3_1_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
  (DD_3_3_U (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))
    (DB_2_1_U (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer))).
Proof.
  now exact ((sigT_map_eq DD_4_3_L ((sigT_map_eq DB_3_1_L
            ((sigT_map_eq DA_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_DBCA :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_DBCA X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dC_1_1_U dE_1_1_U
    dA_1_0_L dE_2_2_U dB_2_1_U dC_2_1_L dD_3_3_U dE_3_3_U dB_3_1_L dE_4_4_U dD_4_3_L cAE_nil
    cBE_AC cCE_A cDE_ABC x).

Local Definition Hv_DBCA: rew [S0] v_DBCA in
  (DD_4_3_L (dB_3_1_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))))
    (DB_3_1_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))) (DC_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
  (DD_3_3_U (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))
    (DB_2_1_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer))).
Proof.
  now exact ((sigT_map_eq DD_4_3_L ((sigT_map_eq DB_3_1_L
            ((sigT_map_eq DC_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_DCAB :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_DCAB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dE_1_1_U dA_1_0_U
    dB_1_0_L dC_2_2_U dE_2_2_U dA_2_0_L dD_3_3_U dE_3_3_U dC_3_2_L dE_4_4_U dD_4_3_L cAE_B cBE_nil
    cCE_AB cDE_ABC x).

Local Definition Hv_DCAB: rew [S0] v_DCAB in
  (DD_4_3_L (dC_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
    (DC_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB))) =
  (DD_3_3_U (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))
    (DC_2_2_U (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer))).
Proof.
  now exact ((sigT_map_eq DD_4_3_L ((sigT_map_eq DC_3_2_L
            ((sigT_map_eq DA_2_0_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation v_DCBA :=
  (@Bonak.SS2Gpd.Coh4Shapes.v_DCBA X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dB_1_1_U dE_1_1_U
    dA_1_0_L dC_2_2_U dE_2_2_U dB_2_1_L dD_3_3_U dE_3_3_U dC_3_2_L dE_4_4_U dD_4_3_L cAE_nil cBE_A
    cCE_AB cDE_ABC x).

Local Definition Hv_DCBA: rew [S0] v_DCBA in
  (DD_4_3_L (dC_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))))
    (DC_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))) (DB_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
  (DD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))
    (DC_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer))).
Proof.
  now exact ((sigT_map_eq DD_4_3_L ((sigT_map_eq DC_3_2_L
            ((sigT_map_eq DB_2_1_L eq_refl) ⊙ eq_refl)) ⊙ eq_refl)) ⊙ eq_refl).
Defined.

Local Abbreviation n_ABCD_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ABCD_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U
    dC_1_0_U dD_1_0_L dE_2_2_U dA_2_0_U dB_2_0_U dC_2_0_L dE_3_3_U dB_3_1_U dA_3_0_U dA_3_0_L
    dB_3_0_L dE_4_4_U dB_4_1_L dA_4_0_L cAB_CD cAB_CDE cAE_BC cAE_BCD cBE_CD cBE_ACD cCE_D cDE_nil
    hABE_CD x).

Local Definition Hn_ABCD_1: rew [fun e => rew [S0] e in
    (DA_4_0_L (dB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DB_3_1_U (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))
      (DA_2_0_U (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer)))] n_ABCD_1 in
  ((Hv_ABCD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cAB_CD (dC_1_0_U (dD_0_0_U x))))
          (HcAB_CD (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer))))) =
    ((HcAB_CDE (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)) ⊙
      Hv_BACD).
Proof.
  now exact (layer_square_nat_coherence_dep dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U DB_3_0_L
      DA_3_0_L DA_4_0_L DB_4_1_L (fun _ a => a) cAB_CDE HcAB_CDE
      ((f_equal dC_2_0_L (cDE_nil x)) • (cCE_D (dD_0_0_U x))) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
      (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x)))
      (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))) (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x))))
      (hABE_CD (dC_1_0_U (dD_0_0_U x))) ((sigT_map_eq (f := dC_2_0_L) DC_2_0_L (p := (cDE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcAB_CD (dC_1_0_U (dD_0_0_U x))
        (DC_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
      (layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BC (dC_1_0_U
        (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x))))
        (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) _ _ (hABE_CD (dC_1_0_U (dD_0_0_U x))))).
Defined.


Local Abbreviation n_ABCD_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ABCD_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dD_0_0_U dE_0_0_U
    dD_1_1_U dE_1_1_U dC_1_0_U dC_1_0_L dD_1_0_L dE_2_2_U dD_2_1_L dB_2_0_U dC_2_0_L dE_3_3_U
    dA_3_0_U dB_3_0_L dE_4_4_U dA_4_0_L cAE_BCD cBE_CD cCD_nil cCD_E cCE_nil cCE_D cDE_nil cDE_A
    hCDE_nil x).

Local Definition Hn_ABCD_3: rew [fun e => rew [S0] e in
    (DA_4_0_L (dB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DA_3_0_U (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))
      (DB_2_0_U (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer)))] n_ABCD_3 in
  ((Hv_ABCD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dA_3_0_U (f_equal dB_2_0_U (cCD_nil x))))
          (sigT_map_eq (f := dA_3_0_U) DA_3_0_U (p := (f_equal dB_2_0_U (cCD_nil x)))
            (sigT_map_eq (f := dB_2_0_U) DB_2_0_U (p := (cCD_nil x)) HcCD_nil))))) =
    ((sigT_map_eq (f := dA_4_0_L) DA_4_0_L (p := (f_equal dB_3_0_L (cCD_E (dE_0_0_U x))))
        (sigT_map_eq (f := dB_3_0_L) DB_3_0_L (p := (cCD_E (dE_0_0_U x))) HcCD_E)) ⊙ Hv_ABDC).
Proof.
  now exact (square_stack_dep _ (square_map_dep dA_4_0_L DA_4_0_L
        (square_stack_dep _ (square_map_dep dB_3_0_L DB_3_0_L
            ((layer_square _ _ _ DC_2_0_L DD_2_1_L (cDE_nil x) (cCE_nil x) (cCD_nil x) (cCE_D
              (dD_0_0_U x)) (cDE_A (dC_0_0_U x)) (cCD_E (dE_0_0_U x)) HcCD_E (hCDE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dB_2_0_U dB_3_0_L
            dE_3_3_U (fun _ a => a) DB_2_0_U DB_3_0_L (fun _ a => a) cBE_CD (fun _ _ => eq_refl)
            (cCD_nil x) HcCD_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U dA_4_0_L
        dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
        (f_equal dB_2_0_U (cCD_nil x)) (sigT_map_eq (f := dB_2_0_U) DB_2_0_U (p := (cCD_nil x))
          HcCD_nil))).
Defined.

Local Abbreviation n_ABDC_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ABDC_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dC_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dB_2_0_U dE_3_3_U dB_3_1_U dA_3_0_U dA_3_0_L
    dB_3_0_L dE_4_4_U dB_4_1_L dA_4_0_L cAB_CD cAB_CDE cAE_BC cAE_BCD cBE_CD cBE_ACD cCE_nil cDE_A
    hABE_CD x).

Local Definition Hn_ABDC_1: rew [fun e => rew [S0] e in
    (DA_4_0_L (dB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
      (DB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DB_3_1_U (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))
      (DA_2_0_U (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer)))] n_ABDC_1 in
  ((Hv_ABDC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cAB_CD (dD_1_1_U (dC_0_0_U x))))
          (HcAB_CD (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer))))) =
    ((HcAB_CDE (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC)) ⊙
      Hv_BADC).
Proof.
  now exact (layer_square_nat_coherence_dep dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U DB_3_0_L
      DA_3_0_L DA_4_0_L DB_4_1_L (fun _ a => a) cAB_CDE HcAB_CDE
      ((f_equal dD_2_1_L (cCE_nil x)) • (cDE_A (dC_0_0_U x))) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
      (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x)))
      (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))) (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x))))
      (hABE_CD (dD_1_1_U (dC_0_0_U x))) ((sigT_map_eq (f := dD_2_1_L) DD_2_1_L (p := (cCE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcAB_CD (dD_1_1_U (dC_0_0_U x))
        (DD_1_1_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
      (layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BC (dD_1_1_U
        (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x))))
        (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) _ _ (hABE_CD (dD_1_1_U (dC_0_0_U x))))).
Defined.

Local Abbreviation n_ABDC_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ABDC_2 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dB_1_0_U dC_1_0_L dD_2_2_U dE_2_2_U dD_2_1_L dB_2_0_U dB_2_0_L dE_3_3_U dD_3_2_L
    dA_3_0_U dB_3_0_L dE_4_4_U dA_4_0_L cAE_BCD cBD_C cBD_CE cBE_C cBE_CD cCE_nil cDE_A cDE_AB
    hBDE_C x).

Local Definition Hn_ABDC_2: rew [fun e => rew [S0] e in
    (DA_4_0_L (dB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
      (DB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DA_3_0_U (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))
      (DD_2_2_U (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer)))] n_ABDC_2 in
  ((Hv_ABDC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dA_3_0_U (cBD_C (dC_0_0_U x))))
          (sigT_map_eq (f := dA_3_0_U) DA_3_0_U (p := (cBD_C (dC_0_0_U x)))
            (HcBD_C (dC_0_0_U x) aC_layer))))) =
    ((sigT_map_eq (f := dA_4_0_L) DA_4_0_L (p := (cBD_CE (dC_1_0_L (dE_0_0_U x))))
        (HcBD_CE (dC_1_0_L (dE_0_0_U x)) aC)) ⊙ Hv_ADBC).
Proof.
  now exact (square_stack_dep _ (square_map_dep dA_4_0_L DA_4_0_L
        (layer_square_nat_coherence_dep dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L
          DB_2_0_L DB_3_0_L DD_3_2_L (fun _ a => a) cBD_CE HcBD_CE (cCE_nil x)
          (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cBD_C (dC_0_0_U x))
          (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x))) (hBDE_C (dC_0_0_U x))
          eq_refl eq_refl eq_refl (HcBD_C (dC_0_0_U x) aC_layer) eq_refl eq_refl
          (layer_square _ _ _ DB_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cBD_C
            (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x))) _ _ (hBDE_C
            (dC_0_0_U x))))) (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U
        dA_4_0_L dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD
        (fun _ _ => eq_refl) (cBD_C (dC_0_0_U x)) (HcBD_C (dC_0_0_U x) aC_layer))).
Defined.

Local Abbreviation n_ACBD_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ACBD_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U
    dB_1_0_U dD_1_0_L dE_2_2_U dC_2_1_U dA_2_0_U dB_2_0_L dE_3_3_U dC_3_2_U dC_3_1_L dA_3_0_U
    dA_3_0_L dE_4_4_U dC_4_2_L dA_4_0_L cAC_BD cAC_BDE cAE_BC cAE_BCD cBE_C cCE_AD cCE_ABD cDE_nil
    hACE_BD x).

Local Definition Hn_ACBD_1: rew [fun e => rew [S0] e in
    (DA_4_0_L (dC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DC_3_2_U (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))
      (DA_2_0_U (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer)))] n_ACBD_1 in
  ((Hv_ACBD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cAC_BD (dB_1_0_U (dD_0_0_U x))))
          (HcAC_BD (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer))))) =
    ((HcAC_BDE (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)) ⊙
      Hv_CABD).
Proof.
  now exact (layer_square_nat_coherence_dep dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U DC_3_1_L
      DA_3_0_L DA_4_0_L DC_4_2_L (fun _ a => a) cAC_BDE HcAC_BDE
      ((f_equal dB_2_0_L (cDE_nil x)) • (cBE_C (dD_0_0_U x))) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
      (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
      (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))) (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x))))
      (hACE_BD (dB_1_0_U (dD_0_0_U x))) ((sigT_map_eq (f := dB_2_0_L) DB_2_0_L (p := (cDE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcAC_BD (dB_1_0_U (dD_0_0_U x))
        (DB_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
      (layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD (dB_1_0_U (dD_0_0_U x))) (cAE_BC (dB_1_0_U
        (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x))) (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
        (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) _ _ (hACE_BD (dB_1_0_U (dD_0_0_U x))))).
Defined.

Local Abbreviation n_ACBD_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ACBD_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dD_0_0_U dE_0_0_U
    dD_1_1_U dE_1_1_U dB_1_0_U dB_1_0_L dD_1_0_L dE_2_2_U dC_2_1_U dD_2_1_L dB_2_0_L dE_3_3_U
    dC_3_1_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD cBD_nil cBD_E cBE_nil cBE_C cCE_AD cDE_nil cDE_A
    hBDE_nil x).

Local Definition Hn_ACBD_3: rew [fun e => rew [S0] e in
    (DA_4_0_L (dC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DA_3_0_U (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))
      (DC_2_1_U (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer)))] n_ACBD_3 in
  ((Hv_ACBD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dA_3_0_U (f_equal dC_2_1_U (cBD_nil x))))
          (sigT_map_eq (f := dA_3_0_U) DA_3_0_U (p := (f_equal dC_2_1_U (cBD_nil x)))
            (sigT_map_eq (f := dC_2_1_U) DC_2_1_U (p := (cBD_nil x)) HcBD_nil))))) =
    ((sigT_map_eq (f := dA_4_0_L) DA_4_0_L (p := (f_equal dC_3_1_L (cBD_E (dE_0_0_U x))))
        (sigT_map_eq (f := dC_3_1_L) DC_3_1_L (p := (cBD_E (dE_0_0_U x))) HcBD_E)) ⊙ Hv_ACDB).
Proof.
  now exact (square_stack_dep _ (square_map_dep dA_4_0_L DA_4_0_L
        (square_stack_dep _ (square_map_dep dC_3_1_L DC_3_1_L
            ((layer_square _ _ _ DB_2_0_L DD_2_1_L (cDE_nil x) (cBE_nil x) (cBD_nil x) (cBE_C
              (dD_0_0_U x)) (cDE_A (dB_0_0_U x)) (cBD_E (dE_0_0_U x)) HcBD_E (hBDE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dC_2_1_U dC_3_1_L
            dE_3_3_U (fun _ a => a) DC_2_1_U DC_3_1_L (fun _ a => a) cCE_AD (fun _ _ => eq_refl)
            (cBD_nil x) HcBD_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U dA_4_0_L
        dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
        (f_equal dC_2_1_U (cBD_nil x)) (sigT_map_eq (f := dC_2_1_U) DC_2_1_U (p := (cBD_nil x))
          HcBD_nil))).
Defined.

Local Abbreviation n_ACDB_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ACDB_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dB_1_0_L dE_2_2_U dC_2_1_U dD_2_1_L dA_2_0_U dE_3_3_U dC_3_2_U dC_3_1_L dA_3_0_U
    dA_3_0_L dE_4_4_U dC_4_2_L dA_4_0_L cAC_BD cAC_BDE cAE_BC cAE_BCD cBE_nil cCE_AD cCE_ABD cDE_A
    hACE_BD x).

Local Definition Hn_ACDB_1: rew [fun e => rew [S0] e in
    (DA_4_0_L (dC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DC_3_2_U (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))
      (DA_2_0_U (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer)))] n_ACDB_1 in
  ((Hv_ACDB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cAC_BD (dD_1_1_U (dB_0_0_U x))))
          (HcAC_BD (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer))))) =
    ((HcAC_BDE (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB)) ⊙
      Hv_CADB).
Proof.
  now exact (layer_square_nat_coherence_dep dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U DC_3_1_L
      DA_3_0_L DA_4_0_L DC_4_2_L (fun _ a => a) cAC_BDE HcAC_BDE
      ((f_equal dD_2_1_L (cBE_nil x)) • (cDE_A (dB_0_0_U x))) (cCE_AD (dD_1_1_U (dB_0_0_U x)))
      (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x)))
      (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))) (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x))))
      (hACE_BD (dD_1_1_U (dB_0_0_U x))) ((sigT_map_eq (f := dD_2_1_L) DD_2_1_L (p := (cBE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcAC_BD (dD_1_1_U (dB_0_0_U x))
        (DD_1_1_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
      (layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cAE_BC (dD_1_1_U
        (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x))) (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x))))
        (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) _ _ (hACE_BD (dD_1_1_U (dB_0_0_U x))))).
Defined.

Local Abbreviation n_ACDB_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ACDB_2 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dC_1_1_U
    dD_1_1_U dE_1_1_U dB_1_0_L dD_2_2_U dE_2_2_U dC_2_1_U dC_2_1_L dD_2_1_L dE_3_3_U dD_3_2_L
    dC_3_1_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD cBE_nil cCD_B cCD_BE cCE_A cCE_AD cDE_A cDE_AB
    hCDE_B x).

Local Definition Hn_ACDB_2: rew [fun e => rew [S0] e in
    (DA_4_0_L (dC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DA_3_0_U (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))
      (DD_2_2_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer)))] n_ACDB_2 in
  ((Hv_ACDB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dA_3_0_U (cCD_B (dB_0_0_U x))))
          (sigT_map_eq (f := dA_3_0_U) DA_3_0_U (p := (cCD_B (dB_0_0_U x)))
            (HcCD_B (dB_0_0_U x) aB_layer))))) =
    ((sigT_map_eq (f := dA_4_0_L) DA_4_0_L (p := (cCD_BE (dB_1_0_L (dE_0_0_U x))))
        (HcCD_BE (dB_1_0_L (dE_0_0_U x)) aB)) ⊙ Hv_ADCB).
Proof.
  now exact (square_stack_dep _ (square_map_dep dA_4_0_L DA_4_0_L
        (layer_square_nat_coherence_dep dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L
          DC_2_1_L DC_3_1_L DD_3_2_L (fun _ a => a) cCD_BE HcCD_BE (cBE_nil x)
          (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x)) (cCD_B (dB_0_0_U x))
          (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x))) (hCDE_B (dB_0_0_U x))
          eq_refl eq_refl eq_refl (HcCD_B (dB_0_0_U x) aB_layer) eq_refl eq_refl
          (layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x)) (cCD_B
            (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x))) _ _ (hCDE_B
            (dB_0_0_U x))))) (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U
        dA_4_0_L dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD
        (fun _ _ => eq_refl) (cCD_B (dB_0_0_U x)) (HcCD_B (dB_0_0_U x) aB_layer))).
Defined.

Local Abbreviation n_ADBC_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ADBC_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dE_1_1_U
    dB_1_0_U dC_1_0_L dD_2_2_U dE_2_2_U dA_2_0_U dB_2_0_L dD_3_3_U dE_3_3_U dD_3_2_L dA_3_0_U
    dA_3_0_L dE_4_4_U dD_4_3_L dA_4_0_L cAD_BC cAD_BCE cAE_BC cAE_BCD cBE_C cCE_nil cDE_AB cDE_ABC
    hADE_BC x).

Local Definition Hn_ADBC_1: rew [fun e => rew [S0] e in
    (DA_4_0_L (dD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DD_3_3_U (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))
      (DA_2_0_U (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer)))] n_ADBC_1 in
  ((Hv_ADBC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cAD_BC (dB_1_0_U (dC_0_0_U x))))
          (HcAD_BC (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer))))) =
    ((HcAD_BCE (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC)) ⊙
      Hv_DABC).
Proof.
  now exact (layer_square_nat_coherence_dep dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U DD_3_2_L
      DA_3_0_L DA_4_0_L DD_4_3_L (fun _ a => a) cAD_BCE HcAD_BCE
      ((f_equal dB_2_0_L (cCE_nil x)) • (cBE_C (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
      (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
      (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))) (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x))))
      (hADE_BC (dB_1_0_U (dC_0_0_U x))) ((sigT_map_eq (f := dB_2_0_L) DB_2_0_L (p := (cCE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcAD_BC (dB_1_0_U (dC_0_0_U x))
        (DB_1_0_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
      (layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB (dB_1_0_U (dC_0_0_U x))) (cAE_BC (dB_1_0_U
        (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x))) (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
        (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) _ _ (hADE_BC (dB_1_0_U (dC_0_0_U x))))).
Defined.

Local Abbreviation n_ADBC_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ADBC_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dC_0_0_U dE_0_0_U
    dC_1_1_U dE_1_1_U dB_1_0_U dB_1_0_L dC_1_0_L dD_2_2_U dE_2_2_U dC_2_1_L dB_2_0_L dE_3_3_U
    dD_3_2_L dA_3_0_U dE_4_4_U dA_4_0_L cAE_BCD cBC_nil cBC_E cBE_nil cBE_C cCE_nil cCE_A cDE_AB
    hBCE_nil x).

Local Definition Hn_ADBC_3: rew [fun e => rew [S0] e in
    (DA_4_0_L (dD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DA_3_0_U (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))
      (DD_2_2_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer)))] n_ADBC_3 in
  ((Hv_ADBC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dA_3_0_U (f_equal dD_2_2_U (cBC_nil x))))
          (sigT_map_eq (f := dA_3_0_U) DA_3_0_U (p := (f_equal dD_2_2_U (cBC_nil x)))
            (sigT_map_eq (f := dD_2_2_U) DD_2_2_U (p := (cBC_nil x)) HcBC_nil))))) =
    ((sigT_map_eq (f := dA_4_0_L) DA_4_0_L (p := (f_equal dD_3_2_L (cBC_E (dE_0_0_U x))))
        (sigT_map_eq (f := dD_3_2_L) DD_3_2_L (p := (cBC_E (dE_0_0_U x))) HcBC_E)) ⊙ Hv_ADCB).
Proof.
  now exact (square_stack_dep _ (square_map_dep dA_4_0_L DA_4_0_L
        (square_stack_dep _ (square_map_dep dD_3_2_L DD_3_2_L
            ((layer_square _ _ _ DB_2_0_L DC_2_1_L (cCE_nil x) (cBE_nil x) (cBC_nil x) (cBE_C
              (dC_0_0_U x)) (cCE_A (dB_0_0_U x)) (cBC_E (dE_0_0_U x)) HcBC_E (hBCE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dD_2_2_U dD_3_2_L
            dE_3_3_U (fun _ a => a) DD_2_2_U DD_3_2_L (fun _ a => a) cDE_AB (fun _ _ => eq_refl)
            (cBC_nil x) HcBC_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U dA_4_0_L
        dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
        (f_equal dD_2_2_U (cBC_nil x)) (sigT_map_eq (f := dD_2_2_U) DD_2_2_U (p := (cBC_nil x))
          HcBC_nil))).
Defined.

Local Abbreviation n_ADCB_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ADCB_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dC_1_1_U
    dE_1_1_U dB_1_0_L dD_2_2_U dE_2_2_U dC_2_1_L dA_2_0_U dD_3_3_U dE_3_3_U dD_3_2_L dA_3_0_U
    dA_3_0_L dE_4_4_U dD_4_3_L dA_4_0_L cAD_BC cAD_BCE cAE_BC cAE_BCD cBE_nil cCE_A cDE_AB cDE_ABC
    hADE_BC x).

Local Definition Hn_ADCB_1: rew [fun e => rew [S0] e in
    (DA_4_0_L (dD_3_2_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))) (DC_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DD_3_3_U (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))
      (DA_2_0_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer)))] n_ADCB_1 in
  ((Hv_ADCB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cAD_BC (dC_1_1_U (dB_0_0_U x))))
          (HcAD_BC (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer))))) =
    ((HcAD_BCE (dC_2_1_L (dB_1_0_L (dE_0_0_U x))) (DC_2_1_L (dB_1_0_L (dE_0_0_U x)) aB)) ⊙
      Hv_DACB).
Proof.
  now exact (layer_square_nat_coherence_dep dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U DD_3_2_L
      DA_3_0_L DA_4_0_L DD_4_3_L (fun _ a => a) cAD_BCE HcAD_BCE
      ((f_equal dC_2_1_L (cBE_nil x)) • (cCE_A (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
      (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
      (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))) (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x))))
      (hADE_BC (dC_1_1_U (dB_0_0_U x))) ((sigT_map_eq (f := dC_2_1_L) DC_2_1_L (p := (cBE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcAD_BC (dC_1_1_U (dB_0_0_U x))
        (DC_1_1_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
      (layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB (dC_1_1_U (dB_0_0_U x))) (cAE_BC (dC_1_1_U
        (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x))) (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
        (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) _ _ (hADE_BC (dC_1_1_U (dB_0_0_U x))))).
Defined.


Local Abbreviation n_BACD_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BACD_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dD_0_0_U dE_0_0_U
    dD_1_1_U dE_1_1_U dC_1_0_U dC_1_0_L dD_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dC_2_0_L dE_3_3_U
    dB_3_1_U dA_3_0_L dE_4_4_U dB_4_1_L cAE_BC cBE_ACD cCD_nil cCD_E cCE_nil cCE_D cDE_nil cDE_A
    hCDE_nil x).

Local Definition Hn_BACD_3: rew [fun e => rew [S0] e in
    (DB_4_1_L (dA_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DA_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DB_3_1_U (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))
      (DA_2_0_U (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer)))] n_BACD_3 in
  ((Hv_BACD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dB_3_1_U (f_equal dA_2_0_U (cCD_nil x))))
          (sigT_map_eq (f := dB_3_1_U) DB_3_1_U (p := (f_equal dA_2_0_U (cCD_nil x)))
            (sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cCD_nil x)) HcCD_nil))))) =
    ((sigT_map_eq (f := dB_4_1_L) DB_4_1_L (p := (f_equal dA_3_0_L (cCD_E (dE_0_0_U x))))
        (sigT_map_eq (f := dA_3_0_L) DA_3_0_L (p := (cCD_E (dE_0_0_U x))) HcCD_E)) ⊙ Hv_BADC).
Proof.
  now exact (square_stack_dep _ (square_map_dep dB_4_1_L DB_4_1_L
        (square_stack_dep _ (square_map_dep dA_3_0_L DA_3_0_L
            ((layer_square _ _ _ DC_2_0_L DD_2_1_L (cDE_nil x) (cCE_nil x) (cCD_nil x) (cCE_D
              (dD_0_0_U x)) (cDE_A (dC_0_0_U x)) (cCD_E (dE_0_0_U x)) HcCD_E (hCDE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dA_2_0_U dA_3_0_L
            dE_3_3_U (fun _ a => a) DA_2_0_U DA_3_0_L (fun _ a => a) cAE_BC (fun _ _ => eq_refl)
            (cCD_nil x) HcCD_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U dB_4_1_L
        dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl)
        (f_equal dA_2_0_U (cCD_nil x)) (sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cCD_nil x))
          HcCD_nil))).
Defined.

Local Abbreviation n_BADC_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BADC_2 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dA_1_0_U dC_1_0_L dD_2_2_U dE_2_2_U dD_2_1_L dA_2_0_U dA_2_0_L dE_3_3_U dD_3_2_L
    dB_3_1_U dA_3_0_L dE_4_4_U dB_4_1_L cAD_C cAD_CE cAE_B cAE_BC cBE_ACD cCE_nil cDE_A cDE_AB
    hADE_C x).

Local Definition Hn_BADC_2: rew [fun e => rew [S0] e in
    (DB_4_1_L (dA_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
      (DA_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DB_3_1_U (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))
      (DD_2_2_U (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer)))] n_BADC_2 in
  ((Hv_BADC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dB_3_1_U (cAD_C (dC_0_0_U x))))
          (sigT_map_eq (f := dB_3_1_U) DB_3_1_U (p := (cAD_C (dC_0_0_U x)))
            (HcAD_C (dC_0_0_U x) aC_layer))))) =
    ((sigT_map_eq (f := dB_4_1_L) DB_4_1_L (p := (cAD_CE (dC_1_0_L (dE_0_0_U x))))
        (HcAD_CE (dC_1_0_L (dE_0_0_U x)) aC)) ⊙ Hv_BDAC).
Proof.
  now exact (square_stack_dep _ (square_map_dep dB_4_1_L DB_4_1_L
        (layer_square_nat_coherence_dep dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L
          DA_2_0_L DA_3_0_L DD_3_2_L (fun _ a => a) cAD_CE HcAD_CE (cCE_nil x)
          (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cAD_C (dC_0_0_U x))
          (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x))) (hADE_C (dC_0_0_U x))
          eq_refl eq_refl eq_refl (HcAD_C (dC_0_0_U x) aC_layer) eq_refl eq_refl
          (layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cAD_C
            (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x))) _ _ (hADE_C
            (dC_0_0_U x))))) (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U
        dB_4_1_L dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD
        (fun _ _ => eq_refl) (cAD_C (dC_0_0_U x)) (HcAD_C (dC_0_0_U x) aC_layer))).
Defined.

Local Abbreviation n_BCAD_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BCAD_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dD_0_0_U dE_0_0_U dE_1_1_U
    dA_1_0_U dD_1_0_L dE_2_2_U dB_2_1_U dC_2_1_U dA_2_0_L dE_3_3_U dC_3_2_U dB_3_1_U dB_3_1_L
    dC_3_1_L dE_4_4_U dC_4_2_L dB_4_1_L cAE_B cBC_AD cBC_ADE cBE_AC cBE_ACD cCE_AD cCE_ABD cDE_nil
    hBCE_AD x).

Local Definition Hn_BCAD_1: rew [fun e => rew [S0] e in
    (DB_4_1_L (dC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DC_3_2_U (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))
      (DB_2_1_U (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer)))] n_BCAD_1 in
  ((Hv_BCAD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cBC_AD (dA_1_0_U (dD_0_0_U x))))
          (HcBC_AD (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer))))) =
    ((HcBC_ADE (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)) ⊙
      Hv_CBAD).
Proof.
  now exact (layer_square_nat_coherence_dep dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U DC_3_1_L
      DB_3_1_L DB_4_1_L DC_4_2_L (fun _ a => a) cBC_ADE HcBC_ADE
      ((f_equal dA_2_0_L (cDE_nil x)) • (cAE_B (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
      (cBE_AC (dA_1_0_U (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x)))
      (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))) (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x))))
      (hBCE_AD (dA_1_0_U (dD_0_0_U x))) ((sigT_map_eq (f := dA_2_0_L) DA_2_0_L (p := (cDE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcBC_AD (dA_1_0_U (dD_0_0_U x))
        (DA_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
      (layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U
        (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x))) (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
        (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) _ _ (hBCE_AD (dA_1_0_U (dD_0_0_U x))))).
Defined.

Local Abbreviation n_BCAD_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BCAD_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dD_0_0_U dE_0_0_U
    dD_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dD_1_0_L dE_2_2_U dC_2_1_U dD_2_1_L dA_2_0_L dE_3_3_U
    dB_3_1_U dC_3_1_L dE_4_4_U dB_4_1_L cAD_nil cAD_E cAE_nil cAE_B cBE_ACD cCE_AD cDE_nil cDE_A
    hADE_nil x).

Local Definition Hn_BCAD_3: rew [fun e => rew [S0] e in
    (DB_4_1_L (dC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DB_3_1_U (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))
      (DC_2_1_U (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer)))] n_BCAD_3 in
  ((Hv_BCAD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dB_3_1_U (f_equal dC_2_1_U (cAD_nil x))))
          (sigT_map_eq (f := dB_3_1_U) DB_3_1_U (p := (f_equal dC_2_1_U (cAD_nil x)))
            (sigT_map_eq (f := dC_2_1_U) DC_2_1_U (p := (cAD_nil x)) HcAD_nil))))) =
    ((sigT_map_eq (f := dB_4_1_L) DB_4_1_L (p := (f_equal dC_3_1_L (cAD_E (dE_0_0_U x))))
        (sigT_map_eq (f := dC_3_1_L) DC_3_1_L (p := (cAD_E (dE_0_0_U x))) HcAD_E)) ⊙ Hv_BCDA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dB_4_1_L DB_4_1_L
        (square_stack_dep _ (square_map_dep dC_3_1_L DC_3_1_L
            ((layer_square _ _ _ DA_2_0_L DD_2_1_L (cDE_nil x) (cAE_nil x) (cAD_nil x) (cAE_B
              (dD_0_0_U x)) (cDE_A (dA_0_0_U x)) (cAD_E (dE_0_0_U x)) HcAD_E (hADE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dC_2_1_U dC_3_1_L
            dE_3_3_U (fun _ a => a) DC_2_1_U DC_3_1_L (fun _ a => a) cCE_AD (fun _ _ => eq_refl)
            (cAD_nil x) HcAD_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U dB_4_1_L
        dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl)
        (f_equal dC_2_1_U (cAD_nil x)) (sigT_map_eq (f := dC_2_1_U) DC_2_1_U (p := (cAD_nil x))
          HcAD_nil))).
Defined.

Local Abbreviation n_BCDA_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BCDA_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dA_1_0_L dE_2_2_U dB_2_1_U dC_2_1_U dD_2_1_L dE_3_3_U dC_3_2_U dB_3_1_U dB_3_1_L
    dC_3_1_L dE_4_4_U dC_4_2_L dB_4_1_L cAE_nil cBC_AD cBC_ADE cBE_AC cBE_ACD cCE_AD cCE_ABD cDE_A
    hBCE_AD x).

Local Definition Hn_BCDA_1: rew [fun e => rew [S0] e in
    (DB_4_1_L (dC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
    (DC_3_2_U (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))
      (DB_2_1_U (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer)))] n_BCDA_1 in
  ((Hv_BCDA ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cBC_AD (dD_1_1_U (dA_0_0_U x))))
          (HcBC_AD (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer))))) =
    ((HcBC_ADE (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA)) ⊙
      Hv_CBDA).
Proof.
  now exact (layer_square_nat_coherence_dep dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U DC_3_1_L
      DB_3_1_L DB_4_1_L DC_4_2_L (fun _ a => a) cBC_ADE HcBC_ADE
      ((f_equal dD_2_1_L (cAE_nil x)) • (cDE_A (dA_0_0_U x))) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
      (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x)))
      (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))) (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x))))
      (hBCE_AD (dD_1_1_U (dA_0_0_U x))) ((sigT_map_eq (f := dD_2_1_L) DD_2_1_L (p := (cAE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcBC_AD (dD_1_1_U (dA_0_0_U x))
        (DD_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
      (layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cBE_AC (dD_1_1_U
        (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x))) (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x))))
        (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) _ _ (hBCE_AD (dD_1_1_U (dA_0_0_U x))))).
Defined.

Local Abbreviation n_BCDA_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BCDA_2 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dC_1_1_U
    dD_1_1_U dE_1_1_U dA_1_0_L dD_2_2_U dE_2_2_U dC_2_1_U dC_2_1_L dD_2_1_L dE_3_3_U dD_3_2_L
    dB_3_1_U dC_3_1_L dE_4_4_U dB_4_1_L cAE_nil cBE_ACD cCD_A cCD_AE cCE_A cCE_AD cDE_A cDE_AB
    hCDE_A x).

Local Definition Hn_BCDA_2: rew [fun e => rew [S0] e in
    (DB_4_1_L (dC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
      (DC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
    (DB_3_1_U (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))
      (DD_2_2_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer)))] n_BCDA_2 in
  ((Hv_BCDA ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dB_3_1_U (cCD_A (dA_0_0_U x))))
          (sigT_map_eq (f := dB_3_1_U) DB_3_1_U (p := (cCD_A (dA_0_0_U x)))
            (HcCD_A (dA_0_0_U x) aA_layer))))) =
    ((sigT_map_eq (f := dB_4_1_L) DB_4_1_L (p := (cCD_AE (dA_1_0_L (dE_0_0_U x))))
        (HcCD_AE (dA_1_0_L (dE_0_0_U x)) aA)) ⊙ Hv_BDCA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dB_4_1_L DB_4_1_L
        (layer_square_nat_coherence_dep dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L
          DC_2_1_L DC_3_1_L DD_3_2_L (fun _ a => a) cCD_AE HcCD_AE (cAE_nil x)
          (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cCD_A (dA_0_0_U x))
          (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x))) (hCDE_A (dA_0_0_U x))
          eq_refl eq_refl eq_refl (HcCD_A (dA_0_0_U x) aA_layer) eq_refl eq_refl
          (layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cCD_A
            (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x))) _ _ (hCDE_A
            (dA_0_0_U x))))) (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U
        dB_4_1_L dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD
        (fun _ _ => eq_refl) (cCD_A (dA_0_0_U x)) (HcCD_A (dA_0_0_U x) aA_layer))).
Defined.

Local Abbreviation n_BDAC_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BDAC_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dE_1_1_U
    dA_1_0_U dC_1_0_L dD_2_2_U dE_2_2_U dB_2_1_U dA_2_0_L dD_3_3_U dE_3_3_U dD_3_2_L dB_3_1_U
    dB_3_1_L dE_4_4_U dD_4_3_L dB_4_1_L cAE_B cBD_AC cBD_ACE cBE_AC cBE_ACD cCE_nil cDE_AB cDE_ABC
    hBDE_AC x).

Local Definition Hn_BDAC_1: rew [fun e => rew [S0] e in
    (DB_4_1_L (dD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DD_3_3_U (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))
      (DB_2_1_U (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer)))] n_BDAC_1 in
  ((Hv_BDAC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cBD_AC (dA_1_0_U (dC_0_0_U x))))
          (HcBD_AC (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer))))) =
    ((HcBD_ACE (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC)) ⊙
      Hv_DBAC).
Proof.
  now exact (layer_square_nat_coherence_dep dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U DD_3_2_L
      DB_3_1_L DB_4_1_L DD_4_3_L (fun _ a => a) cBD_ACE HcBD_ACE
      ((f_equal dA_2_0_L (cCE_nil x)) • (cAE_B (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x)))
      (cBE_AC (dA_1_0_U (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x)))
      (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))) (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x))))
      (hBDE_AC (dA_1_0_U (dC_0_0_U x))) ((sigT_map_eq (f := dA_2_0_L) DA_2_0_L (p := (cCE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcBD_AC (dA_1_0_U (dC_0_0_U x))
        (DA_1_0_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
      (layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U
        (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x))) (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
        (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) _ _ (hBDE_AC (dA_1_0_U (dC_0_0_U x))))).
Defined.

Local Abbreviation n_BDAC_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BDAC_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dC_0_0_U dE_0_0_U
    dC_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dC_1_0_L dD_2_2_U dE_2_2_U dC_2_1_L dA_2_0_L dE_3_3_U
    dD_3_2_L dB_3_1_U dE_4_4_U dB_4_1_L cAC_nil cAC_E cAE_nil cAE_B cBE_ACD cCE_nil cCE_A cDE_AB
    hACE_nil x).

Local Definition Hn_BDAC_3: rew [fun e => rew [S0] e in
    (DB_4_1_L (dD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DB_3_1_U (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))
      (DD_2_2_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer)))] n_BDAC_3 in
  ((Hv_BDAC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dB_3_1_U (f_equal dD_2_2_U (cAC_nil x))))
          (sigT_map_eq (f := dB_3_1_U) DB_3_1_U (p := (f_equal dD_2_2_U (cAC_nil x)))
            (sigT_map_eq (f := dD_2_2_U) DD_2_2_U (p := (cAC_nil x)) HcAC_nil))))) =
    ((sigT_map_eq (f := dB_4_1_L) DB_4_1_L (p := (f_equal dD_3_2_L (cAC_E (dE_0_0_U x))))
        (sigT_map_eq (f := dD_3_2_L) DD_3_2_L (p := (cAC_E (dE_0_0_U x))) HcAC_E)) ⊙ Hv_BDCA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dB_4_1_L DB_4_1_L
        (square_stack_dep _ (square_map_dep dD_3_2_L DD_3_2_L
            ((layer_square _ _ _ DA_2_0_L DC_2_1_L (cCE_nil x) (cAE_nil x) (cAC_nil x) (cAE_B
              (dC_0_0_U x)) (cCE_A (dA_0_0_U x)) (cAC_E (dE_0_0_U x)) HcAC_E (hACE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dD_2_2_U dD_3_2_L
            dE_3_3_U (fun _ a => a) DD_2_2_U DD_3_2_L (fun _ a => a) cDE_AB (fun _ _ => eq_refl)
            (cAC_nil x) HcAC_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U dB_4_1_L
        dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl)
        (f_equal dD_2_2_U (cAC_nil x)) (sigT_map_eq (f := dD_2_2_U) DD_2_2_U (p := (cAC_nil x))
          HcAC_nil))).
Defined.

Local Abbreviation n_BDCA_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BDCA_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dC_1_1_U
    dE_1_1_U dA_1_0_L dD_2_2_U dE_2_2_U dB_2_1_U dC_2_1_L dD_3_3_U dE_3_3_U dD_3_2_L dB_3_1_U
    dB_3_1_L dE_4_4_U dD_4_3_L dB_4_1_L cAE_nil cBD_AC cBD_ACE cBE_AC cBE_ACD cCE_A cDE_AB cDE_ABC
    hBDE_AC x).

Local Definition Hn_BDCA_1: rew [fun e => rew [S0] e in
    (DB_4_1_L (dD_3_2_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))) (DC_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
    (DD_3_3_U (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))
      (DB_2_1_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer)))] n_BDCA_1 in
  ((Hv_BDCA ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cBD_AC (dC_1_1_U (dA_0_0_U x))))
          (HcBD_AC (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer))))) =
    ((HcBD_ACE (dC_2_1_L (dA_1_0_L (dE_0_0_U x))) (DC_2_1_L (dA_1_0_L (dE_0_0_U x)) aA)) ⊙
      Hv_DBCA).
Proof.
  now exact (layer_square_nat_coherence_dep dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U DD_3_2_L
      DB_3_1_L DB_4_1_L DD_4_3_L (fun _ a => a) cBD_ACE HcBD_ACE
      ((f_equal dC_2_1_L (cAE_nil x)) • (cCE_A (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
      (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
      (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))) (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x))))
      (hBDE_AC (dC_1_1_U (dA_0_0_U x))) ((sigT_map_eq (f := dC_2_1_L) DC_2_1_L (p := (cAE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcBD_AC (dC_1_1_U (dA_0_0_U x))
        (DC_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
      (layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB (dC_1_1_U (dA_0_0_U x))) (cBE_AC (dC_1_1_U
        (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x))) (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
        (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) _ _ (hBDE_AC (dC_1_1_U (dA_0_0_U x))))).
Defined.


Local Abbreviation n_CABD_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CABD_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dD_0_0_U dE_0_0_U
    dD_1_1_U dE_1_1_U dB_1_0_U dB_1_0_L dD_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dB_2_0_L dE_3_3_U
    dC_3_2_U dA_3_0_L dE_4_4_U dC_4_2_L cAE_BC cBD_nil cBD_E cBE_nil cBE_C cCE_ABD cDE_nil cDE_A
    hBDE_nil x).

Local Definition Hn_CABD_3: rew [fun e => rew [S0] e in
    (DC_4_2_L (dA_3_0_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DA_3_0_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DC_3_2_U (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))
      (DA_2_0_U (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer)))] n_CABD_3 in
  ((Hv_CABD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dC_3_2_U (f_equal dA_2_0_U (cBD_nil x))))
          (sigT_map_eq (f := dC_3_2_U) DC_3_2_U (p := (f_equal dA_2_0_U (cBD_nil x)))
            (sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cBD_nil x)) HcBD_nil))))) =
    ((sigT_map_eq (f := dC_4_2_L) DC_4_2_L (p := (f_equal dA_3_0_L (cBD_E (dE_0_0_U x))))
        (sigT_map_eq (f := dA_3_0_L) DA_3_0_L (p := (cBD_E (dE_0_0_U x))) HcBD_E)) ⊙ Hv_CADB).
Proof.
  now exact (square_stack_dep _ (square_map_dep dC_4_2_L DC_4_2_L
        (square_stack_dep _ (square_map_dep dA_3_0_L DA_3_0_L
            ((layer_square _ _ _ DB_2_0_L DD_2_1_L (cDE_nil x) (cBE_nil x) (cBD_nil x) (cBE_C
              (dD_0_0_U x)) (cDE_A (dB_0_0_U x)) (cBD_E (dE_0_0_U x)) HcBD_E (hBDE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dA_2_0_U dA_3_0_L
            dE_3_3_U (fun _ a => a) DA_2_0_U DA_3_0_L (fun _ a => a) cAE_BC (fun _ _ => eq_refl)
            (cBD_nil x) HcBD_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U dC_4_2_L
        dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl)
        (f_equal dA_2_0_U (cBD_nil x)) (sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cBD_nil x))
          HcBD_nil))).
Defined.

Local Abbreviation n_CADB_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CADB_2 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dA_1_0_U dB_1_0_L dD_2_2_U dE_2_2_U dD_2_1_L dA_2_0_U dA_2_0_L dE_3_3_U dC_3_2_U
    dD_3_2_L dA_3_0_L dE_4_4_U dC_4_2_L cAD_B cAD_BE cAE_B cAE_BC cBE_nil cCE_ABD cDE_A cDE_AB
    hADE_B x).

Local Definition Hn_CADB_2: rew [fun e => rew [S0] e in
    (DC_4_2_L (dA_3_0_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
      (DA_3_0_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DC_3_2_U (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))
      (DD_2_2_U (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer)))] n_CADB_2 in
  ((Hv_CADB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dC_3_2_U (cAD_B (dB_0_0_U x))))
          (sigT_map_eq (f := dC_3_2_U) DC_3_2_U (p := (cAD_B (dB_0_0_U x)))
            (HcAD_B (dB_0_0_U x) aB_layer))))) =
    ((sigT_map_eq (f := dC_4_2_L) DC_4_2_L (p := (cAD_BE (dB_1_0_L (dE_0_0_U x))))
        (HcAD_BE (dB_1_0_L (dE_0_0_U x)) aB)) ⊙ Hv_CDAB).
Proof.
  now exact (square_stack_dep _ (square_map_dep dC_4_2_L DC_4_2_L
        (layer_square_nat_coherence_dep dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L
          DA_2_0_L DA_3_0_L DD_3_2_L (fun _ a => a) cAD_BE HcAD_BE (cBE_nil x)
          (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x))
          (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x))) (hADE_B (dB_0_0_U x))
          eq_refl eq_refl eq_refl (HcAD_B (dB_0_0_U x) aB_layer) eq_refl eq_refl
          (layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B
            (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x))) _ _ (hADE_B
            (dB_0_0_U x))))) (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U
        dC_4_2_L dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD
        (fun _ _ => eq_refl) (cAD_B (dB_0_0_U x)) (HcAD_B (dB_0_0_U x) aB_layer))).
Defined.

Local Abbreviation n_CBAD_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CBAD_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dD_0_0_U dE_0_0_U
    dD_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dD_1_0_L dE_2_2_U dB_2_1_U dD_2_1_L dA_2_0_L dE_3_3_U
    dC_3_2_U dB_3_1_L dE_4_4_U dC_4_2_L cAD_nil cAD_E cAE_nil cAE_B cBE_AC cCE_ABD cDE_nil cDE_A
    hADE_nil x).

Local Definition Hn_CBAD_3: rew [fun e => rew [S0] e in
    (DC_4_2_L (dB_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
      (DB_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD))) =
    (DC_3_2_U (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))
      (DB_2_1_U (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer)))] n_CBAD_3 in
  ((Hv_CBAD ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dC_3_2_U (f_equal dB_2_1_U (cAD_nil x))))
          (sigT_map_eq (f := dC_3_2_U) DC_3_2_U (p := (f_equal dB_2_1_U (cAD_nil x)))
            (sigT_map_eq (f := dB_2_1_U) DB_2_1_U (p := (cAD_nil x)) HcAD_nil))))) =
    ((sigT_map_eq (f := dC_4_2_L) DC_4_2_L (p := (f_equal dB_3_1_L (cAD_E (dE_0_0_U x))))
        (sigT_map_eq (f := dB_3_1_L) DB_3_1_L (p := (cAD_E (dE_0_0_U x))) HcAD_E)) ⊙ Hv_CBDA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dC_4_2_L DC_4_2_L
        (square_stack_dep _ (square_map_dep dB_3_1_L DB_3_1_L
            ((layer_square _ _ _ DA_2_0_L DD_2_1_L (cDE_nil x) (cAE_nil x) (cAD_nil x) (cAE_B
              (dD_0_0_U x)) (cDE_A (dA_0_0_U x)) (cAD_E (dE_0_0_U x)) HcAD_E (hADE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dB_2_1_U dB_3_1_L
            dE_3_3_U (fun _ a => a) DB_2_1_U DB_3_1_L (fun _ a => a) cBE_AC (fun _ _ => eq_refl)
            (cAD_nil x) HcAD_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U dC_4_2_L
        dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl)
        (f_equal dB_2_1_U (cAD_nil x)) (sigT_map_eq (f := dB_2_1_U) DB_2_1_U (p := (cAD_nil x))
          HcAD_nil))).
Defined.

Local Abbreviation n_CBDA_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CBDA_2 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dB_1_1_U
    dD_1_1_U dE_1_1_U dA_1_0_L dD_2_2_U dE_2_2_U dB_2_1_U dB_2_1_L dD_2_1_L dE_3_3_U dC_3_2_U
    dD_3_2_L dB_3_1_L dE_4_4_U dC_4_2_L cAE_nil cBD_A cBD_AE cBE_A cBE_AC cCE_ABD cDE_A cDE_AB
    hBDE_A x).

Local Definition Hn_CBDA_2: rew [fun e => rew [S0] e in
    (DC_4_2_L (dB_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
      (DB_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
    (DC_3_2_U (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))
      (DD_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)))] n_CBDA_2 in
  ((Hv_CBDA ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dC_3_2_U (cBD_A (dA_0_0_U x))))
          (sigT_map_eq (f := dC_3_2_U) DC_3_2_U (p := (cBD_A (dA_0_0_U x)))
            (HcBD_A (dA_0_0_U x) aA_layer))))) =
    ((sigT_map_eq (f := dC_4_2_L) DC_4_2_L (p := (cBD_AE (dA_1_0_L (dE_0_0_U x))))
        (HcBD_AE (dA_1_0_L (dE_0_0_U x)) aA)) ⊙ Hv_CDBA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dC_4_2_L DC_4_2_L
        (layer_square_nat_coherence_dep dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L
          DB_2_1_L DB_3_1_L DD_3_2_L (fun _ a => a) cBD_AE HcBD_AE (cAE_nil x)
          (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x))
          (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x))) (hBDE_A (dA_0_0_U x))
          eq_refl eq_refl eq_refl (HcBD_A (dA_0_0_U x) aA_layer) eq_refl eq_refl
          (layer_square _ _ _ DB_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A
            (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x))) _ _ (hBDE_A
            (dA_0_0_U x))))) (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U
        dC_4_2_L dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD
        (fun _ _ => eq_refl) (cBD_A (dA_0_0_U x)) (HcBD_A (dA_0_0_U x) aA_layer))).
Defined.

Local Abbreviation n_CDAB_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CDAB_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dE_0_0_U dE_1_1_U
    dA_1_0_U dB_1_0_L dC_2_2_U dD_2_2_U dE_2_2_U dA_2_0_L dD_3_3_U dE_3_3_U dC_3_2_U dC_3_2_L
    dD_3_2_L dE_4_4_U dD_4_3_L dC_4_2_L cAE_B cBE_nil cCD_AB cCD_ABE cCE_AB cCE_ABD cDE_AB cDE_ABC
    hCDE_AB x).

Local Definition Hn_CDAB_1: rew [fun e => rew [S0] e in
    (DC_4_2_L (dD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DD_3_3_U (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))
      (DC_2_2_U (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer)))] n_CDAB_1 in
  ((Hv_CDAB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cCD_AB (dA_1_0_U (dB_0_0_U x))))
          (HcCD_AB (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer))))) =
    ((HcCD_ABE (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB)) ⊙
      Hv_DCAB).
Proof.
  now exact (layer_square_nat_coherence_dep dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U DD_3_2_L
      DC_3_2_L DC_4_2_L DD_4_3_L (fun _ a => a) cCD_ABE HcCD_ABE
      ((f_equal dA_2_0_L (cBE_nil x)) • (cAE_B (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
      (cCE_AB (dA_1_0_U (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x)))
      (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))) (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x))))
      (hCDE_AB (dA_1_0_U (dB_0_0_U x))) ((sigT_map_eq (f := dA_2_0_L) DA_2_0_L (p := (cBE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcCD_AB (dA_1_0_U (dB_0_0_U x))
        (DA_1_0_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
      (layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U
        (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x))) (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
        (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) _ _ (hCDE_AB (dA_1_0_U (dB_0_0_U x))))).
Defined.

Local Abbreviation n_CDAB_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CDAB_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dB_0_0_U dE_0_0_U
    dB_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dB_1_0_L dD_2_2_U dE_2_2_U dB_2_1_L dA_2_0_L dE_3_3_U
    dC_3_2_U dD_3_2_L dE_4_4_U dC_4_2_L cAB_nil cAB_E cAE_nil cAE_B cBE_nil cBE_A cCE_ABD cDE_AB
    hABE_nil x).

Local Definition Hn_CDAB_3: rew [fun e => rew [S0] e in
    (DC_4_2_L (dD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DC_3_2_U (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))
      (DD_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)))] n_CDAB_3 in
  ((Hv_CDAB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dC_3_2_U (f_equal dD_2_2_U (cAB_nil x))))
          (sigT_map_eq (f := dC_3_2_U) DC_3_2_U (p := (f_equal dD_2_2_U (cAB_nil x)))
            (sigT_map_eq (f := dD_2_2_U) DD_2_2_U (p := (cAB_nil x)) HcAB_nil))))) =
    ((sigT_map_eq (f := dC_4_2_L) DC_4_2_L (p := (f_equal dD_3_2_L (cAB_E (dE_0_0_U x))))
        (sigT_map_eq (f := dD_3_2_L) DD_3_2_L (p := (cAB_E (dE_0_0_U x))) HcAB_E)) ⊙ Hv_CDBA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dC_4_2_L DC_4_2_L
        (square_stack_dep _ (square_map_dep dD_3_2_L DD_3_2_L
            ((layer_square _ _ _ DA_2_0_L DB_2_1_L (cBE_nil x) (cAE_nil x) (cAB_nil x) (cAE_B
              (dB_0_0_U x)) (cBE_A (dA_0_0_U x)) (cAB_E (dE_0_0_U x)) HcAB_E (hABE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dD_2_2_U dD_3_2_L
            dE_3_3_U (fun _ a => a) DD_2_2_U DD_3_2_L (fun _ a => a) cDE_AB (fun _ _ => eq_refl)
            (cAB_nil x) HcAB_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U dC_4_2_L
        dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl)
        (f_equal dD_2_2_U (cAB_nil x)) (sigT_map_eq (f := dD_2_2_U) DD_2_2_U (p := (cAB_nil x))
          HcAB_nil))).
Defined.

Local Abbreviation n_CDBA_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_CDBA_1 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dB_1_1_U
    dE_1_1_U dA_1_0_L dC_2_2_U dD_2_2_U dE_2_2_U dB_2_1_L dD_3_3_U dE_3_3_U dC_3_2_U dC_3_2_L
    dD_3_2_L dE_4_4_U dD_4_3_L dC_4_2_L cAE_nil cBE_A cCD_AB cCD_ABE cCE_AB cCE_ABD cDE_AB cDE_ABC
    hCDE_AB x).

Local Definition Hn_CDBA_1: rew [fun e => rew [S0] e in
    (DC_4_2_L (dD_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))))
      (DD_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))) (DB_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))) =
    (DD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))
      (DC_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)))] n_CDBA_1 in
  ((Hv_CDBA ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a) (p := (cCD_AB (dB_1_1_U (dA_0_0_U x))))
          (HcCD_AB (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer))))) =
    ((HcCD_ABE (dB_2_1_L (dA_1_0_L (dE_0_0_U x))) (DB_2_1_L (dA_1_0_L (dE_0_0_U x)) aA)) ⊙
      Hv_DCBA).
Proof.
  now exact (layer_square_nat_coherence_dep dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U DD_3_2_L
      DC_3_2_L DC_4_2_L DD_4_3_L (fun _ a => a) cCD_ABE HcCD_ABE
      ((f_equal dB_2_1_L (cAE_nil x)) • (cBE_A (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
      (cCE_AB (dB_1_1_U (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x)))
      (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))) (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))
      (hCDE_AB (dB_1_1_U (dA_0_0_U x))) ((sigT_map_eq (f := dB_2_1_L) DB_2_1_L (p := (cAE_nil x))
          eq_refl) ⊙ eq_refl) eq_refl eq_refl (HcCD_AB (dB_1_1_U (dA_0_0_U x))
        (DB_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
      (layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U
        (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x))) (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
        (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) _ _ (hCDE_AB (dB_1_1_U (dA_0_0_U x))))).
Defined.


Local Abbreviation n_DABC_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_DABC_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dC_0_0_U dE_0_0_U
    dC_1_1_U dE_1_1_U dB_1_0_U dB_1_0_L dC_1_0_L dE_2_2_U dC_2_1_L dA_2_0_U dB_2_0_L dD_3_3_U
    dE_3_3_U dA_3_0_L dE_4_4_U dD_4_3_L cAE_BC cBC_nil cBC_E cBE_nil cBE_C cCE_nil cCE_A cDE_ABC
    hBCE_nil x).

Local Definition Hn_DABC_3: rew [fun e => rew [S0] e in
    (DD_4_3_L (dA_3_0_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
      (DA_3_0_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DD_3_3_U (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))
      (DA_2_0_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer)))] n_DABC_3 in
  ((Hv_DABC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dD_3_3_U (f_equal dA_2_0_U (cBC_nil x))))
          (sigT_map_eq (f := dD_3_3_U) DD_3_3_U (p := (f_equal dA_2_0_U (cBC_nil x)))
            (sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cBC_nil x)) HcBC_nil))))) =
    ((sigT_map_eq (f := dD_4_3_L) DD_4_3_L (p := (f_equal dA_3_0_L (cBC_E (dE_0_0_U x))))
        (sigT_map_eq (f := dA_3_0_L) DA_3_0_L (p := (cBC_E (dE_0_0_U x))) HcBC_E)) ⊙ Hv_DACB).
Proof.
  now exact (square_stack_dep _ (square_map_dep dD_4_3_L DD_4_3_L
        (square_stack_dep _ (square_map_dep dA_3_0_L DA_3_0_L
            ((layer_square _ _ _ DB_2_0_L DC_2_1_L (cCE_nil x) (cBE_nil x) (cBC_nil x) (cBE_C
              (dC_0_0_U x)) (cCE_A (dB_0_0_U x)) (cBC_E (dE_0_0_U x)) HcBC_E (hBCE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dA_2_0_U dA_3_0_L
            dE_3_3_U (fun _ a => a) DA_2_0_U DA_3_0_L (fun _ a => a) cAE_BC (fun _ _ => eq_refl)
            (cBC_nil x) HcBC_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dD_3_3_U dD_4_3_L
        dE_4_4_U (fun _ a => a) DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl)
        (f_equal dA_2_0_U (cBC_nil x)) (sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cBC_nil x))
          HcBC_nil))).
Defined.


Local Abbreviation n_DBAC_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_DBAC_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dC_0_0_U dE_0_0_U
    dC_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dC_1_0_L dE_2_2_U dB_2_1_U dC_2_1_L dA_2_0_L dD_3_3_U
    dE_3_3_U dB_3_1_L dE_4_4_U dD_4_3_L cAC_nil cAC_E cAE_nil cAE_B cBE_AC cCE_nil cCE_A cDE_ABC
    hACE_nil x).

Local Definition Hn_DBAC_3: rew [fun e => rew [S0] e in
    (DD_4_3_L (dB_3_1_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
      (DB_3_1_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC))) =
    (DD_3_3_U (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))
      (DB_2_1_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer)))] n_DBAC_3 in
  ((Hv_DBAC ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dD_3_3_U (f_equal dB_2_1_U (cAC_nil x))))
          (sigT_map_eq (f := dD_3_3_U) DD_3_3_U (p := (f_equal dB_2_1_U (cAC_nil x)))
            (sigT_map_eq (f := dB_2_1_U) DB_2_1_U (p := (cAC_nil x)) HcAC_nil))))) =
    ((sigT_map_eq (f := dD_4_3_L) DD_4_3_L (p := (f_equal dB_3_1_L (cAC_E (dE_0_0_U x))))
        (sigT_map_eq (f := dB_3_1_L) DB_3_1_L (p := (cAC_E (dE_0_0_U x))) HcAC_E)) ⊙ Hv_DBCA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dD_4_3_L DD_4_3_L
        (square_stack_dep _ (square_map_dep dB_3_1_L DB_3_1_L
            ((layer_square _ _ _ DA_2_0_L DC_2_1_L (cCE_nil x) (cAE_nil x) (cAC_nil x) (cAE_B
              (dC_0_0_U x)) (cCE_A (dA_0_0_U x)) (cAC_E (dE_0_0_U x)) HcAC_E (hACE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dB_2_1_U dB_3_1_L
            dE_3_3_U (fun _ a => a) DB_2_1_U DB_3_1_L (fun _ a => a) cBE_AC (fun _ _ => eq_refl)
            (cAC_nil x) HcAC_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dD_3_3_U dD_4_3_L
        dE_4_4_U (fun _ a => a) DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl)
        (f_equal dB_2_1_U (cAC_nil x)) (sigT_map_eq (f := dB_2_1_U) DB_2_1_U (p := (cAC_nil x))
          HcAC_nil))).
Defined.


Local Abbreviation n_DCAB_3 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_DCAB_3 X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dB_0_0_U dE_0_0_U
    dB_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dB_1_0_L dC_2_2_U dE_2_2_U dB_2_1_L dA_2_0_L dD_3_3_U
    dE_3_3_U dC_3_2_L dE_4_4_U dD_4_3_L cAB_nil cAB_E cAE_nil cAE_B cBE_nil cBE_A cCE_AB cDE_ABC
    hABE_nil x).

Local Definition Hn_DCAB_3: rew [fun e => rew [S0] e in
    (DD_4_3_L (dC_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
      (DC_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB))) =
    (DD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))
      (DC_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)))] n_DCAB_3 in
  ((Hv_DCAB ⊙ (sigT_map_eq (f := dE_4_4_U) (fun _ a => a)
          (p := (f_equal dD_3_3_U (f_equal dC_2_2_U (cAB_nil x))))
          (sigT_map_eq (f := dD_3_3_U) DD_3_3_U (p := (f_equal dC_2_2_U (cAB_nil x)))
            (sigT_map_eq (f := dC_2_2_U) DC_2_2_U (p := (cAB_nil x)) HcAB_nil))))) =
    ((sigT_map_eq (f := dD_4_3_L) DD_4_3_L (p := (f_equal dC_3_2_L (cAB_E (dE_0_0_U x))))
        (sigT_map_eq (f := dC_3_2_L) DC_3_2_L (p := (cAB_E (dE_0_0_U x))) HcAB_E)) ⊙ Hv_DCBA).
Proof.
  now exact (square_stack_dep _ (square_map_dep dD_4_3_L DD_4_3_L
        (square_stack_dep _ (square_map_dep dC_3_2_L DC_3_2_L
            ((layer_square _ _ _ DA_2_0_L DB_2_1_L (cBE_nil x) (cAE_nil x) (cAB_nil x) (cAE_B
              (dB_0_0_U x)) (cBE_A (dA_0_0_U x)) (cAB_E (dE_0_0_U x)) HcAB_E (hABE_nil x))))
              (square_coherence_dep_reverse_fill dE_2_2_U dC_2_2_U dC_3_2_L
            dE_3_3_U (fun _ a => a) DC_2_2_U DC_3_2_L (fun _ a => a) cCE_AB (fun _ _ => eq_refl)
            (cAB_nil x) HcAB_nil))) (square_coherence_dep_reverse_fill dE_3_3_U dD_3_3_U dD_4_3_L
        dE_4_4_U (fun _ a => a) DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl)
        (f_equal dC_2_2_U (cAB_nil x)) (sigT_map_eq (f := dC_2_2_U) DC_2_2_U (p := (cAB_nil x))
          HcAB_nil))).
Defined.

Local Definition HkABCE_nil :=
  @rew_coh2Layer_perm4_coherence Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dA_2_0_U dC_2_2_U
    dB_2_1_U dA_3_0_L dC_3_2_L dB_3_1_L DA_3_0_L DC_3_2_L DB_3_1_L cAE_BC cCE_AB cBE_AC dB_2_0_L
    dC_2_1_L dA_2_0_L dB_2_1_L DB_2_0_L DC_2_1_L DA_2_0_L DB_2_1_L cAC_BE cAB_CE cBC_AE HcAC_BE
    HcAB_CE HcBC_AE (dB_1_0_U (dC_0_0_U x)) (dC_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x))
    (dB_1_1_U (dA_0_0_U x)) (dA_1_0_U (dC_0_0_U x)) (dC_1_1_U (dA_0_0_U x)) (cBC_nil x)
    (cAB_nil x) (cAC_nil x) (cAC_B (dB_0_0_U x)) (cAB_C (dC_0_0_U x)) (cBC_A (dA_0_0_U x))
    (dC_1_0_L (dE_0_0_U x)) (dE_1_1_U (dC_0_0_U x)) (dB_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dB_0_0_U x)) (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cCE_nil x)
    (cBE_nil x) (cAE_nil x) aC aB aA (cBE_C (dC_0_0_U x)) (cCE_A (dB_0_0_U x))
    (cAE_B (dB_0_0_U x)) (cBE_A (dA_0_0_U x)) (cAE_B (dC_0_0_U x)) (cCE_A (dA_0_0_U x))
    (cBC_E (dE_0_0_U x)) (cAB_E (dE_0_0_U x)) (cAC_E (dE_0_0_U x)) HcBC_E HcAB_E HcAC_E
    (hBCE_nil x) (hABE_nil x) (hACE_nil x) (hABC_nil x) (hACE_B (dB_0_0_U x))
    (hABE_C (dC_0_0_U x)) (hBCE_A (dA_0_0_U x)) (hABC_E (dE_0_0_U x)) HhABC_E (kABCE_nil x).

Local Definition HkABCE_D z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4_coherence Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dC_3_2_U
    dB_3_1_U dA_4_0_L dC_4_2_L dB_4_1_L DA_4_0_L DC_4_2_L DB_4_1_L cAE_BCD cCE_ABD cBE_ACD
    dB_3_0_L dC_3_1_L dA_3_0_L dB_3_1_L DB_3_0_L DC_3_1_L DA_3_0_L DB_3_1_L cAC_BDE cAB_CDE
    cBC_ADE HcAC_BDE HcAB_CDE HcBC_ADE (dB_2_0_U (dC_1_0_U z)) (dC_2_1_U (dB_1_0_U z))
    (dA_2_0_U (dB_1_0_U z)) (dB_2_1_U (dA_1_0_U z)) (dA_2_0_U (dC_1_0_U z))
    (dC_2_1_U (dA_1_0_U z)) (cBC_D z) (cAB_D z) (cAC_D z) (cAC_BD (dB_1_0_U z))
    (cAB_CD (dC_1_0_U z)) (cBC_AD (dA_1_0_U z)) (dC_2_0_L (dE_1_1_U z)) (dE_2_2_U (dC_1_0_U z))
    (dB_2_0_L (dE_1_1_U z)) (dE_2_2_U (dB_1_0_U z)) (dA_2_0_L (dE_1_1_U z))
    (dE_2_2_U (dA_1_0_U z)) (cCE_D z) (cBE_C z) (cAE_B z) (DC_2_0_L (dE_1_1_U z) a)
    (DB_2_0_L (dE_1_1_U z) a) (DA_2_0_L (dE_1_1_U z) a) (cBE_CD (dC_1_0_U z))
    (cCE_AD (dB_1_0_U z)) (cAE_BC (dB_1_0_U z)) (cBE_AC (dA_1_0_U z)) (cAE_BC (dC_1_0_U z))
    (cCE_AD (dA_1_0_U z)) (cBC_DE (dE_1_1_U z)) (cAB_DE (dE_1_1_U z)) (cAC_DE (dE_1_1_U z))
    (HcBC_DE (dE_1_1_U z) a) (HcAB_DE (dE_1_1_U z) a) (HcAC_DE (dE_1_1_U z) a) (hBCE_D z)
    (hABE_D z) (hACE_D z) (hABC_D z) (hACE_BD (dB_1_0_U z)) (hABE_CD (dC_1_0_U z))
    (hBCE_AD (dA_1_0_U z)) (hABC_DE (dE_1_1_U z)) (HhABC_DE (dE_1_1_U z) a) (kABCE_D z).

Local Definition HkABDE_nil :=
  @rew_coh2Layer_perm4_coherence Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dA_2_0_U dD_2_2_U
    dB_2_1_U dA_3_0_L dD_3_2_L dB_3_1_L DA_3_0_L DD_3_2_L DB_3_1_L cAE_BC cDE_AB cBE_AC dB_2_0_L
    dD_2_1_L dA_2_0_L dB_2_1_L DB_2_0_L DD_2_1_L DA_2_0_L DB_2_1_L cAD_BE cAB_DE cBD_AE HcAD_BE
    HcAB_DE HcBD_AE (dB_1_0_U (dD_0_0_U x)) (dD_1_1_U (dB_0_0_U x)) (dA_1_0_U (dB_0_0_U x))
    (dB_1_1_U (dA_0_0_U x)) (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cBD_nil x)
    (cAB_nil x) (cAD_nil x) (cAD_B (dB_0_0_U x)) (cAB_D (dD_0_0_U x)) (cBD_A (dA_0_0_U x))
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (dB_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dB_0_0_U x)) (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cDE_nil x)
    (cBE_nil x) (cAE_nil x) aD aB aA (cBE_C (dD_0_0_U x)) (cDE_A (dB_0_0_U x))
    (cAE_B (dB_0_0_U x)) (cBE_A (dA_0_0_U x)) (cAE_B (dD_0_0_U x)) (cDE_A (dA_0_0_U x))
    (cBD_E (dE_0_0_U x)) (cAB_E (dE_0_0_U x)) (cAD_E (dE_0_0_U x)) HcBD_E HcAB_E HcAD_E
    (hBDE_nil x) (hABE_nil x) (hADE_nil x) (hABD_nil x) (hADE_B (dB_0_0_U x))
    (hABE_D (dD_0_0_U x)) (hBDE_A (dA_0_0_U x)) (hABD_E (dE_0_0_U x)) HhABD_E (kABDE_nil x).

Local Definition HkABDE_C z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4_coherence Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dD_3_3_U
    dB_3_1_U dA_4_0_L dD_4_3_L dB_4_1_L DA_4_0_L DD_4_3_L DB_4_1_L cAE_BCD cDE_ABC cBE_ACD
    dB_3_0_L dD_3_2_L dA_3_0_L dB_3_1_L DB_3_0_L DD_3_2_L DA_3_0_L DB_3_1_L cAD_BCE cAB_CDE
    cBD_ACE HcAD_BCE HcAB_CDE HcBD_ACE (dB_2_0_U (dD_1_1_U z)) (dD_2_2_U (dB_1_0_U z))
    (dA_2_0_U (dB_1_0_U z)) (dB_2_1_U (dA_1_0_U z)) (dA_2_0_U (dD_1_1_U z))
    (dD_2_2_U (dA_1_0_U z)) (cBD_C z) (cAB_C z) (cAD_C z) (cAD_BC (dB_1_0_U z))
    (cAB_CD (dD_1_1_U z)) (cBD_AC (dA_1_0_U z)) (dD_2_1_L (dE_1_1_U z)) (dE_2_2_U (dD_1_1_U z))
    (dB_2_0_L (dE_1_1_U z)) (dE_2_2_U (dB_1_0_U z)) (dA_2_0_L (dE_1_1_U z))
    (dE_2_2_U (dA_1_0_U z)) (cDE_A z) (cBE_C z) (cAE_B z) (DD_2_1_L (dE_1_1_U z) a)
    (DB_2_0_L (dE_1_1_U z) a) (DA_2_0_L (dE_1_1_U z) a) (cBE_CD (dD_1_1_U z))
    (cDE_AB (dB_1_0_U z)) (cAE_BC (dB_1_0_U z)) (cBE_AC (dA_1_0_U z)) (cAE_BC (dD_1_1_U z))
    (cDE_AB (dA_1_0_U z)) (cBD_CE (dE_1_1_U z)) (cAB_CE (dE_1_1_U z)) (cAD_CE (dE_1_1_U z))
    (HcBD_CE (dE_1_1_U z) a) (HcAB_CE (dE_1_1_U z) a) (HcAD_CE (dE_1_1_U z) a) (hBDE_C z)
    (hABE_C z) (hADE_C z) (hABD_C z) (hADE_BC (dB_1_0_U z)) (hABE_CD (dD_1_1_U z))
    (hBDE_AC (dA_1_0_U z)) (hABD_CE (dE_1_1_U z)) (HhABD_CE (dE_1_1_U z) a) (kABDE_C z).

Local Definition HkACDE_nil :=
  @rew_coh2Layer_perm4_coherence Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dA_2_0_U dD_2_2_U
    dC_2_1_U dA_3_0_L dD_3_2_L dC_3_1_L DA_3_0_L DD_3_2_L DC_3_1_L cAE_BC cDE_AB cCE_AD dC_2_0_L
    dD_2_1_L dA_2_0_L dC_2_1_L DC_2_0_L DD_2_1_L DA_2_0_L DC_2_1_L cAD_CE cAC_DE cCD_AE HcAD_CE
    HcAC_DE HcCD_AE (dC_1_0_U (dD_0_0_U x)) (dD_1_1_U (dC_0_0_U x)) (dA_1_0_U (dC_0_0_U x))
    (dC_1_1_U (dA_0_0_U x)) (dA_1_0_U (dD_0_0_U x)) (dD_1_1_U (dA_0_0_U x)) (cCD_nil x)
    (cAC_nil x) (cAD_nil x) (cAD_C (dC_0_0_U x)) (cAC_D (dD_0_0_U x)) (cCD_A (dA_0_0_U x))
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (dC_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dC_0_0_U x)) (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cDE_nil x)
    (cCE_nil x) (cAE_nil x) aD aC aA (cCE_D (dD_0_0_U x)) (cDE_A (dC_0_0_U x))
    (cAE_B (dC_0_0_U x)) (cCE_A (dA_0_0_U x)) (cAE_B (dD_0_0_U x)) (cDE_A (dA_0_0_U x))
    (cCD_E (dE_0_0_U x)) (cAC_E (dE_0_0_U x)) (cAD_E (dE_0_0_U x)) HcCD_E HcAC_E HcAD_E
    (hCDE_nil x) (hACE_nil x) (hADE_nil x) (hACD_nil x) (hADE_C (dC_0_0_U x))
    (hACE_D (dD_0_0_U x)) (hCDE_A (dA_0_0_U x)) (hACD_E (dE_0_0_U x)) HhACD_E (kACDE_nil x).

Local Definition HkACDE_B z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4_coherence Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dD_3_3_U
    dC_3_2_U dA_4_0_L dD_4_3_L dC_4_2_L DA_4_0_L DD_4_3_L DC_4_2_L cAE_BCD cDE_ABC cCE_ABD
    dC_3_1_L dD_3_2_L dA_3_0_L dC_3_2_L DC_3_1_L DD_3_2_L DA_3_0_L DC_3_2_L cAD_BCE cAC_BDE
    cCD_ABE HcAD_BCE HcAC_BDE HcCD_ABE (dC_2_1_U (dD_1_1_U z)) (dD_2_2_U (dC_1_1_U z))
    (dA_2_0_U (dC_1_1_U z)) (dC_2_2_U (dA_1_0_U z)) (dA_2_0_U (dD_1_1_U z))
    (dD_2_2_U (dA_1_0_U z)) (cCD_B z) (cAC_B z) (cAD_B z) (cAD_BC (dC_1_1_U z))
    (cAC_BD (dD_1_1_U z)) (cCD_AB (dA_1_0_U z)) (dD_2_1_L (dE_1_1_U z)) (dE_2_2_U (dD_1_1_U z))
    (dC_2_1_L (dE_1_1_U z)) (dE_2_2_U (dC_1_1_U z)) (dA_2_0_L (dE_1_1_U z))
    (dE_2_2_U (dA_1_0_U z)) (cDE_A z) (cCE_A z) (cAE_B z) (DD_2_1_L (dE_1_1_U z) a)
    (DC_2_1_L (dE_1_1_U z) a) (DA_2_0_L (dE_1_1_U z) a) (cCE_AD (dD_1_1_U z))
    (cDE_AB (dC_1_1_U z)) (cAE_BC (dC_1_1_U z)) (cCE_AB (dA_1_0_U z)) (cAE_BC (dD_1_1_U z))
    (cDE_AB (dA_1_0_U z)) (cCD_BE (dE_1_1_U z)) (cAC_BE (dE_1_1_U z)) (cAD_BE (dE_1_1_U z))
    (HcCD_BE (dE_1_1_U z) a) (HcAC_BE (dE_1_1_U z) a) (HcAD_BE (dE_1_1_U z) a) (hCDE_B z)
    (hACE_B z) (hADE_B z) (hACD_B z) (hADE_BC (dC_1_1_U z)) (hACE_BD (dD_1_1_U z))
    (hCDE_AB (dA_1_0_U z)) (hACD_BE (dE_1_1_U z)) (HhACD_BE (dE_1_1_U z) a) (kACDE_B z).

Local Definition HkBCDE_nil :=
  @rew_coh2Layer_perm4_coherence Y3 Y2 Y1 S3 S2 S1 X3 X2 dE_2_2_U dE_3_3_U dB_2_0_U dD_2_2_U
    dC_2_1_U dB_3_0_L dD_3_2_L dC_3_1_L DB_3_0_L DD_3_2_L DC_3_1_L cBE_CD cDE_AB cCE_AD dC_2_0_L
    dD_2_1_L dB_2_0_L dC_2_1_L DC_2_0_L DD_2_1_L DB_2_0_L DC_2_1_L cBD_CE cBC_DE cCD_BE HcBD_CE
    HcBC_DE HcCD_BE (dC_1_0_U (dD_0_0_U x)) (dD_1_1_U (dC_0_0_U x)) (dB_1_0_U (dC_0_0_U x))
    (dC_1_1_U (dB_0_0_U x)) (dB_1_0_U (dD_0_0_U x)) (dD_1_1_U (dB_0_0_U x)) (cCD_nil x)
    (cBC_nil x) (cBD_nil x) (cBD_C (dC_0_0_U x)) (cBC_D (dD_0_0_U x)) (cCD_B (dB_0_0_U x))
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (dC_1_0_L (dE_0_0_U x))
    (dE_1_1_U (dC_0_0_U x)) (dB_1_0_L (dE_0_0_U x)) (dE_1_1_U (dB_0_0_U x)) (cDE_nil x)
    (cCE_nil x) (cBE_nil x) aD aC aB (cCE_D (dD_0_0_U x)) (cDE_A (dC_0_0_U x))
    (cBE_C (dC_0_0_U x)) (cCE_A (dB_0_0_U x)) (cBE_C (dD_0_0_U x)) (cDE_A (dB_0_0_U x))
    (cCD_E (dE_0_0_U x)) (cBC_E (dE_0_0_U x)) (cBD_E (dE_0_0_U x)) HcCD_E HcBC_E HcBD_E
    (hCDE_nil x) (hBCE_nil x) (hBDE_nil x) (hBCD_nil x) (hBDE_C (dC_0_0_U x))
    (hBCE_D (dD_0_0_U x)) (hCDE_B (dB_0_0_U x)) (hBCD_E (dE_0_0_U x)) HhBCD_E (kBCDE_nil x).

Local Definition HkBCDE_A z (a: S3 (dE_1_1_U z)) :=
  @rew_coh2Layer_perm4_coherence Y2 Y1 Y0 S2 S1 S0 X2 X1 dE_3_3_U dE_4_4_U dB_3_1_U dD_3_3_U
    dC_3_2_U dB_4_1_L dD_4_3_L dC_4_2_L DB_4_1_L DD_4_3_L DC_4_2_L cBE_ACD cDE_ABC cCE_ABD
    dC_3_1_L dD_3_2_L dB_3_1_L dC_3_2_L DC_3_1_L DD_3_2_L DB_3_1_L DC_3_2_L cBD_ACE cBC_ADE
    cCD_ABE HcBD_ACE HcBC_ADE HcCD_ABE (dC_2_1_U (dD_1_1_U z)) (dD_2_2_U (dC_1_1_U z))
    (dB_2_1_U (dC_1_1_U z)) (dC_2_2_U (dB_1_1_U z)) (dB_2_1_U (dD_1_1_U z))
    (dD_2_2_U (dB_1_1_U z)) (cCD_A z) (cBC_A z) (cBD_A z) (cBD_AC (dC_1_1_U z))
    (cBC_AD (dD_1_1_U z)) (cCD_AB (dB_1_1_U z)) (dD_2_1_L (dE_1_1_U z)) (dE_2_2_U (dD_1_1_U z))
    (dC_2_1_L (dE_1_1_U z)) (dE_2_2_U (dC_1_1_U z)) (dB_2_1_L (dE_1_1_U z))
    (dE_2_2_U (dB_1_1_U z)) (cDE_A z) (cCE_A z) (cBE_A z) (DD_2_1_L (dE_1_1_U z) a)
    (DC_2_1_L (dE_1_1_U z) a) (DB_2_1_L (dE_1_1_U z) a) (cCE_AD (dD_1_1_U z))
    (cDE_AB (dC_1_1_U z)) (cBE_AC (dC_1_1_U z)) (cCE_AB (dB_1_1_U z)) (cBE_AC (dD_1_1_U z))
    (cDE_AB (dB_1_1_U z)) (cCD_AE (dE_1_1_U z)) (cBC_AE (dE_1_1_U z)) (cBD_AE (dE_1_1_U z))
    (HcCD_AE (dE_1_1_U z) a) (HcBC_AE (dE_1_1_U z) a) (HcBD_AE (dE_1_1_U z) a) (hCDE_A z)
    (hBCE_A z) (hBDE_A z) (hBCD_A z) (hBDE_AC (dC_1_1_U z)) (hBCE_AD (dD_1_1_U z))
    (hCDE_AB (dB_1_1_U z)) (hBCD_AE (dE_1_1_U z)) (HhBCD_AE (dE_1_1_U z) a) (kBCDE_A z).


Local Definition Hraw_nat_BCD_A :=
  square_cube_nat_prism_coherence_dep dB_4_1_L dD_4_3_L dC_4_2_L (fun z => dC_3_1_L (dD_2_1_L z))
    (fun z => dD_3_2_L (dC_2_1_L z)) (fun z => dB_3_1_L (dC_2_1_L z))
    (fun z => dC_3_2_L (dB_2_1_L z)) (fun z => dB_3_1_L (dD_2_1_L z))
    (fun z => dD_3_2_L (dB_2_1_L z)) cCD_AE cBC_AE cBD_AE (fun z => cBD_ACE (dC_2_1_L z))
    (fun z => cBC_ADE (dD_2_1_L z)) (fun z => cCD_ABE (dB_2_1_L z)) hBCD_AE
    (fun z a => DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a))
    (fun z a => DB_3_1_L (dC_2_1_L z) (DC_2_1_L z a))
    (fun z a => DC_3_2_L (dB_2_1_L z) (DB_2_1_L z a))
    (fun z a => DB_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => DD_3_2_L (dB_2_1_L z) (DB_2_1_L z a)) DB_4_1_L DD_4_3_L DC_4_2_L HcCD_AE HcBC_AE
    HcBD_AE (fun z a => HcBD_ACE (dC_2_1_L z) (DC_2_1_L z a))
    (fun z a => HcBC_ADE (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => HcCD_ABE (dB_2_1_L z) (DB_2_1_L z a)) HhBCD_AE (cAE_nil x) eq_refl
    (kBCDE_A (dA_0_0_U x)) (HkBCDE_A (dA_0_0_U x) aA_layer)
    (layer_cube_nat_side_coherence_dep dD_2_1_L dC_3_1_L dB_4_1_L DD_2_1_L DC_3_1_L DB_4_1_L
      (cAE_nil x) (cDE_A ((dA_0_0_U x))) (cCE_AD (dD_1_1_U ((dA_0_0_U x))))
      (cBE_ACD (dC_2_1_U (dD_1_1_U ((dA_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl)
    (layer_cube_nat_side_coherence_dep dB_2_1_L dC_3_2_L dD_4_3_L DB_2_1_L DC_3_2_L DD_4_3_L
      (cAE_nil x) (cBE_A ((dA_0_0_U x))) (cCE_AB (dB_1_1_U ((dA_0_0_U x))))
      (cDE_ABC (dC_2_2_U (dB_1_1_U ((dA_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl).

Local Definition Hraw_nat_ACD_B :=
  square_cube_nat_prism_coherence_dep dA_4_0_L dD_4_3_L dC_4_2_L (fun z => dC_3_1_L (dD_2_1_L z))
    (fun z => dD_3_2_L (dC_2_1_L z)) (fun z => dA_3_0_L (dC_2_1_L z))
    (fun z => dC_3_2_L (dA_2_0_L z)) (fun z => dA_3_0_L (dD_2_1_L z))
    (fun z => dD_3_2_L (dA_2_0_L z)) cCD_BE cAC_BE cAD_BE (fun z => cAD_BCE (dC_2_1_L z))
    (fun z => cAC_BDE (dD_2_1_L z)) (fun z => cCD_ABE (dA_2_0_L z)) hACD_BE
    (fun z a => DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a))
    (fun z a => DA_3_0_L (dC_2_1_L z) (DC_2_1_L z a))
    (fun z a => DC_3_2_L (dA_2_0_L z) (DA_2_0_L z a))
    (fun z a => DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a)) DA_4_0_L DD_4_3_L DC_4_2_L HcCD_BE HcAC_BE
    HcAD_BE (fun z a => HcAD_BCE (dC_2_1_L z) (DC_2_1_L z a))
    (fun z a => HcAC_BDE (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => HcCD_ABE (dA_2_0_L z) (DA_2_0_L z a)) HhACD_BE (cBE_nil x) eq_refl
    (kACDE_B (dB_0_0_U x)) (HkACDE_B (dB_0_0_U x) aB_layer)
    (layer_cube_nat_side_coherence_dep dD_2_1_L dC_3_1_L dA_4_0_L DD_2_1_L DC_3_1_L DA_4_0_L
      (cBE_nil x) (cDE_A ((dB_0_0_U x))) (cCE_AD (dD_1_1_U ((dB_0_0_U x))))
      (cAE_BCD (dC_2_1_U (dD_1_1_U ((dB_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl)
    (layer_cube_nat_side_coherence_dep dA_2_0_L dC_3_2_L dD_4_3_L DA_2_0_L DC_3_2_L DD_4_3_L
      (cBE_nil x) (cAE_B ((dB_0_0_U x))) (cCE_AB (dA_1_0_U ((dB_0_0_U x))))
      (cDE_ABC (dC_2_2_U (dA_1_0_U ((dB_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl).

Local Definition Hraw_nat_ABD_C :=
  square_cube_nat_prism_coherence_dep dA_4_0_L dD_4_3_L dB_4_1_L (fun z => dB_3_0_L (dD_2_1_L z))
    (fun z => dD_3_2_L (dB_2_0_L z)) (fun z => dA_3_0_L (dB_2_0_L z))
    (fun z => dB_3_1_L (dA_2_0_L z)) (fun z => dA_3_0_L (dD_2_1_L z))
    (fun z => dD_3_2_L (dA_2_0_L z)) cBD_CE cAB_CE cAD_CE (fun z => cAD_BCE (dB_2_0_L z))
    (fun z => cAB_CDE (dD_2_1_L z)) (fun z => cBD_ACE (dA_2_0_L z)) hABD_CE
    (fun z a => DB_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => DD_3_2_L (dB_2_0_L z) (DB_2_0_L z a))
    (fun z a => DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a))
    (fun z a => DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a))
    (fun z a => DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a)) DA_4_0_L DD_4_3_L DB_4_1_L HcBD_CE HcAB_CE
    HcAD_CE (fun z a => HcAD_BCE (dB_2_0_L z) (DB_2_0_L z a))
    (fun z a => HcAB_CDE (dD_2_1_L z) (DD_2_1_L z a))
    (fun z a => HcBD_ACE (dA_2_0_L z) (DA_2_0_L z a)) HhABD_CE (cCE_nil x) eq_refl
    (kABDE_C (dC_0_0_U x)) (HkABDE_C (dC_0_0_U x) aC_layer)
    (layer_cube_nat_side_coherence_dep dD_2_1_L dB_3_0_L dA_4_0_L DD_2_1_L DB_3_0_L DA_4_0_L
      (cCE_nil x) (cDE_A ((dC_0_0_U x))) (cBE_CD (dD_1_1_U ((dC_0_0_U x))))
      (cAE_BCD (dB_2_0_U (dD_1_1_U ((dC_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl)
    (layer_cube_nat_side_coherence_dep dA_2_0_L dB_3_1_L dD_4_3_L DA_2_0_L DB_3_1_L DD_4_3_L
      (cCE_nil x) (cAE_B ((dC_0_0_U x))) (cBE_AC (dA_1_0_U ((dC_0_0_U x))))
      (cDE_ABC (dB_2_1_U (dA_1_0_U ((dC_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl).

Local Definition Hraw_nat_ABC_D :=
  square_cube_nat_prism_coherence_dep dA_4_0_L dC_4_2_L dB_4_1_L (fun z => dB_3_0_L (dC_2_0_L z))
    (fun z => dC_3_1_L (dB_2_0_L z)) (fun z => dA_3_0_L (dB_2_0_L z))
    (fun z => dB_3_1_L (dA_2_0_L z)) (fun z => dA_3_0_L (dC_2_0_L z))
    (fun z => dC_3_1_L (dA_2_0_L z)) cBC_DE cAB_DE cAC_DE (fun z => cAC_BDE (dB_2_0_L z))
    (fun z => cAB_CDE (dC_2_0_L z)) (fun z => cBC_ADE (dA_2_0_L z)) hABC_DE
    (fun z a => DB_3_0_L (dC_2_0_L z) (DC_2_0_L z a))
    (fun z a => DC_3_1_L (dB_2_0_L z) (DB_2_0_L z a))
    (fun z a => DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a))
    (fun z a => DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a))
    (fun z a => DA_3_0_L (dC_2_0_L z) (DC_2_0_L z a))
    (fun z a => DC_3_1_L (dA_2_0_L z) (DA_2_0_L z a)) DA_4_0_L DC_4_2_L DB_4_1_L HcBC_DE HcAB_DE
    HcAC_DE (fun z a => HcAC_BDE (dB_2_0_L z) (DB_2_0_L z a))
    (fun z a => HcAB_CDE (dC_2_0_L z) (DC_2_0_L z a))
    (fun z a => HcBC_ADE (dA_2_0_L z) (DA_2_0_L z a)) HhABC_DE (cDE_nil x) eq_refl
    (kABCE_D (dD_0_0_U x)) (HkABCE_D (dD_0_0_U x) aD_layer)
    (layer_cube_nat_side_coherence_dep dC_2_0_L dB_3_0_L dA_4_0_L DC_2_0_L DB_3_0_L DA_4_0_L
      (cDE_nil x) (cCE_D ((dD_0_0_U x))) (cBE_CD (dC_1_0_U ((dD_0_0_U x))))
      (cAE_BCD (dB_2_0_U (dC_1_0_U ((dD_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl)
    (layer_cube_nat_side_coherence_dep dA_2_0_L dB_3_1_L dC_4_2_L DA_2_0_L DB_3_1_L DC_4_2_L
      (cDE_nil x) (cAE_B ((dD_0_0_U x))) (cBE_AC (dA_1_0_U ((dD_0_0_U x))))
      (cCE_ABD (dB_2_1_U (dA_1_0_U ((dD_0_0_U x))))) eq_refl eq_refl eq_refl eq_refl).

Local Definition Hhcube_BCD_A :=
  square_cube_change_faces_coherence_dep S0
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k =>
      (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
            (layer_square_map_source dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_AE dB_4_1_L
        dB_3_1_U dE_4_4_U cBE_ACD (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x))
        (cCD_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
        (hCDE_A (dA_0_0_U x))) (layer_square_nat_source dC_2_1_L dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L
          dE_4_4_U cBD_ACE
          (cAE_nil x) (cCE_A (dA_0_0_U x)) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
          (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) (hBDE_AC (dC_1_1_U (dA_0_0_U x)))))
            (layer_square_map_source dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L dE_3_3_U cBC_AE dD_4_3_L
          dD_3_3_U dE_4_4_U cDE_ABC (cAE_nil x) (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x))
          (cBC_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (hBCE_A (dA_0_0_U x))) (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k
            => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (layer_square_map_source dD_2_1_L dC_2_1_L dC_3_1_L
            dD_3_2_L dE_3_3_U cCD_AE dB_4_1_L
        dB_3_1_U dE_4_4_U cBE_ACD (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x))
        (cCD_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
        (hCDE_A (dA_0_0_U x))) (layer_square_nat_source dC_2_1_L dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L
          dE_4_4_U cBD_ACE
          (cAE_nil x) (cCE_A (dA_0_0_U x)) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
          (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) (hBDE_AC (dC_1_1_U (dA_0_0_U x))))
            (layer_square_map_source_coherence_dep dD_2_1_L dC_2_1_L
        dC_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L DC_2_1_L DC_3_1_L DD_3_2_L (fun _ a => a) cCD_AE
        HcCD_AE dB_4_1_L dB_3_1_U dE_4_4_U DB_4_1_L DB_3_1_U (fun _ a => a) cBE_ACD
        (fun _ _ => eq_refl) (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x))
        (cCD_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
        (hCDE_A (dA_0_0_U x)) eq_refl eq_refl eq_refl (HcCD_A (dA_0_0_U x) aA_layer) eq_refl
        eq_refl (layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cCD_A
          (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x))) (cCD_AE
          (dE_1_1_U (dA_0_0_U x))) (HcCD_AE (dE_1_1_U (dA_0_0_U x)) aA_layer) (hCDE_A (dA_0_0_U x))))
            (layer_square_nat_source_coherence_dep dC_2_1_L dD_3_2_L dB_3_1_L
          dB_4_1_L dD_4_3_L dE_4_4_U DC_2_1_L DD_3_2_L DB_3_1_L DB_4_1_L DD_4_3_L (fun _ a => a)
          cBD_ACE HcBD_ACE (cAE_nil x) (cCE_A (dA_0_0_U x)) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
          (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) (hBDE_AC (dC_1_1_U (dA_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcBD_AC (dC_1_1_U (dA_0_0_U x))
            (DC_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
          (layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB (dC_1_1_U (dA_0_0_U x))) (cBE_AC (dC_1_1_U
            (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x))) (cBE_ACD (dD_2_2_U (dC_1_1_U
            (dA_0_0_U x)))) (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) (cBD_ACE (dE_2_2_U (dC_1_1_U
            (dA_0_0_U x)))) (HcBD_ACE (dE_2_2_U (dC_1_1_U (dA_0_0_U x))) (DC_1_1_U
            (dA_0_0_U x) aA_layer)) (hBDE_AC (dC_1_1_U (dA_0_0_U x))))))
            (layer_square_map_source_coherence_dep dC_2_1_L
          dB_2_1_L dB_3_1_L dC_3_2_L dE_3_3_U DC_2_1_L DB_2_1_L DB_3_1_L DC_3_2_L (fun _ a => a)
          cBC_AE HcBC_AE dD_4_3_L dD_3_3_U dE_4_4_U DD_4_3_L DD_3_3_U (fun _ a => a) cDE_ABC
          (fun _ _ => eq_refl) (cAE_nil x) (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x))
          (cBC_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (hBCE_A (dA_0_0_U x)) eq_refl eq_refl eq_refl (HcBC_A (dA_0_0_U x) aA_layer) eq_refl
          eq_refl (layer_square _ _ _ DB_3_1_L DC_3_2_L (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x))
            (cBC_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
            (cBC_AE (dE_1_1_U (dA_0_0_U x))) (HcBC_AE (dE_1_1_U (dA_0_0_U x)) aA_layer) (hBCE_A
            (dA_0_0_U x)))) ⊙
              square_nat_route_left_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
              (layer_cube_nat_side_coherence_dep dD_2_1_L dC_3_1_L dB_4_1_L DD_2_1_L DC_3_1_L DB_4_1_L
        (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
        (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dC_2_1_L dD_3_2_L dB_4_1_L DC_2_1_L DD_3_2_L DB_4_1_L
        (cAE_nil x) (cCE_A (dA_0_0_U x)) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
        (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dC_2_1_L dB_3_1_L dD_4_3_L DC_2_1_L DB_3_1_L DD_4_3_L
        (cAE_nil x) (cCE_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x)))
        (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dB_2_1_L dC_3_2_L dD_4_3_L DB_2_1_L DC_3_2_L DD_4_3_L
        (cAE_nil x) (cBE_A (dA_0_0_U x)) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
        (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (square_coherence_dep_fill (fun z => dC_3_1_L ( dD_2_1_L z ))
        (fun z => dD_3_2_L ( dC_2_1_L z )) dB_4_1_L dB_4_1_L
        (fun z a => DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a)) DB_4_1_L DB_4_1_L
        (fun z => f_equal dB_4_1_L ( cCD_AE z )) (fun z a => sigT_map_eq DB_4_1_L (HcCD_AE z a))
        (cAE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dD_3_2_L ( dC_2_1_L z ))
        (fun z => dB_3_1_L ( dC_2_1_L z )) dB_4_1_L dD_4_3_L
        (fun z a => DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a))
        (fun z a => DB_3_1_L (dC_2_1_L z) (DC_2_1_L z a)) DB_4_1_L DD_4_3_L
        (fun z => cBD_ACE ( dC_2_1_L z )) (fun z a => HcBD_ACE (dC_2_1_L z) (DC_2_1_L z a))
        (cAE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dB_3_1_L ( dC_2_1_L z ))
        (fun z => dC_3_2_L ( dB_2_1_L z )) dD_4_3_L dD_4_3_L
        (fun z a => DB_3_1_L (dC_2_1_L z) (DC_2_1_L z a))
        (fun z a => DC_3_2_L (dB_2_1_L z) (DB_2_1_L z a)) DD_4_3_L DD_4_3_L
        (fun z => f_equal dD_4_3_L ( cBC_AE z )) (fun z a => sigT_map_eq DD_4_3_L (HcBC_AE z a))
        (cAE_nil x) eq_refl) (square_stack_dep _
        (square_map_dep dB_4_1_L DB_4_1_L ((layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x))
          (cCE_A (dA_0_0_U x)) (cCD_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U
          (dA_0_0_U x))) (cCD_AE (dE_1_1_U (dA_0_0_U x))) (HcCD_AE (dE_1_1_U (dA_0_0_U x)) aA_layer)
          (hCDE_A (dA_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U (fun _ a => a)
          DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl) (cCD_A (dA_0_0_U x))
          (HcCD_A (dA_0_0_U x) aA_layer))) (layer_square_nat_coherence_dep dD_3_2_L dB_3_1_L
        dB_4_1_L dD_4_3_L dE_4_4_U DD_3_2_L DB_3_1_L DB_4_1_L DD_4_3_L (fun _ a => a) cBD_ACE
        HcBD_ACE (cCE_A (dA_0_0_U x)) (cDE_AB (dC_1_1_U (dA_0_0_U x)))
        (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
        (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))) (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x))))
        (hBDE_AC (dC_1_1_U (dA_0_0_U x))) eq_refl eq_refl eq_refl
        (HcBD_AC (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
        (layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB (dC_1_1_U (dA_0_0_U x))) (cBE_AC (dC_1_1_U
          (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x))) (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) (cBD_ACE (dE_2_2_U (dC_1_1_U (dA_0_0_U x))))
          (HcBD_ACE (dE_2_2_U (dC_1_1_U (dA_0_0_U x))) (DC_1_1_U (dA_0_0_U x) aA_layer)) (hBDE_AC
          (dC_1_1_U (dA_0_0_U x))))) (square_stack_dep _
        (square_map_dep dD_4_3_L DD_4_3_L ((layer_square _ _ _ DB_3_1_L DC_3_2_L (cCE_A (dA_0_0_U x))
          (cBE_A (dA_0_0_U x)) (cBC_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U
          (dA_0_0_U x))) (cBC_AE (dE_1_1_U (dA_0_0_U x))) (HcBC_AE (dE_1_1_U (dA_0_0_U x)) aA_layer)
          (hBCE_A (dA_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U (fun _ a => a)
          DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl) (cBC_A (dA_0_0_U x))
          (HcBC_A (dA_0_0_U x) aA_layer)))) Hraw_nat_BCD_A
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K)
      (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k))
      (layer_square_nat_source dD_2_1_L dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U cBC_ADE
        (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
        (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x)))
        (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))) (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x))))
        (hBCE_AD (dD_1_1_U (dA_0_0_U x)))) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_map_source dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U cBD_AE dC_4_2_L
          dC_3_2_U dE_4_4_U cCE_ABD (cAE_nil x) (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x))
          (cBD_A (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
          (hBDE_A (dA_0_0_U x))) (layer_square_nat_source dB_2_1_L dD_3_2_L dC_3_2_L dC_4_2_L
          dD_4_3_L dE_4_4_U cCD_ABE (cAE_nil x) (cBE_A (dA_0_0_U x))
          (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (cCD_AB (dB_1_1_U (dA_0_0_U x))) (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) (hCDE_AB (dB_1_1_U (dA_0_0_U x)))))
      (layer_square_nat_source_coherence_dep dD_2_1_L dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U
        DD_2_1_L DC_3_1_L DB_3_1_L DB_4_1_L DC_4_2_L (fun _ a => a) cBC_ADE HcBC_ADE (cAE_nil x)
        (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cBE_AC (dD_1_1_U (dA_0_0_U x)))
        (cBC_AD (dD_1_1_U (dA_0_0_U x))) (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x))))
        (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) (hBCE_AD (dD_1_1_U (dA_0_0_U x))) eq_refl
        eq_refl eq_refl eq_refl (HcBC_AD (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer))
        eq_refl eq_refl (layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cBE_AC
          (dD_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x))) (cBE_ACD (dC_2_1_U (dD_1_1_U
          (dA_0_0_U x)))) (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) (cBC_ADE (dE_2_2_U (dD_1_1_U
          (dA_0_0_U x)))) (HcBC_ADE (dE_2_2_U (dD_1_1_U (dA_0_0_U x))) (DD_1_1_U
          (dA_0_0_U x) aA_layer)) (hBCE_AD (dD_1_1_U (dA_0_0_U x))))) (path_map2_dep
        (fun H K => square_compose_map dE_4_4_U H K)
        (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
            (fun _ a => a) (H := H) (K := K) h k))
        (layer_square_map_source dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U cBD_AE dC_4_2_L
          dC_3_2_U dE_4_4_U cCE_ABD (cAE_nil x) (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x))
          (cBD_A (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
          (hBDE_A (dA_0_0_U x))) (layer_square_nat_source dB_2_1_L dD_3_2_L dC_3_2_L dC_4_2_L
          dD_4_3_L dE_4_4_U cCD_ABE (cAE_nil x) (cBE_A (dA_0_0_U x))
          (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (cCD_AB (dB_1_1_U (dA_0_0_U x))) (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) (hCDE_AB (dB_1_1_U (dA_0_0_U x))))
        (layer_square_map_source_coherence_dep dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U
          DD_2_1_L DB_2_1_L DB_3_1_L DD_3_2_L (fun _ a => a) cBD_AE HcBD_AE dC_4_2_L dC_3_2_U
          dE_4_4_U DC_4_2_L DC_3_2_U (fun _ a => a) cCE_ABD (fun _ _ => eq_refl) (cAE_nil x)
          (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x))
          (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x))) (hBDE_A (dA_0_0_U x))
          eq_refl eq_refl eq_refl (HcBD_A (dA_0_0_U x) aA_layer) eq_refl eq_refl
          (layer_square _ _ _ DB_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A
            (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cBD_AE
            (dE_1_1_U (dA_0_0_U x))) (HcBD_AE (dE_1_1_U (dA_0_0_U x)) aA_layer) (hBDE_A (dA_0_0_U x))))
            (layer_square_nat_source_coherence_dep dB_2_1_L dD_3_2_L
          dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U DB_2_1_L DD_3_2_L DC_3_2_L DC_4_2_L DD_4_3_L
          (fun _ a => a) cCD_ABE HcCD_ABE (cAE_nil x) (cBE_A (dA_0_0_U x))
          (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (cCD_AB (dB_1_1_U (dA_0_0_U x))) (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) (hCDE_AB (dB_1_1_U (dA_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcCD_AB (dB_1_1_U (dA_0_0_U x))
            (DB_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
          (layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U
            (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x))) (cCE_ABD (dD_2_2_U (dB_1_1_U
            (dA_0_0_U x)))) (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) (cCD_ABE (dE_2_2_U (dB_1_1_U
            (dA_0_0_U x)))) (HcCD_ABE (dE_2_2_U (dB_1_1_U (dA_0_0_U x))) (DB_1_1_U
            (dA_0_0_U x) aA_layer)) (hCDE_AB (dB_1_1_U
            (dA_0_0_U x)))))) ⊙ square_nat_route_coherence_dep dE_4_4_U S0
      (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
      (layer_cube_nat_side_coherence_dep dD_2_1_L dC_3_1_L dB_4_1_L DD_2_1_L DC_3_1_L DB_4_1_L
        (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
        (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dD_2_1_L dB_3_1_L dC_4_2_L DD_2_1_L DB_3_1_L DC_4_2_L
        (cAE_nil x) (cDE_A (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x)))
        (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dB_2_1_L dD_3_2_L dC_4_2_L DB_2_1_L DD_3_2_L DC_4_2_L
        (cAE_nil x) (cBE_A (dA_0_0_U x)) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
        (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dB_2_1_L dC_3_2_L dD_4_3_L DB_2_1_L DC_3_2_L DD_4_3_L
        (cAE_nil x) (cBE_A (dA_0_0_U x)) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
        (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (square_coherence_dep_fill (fun z => dC_3_1_L ( dD_2_1_L z ))
        (fun z => dB_3_1_L ( dD_2_1_L z )) dB_4_1_L dC_4_2_L
        (fun z a => DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DB_3_1_L (dD_2_1_L z) (DD_2_1_L z a)) DB_4_1_L DC_4_2_L
        (fun z => cBC_ADE ( dD_2_1_L z )) (fun z a => HcBC_ADE (dD_2_1_L z) (DD_2_1_L z a))
        (cAE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dB_3_1_L ( dD_2_1_L z ))
        (fun z => dD_3_2_L ( dB_2_1_L z )) dC_4_2_L dC_4_2_L
        (fun z a => DB_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DD_3_2_L (dB_2_1_L z) (DB_2_1_L z a)) DC_4_2_L DC_4_2_L
        (fun z => f_equal dC_4_2_L ( cBD_AE z )) (fun z a => sigT_map_eq DC_4_2_L (HcBD_AE z a))
        (cAE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dD_3_2_L ( dB_2_1_L z ))
        (fun z => dC_3_2_L ( dB_2_1_L z )) dC_4_2_L dD_4_3_L
        (fun z a => DD_3_2_L (dB_2_1_L z) (DB_2_1_L z a))
        (fun z a => DC_3_2_L (dB_2_1_L z) (DB_2_1_L z a)) DC_4_2_L DD_4_3_L
        (fun z => cCD_ABE ( dB_2_1_L z )) (fun z a => HcCD_ABE (dB_2_1_L z) (DB_2_1_L z a))
        (cAE_nil x) eq_refl) (layer_square_nat_coherence_dep dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L
        dE_4_4_U DC_3_1_L DB_3_1_L DB_4_1_L DC_4_2_L (fun _ a => a) cBC_ADE HcBC_ADE
        (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cBE_AC (dD_1_1_U (dA_0_0_U x)))
        (cBC_AD (dD_1_1_U (dA_0_0_U x))) (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x))))
        (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) (hBCE_AD (dD_1_1_U (dA_0_0_U x))) eq_refl
        eq_refl eq_refl (HcBC_AD (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer)) eq_refl
        eq_refl (layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cBE_AC
          (dD_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x))) (cBE_ACD (dC_2_1_U (dD_1_1_U
          (dA_0_0_U x)))) (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) (cBC_ADE (dE_2_2_U (dD_1_1_U
          (dA_0_0_U x)))) (HcBC_ADE (dE_2_2_U (dD_1_1_U (dA_0_0_U x))) (DD_1_1_U
          (dA_0_0_U x) aA_layer)) (hBCE_AD (dD_1_1_U (dA_0_0_U x))))) (square_stack_dep _
        (square_map_dep dC_4_2_L DC_4_2_L ((layer_square _ _ _ DB_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x))
          (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U
          (dA_0_0_U x))) (cBD_AE (dE_1_1_U (dA_0_0_U x))) (HcBD_AE (dE_1_1_U (dA_0_0_U x)) aA_layer)
          (hBDE_A (dA_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U (fun _ a => a)
          DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl) (cBD_A (dA_0_0_U x))
          (HcBD_A (dA_0_0_U x) aA_layer))) (layer_square_nat_coherence_dep dD_3_2_L dC_3_2_L
        dC_4_2_L dD_4_3_L dE_4_4_U DD_3_2_L DC_3_2_L DC_4_2_L DD_4_3_L (fun _ a => a) cCD_ABE
        HcCD_ABE (cBE_A (dA_0_0_U x)) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
        (cCE_AB (dB_1_1_U (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x)))
        (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))) (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))
        (hCDE_AB (dB_1_1_U (dA_0_0_U x))) eq_refl eq_refl eq_refl
        (HcCD_AB (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)) eq_refl eq_refl
        (layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U
          (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x))) (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) (cCD_ABE (dE_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (HcCD_ABE (dE_2_2_U (dB_1_1_U (dA_0_0_U x))) (DB_1_1_U (dA_0_0_U x) aA_layer)) (hCDE_AB
          (dB_1_1_U (dA_0_0_U x)))))).

Local Definition Hhcube_ACD_B :=
  square_cube_change_faces_coherence_dep S0
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k =>
      (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
            (layer_square_map_source dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_BE dA_4_0_L
        dA_3_0_U dE_4_4_U cAE_BCD (cBE_nil x) (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x))
        (cCD_B (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
        (hCDE_B (dB_0_0_U x))) (layer_square_nat_source dC_2_1_L dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L
          dE_4_4_U cAD_BCE
          (cBE_nil x) (cCE_A (dB_0_0_U x)) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
          (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) (hADE_BC (dC_1_1_U (dB_0_0_U x)))))
            (layer_square_map_source dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L dE_3_3_U cAC_BE dD_4_3_L
          dD_3_3_U dE_4_4_U cDE_ABC (cBE_nil x) (cCE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x))
          (cAC_B (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (hACE_B (dB_0_0_U x))) (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k
            => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (layer_square_map_source dD_2_1_L dC_2_1_L dC_3_1_L
            dD_3_2_L dE_3_3_U cCD_BE dA_4_0_L
        dA_3_0_U dE_4_4_U cAE_BCD (cBE_nil x) (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x))
        (cCD_B (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
        (hCDE_B (dB_0_0_U x))) (layer_square_nat_source dC_2_1_L dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L
          dE_4_4_U cAD_BCE
          (cBE_nil x) (cCE_A (dB_0_0_U x)) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
          (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) (hADE_BC (dC_1_1_U (dB_0_0_U x))))
            (layer_square_map_source_coherence_dep dD_2_1_L dC_2_1_L
        dC_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L DC_2_1_L DC_3_1_L DD_3_2_L (fun _ a => a) cCD_BE
        HcCD_BE dA_4_0_L dA_3_0_U dE_4_4_U DA_4_0_L DA_3_0_U (fun _ a => a) cAE_BCD
        (fun _ _ => eq_refl) (cBE_nil x) (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x))
        (cCD_B (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
        (hCDE_B (dB_0_0_U x)) eq_refl eq_refl eq_refl (HcCD_B (dB_0_0_U x) aB_layer) eq_refl
        eq_refl (layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x)) (cCD_B
          (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x))) (cCD_BE
          (dE_1_1_U (dB_0_0_U x))) (HcCD_BE (dE_1_1_U (dB_0_0_U x)) aB_layer) (hCDE_B (dB_0_0_U x))))
            (layer_square_nat_source_coherence_dep dC_2_1_L dD_3_2_L dA_3_0_L
          dA_4_0_L dD_4_3_L dE_4_4_U DC_2_1_L DD_3_2_L DA_3_0_L DA_4_0_L DD_4_3_L (fun _ a => a)
          cAD_BCE HcAD_BCE (cBE_nil x) (cCE_A (dB_0_0_U x)) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
          (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) (hADE_BC (dC_1_1_U (dB_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcAD_BC (dC_1_1_U (dB_0_0_U x))
            (DC_1_1_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
          (layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB (dC_1_1_U (dB_0_0_U x))) (cAE_BC (dC_1_1_U
            (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x))) (cAE_BCD (dD_2_2_U (dC_1_1_U
            (dB_0_0_U x)))) (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) (cAD_BCE (dE_2_2_U (dC_1_1_U
            (dB_0_0_U x)))) (HcAD_BCE (dE_2_2_U (dC_1_1_U (dB_0_0_U x))) (DC_1_1_U
            (dB_0_0_U x) aB_layer)) (hADE_BC (dC_1_1_U (dB_0_0_U x))))))
            (layer_square_map_source_coherence_dep dC_2_1_L
          dA_2_0_L dA_3_0_L dC_3_2_L dE_3_3_U DC_2_1_L DA_2_0_L DA_3_0_L DC_3_2_L (fun _ a => a)
          cAC_BE HcAC_BE dD_4_3_L dD_3_3_U dE_4_4_U DD_4_3_L DD_3_3_U (fun _ a => a) cDE_ABC
          (fun _ _ => eq_refl) (cBE_nil x) (cCE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x))
          (cAC_B (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (hACE_B (dB_0_0_U x)) eq_refl eq_refl eq_refl (HcAC_B (dB_0_0_U x) aB_layer) eq_refl
          eq_refl (layer_square _ _ _ DA_3_0_L DC_3_2_L (cCE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x))
            (cAC_B (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
            (cAC_BE (dE_1_1_U (dB_0_0_U x))) (HcAC_BE (dE_1_1_U (dB_0_0_U x)) aB_layer) (hACE_B
            (dB_0_0_U x)))) ⊙
              square_nat_route_left_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
              (layer_cube_nat_side_coherence_dep dD_2_1_L dC_3_1_L dA_4_0_L DD_2_1_L DC_3_1_L DA_4_0_L
        (cBE_nil x) (cDE_A (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x)))
        (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dC_2_1_L dD_3_2_L dA_4_0_L DC_2_1_L DD_3_2_L DA_4_0_L
        (cBE_nil x) (cCE_A (dB_0_0_U x)) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
        (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dC_2_1_L dA_3_0_L dD_4_3_L DC_2_1_L DA_3_0_L DD_4_3_L
        (cBE_nil x) (cCE_A (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x)))
        (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dA_2_0_L dC_3_2_L dD_4_3_L DA_2_0_L DC_3_2_L DD_4_3_L
        (cBE_nil x) (cAE_B (dB_0_0_U x)) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
        (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (square_coherence_dep_fill (fun z => dC_3_1_L ( dD_2_1_L z ))
        (fun z => dD_3_2_L ( dC_2_1_L z )) dA_4_0_L dA_4_0_L
        (fun z a => DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a)) DA_4_0_L DA_4_0_L
        (fun z => f_equal dA_4_0_L ( cCD_BE z )) (fun z a => sigT_map_eq DA_4_0_L (HcCD_BE z a))
        (cBE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dD_3_2_L ( dC_2_1_L z ))
        (fun z => dA_3_0_L ( dC_2_1_L z )) dA_4_0_L dD_4_3_L
        (fun z a => DD_3_2_L (dC_2_1_L z) (DC_2_1_L z a))
        (fun z a => DA_3_0_L (dC_2_1_L z) (DC_2_1_L z a)) DA_4_0_L DD_4_3_L
        (fun z => cAD_BCE ( dC_2_1_L z )) (fun z a => HcAD_BCE (dC_2_1_L z) (DC_2_1_L z a))
        (cBE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dA_3_0_L ( dC_2_1_L z ))
        (fun z => dC_3_2_L ( dA_2_0_L z )) dD_4_3_L dD_4_3_L
        (fun z a => DA_3_0_L (dC_2_1_L z) (DC_2_1_L z a))
        (fun z a => DC_3_2_L (dA_2_0_L z) (DA_2_0_L z a)) DD_4_3_L DD_4_3_L
        (fun z => f_equal dD_4_3_L ( cAC_BE z )) (fun z a => sigT_map_eq DD_4_3_L (HcAC_BE z a))
        (cBE_nil x) eq_refl) (square_stack_dep _
        (square_map_dep dA_4_0_L DA_4_0_L ((layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dB_0_0_U x))
          (cCE_A (dB_0_0_U x)) (cCD_B (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U
          (dB_0_0_U x))) (cCD_BE (dE_1_1_U (dB_0_0_U x))) (HcCD_BE (dE_1_1_U (dB_0_0_U x)) aB_layer)
          (hCDE_B (dB_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a)
          DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl) (cCD_B (dB_0_0_U x))
          (HcCD_B (dB_0_0_U x) aB_layer))) (layer_square_nat_coherence_dep dD_3_2_L dA_3_0_L
        dA_4_0_L dD_4_3_L dE_4_4_U DD_3_2_L DA_3_0_L DA_4_0_L DD_4_3_L (fun _ a => a) cAD_BCE
        HcAD_BCE (cCE_A (dB_0_0_U x)) (cDE_AB (dC_1_1_U (dB_0_0_U x)))
        (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
        (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))) (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x))))
        (hADE_BC (dC_1_1_U (dB_0_0_U x))) eq_refl eq_refl eq_refl
        (HcAD_BC (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
        (layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB (dC_1_1_U (dB_0_0_U x))) (cAE_BC (dC_1_1_U
          (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x))) (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) (cAD_BCE (dE_2_2_U (dC_1_1_U (dB_0_0_U x))))
          (HcAD_BCE (dE_2_2_U (dC_1_1_U (dB_0_0_U x))) (DC_1_1_U (dB_0_0_U x) aB_layer)) (hADE_BC
          (dC_1_1_U (dB_0_0_U x))))) (square_stack_dep _
        (square_map_dep dD_4_3_L DD_4_3_L ((layer_square _ _ _ DA_3_0_L DC_3_2_L (cCE_A (dB_0_0_U x))
          (cAE_B (dB_0_0_U x)) (cAC_B (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U
          (dB_0_0_U x))) (cAC_BE (dE_1_1_U (dB_0_0_U x))) (HcAC_BE (dE_1_1_U (dB_0_0_U x)) aB_layer)
          (hACE_B (dB_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U (fun _ a => a)
          DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl) (cAC_B (dB_0_0_U x))
          (HcAC_B (dB_0_0_U x) aB_layer)))) Hraw_nat_ACD_B
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K)
      (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k))
      (layer_square_nat_source dD_2_1_L dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U cAC_BDE
        (cBE_nil x) (cDE_A (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x)))
        (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x)))
        (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))) (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x))))
        (hACE_BD (dD_1_1_U (dB_0_0_U x)))) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_map_source dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_BE dC_4_2_L
          dC_3_2_U dE_4_4_U cCE_ABD (cBE_nil x) (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x))
          (cAD_B (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
          (hADE_B (dB_0_0_U x))) (layer_square_nat_source dA_2_0_L dD_3_2_L dC_3_2_L dC_4_2_L
          dD_4_3_L dE_4_4_U cCD_ABE (cBE_nil x) (cAE_B (dB_0_0_U x))
          (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (cCD_AB (dA_1_0_U (dB_0_0_U x))) (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) (hCDE_AB (dA_1_0_U (dB_0_0_U x)))))
      (layer_square_nat_source_coherence_dep dD_2_1_L dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U
        DD_2_1_L DC_3_1_L DA_3_0_L DA_4_0_L DC_4_2_L (fun _ a => a) cAC_BDE HcAC_BDE (cBE_nil x)
        (cDE_A (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cAE_BC (dD_1_1_U (dB_0_0_U x)))
        (cAC_BD (dD_1_1_U (dB_0_0_U x))) (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x))))
        (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) (hACE_BD (dD_1_1_U (dB_0_0_U x))) eq_refl
        eq_refl eq_refl eq_refl (HcAC_BD (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer))
        eq_refl eq_refl (layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cAE_BC
          (dD_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x))) (cAE_BCD (dC_2_1_U (dD_1_1_U
          (dB_0_0_U x)))) (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) (cAC_BDE (dE_2_2_U (dD_1_1_U
          (dB_0_0_U x)))) (HcAC_BDE (dE_2_2_U (dD_1_1_U (dB_0_0_U x))) (DD_1_1_U
          (dB_0_0_U x) aB_layer)) (hACE_BD (dD_1_1_U (dB_0_0_U x))))) (path_map2_dep
        (fun H K => square_compose_map dE_4_4_U H K)
        (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
            (fun _ a => a) (H := H) (K := K) h k))
        (layer_square_map_source dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_BE dC_4_2_L
          dC_3_2_U dE_4_4_U cCE_ABD (cBE_nil x) (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x))
          (cAD_B (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
          (hADE_B (dB_0_0_U x))) (layer_square_nat_source dA_2_0_L dD_3_2_L dC_3_2_L dC_4_2_L
          dD_4_3_L dE_4_4_U cCD_ABE (cBE_nil x) (cAE_B (dB_0_0_U x))
          (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (cCD_AB (dA_1_0_U (dB_0_0_U x))) (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) (hCDE_AB (dA_1_0_U (dB_0_0_U x))))
        (layer_square_map_source_coherence_dep dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U
          DD_2_1_L DA_2_0_L DA_3_0_L DD_3_2_L (fun _ a => a) cAD_BE HcAD_BE dC_4_2_L dC_3_2_U
          dE_4_4_U DC_4_2_L DC_3_2_U (fun _ a => a) cCE_ABD (fun _ _ => eq_refl) (cBE_nil x)
          (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x))
          (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x))) (hADE_B (dB_0_0_U x))
          eq_refl eq_refl eq_refl (HcAD_B (dB_0_0_U x) aB_layer) eq_refl eq_refl
          (layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B
            (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cAD_BE
            (dE_1_1_U (dB_0_0_U x))) (HcAD_BE (dE_1_1_U (dB_0_0_U x)) aB_layer) (hADE_B (dB_0_0_U x))))
            (layer_square_nat_source_coherence_dep dA_2_0_L dD_3_2_L
          dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U DA_2_0_L DD_3_2_L DC_3_2_L DC_4_2_L DD_4_3_L
          (fun _ a => a) cCD_ABE HcCD_ABE (cBE_nil x) (cAE_B (dB_0_0_U x))
          (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (cCD_AB (dA_1_0_U (dB_0_0_U x))) (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) (hCDE_AB (dA_1_0_U (dB_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcCD_AB (dA_1_0_U (dB_0_0_U x))
            (DA_1_0_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
          (layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U
            (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x))) (cCE_ABD (dD_2_2_U (dA_1_0_U
            (dB_0_0_U x)))) (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) (cCD_ABE (dE_2_2_U (dA_1_0_U
            (dB_0_0_U x)))) (HcCD_ABE (dE_2_2_U (dA_1_0_U (dB_0_0_U x))) (DA_1_0_U
            (dB_0_0_U x) aB_layer)) (hCDE_AB (dA_1_0_U
            (dB_0_0_U x)))))) ⊙ square_nat_route_coherence_dep dE_4_4_U S0
      (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
      (layer_cube_nat_side_coherence_dep dD_2_1_L dC_3_1_L dA_4_0_L DD_2_1_L DC_3_1_L DA_4_0_L
        (cBE_nil x) (cDE_A (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x)))
        (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dD_2_1_L dA_3_0_L dC_4_2_L DD_2_1_L DA_3_0_L DC_4_2_L
        (cBE_nil x) (cDE_A (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x)))
        (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dA_2_0_L dD_3_2_L dC_4_2_L DA_2_0_L DD_3_2_L DC_4_2_L
        (cBE_nil x) (cAE_B (dB_0_0_U x)) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
        (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dA_2_0_L dC_3_2_L dD_4_3_L DA_2_0_L DC_3_2_L DD_4_3_L
        (cBE_nil x) (cAE_B (dB_0_0_U x)) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
        (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (square_coherence_dep_fill (fun z => dC_3_1_L ( dD_2_1_L z ))
        (fun z => dA_3_0_L ( dD_2_1_L z )) dA_4_0_L dC_4_2_L
        (fun z a => DC_3_1_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a)) DA_4_0_L DC_4_2_L
        (fun z => cAC_BDE ( dD_2_1_L z )) (fun z a => HcAC_BDE (dD_2_1_L z) (DD_2_1_L z a))
        (cBE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dA_3_0_L ( dD_2_1_L z ))
        (fun z => dD_3_2_L ( dA_2_0_L z )) dC_4_2_L dC_4_2_L
        (fun z a => DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a)) DC_4_2_L DC_4_2_L
        (fun z => f_equal dC_4_2_L ( cAD_BE z )) (fun z a => sigT_map_eq DC_4_2_L (HcAD_BE z a))
        (cBE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dD_3_2_L ( dA_2_0_L z ))
        (fun z => dC_3_2_L ( dA_2_0_L z )) dC_4_2_L dD_4_3_L
        (fun z a => DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a))
        (fun z a => DC_3_2_L (dA_2_0_L z) (DA_2_0_L z a)) DC_4_2_L DD_4_3_L
        (fun z => cCD_ABE ( dA_2_0_L z )) (fun z a => HcCD_ABE (dA_2_0_L z) (DA_2_0_L z a))
        (cBE_nil x) eq_refl) (layer_square_nat_coherence_dep dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L
        dE_4_4_U DC_3_1_L DA_3_0_L DA_4_0_L DC_4_2_L (fun _ a => a) cAC_BDE HcAC_BDE
        (cDE_A (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cAE_BC (dD_1_1_U (dB_0_0_U x)))
        (cAC_BD (dD_1_1_U (dB_0_0_U x))) (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x))))
        (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) (hACE_BD (dD_1_1_U (dB_0_0_U x))) eq_refl
        eq_refl eq_refl (HcAC_BD (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer)) eq_refl
        eq_refl (layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cAE_BC
          (dD_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x))) (cAE_BCD (dC_2_1_U (dD_1_1_U
          (dB_0_0_U x)))) (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) (cAC_BDE (dE_2_2_U (dD_1_1_U
          (dB_0_0_U x)))) (HcAC_BDE (dE_2_2_U (dD_1_1_U (dB_0_0_U x))) (DD_1_1_U
          (dB_0_0_U x) aB_layer)) (hACE_BD (dD_1_1_U (dB_0_0_U x))))) (square_stack_dep _
        (square_map_dep dC_4_2_L DC_4_2_L ((layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dB_0_0_U x))
          (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U
          (dB_0_0_U x))) (cAD_BE (dE_1_1_U (dB_0_0_U x))) (HcAD_BE (dE_1_1_U (dB_0_0_U x)) aB_layer)
          (hADE_B (dB_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U (fun _ a => a)
          DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl) (cAD_B (dB_0_0_U x))
          (HcAD_B (dB_0_0_U x) aB_layer))) (layer_square_nat_coherence_dep dD_3_2_L dC_3_2_L
        dC_4_2_L dD_4_3_L dE_4_4_U DD_3_2_L DC_3_2_L DC_4_2_L DD_4_3_L (fun _ a => a) cCD_ABE
        HcCD_ABE (cAE_B (dB_0_0_U x)) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
        (cCE_AB (dA_1_0_U (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x)))
        (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))) (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x))))
        (hCDE_AB (dA_1_0_U (dB_0_0_U x))) eq_refl eq_refl eq_refl
        (HcCD_AB (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer)) eq_refl eq_refl
        (layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U
          (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x))) (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) (cCD_ABE (dE_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (HcCD_ABE (dE_2_2_U (dA_1_0_U (dB_0_0_U x))) (DA_1_0_U (dB_0_0_U x) aB_layer)) (hCDE_AB
          (dA_1_0_U (dB_0_0_U x)))))).

Local Definition Hhcube_ABD_C :=
  square_cube_change_faces_coherence_dep S0
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k =>
      (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
            (layer_square_map_source dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L dE_3_3_U cBD_CE dA_4_0_L
        dA_3_0_U dE_4_4_U cAE_BCD (cCE_nil x) (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x))
        (cBD_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
        (hBDE_C (dC_0_0_U x))) (layer_square_nat_source dB_2_0_L dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L
          dE_4_4_U cAD_BCE
          (cCE_nil x) (cBE_C (dC_0_0_U x)) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
          (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) (hADE_BC (dB_1_0_U (dC_0_0_U x)))))
            (layer_square_map_source dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_CE dD_4_3_L
          dD_3_3_U dE_4_4_U cDE_ABC (cCE_nil x) (cBE_C (dC_0_0_U x)) (cAE_B (dC_0_0_U x))
          (cAB_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (hABE_C (dC_0_0_U x))) (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k
            => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (layer_square_map_source dD_2_1_L dB_2_0_L dB_3_0_L
            dD_3_2_L dE_3_3_U cBD_CE dA_4_0_L
        dA_3_0_U dE_4_4_U cAE_BCD (cCE_nil x) (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x))
        (cBD_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
        (hBDE_C (dC_0_0_U x))) (layer_square_nat_source dB_2_0_L dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L
          dE_4_4_U cAD_BCE
          (cCE_nil x) (cBE_C (dC_0_0_U x)) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
          (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) (hADE_BC (dB_1_0_U (dC_0_0_U x))))
            (layer_square_map_source_coherence_dep dD_2_1_L dB_2_0_L
        dB_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L DB_2_0_L DB_3_0_L DD_3_2_L (fun _ a => a) cBD_CE
        HcBD_CE dA_4_0_L dA_3_0_U dE_4_4_U DA_4_0_L DA_3_0_U (fun _ a => a) cAE_BCD
        (fun _ _ => eq_refl) (cCE_nil x) (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x))
        (cBD_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
        (hBDE_C (dC_0_0_U x)) eq_refl eq_refl eq_refl (HcBD_C (dC_0_0_U x) aC_layer) eq_refl
        eq_refl (layer_square _ _ _ DB_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cBD_C
          (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x))) (cBD_CE
          (dE_1_1_U (dC_0_0_U x))) (HcBD_CE (dE_1_1_U (dC_0_0_U x)) aC_layer) (hBDE_C (dC_0_0_U x))))
            (layer_square_nat_source_coherence_dep dB_2_0_L dD_3_2_L dA_3_0_L
          dA_4_0_L dD_4_3_L dE_4_4_U DB_2_0_L DD_3_2_L DA_3_0_L DA_4_0_L DD_4_3_L (fun _ a => a)
          cAD_BCE HcAD_BCE (cCE_nil x) (cBE_C (dC_0_0_U x)) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
          (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) (hADE_BC (dB_1_0_U (dC_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcAD_BC (dB_1_0_U (dC_0_0_U x))
            (DB_1_0_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
          (layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB (dB_1_0_U (dC_0_0_U x))) (cAE_BC (dB_1_0_U
            (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x))) (cAE_BCD (dD_2_2_U (dB_1_0_U
            (dC_0_0_U x)))) (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) (cAD_BCE (dE_2_2_U (dB_1_0_U
            (dC_0_0_U x)))) (HcAD_BCE (dE_2_2_U (dB_1_0_U (dC_0_0_U x))) (DB_1_0_U
            (dC_0_0_U x) aC_layer)) (hADE_BC (dB_1_0_U (dC_0_0_U x))))))
            (layer_square_map_source_coherence_dep dB_2_0_L
          dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U DB_2_0_L DA_2_0_L DA_3_0_L DB_3_1_L (fun _ a => a)
          cAB_CE HcAB_CE dD_4_3_L dD_3_3_U dE_4_4_U DD_4_3_L DD_3_3_U (fun _ a => a) cDE_ABC
          (fun _ _ => eq_refl) (cCE_nil x) (cBE_C (dC_0_0_U x)) (cAE_B (dC_0_0_U x))
          (cAB_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (hABE_C (dC_0_0_U x)) eq_refl eq_refl eq_refl (HcAB_C (dC_0_0_U x) aC_layer) eq_refl
          eq_refl (layer_square _ _ _ DA_3_0_L DB_3_1_L (cBE_C (dC_0_0_U x)) (cAE_B (dC_0_0_U x))
            (cAB_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
            (cAB_CE (dE_1_1_U (dC_0_0_U x))) (HcAB_CE (dE_1_1_U (dC_0_0_U x)) aC_layer) (hABE_C
            (dC_0_0_U x)))) ⊙
              square_nat_route_left_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
              (layer_cube_nat_side_coherence_dep dD_2_1_L dB_3_0_L dA_4_0_L DD_2_1_L DB_3_0_L DA_4_0_L
        (cCE_nil x) (cDE_A (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
        (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dB_2_0_L dD_3_2_L dA_4_0_L DB_2_0_L DD_3_2_L DA_4_0_L
        (cCE_nil x) (cBE_C (dC_0_0_U x)) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
        (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dB_2_0_L dA_3_0_L dD_4_3_L DB_2_0_L DA_3_0_L DD_4_3_L
        (cCE_nil x) (cBE_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x)))
        (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dA_2_0_L dB_3_1_L dD_4_3_L DA_2_0_L DB_3_1_L DD_4_3_L
        (cCE_nil x) (cAE_B (dC_0_0_U x)) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
        (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (square_coherence_dep_fill (fun z => dB_3_0_L ( dD_2_1_L z ))
        (fun z => dD_3_2_L ( dB_2_0_L z )) dA_4_0_L dA_4_0_L
        (fun z a => DB_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DD_3_2_L (dB_2_0_L z) (DB_2_0_L z a)) DA_4_0_L DA_4_0_L
        (fun z => f_equal dA_4_0_L ( cBD_CE z )) (fun z a => sigT_map_eq DA_4_0_L (HcBD_CE z a))
        (cCE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dD_3_2_L ( dB_2_0_L z ))
        (fun z => dA_3_0_L ( dB_2_0_L z )) dA_4_0_L dD_4_3_L
        (fun z a => DD_3_2_L (dB_2_0_L z) (DB_2_0_L z a))
        (fun z a => DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a)) DA_4_0_L DD_4_3_L
        (fun z => cAD_BCE ( dB_2_0_L z )) (fun z a => HcAD_BCE (dB_2_0_L z) (DB_2_0_L z a))
        (cCE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dA_3_0_L ( dB_2_0_L z ))
        (fun z => dB_3_1_L ( dA_2_0_L z )) dD_4_3_L dD_4_3_L
        (fun z a => DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a))
        (fun z a => DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a)) DD_4_3_L DD_4_3_L
        (fun z => f_equal dD_4_3_L ( cAB_CE z )) (fun z a => sigT_map_eq DD_4_3_L (HcAB_CE z a))
        (cCE_nil x) eq_refl) (square_stack_dep _
        (square_map_dep dA_4_0_L DA_4_0_L ((layer_square _ _ _ DB_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x))
          (cBE_C (dC_0_0_U x)) (cBD_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U
          (dC_0_0_U x))) (cBD_CE (dE_1_1_U (dC_0_0_U x))) (HcBD_CE (dE_1_1_U (dC_0_0_U x)) aC_layer)
          (hBDE_C (dC_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a)
          DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl) (cBD_C (dC_0_0_U x))
          (HcBD_C (dC_0_0_U x) aC_layer))) (layer_square_nat_coherence_dep dD_3_2_L dA_3_0_L
        dA_4_0_L dD_4_3_L dE_4_4_U DD_3_2_L DA_3_0_L DA_4_0_L DD_4_3_L (fun _ a => a) cAD_BCE
        HcAD_BCE (cBE_C (dC_0_0_U x)) (cDE_AB (dB_1_0_U (dC_0_0_U x)))
        (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
        (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))) (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x))))
        (hADE_BC (dB_1_0_U (dC_0_0_U x))) eq_refl eq_refl eq_refl
        (HcAD_BC (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
        (layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB (dB_1_0_U (dC_0_0_U x))) (cAE_BC (dB_1_0_U
          (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x))) (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) (cAD_BCE (dE_2_2_U (dB_1_0_U (dC_0_0_U x))))
          (HcAD_BCE (dE_2_2_U (dB_1_0_U (dC_0_0_U x))) (DB_1_0_U (dC_0_0_U x) aC_layer)) (hADE_BC
          (dB_1_0_U (dC_0_0_U x))))) (square_stack_dep _
        (square_map_dep dD_4_3_L DD_4_3_L ((layer_square _ _ _ DA_3_0_L DB_3_1_L (cBE_C (dC_0_0_U x))
          (cAE_B (dC_0_0_U x)) (cAB_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U
          (dC_0_0_U x))) (cAB_CE (dE_1_1_U (dC_0_0_U x))) (HcAB_CE (dE_1_1_U (dC_0_0_U x)) aC_layer)
          (hABE_C (dC_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U (fun _ a => a)
          DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl) (cAB_C (dC_0_0_U x))
          (HcAB_C (dC_0_0_U x) aC_layer)))) Hraw_nat_ABD_C
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K)
      (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k))
      (layer_square_nat_source dD_2_1_L dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U cAB_CDE
        (cCE_nil x) (cDE_A (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
        (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x)))
        (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))) (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x))))
        (hABE_CD (dD_1_1_U (dC_0_0_U x)))) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_map_source dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_CE dB_4_1_L
          dB_3_1_U dE_4_4_U cBE_ACD (cCE_nil x) (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x))
          (cAD_C (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x)))
          (hADE_C (dC_0_0_U x))) (layer_square_nat_source dA_2_0_L dD_3_2_L dB_3_1_L dB_4_1_L
          dD_4_3_L dE_4_4_U cBD_ACE (cCE_nil x) (cAE_B (dC_0_0_U x))
          (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (cBD_AC (dA_1_0_U (dC_0_0_U x))) (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) (hBDE_AC (dA_1_0_U (dC_0_0_U x)))))
      (layer_square_nat_source_coherence_dep dD_2_1_L dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U
        DD_2_1_L DB_3_0_L DA_3_0_L DA_4_0_L DB_4_1_L (fun _ a => a) cAB_CDE HcAB_CDE (cCE_nil x)
        (cDE_A (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BC (dD_1_1_U (dC_0_0_U x)))
        (cAB_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x))))
        (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) (hABE_CD (dD_1_1_U (dC_0_0_U x))) eq_refl
        eq_refl eq_refl eq_refl (HcAB_CD (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer))
        eq_refl eq_refl (layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BC
          (dD_1_1_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BCD (dB_2_0_U (dD_1_1_U
          (dC_0_0_U x)))) (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) (cAB_CDE (dE_2_2_U (dD_1_1_U
          (dC_0_0_U x)))) (HcAB_CDE (dE_2_2_U (dD_1_1_U (dC_0_0_U x))) (DD_1_1_U
          (dC_0_0_U x) aC_layer)) (hABE_CD (dD_1_1_U (dC_0_0_U x))))) (path_map2_dep
        (fun H K => square_compose_map dE_4_4_U H K)
        (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
            (fun _ a => a) (H := H) (K := K) h k))
        (layer_square_map_source dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_CE dB_4_1_L
          dB_3_1_U dE_4_4_U cBE_ACD (cCE_nil x) (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x))
          (cAD_C (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x)))
          (hADE_C (dC_0_0_U x))) (layer_square_nat_source dA_2_0_L dD_3_2_L dB_3_1_L dB_4_1_L
          dD_4_3_L dE_4_4_U cBD_ACE (cCE_nil x) (cAE_B (dC_0_0_U x))
          (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (cBD_AC (dA_1_0_U (dC_0_0_U x))) (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) (hBDE_AC (dA_1_0_U (dC_0_0_U x))))
        (layer_square_map_source_coherence_dep dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U
          DD_2_1_L DA_2_0_L DA_3_0_L DD_3_2_L (fun _ a => a) cAD_CE HcAD_CE dB_4_1_L dB_3_1_U
          dE_4_4_U DB_4_1_L DB_3_1_U (fun _ a => a) cBE_ACD (fun _ _ => eq_refl) (cCE_nil x)
          (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cAD_C (dC_0_0_U x))
          (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x))) (hADE_C (dC_0_0_U x))
          eq_refl eq_refl eq_refl (HcAD_C (dC_0_0_U x) aC_layer) eq_refl eq_refl
          (layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cAD_C
            (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cAD_CE
            (dE_1_1_U (dC_0_0_U x))) (HcAD_CE (dE_1_1_U (dC_0_0_U x)) aC_layer) (hADE_C (dC_0_0_U x))))
            (layer_square_nat_source_coherence_dep dA_2_0_L dD_3_2_L
          dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U DA_2_0_L DD_3_2_L DB_3_1_L DB_4_1_L DD_4_3_L
          (fun _ a => a) cBD_ACE HcBD_ACE (cCE_nil x) (cAE_B (dC_0_0_U x))
          (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (cBD_AC (dA_1_0_U (dC_0_0_U x))) (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) (hBDE_AC (dA_1_0_U (dC_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcBD_AC (dA_1_0_U (dC_0_0_U x))
            (DA_1_0_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
          (layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U
            (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x))) (cBE_ACD (dD_2_2_U (dA_1_0_U
            (dC_0_0_U x)))) (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) (cBD_ACE (dE_2_2_U (dA_1_0_U
            (dC_0_0_U x)))) (HcBD_ACE (dE_2_2_U (dA_1_0_U (dC_0_0_U x))) (DA_1_0_U
            (dC_0_0_U x) aC_layer)) (hBDE_AC (dA_1_0_U
            (dC_0_0_U x)))))) ⊙ square_nat_route_coherence_dep dE_4_4_U S0
      (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
      (layer_cube_nat_side_coherence_dep dD_2_1_L dB_3_0_L dA_4_0_L DD_2_1_L DB_3_0_L DA_4_0_L
        (cCE_nil x) (cDE_A (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
        (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dD_2_1_L dA_3_0_L dB_4_1_L DD_2_1_L DA_3_0_L DB_4_1_L
        (cCE_nil x) (cDE_A (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x)))
        (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dA_2_0_L dD_3_2_L dB_4_1_L DA_2_0_L DD_3_2_L DB_4_1_L
        (cCE_nil x) (cAE_B (dC_0_0_U x)) (cDE_AB (dA_1_0_U (dC_0_0_U x)))
        (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dA_2_0_L dB_3_1_L dD_4_3_L DA_2_0_L DB_3_1_L DD_4_3_L
        (cCE_nil x) (cAE_B (dC_0_0_U x)) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
        (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (square_coherence_dep_fill (fun z => dB_3_0_L ( dD_2_1_L z ))
        (fun z => dA_3_0_L ( dD_2_1_L z )) dA_4_0_L dB_4_1_L
        (fun z a => DB_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a)) DA_4_0_L DB_4_1_L
        (fun z => cAB_CDE ( dD_2_1_L z )) (fun z a => HcAB_CDE (dD_2_1_L z) (DD_2_1_L z a))
        (cCE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dA_3_0_L ( dD_2_1_L z ))
        (fun z => dD_3_2_L ( dA_2_0_L z )) dB_4_1_L dB_4_1_L
        (fun z a => DA_3_0_L (dD_2_1_L z) (DD_2_1_L z a))
        (fun z a => DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a)) DB_4_1_L DB_4_1_L
        (fun z => f_equal dB_4_1_L ( cAD_CE z )) (fun z a => sigT_map_eq DB_4_1_L (HcAD_CE z a))
        (cCE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dD_3_2_L ( dA_2_0_L z ))
        (fun z => dB_3_1_L ( dA_2_0_L z )) dB_4_1_L dD_4_3_L
        (fun z a => DD_3_2_L (dA_2_0_L z) (DA_2_0_L z a))
        (fun z a => DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a)) DB_4_1_L DD_4_3_L
        (fun z => cBD_ACE ( dA_2_0_L z )) (fun z a => HcBD_ACE (dA_2_0_L z) (DA_2_0_L z a))
        (cCE_nil x) eq_refl) (layer_square_nat_coherence_dep dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L
        dE_4_4_U DB_3_0_L DA_3_0_L DA_4_0_L DB_4_1_L (fun _ a => a) cAB_CDE HcAB_CDE
        (cDE_A (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BC (dD_1_1_U (dC_0_0_U x)))
        (cAB_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x))))
        (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) (hABE_CD (dD_1_1_U (dC_0_0_U x))) eq_refl
        eq_refl eq_refl (HcAB_CD (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer)) eq_refl
        eq_refl (layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BC
          (dD_1_1_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x))) (cAE_BCD (dB_2_0_U (dD_1_1_U
          (dC_0_0_U x)))) (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) (cAB_CDE (dE_2_2_U (dD_1_1_U
          (dC_0_0_U x)))) (HcAB_CDE (dE_2_2_U (dD_1_1_U (dC_0_0_U x))) (DD_1_1_U
          (dC_0_0_U x) aC_layer)) (hABE_CD (dD_1_1_U (dC_0_0_U x))))) (square_stack_dep _
        (square_map_dep dB_4_1_L DB_4_1_L ((layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x))
          (cAE_B (dC_0_0_U x)) (cAD_C (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U
          (dC_0_0_U x))) (cAD_CE (dE_1_1_U (dC_0_0_U x))) (HcAD_CE (dE_1_1_U (dC_0_0_U x)) aC_layer)
          (hADE_C (dC_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U (fun _ a => a)
          DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl) (cAD_C (dC_0_0_U x))
          (HcAD_C (dC_0_0_U x) aC_layer))) (layer_square_nat_coherence_dep dD_3_2_L dB_3_1_L
        dB_4_1_L dD_4_3_L dE_4_4_U DD_3_2_L DB_3_1_L DB_4_1_L DD_4_3_L (fun _ a => a) cBD_ACE
        HcBD_ACE (cAE_B (dC_0_0_U x)) (cDE_AB (dA_1_0_U (dC_0_0_U x)))
        (cBE_AC (dA_1_0_U (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x)))
        (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))) (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x))))
        (hBDE_AC (dA_1_0_U (dC_0_0_U x))) eq_refl eq_refl eq_refl
        (HcBD_AC (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer)) eq_refl eq_refl
        (layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U
          (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x))) (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) (cBD_ACE (dE_2_2_U (dA_1_0_U (dC_0_0_U x))))
          (HcBD_ACE (dE_2_2_U (dA_1_0_U (dC_0_0_U x))) (DA_1_0_U (dC_0_0_U x) aC_layer)) (hBDE_AC
          (dA_1_0_U (dC_0_0_U x)))))).

Local Definition Hhcube_ABC_D :=
  square_cube_change_faces_coherence_dep S0
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k =>
      (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
            (layer_square_map_source dC_2_0_L dB_2_0_L dB_3_0_L dC_3_1_L dE_3_3_U cBC_DE dA_4_0_L
        dA_3_0_U dE_4_4_U cAE_BCD (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_C (dD_0_0_U x))
        (cBC_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
        (hBCE_D (dD_0_0_U x))) (layer_square_nat_source dB_2_0_L dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L
          dE_4_4_U cAC_BDE
          (cDE_nil x) (cBE_C (dD_0_0_U x)) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) (hACE_BD (dB_1_0_U (dD_0_0_U x)))))
            (layer_square_map_source dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_DE dC_4_2_L
          dC_3_2_U dE_4_4_U cCE_ABD (cDE_nil x) (cBE_C (dD_0_0_U x)) (cAE_B (dD_0_0_U x))
          (cAB_D (dD_0_0_U x)) (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
          (hABE_D (dD_0_0_U x))) (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K) (fun H K h k
            => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k)) (layer_square_map_source dC_2_0_L dB_2_0_L dB_3_0_L
            dC_3_1_L dE_3_3_U cBC_DE dA_4_0_L
        dA_3_0_U dE_4_4_U cAE_BCD (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_C (dD_0_0_U x))
        (cBC_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
        (hBCE_D (dD_0_0_U x))) (layer_square_nat_source dB_2_0_L dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L
          dE_4_4_U cAC_BDE
          (cDE_nil x) (cBE_C (dD_0_0_U x)) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) (hACE_BD (dB_1_0_U (dD_0_0_U x))))
            (layer_square_map_source_coherence_dep dC_2_0_L dB_2_0_L
        dB_3_0_L dC_3_1_L dE_3_3_U DC_2_0_L DB_2_0_L DB_3_0_L DC_3_1_L (fun _ a => a) cBC_DE
        HcBC_DE dA_4_0_L dA_3_0_U dE_4_4_U DA_4_0_L DA_3_0_U (fun _ a => a) cAE_BCD
        (fun _ _ => eq_refl) (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_C (dD_0_0_U x))
        (cBC_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
        (hBCE_D (dD_0_0_U x)) eq_refl eq_refl eq_refl (HcBC_D (dD_0_0_U x) aD_layer) eq_refl
        eq_refl (layer_square _ _ _ DB_3_0_L DC_3_1_L (cCE_D (dD_0_0_U x)) (cBE_C (dD_0_0_U x)) (cBC_D
          (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dB_1_0_U (dD_0_0_U x))) (cBC_DE
          (dE_1_1_U (dD_0_0_U x))) (HcBC_DE (dE_1_1_U (dD_0_0_U x)) aD_layer) (hBCE_D (dD_0_0_U x))))
            (layer_square_nat_source_coherence_dep dB_2_0_L dC_3_1_L dA_3_0_L
          dA_4_0_L dC_4_2_L dE_4_4_U DB_2_0_L DC_3_1_L DA_3_0_L DA_4_0_L DC_4_2_L (fun _ a => a)
          cAC_BDE HcAC_BDE (cDE_nil x) (cBE_C (dD_0_0_U x)) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) (hACE_BD (dB_1_0_U (dD_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcAC_BD (dB_1_0_U (dD_0_0_U x))
            (DB_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
          (layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD (dB_1_0_U (dD_0_0_U x))) (cAE_BC (dB_1_0_U
            (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x))) (cAE_BCD (dC_2_1_U (dB_1_0_U
            (dD_0_0_U x)))) (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) (cAC_BDE (dE_2_2_U (dB_1_0_U
            (dD_0_0_U x)))) (HcAC_BDE (dE_2_2_U (dB_1_0_U (dD_0_0_U x))) (DB_1_0_U
            (dD_0_0_U x) aD_layer)) (hACE_BD (dB_1_0_U (dD_0_0_U x))))))
            (layer_square_map_source_coherence_dep dB_2_0_L
          dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U DB_2_0_L DA_2_0_L DA_3_0_L DB_3_1_L (fun _ a => a)
          cAB_DE HcAB_DE dC_4_2_L dC_3_2_U dE_4_4_U DC_4_2_L DC_3_2_U (fun _ a => a) cCE_ABD
          (fun _ _ => eq_refl) (cDE_nil x) (cBE_C (dD_0_0_U x)) (cAE_B (dD_0_0_U x))
          (cAB_D (dD_0_0_U x)) (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
          (hABE_D (dD_0_0_U x)) eq_refl eq_refl eq_refl (HcAB_D (dD_0_0_U x) aD_layer) eq_refl
          eq_refl (layer_square _ _ _ DA_3_0_L DB_3_1_L (cBE_C (dD_0_0_U x)) (cAE_B (dD_0_0_U x))
            (cAB_D (dD_0_0_U x)) (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
            (cAB_DE (dE_1_1_U (dD_0_0_U x))) (HcAB_DE (dE_1_1_U (dD_0_0_U x)) aD_layer) (hABE_D
            (dD_0_0_U x)))) ⊙
              square_nat_route_left_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
              (layer_cube_nat_side_coherence_dep dC_2_0_L dB_3_0_L dA_4_0_L DC_2_0_L DB_3_0_L DA_4_0_L
        (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
        (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dB_2_0_L dC_3_1_L dA_4_0_L DB_2_0_L DC_3_1_L DA_4_0_L
        (cDE_nil x) (cBE_C (dD_0_0_U x)) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
        (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dB_2_0_L dA_3_0_L dC_4_2_L DB_2_0_L DA_3_0_L DC_4_2_L
        (cDE_nil x) (cBE_C (dD_0_0_U x)) (cAE_BC (dB_1_0_U (dD_0_0_U x)))
        (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (layer_cube_nat_side_coherence_dep dA_2_0_L dB_3_1_L dC_4_2_L DA_2_0_L DB_3_1_L DC_4_2_L
        (cDE_nil x) (cAE_B (dD_0_0_U x)) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
        (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
          (square_coherence_dep_fill (fun z => dB_3_0_L ( dC_2_0_L z ))
        (fun z => dC_3_1_L ( dB_2_0_L z )) dA_4_0_L dA_4_0_L
        (fun z a => DB_3_0_L (dC_2_0_L z) (DC_2_0_L z a))
        (fun z a => DC_3_1_L (dB_2_0_L z) (DB_2_0_L z a)) DA_4_0_L DA_4_0_L
        (fun z => f_equal dA_4_0_L ( cBC_DE z )) (fun z a => sigT_map_eq DA_4_0_L (HcBC_DE z a))
        (cDE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dC_3_1_L ( dB_2_0_L z ))
        (fun z => dA_3_0_L ( dB_2_0_L z )) dA_4_0_L dC_4_2_L
        (fun z a => DC_3_1_L (dB_2_0_L z) (DB_2_0_L z a))
        (fun z a => DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a)) DA_4_0_L DC_4_2_L
        (fun z => cAC_BDE ( dB_2_0_L z )) (fun z a => HcAC_BDE (dB_2_0_L z) (DB_2_0_L z a))
        (cDE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dA_3_0_L ( dB_2_0_L z ))
        (fun z => dB_3_1_L ( dA_2_0_L z )) dC_4_2_L dC_4_2_L
        (fun z a => DA_3_0_L (dB_2_0_L z) (DB_2_0_L z a))
        (fun z a => DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a)) DC_4_2_L DC_4_2_L
        (fun z => f_equal dC_4_2_L ( cAB_DE z )) (fun z a => sigT_map_eq DC_4_2_L (HcAB_DE z a))
        (cDE_nil x) eq_refl) (square_stack_dep _
        (square_map_dep dA_4_0_L DA_4_0_L ((layer_square _ _ _ DB_3_0_L DC_3_1_L (cCE_D (dD_0_0_U x))
          (cBE_C (dD_0_0_U x)) (cBC_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dB_1_0_U
          (dD_0_0_U x))) (cBC_DE (dE_1_1_U (dD_0_0_U x))) (HcBC_DE (dE_1_1_U (dD_0_0_U x)) aD_layer)
          (hBCE_D (dD_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a)
          DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl) (cBC_D (dD_0_0_U x))
          (HcBC_D (dD_0_0_U x) aD_layer))) (layer_square_nat_coherence_dep dC_3_1_L dA_3_0_L
        dA_4_0_L dC_4_2_L dE_4_4_U DC_3_1_L DA_3_0_L DA_4_0_L DC_4_2_L (fun _ a => a) cAC_BDE
        HcAC_BDE (cBE_C (dD_0_0_U x)) (cCE_AD (dB_1_0_U (dD_0_0_U x)))
        (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
        (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))) (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x))))
        (hACE_BD (dB_1_0_U (dD_0_0_U x))) eq_refl eq_refl eq_refl
        (HcAC_BD (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
        (layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD (dB_1_0_U (dD_0_0_U x))) (cAE_BC (dB_1_0_U
          (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x))) (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) (cAC_BDE (dE_2_2_U (dB_1_0_U (dD_0_0_U x))))
          (HcAC_BDE (dE_2_2_U (dB_1_0_U (dD_0_0_U x))) (DB_1_0_U (dD_0_0_U x) aD_layer)) (hACE_BD
          (dB_1_0_U (dD_0_0_U x))))) (square_stack_dep _
        (square_map_dep dC_4_2_L DC_4_2_L ((layer_square _ _ _ DA_3_0_L DB_3_1_L (cBE_C (dD_0_0_U x))
          (cAE_B (dD_0_0_U x)) (cAB_D (dD_0_0_U x)) (cAE_BC (dB_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U
          (dD_0_0_U x))) (cAB_DE (dE_1_1_U (dD_0_0_U x))) (HcAB_DE (dE_1_1_U (dD_0_0_U x)) aD_layer)
          (hABE_D (dD_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U (fun _ a => a)
          DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl) (cAB_D (dD_0_0_U x))
          (HcAB_D (dD_0_0_U x) aD_layer)))) Hraw_nat_ABC_D
    (path_map2_dep (fun H K => square_compose_map dE_4_4_U H K)
      (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ a => a) (H := H) (K := K) h k))
      (layer_square_nat_source dC_2_0_L dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U cAB_CDE
        (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
        (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x)))
        (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))) (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x))))
        (hABE_CD (dC_1_0_U (dD_0_0_U x)))) (path_map2 (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_map_source dC_2_0_L dA_2_0_L dA_3_0_L dC_3_1_L dE_3_3_U cAC_DE dB_4_1_L
          dB_3_1_U dE_4_4_U cBE_ACD (cDE_nil x) (cCE_D (dD_0_0_U x)) (cAE_B (dD_0_0_U x))
          (cAC_D (dD_0_0_U x)) (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
          (hACE_D (dD_0_0_U x))) (layer_square_nat_source dA_2_0_L dC_3_1_L dB_3_1_L dB_4_1_L
          dC_4_2_L dE_4_4_U cBC_ADE (cDE_nil x) (cAE_B (dD_0_0_U x))
          (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
          (cBC_AD (dA_1_0_U (dD_0_0_U x))) (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) (hBCE_AD (dA_1_0_U (dD_0_0_U x)))))
      (layer_square_nat_source_coherence_dep dC_2_0_L dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U
        DC_2_0_L DB_3_0_L DA_3_0_L DA_4_0_L DB_4_1_L (fun _ a => a) cAB_CDE HcAB_CDE (cDE_nil x)
        (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BC (dC_1_0_U (dD_0_0_U x)))
        (cAB_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x))))
        (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) (hABE_CD (dC_1_0_U (dD_0_0_U x))) eq_refl
        eq_refl eq_refl eq_refl (HcAB_CD (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer))
        eq_refl eq_refl (layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BC
          (dC_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BCD (dB_2_0_U (dC_1_0_U
          (dD_0_0_U x)))) (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) (cAB_CDE (dE_2_2_U (dC_1_0_U
          (dD_0_0_U x)))) (HcAB_CDE (dE_2_2_U (dC_1_0_U (dD_0_0_U x))) (DC_1_0_U
          (dD_0_0_U x) aD_layer)) (hABE_CD (dC_1_0_U (dD_0_0_U x))))) (path_map2_dep
        (fun H K => square_compose_map dE_4_4_U H K)
        (fun H K h k => (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
            (fun _ a => a) (H := H) (K := K) h k))
        (layer_square_map_source dC_2_0_L dA_2_0_L dA_3_0_L dC_3_1_L dE_3_3_U cAC_DE dB_4_1_L
          dB_3_1_U dE_4_4_U cBE_ACD (cDE_nil x) (cCE_D (dD_0_0_U x)) (cAE_B (dD_0_0_U x))
          (cAC_D (dD_0_0_U x)) (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
          (hACE_D (dD_0_0_U x))) (layer_square_nat_source dA_2_0_L dC_3_1_L dB_3_1_L dB_4_1_L
          dC_4_2_L dE_4_4_U cBC_ADE (cDE_nil x) (cAE_B (dD_0_0_U x))
          (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
          (cBC_AD (dA_1_0_U (dD_0_0_U x))) (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) (hBCE_AD (dA_1_0_U (dD_0_0_U x))))
        (layer_square_map_source_coherence_dep dC_2_0_L dA_2_0_L dA_3_0_L dC_3_1_L dE_3_3_U
          DC_2_0_L DA_2_0_L DA_3_0_L DC_3_1_L (fun _ a => a) cAC_DE HcAC_DE dB_4_1_L dB_3_1_U
          dE_4_4_U DB_4_1_L DB_3_1_U (fun _ a => a) cBE_ACD (fun _ _ => eq_refl) (cDE_nil x)
          (cCE_D (dD_0_0_U x)) (cAE_B (dD_0_0_U x)) (cAC_D (dD_0_0_U x))
          (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x))) (hACE_D (dD_0_0_U x))
          eq_refl eq_refl eq_refl (HcAC_D (dD_0_0_U x) aD_layer) eq_refl eq_refl
          (layer_square _ _ _ DA_3_0_L DC_3_1_L (cCE_D (dD_0_0_U x)) (cAE_B (dD_0_0_U x)) (cAC_D
            (dD_0_0_U x)) (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cAC_DE
            (dE_1_1_U (dD_0_0_U x))) (HcAC_DE (dE_1_1_U (dD_0_0_U x)) aD_layer) (hACE_D (dD_0_0_U x))))
            (layer_square_nat_source_coherence_dep dA_2_0_L dC_3_1_L
          dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U DA_2_0_L DC_3_1_L DB_3_1_L DB_4_1_L DC_4_2_L
          (fun _ a => a) cBC_ADE HcBC_ADE (cDE_nil x) (cAE_B (dD_0_0_U x))
          (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
          (cBC_AD (dA_1_0_U (dD_0_0_U x))) (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) (hBCE_AD (dA_1_0_U (dD_0_0_U x))) eq_refl
          eq_refl eq_refl eq_refl (HcBC_AD (dA_1_0_U (dD_0_0_U x))
            (DA_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
          (layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U
            (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x))) (cBE_ACD (dC_2_1_U (dA_1_0_U
            (dD_0_0_U x)))) (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) (cBC_ADE (dE_2_2_U (dA_1_0_U
            (dD_0_0_U x)))) (HcBC_ADE (dE_2_2_U (dA_1_0_U (dD_0_0_U x))) (DA_1_0_U
            (dD_0_0_U x) aD_layer)) (hBCE_AD (dA_1_0_U
            (dD_0_0_U x)))))) ⊙ square_nat_route_coherence_dep dE_4_4_U S0
      (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
      (layer_cube_nat_side_coherence_dep dC_2_0_L dB_3_0_L dA_4_0_L DC_2_0_L DB_3_0_L DA_4_0_L
        (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
        (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dC_2_0_L dA_3_0_L dB_4_1_L DC_2_0_L DA_3_0_L DB_4_1_L
        (cDE_nil x) (cCE_D (dD_0_0_U x)) (cAE_BC (dC_1_0_U (dD_0_0_U x)))
        (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dA_2_0_L dC_3_1_L dB_4_1_L DA_2_0_L DC_3_1_L DB_4_1_L
        (cDE_nil x) (cAE_B (dD_0_0_U x)) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
        (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (layer_cube_nat_side_coherence_dep dA_2_0_L dB_3_1_L dC_4_2_L DA_2_0_L DB_3_1_L DC_4_2_L
        (cDE_nil x) (cAE_B (dD_0_0_U x)) (cBE_AC (dA_1_0_U (dD_0_0_U x)))
        (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) eq_refl eq_refl eq_refl eq_refl)
      (square_coherence_dep_fill (fun z => dB_3_0_L ( dC_2_0_L z ))
        (fun z => dA_3_0_L ( dC_2_0_L z )) dA_4_0_L dB_4_1_L
        (fun z a => DB_3_0_L (dC_2_0_L z) (DC_2_0_L z a))
        (fun z a => DA_3_0_L (dC_2_0_L z) (DC_2_0_L z a)) DA_4_0_L DB_4_1_L
        (fun z => cAB_CDE ( dC_2_0_L z )) (fun z a => HcAB_CDE (dC_2_0_L z) (DC_2_0_L z a))
        (cDE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dA_3_0_L ( dC_2_0_L z ))
        (fun z => dC_3_1_L ( dA_2_0_L z )) dB_4_1_L dB_4_1_L
        (fun z a => DA_3_0_L (dC_2_0_L z) (DC_2_0_L z a))
        (fun z a => DC_3_1_L (dA_2_0_L z) (DA_2_0_L z a)) DB_4_1_L DB_4_1_L
        (fun z => f_equal dB_4_1_L ( cAC_DE z )) (fun z a => sigT_map_eq DB_4_1_L (HcAC_DE z a))
        (cDE_nil x) eq_refl) (square_coherence_dep_fill (fun z => dC_3_1_L ( dA_2_0_L z ))
        (fun z => dB_3_1_L ( dA_2_0_L z )) dB_4_1_L dC_4_2_L
        (fun z a => DC_3_1_L (dA_2_0_L z) (DA_2_0_L z a))
        (fun z a => DB_3_1_L (dA_2_0_L z) (DA_2_0_L z a)) DB_4_1_L DC_4_2_L
        (fun z => cBC_ADE ( dA_2_0_L z )) (fun z a => HcBC_ADE (dA_2_0_L z) (DA_2_0_L z a))
        (cDE_nil x) eq_refl) (layer_square_nat_coherence_dep dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L
        dE_4_4_U DB_3_0_L DA_3_0_L DA_4_0_L DB_4_1_L (fun _ a => a) cAB_CDE HcAB_CDE
        (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BC (dC_1_0_U (dD_0_0_U x)))
        (cAB_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x))))
        (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) (hABE_CD (dC_1_0_U (dD_0_0_U x))) eq_refl
        eq_refl eq_refl (HcAB_CD (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer)) eq_refl
        eq_refl (layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BC
          (dC_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x))) (cAE_BCD (dB_2_0_U (dC_1_0_U
          (dD_0_0_U x)))) (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) (cAB_CDE (dE_2_2_U (dC_1_0_U
          (dD_0_0_U x)))) (HcAB_CDE (dE_2_2_U (dC_1_0_U (dD_0_0_U x))) (DC_1_0_U
          (dD_0_0_U x) aD_layer)) (hABE_CD (dC_1_0_U (dD_0_0_U x))))) (square_stack_dep _
        (square_map_dep dB_4_1_L DB_4_1_L ((layer_square _ _ _ DA_3_0_L DC_3_1_L (cCE_D (dD_0_0_U x))
          (cAE_B (dD_0_0_U x)) (cAC_D (dD_0_0_U x)) (cAE_BC (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U
          (dD_0_0_U x))) (cAC_DE (dE_1_1_U (dD_0_0_U x))) (HcAC_DE (dE_1_1_U (dD_0_0_U x)) aD_layer)
          (hACE_D (dD_0_0_U x)))))
        (square_coherence_dep_reverse_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U (fun _ a => a)
          DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl) (cAC_D (dD_0_0_U x))
          (HcAC_D (dD_0_0_U x) aD_layer))) (layer_square_nat_coherence_dep dC_3_1_L dB_3_1_L
        dB_4_1_L dC_4_2_L dE_4_4_U DC_3_1_L DB_3_1_L DB_4_1_L DC_4_2_L (fun _ a => a) cBC_ADE
        HcBC_ADE (cAE_B (dD_0_0_U x)) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
        (cBE_AC (dA_1_0_U (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x)))
        (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))) (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x))))
        (hBCE_AD (dA_1_0_U (dD_0_0_U x))) eq_refl eq_refl eq_refl
        (HcBC_AD (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer)) eq_refl eq_refl
        (layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AC (dA_1_0_U
          (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x))) (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) (cBC_ADE (dE_2_2_U (dA_1_0_U (dD_0_0_U x))))
          (HcBC_ADE (dE_2_2_U (dA_1_0_U (dD_0_0_U x))) (DA_1_0_U (dD_0_0_U x) aD_layer)) (hBCE_AD
          (dA_1_0_U (dD_0_0_U x)))))).

Local Abbreviation positive_square_AB_CD :=
  (@Bonak.SS2Gpd.Coh4Shapes.positive_square_AB_CD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dC_0_0_U dD_0_0_U
    dE_0_0_U dD_1_1_U dE_1_1_U dC_1_0_U dC_1_0_L dD_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dB_2_0_U
    dC_2_0_L dE_3_3_U dB_3_1_U dA_3_0_U dA_3_0_L dB_3_0_L dE_4_4_U dB_4_1_L dA_4_0_L cAB_CD
    cAB_CDE cAE_BC cAE_BCD cBE_CD cBE_ACD cCD_nil cCD_E cCE_nil cCE_D cDE_nil cDE_A hABE_CD
    hCDE_nil x).

Local Definition Hpositive_square_AB_CD_raw :=
  hexagonal_prism_pair_cube_coherence_dep dC_2_0_L dE_2_2_U dD_2_1_L dB_2_0_U dA_2_0_U dB_3_0_L
    dA_3_0_L dE_3_3_U dE_3_3_U dA_4_0_L dB_4_1_L dA_3_0_U dB_3_1_U dE_4_4_U cBE_CD cAE_BC cAE_BCD
    cBE_ACD cAB_CDE cAB_CD hABE_CD DC_2_0_L (fun _ a => a) DD_2_1_L DB_2_0_U DA_2_0_U DB_3_0_L
    DA_3_0_L (fun _ a => a) (fun _ a => a) DA_4_0_L DB_4_1_L DA_3_0_U DB_3_1_U (fun _ a => a)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) HcAB_CDE
    HcAB_CD (fun z a => layer_square _ _ _ DA_4_0_L DB_4_1_L (cBE_CD z) (cAE_BC z) (cAB_CD z) (cAE_BCD
      (dB_2_0_U z)) (cBE_ACD (dA_2_0_U z)) (cAB_CDE (dE_2_2_U z)) (HcAB_CDE (dE_2_2_U z) a) (hABE_CD z))
    (cDE_nil x) (cCD_nil x) (cCE_nil x) (cCE_D (dD_0_0_U x)) (cCD_E (dE_0_0_U x))
    (cDE_A (dC_0_0_U x)) (hCDE_nil x) eq_refl HcCD_nil eq_refl eq_refl HcCD_E eq_refl
    (layer_square _ _ _ DC_2_0_L DD_2_1_L (cDE_nil x) (cCE_nil x) (cCD_nil x) (cCE_D (dD_0_0_U x))
      (cDE_A (dC_0_0_U x)) (cCD_E (dE_0_0_U x)) HcCD_E (hCDE_nil x)).

Local Abbreviation positive_square_AC_BD :=
  (@Bonak.SS2Gpd.Coh4Shapes.positive_square_AC_BD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dD_0_0_U
    dE_0_0_U dD_1_1_U dE_1_1_U dB_1_0_U dB_1_0_L dD_1_0_L dE_2_2_U dC_2_1_U dD_2_1_L dA_2_0_U
    dB_2_0_L dE_3_3_U dC_3_2_U dC_3_1_L dA_3_0_U dA_3_0_L dE_4_4_U dC_4_2_L dA_4_0_L cAC_BD
    cAC_BDE cAE_BC cAE_BCD cBD_nil cBD_E cBE_nil cBE_C cCE_AD cCE_ABD cDE_nil cDE_A hACE_BD
    hBDE_nil x).

Local Definition Hpositive_square_AC_BD_raw :=
  hexagonal_prism_pair_cube_coherence_dep dB_2_0_L dE_2_2_U dD_2_1_L dC_2_1_U dA_2_0_U dC_3_1_L
    dA_3_0_L dE_3_3_U dE_3_3_U dA_4_0_L dC_4_2_L dA_3_0_U dC_3_2_U dE_4_4_U cCE_AD cAE_BC cAE_BCD
    cCE_ABD cAC_BDE cAC_BD hACE_BD DB_2_0_L (fun _ a => a) DD_2_1_L DC_2_1_U DA_2_0_U DC_3_1_L
    DA_3_0_L (fun _ a => a) (fun _ a => a) DA_4_0_L DC_4_2_L DA_3_0_U DC_3_2_U (fun _ a => a)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) HcAC_BDE
    HcAC_BD (fun z a => layer_square _ _ _ DA_4_0_L DC_4_2_L (cCE_AD z) (cAE_BC z) (cAC_BD z) (cAE_BCD
      (dC_2_1_U z)) (cCE_ABD (dA_2_0_U z)) (cAC_BDE (dE_2_2_U z)) (HcAC_BDE (dE_2_2_U z) a) (hACE_BD z))
    (cDE_nil x) (cBD_nil x) (cBE_nil x) (cBE_C (dD_0_0_U x)) (cBD_E (dE_0_0_U x))
    (cDE_A (dB_0_0_U x)) (hBDE_nil x) eq_refl HcBD_nil eq_refl eq_refl HcBD_E eq_refl
    (layer_square _ _ _ DB_2_0_L DD_2_1_L (cDE_nil x) (cBE_nil x) (cBD_nil x) (cBE_C (dD_0_0_U x))
      (cDE_A (dB_0_0_U x)) (cBD_E (dE_0_0_U x)) HcBD_E (hBDE_nil x)).

Local Abbreviation positive_square_AD_BC :=
  (@Bonak.SS2Gpd.Coh4Shapes.positive_square_AD_BC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dB_0_0_U dC_0_0_U
    dE_0_0_U dC_1_1_U dE_1_1_U dB_1_0_U dB_1_0_L dC_1_0_L dD_2_2_U dE_2_2_U dC_2_1_L dA_2_0_U
    dB_2_0_L dD_3_3_U dE_3_3_U dD_3_2_L dA_3_0_U dA_3_0_L dE_4_4_U dD_4_3_L dA_4_0_L cAD_BC
    cAD_BCE cAE_BC cAE_BCD cBC_nil cBC_E cBE_nil cBE_C cCE_nil cCE_A cDE_AB cDE_ABC hADE_BC
    hBCE_nil x).

Local Definition Hpositive_square_AD_BC_raw :=
  hexagonal_prism_pair_cube_coherence_dep dB_2_0_L dE_2_2_U dC_2_1_L dD_2_2_U dA_2_0_U dD_3_2_L
    dA_3_0_L dE_3_3_U dE_3_3_U dA_4_0_L dD_4_3_L dA_3_0_U dD_3_3_U dE_4_4_U cDE_AB cAE_BC cAE_BCD
    cDE_ABC cAD_BCE cAD_BC hADE_BC DB_2_0_L (fun _ a => a) DC_2_1_L DD_2_2_U DA_2_0_U DD_3_2_L
    DA_3_0_L (fun _ a => a) (fun _ a => a) DA_4_0_L DD_4_3_L DA_3_0_U DD_3_3_U (fun _ a => a)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) HcAD_BCE
    HcAD_BC (fun z a => layer_square _ _ _ DA_4_0_L DD_4_3_L (cDE_AB z) (cAE_BC z) (cAD_BC z) (cAE_BCD
      (dD_2_2_U z)) (cDE_ABC (dA_2_0_U z)) (cAD_BCE (dE_2_2_U z)) (HcAD_BCE (dE_2_2_U z) a) (hADE_BC z))
    (cCE_nil x) (cBC_nil x) (cBE_nil x) (cBE_C (dC_0_0_U x)) (cBC_E (dE_0_0_U x))
    (cCE_A (dB_0_0_U x)) (hBCE_nil x) eq_refl HcBC_nil eq_refl eq_refl HcBC_E eq_refl
    (layer_square _ _ _ DB_2_0_L DC_2_1_L (cCE_nil x) (cBE_nil x) (cBC_nil x) (cBE_C (dC_0_0_U x))
      (cCE_A (dB_0_0_U x)) (cBC_E (dE_0_0_U x)) HcBC_E (hBCE_nil x)).

Local Abbreviation positive_square_BC_AD :=
  (@Bonak.SS2Gpd.Coh4Shapes.positive_square_BC_AD X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dD_0_0_U
    dE_0_0_U dD_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dD_1_0_L dE_2_2_U dB_2_1_U dC_2_1_U dD_2_1_L
    dA_2_0_L dE_3_3_U dC_3_2_U dB_3_1_U dB_3_1_L dC_3_1_L dE_4_4_U dC_4_2_L dB_4_1_L cAD_nil cAD_E
    cAE_nil cAE_B cBC_AD cBC_ADE cBE_AC cBE_ACD cCE_AD cCE_ABD cDE_nil cDE_A hADE_nil hBCE_AD x).

Local Definition Hpositive_square_BC_AD_raw :=
  hexagonal_prism_pair_cube_coherence_dep dA_2_0_L dE_2_2_U dD_2_1_L dC_2_1_U dB_2_1_U dC_3_1_L
    dB_3_1_L dE_3_3_U dE_3_3_U dB_4_1_L dC_4_2_L dB_3_1_U dC_3_2_U dE_4_4_U cCE_AD cBE_AC cBE_ACD
    cCE_ABD cBC_ADE cBC_AD hBCE_AD DA_2_0_L (fun _ a => a) DD_2_1_L DC_2_1_U DB_2_1_U DC_3_1_L
    DB_3_1_L (fun _ a => a) (fun _ a => a) DB_4_1_L DC_4_2_L DB_3_1_U DC_3_2_U (fun _ a => a)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) HcBC_ADE
    HcBC_AD (fun z a => layer_square _ _ _ DB_4_1_L DC_4_2_L (cCE_AD z) (cBE_AC z) (cBC_AD z) (cBE_ACD
      (dC_2_1_U z)) (cCE_ABD (dB_2_1_U z)) (cBC_ADE (dE_2_2_U z)) (HcBC_ADE (dE_2_2_U z) a) (hBCE_AD z))
    (cDE_nil x) (cAD_nil x) (cAE_nil x) (cAE_B (dD_0_0_U x)) (cAD_E (dE_0_0_U x))
    (cDE_A (dA_0_0_U x)) (hADE_nil x) eq_refl HcAD_nil eq_refl eq_refl HcAD_E eq_refl
    (layer_square _ _ _ DA_2_0_L DD_2_1_L (cDE_nil x) (cAE_nil x) (cAD_nil x) (cAE_B (dD_0_0_U x))
      (cDE_A (dA_0_0_U x)) (cAD_E (dE_0_0_U x)) HcAD_E (hADE_nil x)).

Local Abbreviation positive_square_BD_AC :=
  (@Bonak.SS2Gpd.Coh4Shapes.positive_square_BD_AC X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dC_0_0_U
    dE_0_0_U dC_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dC_1_0_L dD_2_2_U dE_2_2_U dB_2_1_U dC_2_1_L
    dA_2_0_L dD_3_3_U dE_3_3_U dD_3_2_L dB_3_1_U dB_3_1_L dE_4_4_U dD_4_3_L dB_4_1_L cAC_nil cAC_E
    cAE_nil cAE_B cBD_AC cBD_ACE cBE_AC cBE_ACD cCE_nil cCE_A cDE_AB cDE_ABC hACE_nil hBDE_AC x).

Local Definition Hpositive_square_BD_AC_raw :=
  hexagonal_prism_pair_cube_coherence_dep dA_2_0_L dE_2_2_U dC_2_1_L dD_2_2_U dB_2_1_U dD_3_2_L
    dB_3_1_L dE_3_3_U dE_3_3_U dB_4_1_L dD_4_3_L dB_3_1_U dD_3_3_U dE_4_4_U cDE_AB cBE_AC cBE_ACD
    cDE_ABC cBD_ACE cBD_AC hBDE_AC DA_2_0_L (fun _ a => a) DC_2_1_L DD_2_2_U DB_2_1_U DD_3_2_L
    DB_3_1_L (fun _ a => a) (fun _ a => a) DB_4_1_L DD_4_3_L DB_3_1_U DD_3_3_U (fun _ a => a)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) HcBD_ACE
    HcBD_AC (fun z a => layer_square _ _ _ DB_4_1_L DD_4_3_L (cDE_AB z) (cBE_AC z) (cBD_AC z) (cBE_ACD
      (dD_2_2_U z)) (cDE_ABC (dB_2_1_U z)) (cBD_ACE (dE_2_2_U z)) (HcBD_ACE (dE_2_2_U z) a) (hBDE_AC z))
    (cCE_nil x) (cAC_nil x) (cAE_nil x) (cAE_B (dC_0_0_U x)) (cAC_E (dE_0_0_U x))
    (cCE_A (dA_0_0_U x)) (hACE_nil x) eq_refl HcAC_nil eq_refl eq_refl HcAC_E eq_refl
    (layer_square _ _ _ DA_2_0_L DC_2_1_L (cCE_nil x) (cAE_nil x) (cAC_nil x) (cAE_B (dC_0_0_U x))
      (cCE_A (dA_0_0_U x)) (cAC_E (dE_0_0_U x)) HcAC_E (hACE_nil x)).

Local Abbreviation positive_square_CD_AB :=
  (@Bonak.SS2Gpd.Coh4Shapes.positive_square_CD_AB X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4 dA_0_0_U dB_0_0_U
    dE_0_0_U dB_1_1_U dE_1_1_U dA_1_0_U dA_1_0_L dB_1_0_L dC_2_2_U dD_2_2_U dE_2_2_U dB_2_1_L
    dA_2_0_L dD_3_3_U dE_3_3_U dC_3_2_U dC_3_2_L dD_3_2_L dE_4_4_U dD_4_3_L dC_4_2_L cAB_nil cAB_E
    cAE_nil cAE_B cBE_nil cBE_A cCD_AB cCD_ABE cCE_AB cCE_ABD cDE_AB cDE_ABC hABE_nil hCDE_AB x).

Local Definition Hpositive_square_CD_AB_raw :=
  hexagonal_prism_pair_cube_coherence_dep dA_2_0_L dE_2_2_U dB_2_1_L dD_2_2_U dC_2_2_U dD_3_2_L
    dC_3_2_L dE_3_3_U dE_3_3_U dC_4_2_L dD_4_3_L dC_3_2_U dD_3_3_U dE_4_4_U cDE_AB cCE_AB cCE_ABD
    cDE_ABC cCD_ABE cCD_AB hCDE_AB DA_2_0_L (fun _ a => a) DB_2_1_L DD_2_2_U DC_2_2_U DD_3_2_L
    DC_3_2_L (fun _ a => a) (fun _ a => a) DC_4_2_L DD_4_3_L DC_3_2_U DD_3_3_U (fun _ a => a)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) HcCD_ABE
    HcCD_AB (fun z a => layer_square _ _ _ DC_4_2_L DD_4_3_L (cDE_AB z) (cCE_AB z) (cCD_AB z) (cCE_ABD
      (dD_2_2_U z)) (cDE_ABC (dC_2_2_U z)) (cCD_ABE (dE_2_2_U z)) (HcCD_ABE (dE_2_2_U z) a) (hCDE_AB z))
    (cBE_nil x) (cAB_nil x) (cAE_nil x) (cAE_B (dB_0_0_U x)) (cAB_E (dE_0_0_U x))
    (cBE_A (dA_0_0_U x)) (hABE_nil x) eq_refl HcAB_nil eq_refl eq_refl HcAB_E eq_refl
    (layer_square _ _ _ DA_2_0_L DB_2_1_L (cBE_nil x) (cAE_nil x) (cAB_nil x) (cAE_B (dB_0_0_U x))
      (cBE_A (dA_0_0_U x)) (cAB_E (dE_0_0_U x)) HcAB_E (hABE_nil x)).

Local Lemma Hpositive_square_AB_CD:
  square_cube_coherence_dep S0 (square_compose_map dE_4_4_U n_ABCD_3 n_ABDC_1)
         (square_compose_map dE_4_4_U n_ABCD_1 n_BACD_3)
         (f_equal
            (fun e: dA_3_0_U (dB_2_0_U (dC_1_0_U (dD_0_0_U x))) = dB_3_1_U
                (dA_2_0_U (dD_1_1_U (dC_0_0_U x))) =>
             f_equal dE_4_4_U e)
            (square_coherence_fill dB_2_0_U dA_2_0_U dA_3_0_U dB_3_1_U cAB_CD (cCD_nil x)))
         (square_coherence_fill dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L cAB_CDE (cCD_E (dE_0_0_U x)))
           positive_square_AB_CD
         (sigT_map_eq DA_4_0_L (sigT_map_eq DB_3_0_L HcCD_E)
          ⊙ HcAB_CDE (dD_2_1_L (dC_1_0_L (dE_0_0_U x))) (DD_2_1_L (dC_1_0_L (dE_0_0_U x)) aC))
         (HcAB_CDE (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)
          ⊙ sigT_map_eq DB_4_1_L (sigT_map_eq DA_3_0_L HcCD_E))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (sigT_map_eq DA_3_0_U (sigT_map_eq DB_2_0_U HcCD_nil)
             ⊙ HcAB_CD (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer)))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (HcAB_CD (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer)
             ⊙ sigT_map_eq DB_3_1_U (sigT_map_eq DA_2_0_U HcCD_nil)))
         (sigT_map_eq DA_4_0_L (sigT_map_eq DB_3_0_L (sigT_map_eq DC_2_0_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (sigT_map_eq DB_4_1_L (sigT_map_eq DA_3_0_L (sigT_map_eq DD_2_1_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_ABCD_3
            Hn_ABDC_1)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_ABCD_1 Hn_BACD_3)
         (sigT_map_eq
            (fun (e: dA_3_0_U (dB_2_0_U (dC_1_0_U (dD_0_0_U x))) = dB_3_1_U
                  (dA_2_0_U (dD_1_1_U (dC_0_0_U x))))
               (h: rew [fun H: X1 => S0 (dE_4_4_U H)] e in
                    DA_3_0_U (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))
                      (DB_2_0_U (dC_1_0_U (dD_0_0_U x)) (DC_1_0_U (dD_0_0_U x) aD_layer)) =
                    DB_3_1_U (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))
                      (DA_2_0_U (dD_1_1_U (dC_0_0_U x)) (DD_1_1_U (dC_0_0_U x) aC_layer))) =>
             sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a) h)
            (square_coherence_dep_fill dB_2_0_U dA_2_0_U dA_3_0_U dB_3_1_U DB_2_0_U DA_2_0_U
                DA_3_0_U DB_3_1_U cAB_CD
               HcAB_CD (cCD_nil x) HcCD_nil))
         (square_coherence_dep_fill dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L DB_3_0_L DA_3_0_L DA_4_0_L
             DB_4_1_L cAB_CDE
            HcAB_CDE (cCD_E (dE_0_0_U x)) HcCD_E).
Proof. now exact Hpositive_square_AB_CD_raw. Defined.

Local Lemma Hpositive_square_AC_BD:
  square_cube_coherence_dep S0 (square_compose_map dE_4_4_U n_ACBD_3 n_ACDB_1)
         (square_compose_map dE_4_4_U n_ACBD_1 n_CABD_3)
         (f_equal
            (fun e: dA_3_0_U (dC_2_1_U (dB_1_0_U (dD_0_0_U x))) = dC_3_2_U
                (dA_2_0_U (dD_1_1_U (dB_0_0_U x))) =>
             f_equal dE_4_4_U e)
            (square_coherence_fill dC_2_1_U dA_2_0_U dA_3_0_U dC_3_2_U cAC_BD (cBD_nil x)))
         (square_coherence_fill dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L cAC_BDE (cBD_E (dE_0_0_U x)))
           positive_square_AC_BD
         (sigT_map_eq DA_4_0_L (sigT_map_eq DC_3_1_L HcBD_E)
          ⊙ HcAC_BDE (dD_2_1_L (dB_1_0_L (dE_0_0_U x))) (DD_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))
         (HcAC_BDE (dB_2_0_L (dD_1_0_L (dE_0_0_U x))) (DB_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)
          ⊙ sigT_map_eq DC_4_2_L (sigT_map_eq DA_3_0_L HcBD_E))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (sigT_map_eq DA_3_0_U (sigT_map_eq DC_2_1_U HcBD_nil)
             ⊙ HcAC_BD (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer)))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (HcAC_BD (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer)
             ⊙ sigT_map_eq DC_3_2_U (sigT_map_eq DA_2_0_U HcBD_nil)))
         (sigT_map_eq DA_4_0_L (sigT_map_eq DC_3_1_L (sigT_map_eq DB_2_0_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (sigT_map_eq DC_4_2_L (sigT_map_eq DA_3_0_L (sigT_map_eq DD_2_1_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_ACBD_3
            Hn_ACDB_1)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_ACBD_1 Hn_CABD_3)
         (sigT_map_eq
            (fun (e: dA_3_0_U (dC_2_1_U (dB_1_0_U (dD_0_0_U x))) = dC_3_2_U
                  (dA_2_0_U (dD_1_1_U (dB_0_0_U x))))
               (h: rew [fun H: X1 => S0 (dE_4_4_U H)] e in
                    DA_3_0_U (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))
                      (DC_2_1_U (dB_1_0_U (dD_0_0_U x)) (DB_1_0_U (dD_0_0_U x) aD_layer)) =
                    DC_3_2_U (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))
                      (DA_2_0_U (dD_1_1_U (dB_0_0_U x)) (DD_1_1_U (dB_0_0_U x) aB_layer))) =>
             sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a) h)
            (square_coherence_dep_fill dC_2_1_U dA_2_0_U dA_3_0_U dC_3_2_U DC_2_1_U DA_2_0_U
                DA_3_0_U DC_3_2_U cAC_BD
               HcAC_BD (cBD_nil x) HcBD_nil))
         (square_coherence_dep_fill dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L DC_3_1_L DA_3_0_L DA_4_0_L
             DC_4_2_L cAC_BDE
            HcAC_BDE (cBD_E (dE_0_0_U x)) HcBD_E).
Proof. now exact Hpositive_square_AC_BD_raw. Defined.

Local Lemma Hpositive_square_AD_BC:
  square_cube_coherence_dep S0 (square_compose_map dE_4_4_U n_ADBC_3 n_ADCB_1)
         (square_compose_map dE_4_4_U n_ADBC_1 n_DABC_3)
         (f_equal
            (fun e: dA_3_0_U (dD_2_2_U (dB_1_0_U (dC_0_0_U x))) = dD_3_3_U
                (dA_2_0_U (dC_1_1_U (dB_0_0_U x))) =>
             f_equal dE_4_4_U e)
            (square_coherence_fill dD_2_2_U dA_2_0_U dA_3_0_U dD_3_3_U cAD_BC (cBC_nil x)))
         (square_coherence_fill dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L cAD_BCE (cBC_E (dE_0_0_U x)))
           positive_square_AD_BC
         (sigT_map_eq DA_4_0_L (sigT_map_eq DD_3_2_L HcBC_E)
          ⊙ HcAD_BCE (dC_2_1_L (dB_1_0_L (dE_0_0_U x))) (DC_2_1_L (dB_1_0_L (dE_0_0_U x)) aB))
         (HcAD_BCE (dB_2_0_L (dC_1_0_L (dE_0_0_U x))) (DB_2_0_L (dC_1_0_L (dE_0_0_U x)) aC)
          ⊙ sigT_map_eq DD_4_3_L (sigT_map_eq DA_3_0_L HcBC_E))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (sigT_map_eq DA_3_0_U (sigT_map_eq DD_2_2_U HcBC_nil)
             ⊙ HcAD_BC (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer)))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (HcAD_BC (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer)
             ⊙ sigT_map_eq DD_3_3_U (sigT_map_eq DA_2_0_U HcBC_nil)))
         (sigT_map_eq DA_4_0_L (sigT_map_eq DD_3_2_L (sigT_map_eq DB_2_0_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (sigT_map_eq DD_4_3_L (sigT_map_eq DA_3_0_L (sigT_map_eq DC_2_1_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_ADBC_3
            Hn_ADCB_1)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_ADBC_1 Hn_DABC_3)
         (sigT_map_eq
            (fun (e: dA_3_0_U (dD_2_2_U (dB_1_0_U (dC_0_0_U x))) = dD_3_3_U
                  (dA_2_0_U (dC_1_1_U (dB_0_0_U x))))
               (h: rew [fun H: X1 => S0 (dE_4_4_U H)] e in
                    DA_3_0_U (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))
                      (DD_2_2_U (dB_1_0_U (dC_0_0_U x)) (DB_1_0_U (dC_0_0_U x) aC_layer)) =
                    DD_3_3_U (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))
                      (DA_2_0_U (dC_1_1_U (dB_0_0_U x)) (DC_1_1_U (dB_0_0_U x) aB_layer))) =>
             sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a) h)
            (square_coherence_dep_fill dD_2_2_U dA_2_0_U dA_3_0_U dD_3_3_U DD_2_2_U DA_2_0_U
                DA_3_0_U DD_3_3_U cAD_BC
               HcAD_BC (cBC_nil x) HcBC_nil))
         (square_coherence_dep_fill dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L DD_3_2_L DA_3_0_L DA_4_0_L
             DD_4_3_L cAD_BCE
            HcAD_BCE (cBC_E (dE_0_0_U x)) HcBC_E).
Proof. now exact Hpositive_square_AD_BC_raw. Defined.

Local Lemma Hpositive_square_BC_AD:
  square_cube_coherence_dep S0 (square_compose_map dE_4_4_U n_BCAD_3 n_BCDA_1)
         (square_compose_map dE_4_4_U n_BCAD_1 n_CBAD_3)
         (f_equal
            (fun e: dB_3_1_U (dC_2_1_U (dA_1_0_U (dD_0_0_U x))) = dC_3_2_U
                (dB_2_1_U (dD_1_1_U (dA_0_0_U x))) =>
             f_equal dE_4_4_U e)
            (square_coherence_fill dC_2_1_U dB_2_1_U dB_3_1_U dC_3_2_U cBC_AD (cAD_nil x)))
         (square_coherence_fill dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L cBC_ADE (cAD_E (dE_0_0_U x)))
           positive_square_BC_AD
         (sigT_map_eq DB_4_1_L (sigT_map_eq DC_3_1_L HcAD_E)
          ⊙ HcBC_ADE (dD_2_1_L (dA_1_0_L (dE_0_0_U x))) (DD_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))
         (HcBC_ADE (dA_2_0_L (dD_1_0_L (dE_0_0_U x))) (DA_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)
          ⊙ sigT_map_eq DC_4_2_L (sigT_map_eq DB_3_1_L HcAD_E))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (sigT_map_eq DB_3_1_U (sigT_map_eq DC_2_1_U HcAD_nil)
             ⊙ HcBC_AD (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer)))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (HcBC_AD (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer)
             ⊙ sigT_map_eq DC_3_2_U (sigT_map_eq DB_2_1_U HcAD_nil)))
         (sigT_map_eq DB_4_1_L (sigT_map_eq DC_3_1_L (sigT_map_eq DA_2_0_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (sigT_map_eq DC_4_2_L (sigT_map_eq DB_3_1_L (sigT_map_eq DD_2_1_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_BCAD_3
            Hn_BCDA_1)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_BCAD_1 Hn_CBAD_3)
         (sigT_map_eq
            (fun (e: dB_3_1_U (dC_2_1_U (dA_1_0_U (dD_0_0_U x))) = dC_3_2_U
                  (dB_2_1_U (dD_1_1_U (dA_0_0_U x))))
               (h: rew [fun H: X1 => S0 (dE_4_4_U H)] e in
                    DB_3_1_U (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))
                      (DC_2_1_U (dA_1_0_U (dD_0_0_U x)) (DA_1_0_U (dD_0_0_U x) aD_layer)) =
                    DC_3_2_U (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))
                      (DB_2_1_U (dD_1_1_U (dA_0_0_U x)) (DD_1_1_U (dA_0_0_U x) aA_layer))) =>
             sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a) h)
            (square_coherence_dep_fill dC_2_1_U dB_2_1_U dB_3_1_U dC_3_2_U DC_2_1_U DB_2_1_U
                DB_3_1_U DC_3_2_U cBC_AD
               HcBC_AD (cAD_nil x) HcAD_nil))
         (square_coherence_dep_fill dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L DC_3_1_L DB_3_1_L DB_4_1_L
             DC_4_2_L cBC_ADE
            HcBC_ADE (cAD_E (dE_0_0_U x)) HcAD_E).
Proof. now exact Hpositive_square_BC_AD_raw. Defined.

Local Lemma Hpositive_square_BD_AC:
  square_cube_coherence_dep S0 (square_compose_map dE_4_4_U n_BDAC_3 n_BDCA_1)
         (square_compose_map dE_4_4_U n_BDAC_1 n_DBAC_3)
         (f_equal
            (fun e: dB_3_1_U (dD_2_2_U (dA_1_0_U (dC_0_0_U x))) = dD_3_3_U
                (dB_2_1_U (dC_1_1_U (dA_0_0_U x))) =>
             f_equal dE_4_4_U e)
            (square_coherence_fill dD_2_2_U dB_2_1_U dB_3_1_U dD_3_3_U cBD_AC (cAC_nil x)))
         (square_coherence_fill dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L cBD_ACE (cAC_E (dE_0_0_U x)))
           positive_square_BD_AC
         (sigT_map_eq DB_4_1_L (sigT_map_eq DD_3_2_L HcAC_E)
          ⊙ HcBD_ACE (dC_2_1_L (dA_1_0_L (dE_0_0_U x))) (DC_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))
         (HcBD_ACE (dA_2_0_L (dC_1_0_L (dE_0_0_U x))) (DA_2_0_L (dC_1_0_L (dE_0_0_U x)) aC)
          ⊙ sigT_map_eq DD_4_3_L (sigT_map_eq DB_3_1_L HcAC_E))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (sigT_map_eq DB_3_1_U (sigT_map_eq DD_2_2_U HcAC_nil)
             ⊙ HcBD_AC (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer)))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (HcBD_AC (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer)
             ⊙ sigT_map_eq DD_3_3_U (sigT_map_eq DB_2_1_U HcAC_nil)))
         (sigT_map_eq DB_4_1_L (sigT_map_eq DD_3_2_L (sigT_map_eq DA_2_0_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (sigT_map_eq DD_4_3_L (sigT_map_eq DB_3_1_L (sigT_map_eq DC_2_1_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_BDAC_3
            Hn_BDCA_1)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_BDAC_1 Hn_DBAC_3)
         (sigT_map_eq
            (fun (e: dB_3_1_U (dD_2_2_U (dA_1_0_U (dC_0_0_U x))) = dD_3_3_U
                  (dB_2_1_U (dC_1_1_U (dA_0_0_U x))))
               (h: rew [fun H: X1 => S0 (dE_4_4_U H)] e in
                    DB_3_1_U (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))
                      (DD_2_2_U (dA_1_0_U (dC_0_0_U x)) (DA_1_0_U (dC_0_0_U x) aC_layer)) =
                    DD_3_3_U (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))
                      (DB_2_1_U (dC_1_1_U (dA_0_0_U x)) (DC_1_1_U (dA_0_0_U x) aA_layer))) =>
             sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a) h)
            (square_coherence_dep_fill dD_2_2_U dB_2_1_U dB_3_1_U dD_3_3_U DD_2_2_U DB_2_1_U
                DB_3_1_U DD_3_3_U cBD_AC
               HcBD_AC (cAC_nil x) HcAC_nil))
         (square_coherence_dep_fill dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L DD_3_2_L DB_3_1_L DB_4_1_L
             DD_4_3_L cBD_ACE
            HcBD_ACE (cAC_E (dE_0_0_U x)) HcAC_E).
Proof. now exact Hpositive_square_BD_AC_raw. Defined.

Local Lemma Hpositive_square_CD_AB:
  square_cube_coherence_dep S0 (square_compose_map dE_4_4_U n_CDAB_3 n_CDBA_1)
         (square_compose_map dE_4_4_U n_CDAB_1 n_DCAB_3)
         (f_equal
            (fun e: dC_3_2_U (dD_2_2_U (dA_1_0_U (dB_0_0_U x))) = dD_3_3_U
                (dC_2_2_U (dB_1_1_U (dA_0_0_U x))) =>
             f_equal dE_4_4_U e)
            (square_coherence_fill dD_2_2_U dC_2_2_U dC_3_2_U dD_3_3_U cCD_AB (cAB_nil x)))
         (square_coherence_fill dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L cCD_ABE (cAB_E (dE_0_0_U x)))
           positive_square_CD_AB
         (sigT_map_eq DC_4_2_L (sigT_map_eq DD_3_2_L HcAB_E)
          ⊙ HcCD_ABE (dB_2_1_L (dA_1_0_L (dE_0_0_U x))) (DB_2_1_L (dA_1_0_L (dE_0_0_U x)) aA))
         (HcCD_ABE (dA_2_0_L (dB_1_0_L (dE_0_0_U x))) (DA_2_0_L (dB_1_0_L (dE_0_0_U x)) aB)
          ⊙ sigT_map_eq DD_4_3_L (sigT_map_eq DC_3_2_L HcAB_E))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (sigT_map_eq DC_3_2_U (sigT_map_eq DD_2_2_U HcAB_nil)
             ⊙ HcCD_AB (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)))
         (sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a)
            (HcCD_AB (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer)
             ⊙ sigT_map_eq DD_3_3_U (sigT_map_eq DC_2_2_U HcAB_nil)))
         (sigT_map_eq DC_4_2_L (sigT_map_eq DD_3_2_L (sigT_map_eq DA_2_0_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (sigT_map_eq DD_4_3_L (sigT_map_eq DC_3_2_L (sigT_map_eq DB_2_1_L eq_refl ⊙ eq_refl) ⊙
               eq_refl) ⊙ eq_refl)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_CDAB_3
            Hn_CDBA_1)
         (square_compose_map_coherence_dep dE_4_4_U S0 (fun z: X1 => S0 (dE_4_4_U z))
            (fun (y: X1) (elt: S0 (dE_4_4_U y)) => elt)

                Hn_CDAB_1 Hn_DCAB_3)
         (sigT_map_eq
            (fun (e: dC_3_2_U (dD_2_2_U (dA_1_0_U (dB_0_0_U x))) = dD_3_3_U
                  (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))
               (h: rew [fun H: X1 => S0 (dE_4_4_U H)] e in
                    DC_3_2_U (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))
                      (DD_2_2_U (dA_1_0_U (dB_0_0_U x)) (DA_1_0_U (dB_0_0_U x) aB_layer)) =
                    DD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))
                      (DC_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer))) =>
             sigT_map_eq (fun (w: X1) (a: S0 (dE_4_4_U w)) => a) h)
            (square_coherence_dep_fill dD_2_2_U dC_2_2_U dC_3_2_U dD_3_3_U DD_2_2_U DC_2_2_U
                DC_3_2_U DD_3_3_U cCD_AB
               HcCD_AB (cAB_nil x) HcAB_nil))
         (square_coherence_dep_fill dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L DD_3_2_L DC_3_2_L DC_4_2_L
             DD_4_3_L cCD_ABE
            HcCD_ABE (cAB_E (dE_0_0_U x)) HcAB_E).
Proof. now exact Hpositive_square_CD_AB_raw. Defined.

Local Abbreviation n_BCD_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BCD_2 X2 X3 X4 X5 Y1 Y2 Y3 Y4 dC_0_0_U dD_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dC_1_0_U dC_1_0_L dD_1_0_L dE_2_2_U dD_2_1_L dB_2_0_U dC_2_0_L dE_3_3_U dB_3_0_L
    cBE_CD cCD_nil cCD_E cCE_nil cCE_D cDE_nil cDE_A hCDE_nil x).

Local Definition Hn_BCD_2 :=
  (square_stack_dep _ (square_map_dep dB_3_0_L DB_3_0_L
        ((layer_square _ _ _ DC_2_0_L DD_2_1_L (cDE_nil x) (cCE_nil x) (cCD_nil x) (cCE_D (dD_0_0_U x))
          (cDE_A (dC_0_0_U x)) (cCD_E (dE_0_0_U x)) HcCD_E (hCDE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dB_2_0_U dB_3_0_L dE_3_3_U
        (fun _ a => a) DB_2_0_U DB_3_0_L (fun _ a => a) cBE_CD (fun _ _ => eq_refl) (cCD_nil x)
        HcCD_nil)).

Local Abbreviation n_BDC_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BDC_1 X2 X3 X4 X5 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dB_1_0_U dC_1_0_L dD_2_2_U dE_2_2_U dD_2_1_L dB_2_0_U dB_2_0_L dE_3_3_U dD_3_2_L dB_3_0_L
    cBD_C cBD_CE cBE_C cBE_CD cCE_nil cDE_A cDE_AB hBDE_C x).

Local Definition Hn_BDC_1 :=
  (layer_square_nat_coherence_dep dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L DB_2_0_L
      DB_3_0_L DD_3_2_L (fun _ a => a) cBD_CE HcBD_CE (cCE_nil x) (cDE_A (dC_0_0_U x))
      (cBE_C (dC_0_0_U x)) (cBD_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
      (cDE_AB (dB_1_0_U (dC_0_0_U x))) (hBDE_C (dC_0_0_U x)) eq_refl eq_refl eq_refl
      (HcBD_C (dC_0_0_U x) aC_layer) eq_refl eq_refl
      (layer_square _ _ _ DB_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cBD_C
        (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dB_1_0_U (dC_0_0_U x))) (cBD_CE
        (dE_1_1_U (dC_0_0_U x))) (HcBD_CE (dE_1_1_U (dC_0_0_U x)) aC_layer) (hBDE_C (dC_0_0_U x)))).


Local Definition Hn_CBD_2 :=
  (square_stack_dep _ (square_map_dep dC_3_1_L DC_3_1_L
        ((layer_square _ _ _ DB_2_0_L DD_2_1_L (cDE_nil x) (cBE_nil x) (cBD_nil x) (cBE_C (dD_0_0_U x))
          (cDE_A (dB_0_0_U x)) (cBD_E (dE_0_0_U x)) HcBD_E (hBDE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dC_2_1_U dC_3_1_L dE_3_3_U
        (fun _ a => a) DC_2_1_U DC_3_1_L (fun _ a => a) cCE_AD (fun _ _ => eq_refl) (cBD_nil x)
        HcBD_nil)).


Local Definition Hn_CDB_1 :=
  (layer_square_nat_coherence_dep dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L DC_2_1_L
      DC_3_1_L DD_3_2_L (fun _ a => a) cCD_BE HcCD_BE (cBE_nil x) (cDE_A (dB_0_0_U x))
      (cCE_A (dB_0_0_U x)) (cCD_B (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x)))
      (cDE_AB (dC_1_1_U (dB_0_0_U x))) (hCDE_B (dB_0_0_U x)) eq_refl eq_refl eq_refl
      (HcCD_B (dB_0_0_U x) aB_layer) eq_refl eq_refl
      (layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dB_0_0_U x)) (cCE_A (dB_0_0_U x)) (cCD_B
        (dB_0_0_U x)) (cCE_AD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dC_1_1_U (dB_0_0_U x))) (cCD_BE
        (dE_1_1_U (dB_0_0_U x))) (HcCD_BE (dE_1_1_U (dB_0_0_U x)) aB_layer) (hCDE_B (dB_0_0_U x)))).

Local Definition Hn_ABD_2 :=
  (square_stack_dep _ (square_map_dep dA_3_0_L DA_3_0_L
        ((layer_square _ _ _ DB_2_0_L DD_2_1_L (cDE_nil x) (cBE_nil x) (cBD_nil x) (cBE_C (dD_0_0_U x))
          (cDE_A (dB_0_0_U x)) (cBD_E (dE_0_0_U x)) HcBD_E (hBDE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U
        (fun _ a => a) DA_2_0_U DA_3_0_L (fun _ a => a) cAE_BC (fun _ _ => eq_refl) (cBD_nil x)
        HcBD_nil)).

Local Definition Hn_ADB_1 :=
  (layer_square_nat_coherence_dep dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L DA_2_0_L
      DA_3_0_L DD_3_2_L (fun _ a => a) cAD_BE HcAD_BE (cBE_nil x) (cDE_A (dB_0_0_U x))
      (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x)))
      (cDE_AB (dA_1_0_U (dB_0_0_U x))) (hADE_B (dB_0_0_U x)) eq_refl eq_refl eq_refl
      (HcAD_B (dB_0_0_U x) aB_layer) eq_refl eq_refl
      (layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B
        (dB_0_0_U x)) (cAE_BC (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cAD_BE
        (dE_1_1_U (dB_0_0_U x))) (HcAD_BE (dE_1_1_U (dB_0_0_U x)) aB_layer) (hADE_B (dB_0_0_U x)))).

Local Abbreviation n_ACD_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ACD_2 X2 X3 X4 X5 Y1 Y2 Y3 Y4 dC_0_0_U dD_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dC_1_0_U dC_1_0_L dD_1_0_L dE_2_2_U dD_2_1_L dA_2_0_U dC_2_0_L dE_3_3_U dA_3_0_L
    cAE_BC cCD_nil cCD_E cCE_nil cCE_D cDE_nil cDE_A hCDE_nil x).

Local Definition Hn_ACD_2 :=
  (square_stack_dep _ (square_map_dep dA_3_0_L DA_3_0_L
        ((layer_square _ _ _ DC_2_0_L DD_2_1_L (cDE_nil x) (cCE_nil x) (cCD_nil x) (cCE_D (dD_0_0_U x))
          (cDE_A (dC_0_0_U x)) (cCD_E (dE_0_0_U x)) HcCD_E (hCDE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U
        (fun _ a => a) DA_2_0_U DA_3_0_L (fun _ a => a) cAE_BC (fun _ _ => eq_refl) (cCD_nil x)
        HcCD_nil)).

Local Abbreviation n_ADC_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_ADC_1 X2 X3 X4 X5 Y1 Y2 Y3 Y4 dC_0_0_U dE_0_0_U dD_1_1_U dE_1_1_U
    dA_1_0_U dC_1_0_L dD_2_2_U dE_2_2_U dD_2_1_L dA_2_0_U dA_2_0_L dE_3_3_U dD_3_2_L dA_3_0_L
    cAD_C cAD_CE cAE_B cAE_BC cCE_nil cDE_A cDE_AB hADE_C x).

Local Definition Hn_ADC_1 :=
  (layer_square_nat_coherence_dep dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U DD_2_1_L DA_2_0_L
      DA_3_0_L DD_3_2_L (fun _ a => a) cAD_CE HcAD_CE (cCE_nil x) (cDE_A (dC_0_0_U x))
      (cAE_B (dC_0_0_U x)) (cAD_C (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x)))
      (cDE_AB (dA_1_0_U (dC_0_0_U x))) (hADE_C (dC_0_0_U x)) eq_refl eq_refl eq_refl
      (HcAD_C (dC_0_0_U x) aC_layer) eq_refl eq_refl
      (layer_square _ _ _ DA_3_0_L DD_3_2_L (cDE_A (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cAD_C
        (dC_0_0_U x)) (cAE_BC (dD_1_1_U (dC_0_0_U x))) (cDE_AB (dA_1_0_U (dC_0_0_U x))) (cAD_CE
        (dE_1_1_U (dC_0_0_U x))) (HcAD_CE (dE_1_1_U (dC_0_0_U x)) aC_layer) (hADE_C (dC_0_0_U x)))).

Local Definition Hn_CAD_2 :=
  (square_stack_dep _ (square_map_dep dC_3_1_L DC_3_1_L
        ((layer_square _ _ _ DA_2_0_L DD_2_1_L (cDE_nil x) (cAE_nil x) (cAD_nil x) (cAE_B (dD_0_0_U x))
          (cDE_A (dA_0_0_U x)) (cAD_E (dE_0_0_U x)) HcAD_E (hADE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dC_2_1_U dC_3_1_L dE_3_3_U
        (fun _ a => a) DC_2_1_U DC_3_1_L (fun _ a => a) cCE_AD (fun _ _ => eq_refl) (cAD_nil x)
        HcAD_nil)).

Local Definition Hn_CDA_1 :=
  (layer_square_nat_coherence_dep dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L DC_2_1_L
      DC_3_1_L DD_3_2_L (fun _ a => a) cCD_AE HcCD_AE (cAE_nil x) (cDE_A (dA_0_0_U x))
      (cCE_A (dA_0_0_U x)) (cCD_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
      (cDE_AB (dC_1_1_U (dA_0_0_U x))) (hCDE_A (dA_0_0_U x)) eq_refl eq_refl eq_refl
      (HcCD_A (dA_0_0_U x) aA_layer) eq_refl eq_refl
      (layer_square _ _ _ DC_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cCD_A
        (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dC_1_1_U (dA_0_0_U x))) (cCD_AE
        (dE_1_1_U (dA_0_0_U x))) (HcCD_AE (dE_1_1_U (dA_0_0_U x)) aA_layer) (hCDE_A (dA_0_0_U x)))).

Local Abbreviation n_BAD_2 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BAD_2 X2 X3 X4 X5 Y1 Y2 Y3 Y4 dA_0_0_U dD_0_0_U dE_0_0_U dD_1_1_U
    dE_1_1_U dA_1_0_U dA_1_0_L dD_1_0_L dE_2_2_U dB_2_1_U dD_2_1_L dA_2_0_L dE_3_3_U dB_3_1_L
    cAD_nil cAD_E cAE_nil cAE_B cBE_AC cDE_nil cDE_A hADE_nil x).

Local Definition Hn_BAD_2 :=
  (square_stack_dep _ (square_map_dep dB_3_1_L DB_3_1_L
        ((layer_square _ _ _ DA_2_0_L DD_2_1_L (cDE_nil x) (cAE_nil x) (cAD_nil x) (cAE_B (dD_0_0_U x))
          (cDE_A (dA_0_0_U x)) (cAD_E (dE_0_0_U x)) HcAD_E (hADE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dB_2_1_U dB_3_1_L dE_3_3_U
        (fun _ a => a) DB_2_1_U DB_3_1_L (fun _ a => a) cBE_AC (fun _ _ => eq_refl) (cAD_nil x)
        HcAD_nil)).

Local Abbreviation n_BDA_1 :=
  (@Bonak.SS2Gpd.Coh4Shapes.n_BDA_1 X2 X3 X4 X5 Y1 Y2 Y3 Y4 dA_0_0_U dE_0_0_U dB_1_1_U dD_1_1_U
    dE_1_1_U dA_1_0_L dD_2_2_U dE_2_2_U dB_2_1_U dB_2_1_L dD_2_1_L dE_3_3_U dD_3_2_L dB_3_1_L
    cAE_nil cBD_A cBD_AE cBE_A cBE_AC cDE_A cDE_AB hBDE_A x).

Local Definition Hn_BDA_1 :=
  (layer_square_nat_coherence_dep dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U DD_2_1_L DB_2_1_L
      DB_3_1_L DD_3_2_L (fun _ a => a) cBD_AE HcBD_AE (cAE_nil x) (cDE_A (dA_0_0_U x))
      (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x)))
      (cDE_AB (dB_1_1_U (dA_0_0_U x))) (hBDE_A (dA_0_0_U x)) eq_refl eq_refl eq_refl
      (HcBD_A (dA_0_0_U x) aA_layer) eq_refl eq_refl
      (layer_square _ _ _ DB_3_1_L DD_3_2_L (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A
        (dA_0_0_U x)) (cBE_AC (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cBD_AE
        (dE_1_1_U (dA_0_0_U x))) (HcBD_AE (dE_1_1_U (dA_0_0_U x)) aA_layer) (hBDE_A (dA_0_0_U x)))).

Local Definition Hn_ABC_2 :=
  (square_stack_dep _ (square_map_dep dA_3_0_L DA_3_0_L
        ((layer_square _ _ _ DB_2_0_L DC_2_1_L (cCE_nil x) (cBE_nil x) (cBC_nil x) (cBE_C (dC_0_0_U x))
          (cCE_A (dB_0_0_U x)) (cBC_E (dE_0_0_U x)) HcBC_E (hBCE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U
        (fun _ a => a) DA_2_0_U DA_3_0_L (fun _ a => a) cAE_BC (fun _ _ => eq_refl) (cBC_nil x)
        HcBC_nil)).

Local Definition Hn_ACB_1 :=
  (layer_square_nat_coherence_dep dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L dE_3_3_U DC_2_1_L DA_2_0_L
      DA_3_0_L DC_3_2_L (fun _ a => a) cAC_BE HcAC_BE (cBE_nil x) (cCE_A (dB_0_0_U x))
      (cAE_B (dB_0_0_U x)) (cAC_B (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x)))
      (cCE_AB (dA_1_0_U (dB_0_0_U x))) (hACE_B (dB_0_0_U x)) eq_refl eq_refl eq_refl
      (HcAC_B (dB_0_0_U x) aB_layer) eq_refl eq_refl
      (layer_square _ _ _ DA_3_0_L DC_3_2_L (cCE_A (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAC_B
        (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x))) (cAC_BE
        (dE_1_1_U (dB_0_0_U x))) (HcAC_BE (dE_1_1_U (dB_0_0_U x)) aB_layer) (hACE_B (dB_0_0_U x)))).

Local Definition Hn_CAB_2 :=
  (square_stack_dep _ (square_map_dep dC_3_2_L DC_3_2_L
        ((layer_square _ _ _ DA_2_0_L DB_2_1_L (cBE_nil x) (cAE_nil x) (cAB_nil x) (cAE_B (dB_0_0_U x))
          (cBE_A (dA_0_0_U x)) (cAB_E (dE_0_0_U x)) HcAB_E (hABE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dC_2_2_U dC_3_2_L dE_3_3_U
        (fun _ a => a) DC_2_2_U DC_3_2_L (fun _ a => a) cCE_AB (fun _ _ => eq_refl) (cAB_nil x)
        HcAB_nil)).

Local Definition Hn_ABC_1 :=
  (layer_square_nat_coherence_dep dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U DB_2_0_L DA_2_0_L
      DA_3_0_L DB_3_1_L (fun _ a => a) cAB_CE HcAB_CE (cCE_nil x) (cBE_C (dC_0_0_U x))
      (cAE_B (dC_0_0_U x)) (cAB_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x)))
      (cBE_AC (dA_1_0_U (dC_0_0_U x))) (hABE_C (dC_0_0_U x)) eq_refl eq_refl eq_refl
      (HcAB_C (dC_0_0_U x) aC_layer) eq_refl eq_refl
      (layer_square _ _ _ DA_3_0_L DB_3_1_L (cBE_C (dC_0_0_U x)) (cAE_B (dC_0_0_U x)) (cAB_C
        (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x))) (cAB_CE
        (dE_1_1_U (dC_0_0_U x))) (HcAB_CE (dE_1_1_U (dC_0_0_U x)) aC_layer) (hABE_C (dC_0_0_U x)))).

Local Definition Hn_BAC_2 :=
  (square_stack_dep _ (square_map_dep dB_3_1_L DB_3_1_L
        ((layer_square _ _ _ DA_2_0_L DC_2_1_L (cCE_nil x) (cAE_nil x) (cAC_nil x) (cAE_B (dC_0_0_U x))
          (cCE_A (dA_0_0_U x)) (cAC_E (dE_0_0_U x)) HcAC_E (hACE_nil x))))
          (square_coherence_dep_reverse_fill dE_2_2_U dB_2_1_U dB_3_1_L dE_3_3_U
        (fun _ a => a) DB_2_1_U DB_3_1_L (fun _ a => a) cBE_AC (fun _ _ => eq_refl) (cAC_nil x)
        HcAC_nil)).

Local Definition Hn_BCA_1 :=
  (layer_square_nat_coherence_dep dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L dE_3_3_U DC_2_1_L DB_2_1_L
      DB_3_1_L DC_3_2_L (fun _ a => a) cBC_AE HcBC_AE (cAE_nil x) (cCE_A (dA_0_0_U x))
      (cBE_A (dA_0_0_U x)) (cBC_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x)))
      (cCE_AB (dB_1_1_U (dA_0_0_U x))) (hBCE_A (dA_0_0_U x)) eq_refl eq_refl eq_refl
      (HcBC_A (dA_0_0_U x) aA_layer) eq_refl eq_refl
      (layer_square _ _ _ DB_3_1_L DC_3_2_L (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBC_A
        (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x))) (cBC_AE
        (dE_1_1_U (dA_0_0_U x))) (HcBC_AE (dE_1_1_U (dA_0_0_U x)) aA_layer) (hBCE_A (dA_0_0_U x)))).

Local Definition Hp5_left_map_BCD :=
  (square_stack_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
      (square_map_cube_coherence_dep dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U S1
        (fun z => S1 (dE_3_3_U z)) (fun z => S0 (dE_4_4_U z)) S0 (fun _ a => a) DA_3_0_U DA_4_0_L
        (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
        HkBCDE_nil
        (square_coherence_cube_dep_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a) DA_3_0_U
          DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl) (hBCD_nil x) (((sigT_map_eq (f :=
          dB_2_0_U) DB_2_0_U (p := (cCD_nil x)) HcCD_nil) ⊙ (HcBD_C (dC_0_0_U x) aC_layer)) ⊙
          (sigT_map_eq (f := dD_2_2_U) DD_2_2_U
                  (p := (cBC_nil x)) HcBC_nil)) ((HcBC_D (dD_0_0_U x) aD_layer) ⊙
              ((sigT_map_eq (f := dC_2_1_U) DC_2_1_U (p := (cBD_nil x)) HcBD_nil) ⊙
                (HcCD_B (dB_0_0_U x) aB_layer))) HhBCD_nil))
      (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
        (fun _ elt => elt) Hpositive_square_AD_BC)).

Local Definition Hp5_left_nat_ACD :=
  (square_change_sides_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
      (fun _ elt => elt) (square_cube_trans_map_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) Hn_ADCB_1 (square_map_along_compose_coherence_dep dE_3_3_U dA_3_0_U
            dA_4_0_L dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD
            (fun _ _ => eq_refl) Hn_CBD_2 Hn_CDB_1))
        (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_compose_map_assoc_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hn_ACBD_3 Hn_ACDB_2 Hn_ADCB_1)))
      (square_stack_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        Hpositive_square_AC_BD Hhcube_ACD_B) (square_cube_trans_map_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) Hn_CDAB_1 (square_map_along_compose_coherence_dep dE_3_3_U dC_3_2_U
            dC_4_2_L dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD
            (fun _ _ => eq_refl) Hn_ABD_2 Hn_ADB_1))
        (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_compose_map_assoc_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hn_CABD_3 Hn_CADB_2 Hn_CDAB_1)))).

Local Definition Hp5_left_map_ABD :=
  (square_stack_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
      (square_map_cube_coherence_dep dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U S1
        (fun z => S1 (dE_3_3_U z)) (fun z => S0 (dE_4_4_U z)) S0 (fun _ a => a) DC_3_2_U DC_4_2_L
        (fun _ a => a) cCE_ABD (fun _ _ => eq_refl)
        HkABDE_nil
        (square_coherence_cube_dep_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U (fun _ a => a) DC_3_2_U
          DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl) (hABD_nil x) (((sigT_map_eq (f :=
          dA_2_0_U) DA_2_0_U (p := (cBD_nil x)) HcBD_nil) ⊙ (HcAD_B (dB_0_0_U x) aB_layer)) ⊙
          (sigT_map_eq (f := dD_2_2_U) DD_2_2_U
                  (p := (cAB_nil x)) HcAB_nil)) ((HcAB_D (dD_0_0_U x) aD_layer) ⊙
              ((sigT_map_eq (f := dB_2_1_U) DB_2_1_U (p := (cAD_nil x)) HcAD_nil) ⊙
                (HcBD_A (dA_0_0_U x) aA_layer))) HhABD_nil))
      (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
        (fun _ elt => elt) Hpositive_square_CD_AB)).

Local Definition Hp5_right_nat_ABD :=
  (square_change_sides_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
      (fun _ elt => elt) (square_cube_trans_map_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) Hn_ADBC_1 (square_map_along_compose_coherence_dep dE_3_3_U dA_3_0_U
            dA_4_0_L dE_4_4_U (fun _ a => a) DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD
            (fun _ _ => eq_refl) Hn_BCD_2 Hn_BDC_1))
        (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_compose_map_assoc_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hn_ABCD_3 Hn_ABDC_2 Hn_ADBC_1)))
      (square_stack_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        Hpositive_square_AB_CD Hhcube_ABD_C) (square_cube_trans_map_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) Hn_BDAC_1 (square_map_along_compose_coherence_dep dE_3_3_U dB_3_1_U
            dB_4_1_L dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD
            (fun _ _ => eq_refl) Hn_ACD_2 Hn_ADC_1))
        (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_compose_map_assoc_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hn_BACD_3 Hn_BADC_2 Hn_BDAC_1)))).

Local Definition Hp5_right_map_ACD :=
  (square_stack_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
      (square_map_cube_coherence_dep dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U S1
        (fun z => S1 (dE_3_3_U z)) (fun z => S0 (dE_4_4_U z)) S0 (fun _ a => a) DB_3_1_U DB_4_1_L
        (fun _ a => a) cBE_ACD (fun _ _ => eq_refl)
        HkACDE_nil
        (square_coherence_cube_dep_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U (fun _ a => a) DB_3_1_U
          DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl) (hACD_nil x) (((sigT_map_eq (f :=
          dA_2_0_U) DA_2_0_U (p := (cCD_nil x)) HcCD_nil) ⊙ (HcAD_C (dC_0_0_U x) aC_layer)) ⊙
          (sigT_map_eq (f := dD_2_2_U) DD_2_2_U
                  (p := (cAC_nil x)) HcAC_nil)) ((HcAC_D (dD_0_0_U x) aD_layer) ⊙
              ((sigT_map_eq (f := dC_2_1_U) DC_2_1_U (p := (cAD_nil x)) HcAD_nil) ⊙
                (HcCD_A (dA_0_0_U x) aA_layer))) HhACD_nil))
      (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
        (fun _ elt => elt) Hpositive_square_BD_AC)).

Local Definition Hp5_right_nat_BCD :=
  (square_change_sides_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
      (fun _ elt => elt) (square_cube_trans_map_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) Hn_BDCA_1 (square_map_along_compose_coherence_dep dE_3_3_U dB_3_1_U
            dB_4_1_L dE_4_4_U (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD
            (fun _ _ => eq_refl) Hn_CAD_2 Hn_CDA_1))
        (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_compose_map_assoc_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hn_BCAD_3 Hn_BCDA_2 Hn_BDCA_1)))
      (square_stack_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        Hpositive_square_BC_AD Hhcube_BCD_A) (square_cube_trans_map_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
        (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) Hn_CDBA_1 (square_map_along_compose_coherence_dep dE_3_3_U dC_3_2_U
            dC_4_2_L dE_4_4_U (fun _ a => a) DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD
            (fun _ _ => eq_refl) Hn_BAD_2 Hn_BDA_1))
        (square_cube_inverse_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_compose_map_assoc_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hn_CBAD_3 Hn_CBDA_2 Hn_CDBA_1)))).

Local Definition Hp5_left_sides :=
  let prefix := (square_compose_map_coherence_dep dE_4_4_U S0
          (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
          (square_map_along_coherence_dep dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a)
            DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
            (eq_trans (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)))
            (square_compose_map dE_3_3_U n_BCD_2 n_BDC_1)
            ((sigT_map_eq (f := dB_2_0_U) DB_2_0_U (p := (cCD_nil x)) HcCD_nil) ⊙
              (HcBD_C (dC_0_0_U x) aC_layer)) (square_compose_map_coherence_dep dE_3_3_U S1
              (fun z => S1 (dE_3_3_U z)) (fun _ a => a) Hn_BCD_2 Hn_BDC_1)) Hn_ADBC_1) in
  (square_cube_trans_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
    (square_cube_whisker_l_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) prefix
    (square_map_along_compose_coherence_dep dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U (fun _ a => a) DD_3_3_U
    DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl) (square_compose_map_coherence_dep dE_3_3_U S1
    (fun z => S1 (dE_3_3_U z)) (fun _ a => a) Hn_ABC_2 Hn_ACB_1) Hn_CAB_2))
    (square_compose_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
    (square_cube_trans_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
    (square_cube_whisker_l_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) prefix
    (square_map_along_compose_coherence_dep dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U (fun _ a => a) DD_3_3_U
    DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl) Hn_ABC_2 Hn_ACB_1))
    (square_compose_cube_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
    Hp5_left_map_BCD Hp5_left_nat_ACD)) Hp5_left_map_ABD)).

Local Definition Hp5_right_sides :=
  (square_cube_trans_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
      (square_cube_whisker_l_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
        (fun _ elt => elt) (square_compose_map_coherence_dep dE_4_4_U S0
          (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
          (square_map_along_coherence_dep dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a)
            DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
            (eq_trans (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)))
            (square_compose_map dE_3_3_U n_BCD_2 n_BDC_1)
            ((sigT_map_eq (f := dB_2_0_U) DB_2_0_U (p := (cCD_nil x)) HcCD_nil) ⊙
              (HcBD_C (dC_0_0_U x) aC_layer)) (square_compose_map_coherence_dep dE_3_3_U S1
              (fun z => S1 (dE_3_3_U z)) (fun _ a => a) Hn_BCD_2 Hn_BDC_1)) Hn_ADBC_1)
        (square_map_along_compose_coherence_dep dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U (fun _ a => a)
          DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl) Hn_ABC_1
          (square_compose_map_coherence_dep dE_3_3_U S1 (fun z => S1 (dE_3_3_U z)) (fun _ a => a)
            Hn_BAC_2 Hn_BCA_1))) (square_compose_cube_coherence_dep dE_4_4_U S0
        (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hp5_right_nat_ABD
        (square_cube_trans_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
          (fun _ elt => elt) (square_cube_whisker_l_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
            (square_compose_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
              (fun _ a => a) (square_map_along_coherence_dep dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U
                (fun _ a => a) DB_3_1_U DB_4_1_L (fun _ a => a) cBE_ACD (fun _ _ => eq_refl)
                (eq_trans (f_equal dA_2_0_U (cCD_nil x)) (cAD_C (dC_0_0_U x)))
                (square_compose_map dE_3_3_U n_ACD_2 n_ADC_1)
                ((sigT_map_eq (f := dA_2_0_U) DA_2_0_U (p := (cCD_nil x)) HcCD_nil) ⊙
                  (HcAD_C (dC_0_0_U x) aC_layer)) (square_compose_map_coherence_dep dE_3_3_U S1
                  (fun z => S1 (dE_3_3_U z)) (fun _ a => a) Hn_ACD_2 Hn_ADC_1)) Hn_BDAC_1)
            (square_map_along_compose_coherence_dep dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U
              (fun _ a => a) DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl)
              Hn_BAC_2 Hn_BCA_1)) (square_compose_cube_coherence_dep dE_4_4_U S0
            (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt) Hp5_right_map_ACD Hp5_right_nat_BCD)))).

Local Definition Hp5_left_boundary :=
  (square_cube_trans_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
      Hp5_left_sides (square_cube_whisker_r_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
        (fun _ elt => elt) (square_compose_map_coherence_dep dE_4_4_U S0
          (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
          (square_map_along_coherence_dep dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U (fun _ a => a)
            DC_3_2_U DC_4_2_L (fun _ a => a) cCE_ABD (fun _ _ => eq_refl)
            (eq_trans (f_equal dB_2_1_U (cAD_nil x)) (cBD_A (dA_0_0_U x)))
            (square_compose_map dE_3_3_U n_BAD_2 n_BDA_1)
            ((sigT_map_eq (f := dB_2_1_U) DB_2_1_U (p := (cAD_nil x)) HcAD_nil) ⊙
              (HcBD_A (dA_0_0_U x) aA_layer)) (square_compose_map_coherence_dep dE_3_3_U S1
              (fun z => S1 (dE_3_3_U z)) (fun _ a => a) Hn_BAD_2 Hn_BDA_1)) Hn_CDBA_1)
        Hhcube_ABC_D)).

Local Definition Hp5_right_boundary :=
  (square_cube_trans_map_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z)) (fun _ elt => elt)
      (square_cube_whisker_l_coherence_dep dE_4_4_U S0 (fun z => S0 (dE_4_4_U z))
        (fun _ elt => elt) (square_compose_map_coherence_dep dE_4_4_U S0
          (fun z => S0 (dE_4_4_U z)) (fun _ a => a)
          (square_map_along_coherence_dep dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U (fun _ a => a)
            DA_3_0_U DA_4_0_L (fun _ a => a) cAE_BCD (fun _ _ => eq_refl)
            (eq_trans (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)))
            (square_compose_map dE_3_3_U n_BCD_2 n_BDC_1)
            ((sigT_map_eq (f := dB_2_0_U) DB_2_0_U (p := (cCD_nil x)) HcCD_nil) ⊙
              (HcBD_C (dC_0_0_U x) aC_layer)) (square_compose_map_coherence_dep dE_3_3_U S1
              (fun z => S1 (dE_3_3_U z)) (fun _ a => a) Hn_BCD_2 Hn_BDC_1)) Hn_ADBC_1)
        (square_cube_map_along_canonical_coherence_dep dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U
          (fun _ a => a) DD_3_3_U DD_4_3_L (fun _ a => a) cDE_ABC (fun _ _ => eq_refl)
          (kABCE_nil x) HkABCE_nil)) Hp5_right_sides).

Local Definition p5_initial_paint :=
  DA_4_0_L (dB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
    (DB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))) (DC_2_0_L (dD_1_0_L (dE_0_0_U x)) aD)).

Local Definition p5_final_paint :=
  DD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))
    (DC_2_2_U (dB_1_1_U (dA_0_0_U x)) (DB_1_1_U (dA_0_0_U x) aA_layer)).

Local Definition p5_paint_family
  (e: dA_4_0_L (dB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x)))) =
    dE_4_4_U (dD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))): Type :=
  rew [S0] e in p5_initial_paint = p5_final_paint.

(** Transfer the supplied dependent permutahedron across the P5 frame.
    Its two lifted hemispheres fill the remaining cap in the path space;
    the final retraction removes the fixed map and prefix.
    The explicit coherence head lets conversion compare its arguments
    before unfolding the pasting expression. *)
Lemma rew_coh3Layer_perm5 (HP: source_perm4) (HF: frame_perm5):
  permutahedral_coherence_dep (kABCD_nil x) DD_2_2_U DD_3_3_U DA_2_0_U DC_2_2_U DB_2_1_U DA_3_0_U
    DC_3_2_U DB_3_1_U DB_2_0_U DC_2_1_U DA_2_0_U DB_2_1_U HcAD_BC HcCD_AB HcBD_AC HcAC_BD HcAB_CD
    HcBC_AD HcBC_nil HcAB_nil HcAC_nil (HcAC_B (dB_0_0_U x) aB_layer)
    (HcAB_C (dC_0_0_U x) aC_layer) (HcBC_A (dA_0_0_U x) aA_layer) HcCD_nil HcBD_nil HcAD_nil
    (HcBD_C (dC_0_0_U x) aC_layer) (HcCD_B (dB_0_0_U x) aB_layer) (HcAD_B (dB_0_0_U x) aB_layer)
    (HcBD_A (dA_0_0_U x) aA_layer) (HcAD_C (dC_0_0_U x) aC_layer) (HcCD_A (dA_0_0_U x) aA_layer)
    (HcBC_D (dD_0_0_U x) aD_layer) (HcAB_D (dD_0_0_U x) aD_layer) (HcAC_D (dD_0_0_U x) aD_layer)
    HhBCD_nil HhABD_nil HhACD_nil HhABC_nil (HhACD_B (dB_0_0_U x) aB_layer)
    (HhABD_C (dC_0_0_U x) aC_layer) (HhBCD_A (dA_0_0_U x) aA_layer)
    (HhABC_D (dD_0_0_U x) aD_layer).
Proof.
  unfold permutahedral_coherence_dep, square_cube_coherence_dep.
  eapply (prefix_map_coherence_retract dE_4_4_U S0 v_ABCD Hv_ABCD (kABCD_nil x)).
  unfold source_perm4, permutahedral_coherence_dep, square_cube_coherence_dep in HP.
  pose proof (postfix_coherence_map S0 v_DCBA Hv_DCBA HP) as HD.
  unfold frame_perm5, perm5_coherence in HF.
  eapply (square_cube_dep_upper p5_paint_family _ _ _ _ HF).
  3: now exact HD.
  - now exact Hp5_left_boundary.
  - now exact Hp5_right_boundary.
Defined.

End Coh3Layer.
