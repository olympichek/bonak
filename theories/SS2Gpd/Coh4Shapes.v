(** The P5 coherence and its thirty three-dimensional facets. *)

From Bonak.Lib Require Import Notation RewLemmas Coh2Shapes.
From Bonak.SSGpd Require Import Pasting Coh3Shapes.
From Bonak.SS2Gpd Require Import Pasting.

(** [A, B, C, D, E] label the five operations. The distinguished operation
    [E] passes from the upper types [X] to the lower types [Y]. In [dA_r_s_U],
    [r] counts operations already applied and [s] counts those with smaller
    labels; [U, L] select the upper or lower types. Comparison and coherence
    suffixes list the labels already applied, with [nil] for the empty set.
    A facet name records its ordered partition into two blocks. *)
Section FiveOperations.

Context (X1 X2 X3 X4 X5 Y0 Y1 Y2 Y3 Y4: Type).

Context (dA_0_0_U: X5 -> X4).
Context (dB_0_0_U: X5 -> X4).
Context (dC_0_0_U: X5 -> X4).
Context (dD_0_0_U: X5 -> X4).
Context (dE_0_0_U: X5 -> Y4).
Context (dB_1_1_U: X4 -> X3).
Context (dC_1_1_U: X4 -> X3).
Context (dD_1_1_U: X4 -> X3).
Context (dE_1_1_U: X4 -> Y3).
Context (dA_1_0_U: X4 -> X3).
Context (dB_1_0_U: X4 -> X3).
Context (dC_1_0_U: X4 -> X3).
Context (dA_1_0_L: Y4 -> Y3).
Context (dB_1_0_L: Y4 -> Y3).
Context (dC_1_0_L: Y4 -> Y3).
Context (dD_1_0_L: Y4 -> Y3).
Context (dC_2_2_U: X3 -> X2).
Context (dD_2_2_U: X3 -> X2).
Context (dE_2_2_U: X3 -> Y2).
Context (dB_2_1_U: X3 -> X2).
Context (dC_2_1_U: X3 -> X2).
Context (dB_2_1_L: Y3 -> Y2).
Context (dC_2_1_L: Y3 -> Y2).
Context (dD_2_1_L: Y3 -> Y2).
Context (dA_2_0_U: X3 -> X2).
Context (dA_2_0_L: Y3 -> Y2).
Context (dB_2_0_U: X3 -> X2).
Context (dB_2_0_L: Y3 -> Y2).
Context (dC_2_0_L: Y3 -> Y2).
Context (dD_3_3_U: X2 -> X1).
Context (dE_3_3_U: X2 -> Y1).
Context (dC_3_2_U: X2 -> X1).
Context (dC_3_2_L: Y2 -> Y1).
Context (dD_3_2_L: Y2 -> Y1).
Context (dB_3_1_U: X2 -> X1).
Context (dB_3_1_L: Y2 -> Y1).
Context (dC_3_1_L: Y2 -> Y1).
Context (dA_3_0_U: X2 -> X1).
Context (dA_3_0_L: Y2 -> Y1).
Context (dB_3_0_L: Y2 -> Y1).
Context (dE_4_4_U: X1 -> Y0).
Context (dD_4_3_L: Y1 -> Y0).
Context (dC_4_2_L: Y1 -> Y0).
Context (dB_4_1_L: Y1 -> Y0).
Context (dA_4_0_L: Y1 -> Y0).

Context (cAB_nil: forall x: X5,
  dA_1_0_U (dB_0_0_U (x)) = dB_1_1_U (dA_0_0_U (x))).

Context (cAB_C: forall x: X4,
  dA_2_0_U (dB_1_0_U (x)) = dB_2_1_U (dA_1_0_U (x))).

Context (cAB_D: forall x: X4,
  dA_2_0_U (dB_1_0_U (x)) = dB_2_1_U (dA_1_0_U (x))).

Context (cAB_E: forall x: Y4,
  dA_2_0_L (dB_1_0_L (x)) = dB_2_1_L (dA_1_0_L (x))).

Context (cAB_CD: forall x: X3,
  dA_3_0_U (dB_2_0_U (x)) = dB_3_1_U (dA_2_0_U (x))).

Context (cAB_CE: forall x: Y3,
  dA_3_0_L (dB_2_0_L (x)) = dB_3_1_L (dA_2_0_L (x))).

Context (cAB_DE: forall x: Y3,
  dA_3_0_L (dB_2_0_L (x)) = dB_3_1_L (dA_2_0_L (x))).

Context (cAB_CDE: forall x: Y2,
  dA_4_0_L (dB_3_0_L (x)) = dB_4_1_L (dA_3_0_L (x))).

Context (cAC_nil: forall x: X5,
  dA_1_0_U (dC_0_0_U (x)) = dC_1_1_U (dA_0_0_U (x))).

Context (cAC_B: forall x: X4,
  dA_2_0_U (dC_1_1_U (x)) = dC_2_2_U (dA_1_0_U (x))).

Context (cAC_D: forall x: X4,
  dA_2_0_U (dC_1_0_U (x)) = dC_2_1_U (dA_1_0_U (x))).

Context (cAC_E: forall x: Y4,
  dA_2_0_L (dC_1_0_L (x)) = dC_2_1_L (dA_1_0_L (x))).

Context (cAC_BD: forall x: X3,
  dA_3_0_U (dC_2_1_U (x)) = dC_3_2_U (dA_2_0_U (x))).

Context (cAC_BE: forall x: Y3,
  dA_3_0_L (dC_2_1_L (x)) = dC_3_2_L (dA_2_0_L (x))).

Context (cAC_DE: forall x: Y3,
  dA_3_0_L (dC_2_0_L (x)) = dC_3_1_L (dA_2_0_L (x))).

Context (cAC_BDE: forall x: Y2,
  dA_4_0_L (dC_3_1_L (x)) = dC_4_2_L (dA_3_0_L (x))).

Context (cAD_nil: forall x: X5,
  dA_1_0_U (dD_0_0_U (x)) = dD_1_1_U (dA_0_0_U (x))).

Context (cAD_B: forall x: X4,
  dA_2_0_U (dD_1_1_U (x)) = dD_2_2_U (dA_1_0_U (x))).

Context (cAD_C: forall x: X4,
  dA_2_0_U (dD_1_1_U (x)) = dD_2_2_U (dA_1_0_U (x))).

Context (cAD_E: forall x: Y4,
  dA_2_0_L (dD_1_0_L (x)) = dD_2_1_L (dA_1_0_L (x))).

Context (cAD_BC: forall x: X3,
  dA_3_0_U (dD_2_2_U (x)) = dD_3_3_U (dA_2_0_U (x))).

Context (cAD_BE: forall x: Y3,
  dA_3_0_L (dD_2_1_L (x)) = dD_3_2_L (dA_2_0_L (x))).

Context (cAD_CE: forall x: Y3,
  dA_3_0_L (dD_2_1_L (x)) = dD_3_2_L (dA_2_0_L (x))).

Context (cAD_BCE: forall x: Y2,
  dA_4_0_L (dD_3_2_L (x)) = dD_4_3_L (dA_3_0_L (x))).

Context (cAE_nil: forall x: X5,
  dA_1_0_L (dE_0_0_U (x)) = dE_1_1_U (dA_0_0_U (x))).

Context (cAE_B: forall x: X4,
  dA_2_0_L (dE_1_1_U (x)) = dE_2_2_U (dA_1_0_U (x))).

Context (cAE_C: forall x: X4,
  dA_2_0_L (dE_1_1_U (x)) = dE_2_2_U (dA_1_0_U (x))).

Context (cAE_D: forall x: X4,
  dA_2_0_L (dE_1_1_U (x)) = dE_2_2_U (dA_1_0_U (x))).

Context (cAE_BC: forall x: X3,
  dA_3_0_L (dE_2_2_U (x)) = dE_3_3_U (dA_2_0_U (x))).

Context (cAE_BD: forall x: X3,
  dA_3_0_L (dE_2_2_U (x)) = dE_3_3_U (dA_2_0_U (x))).

Context (cAE_CD: forall x: X3,
  dA_3_0_L (dE_2_2_U (x)) = dE_3_3_U (dA_2_0_U (x))).

Context (cAE_BCD: forall x: X2,
  dA_4_0_L (dE_3_3_U (x)) = dE_4_4_U (dA_3_0_U (x))).

Context (cBC_nil: forall x: X5,
  dB_1_0_U (dC_0_0_U (x)) = dC_1_1_U (dB_0_0_U (x))).

Context (cBC_A: forall x: X4,
  dB_2_1_U (dC_1_1_U (x)) = dC_2_2_U (dB_1_1_U (x))).

Context (cBC_D: forall x: X4,
  dB_2_0_U (dC_1_0_U (x)) = dC_2_1_U (dB_1_0_U (x))).

Context (cBC_E: forall x: Y4,
  dB_2_0_L (dC_1_0_L (x)) = dC_2_1_L (dB_1_0_L (x))).

Context (cBC_AD: forall x: X3,
  dB_3_1_U (dC_2_1_U (x)) = dC_3_2_U (dB_2_1_U (x))).

Context (cBC_AE: forall x: Y3,
  dB_3_1_L (dC_2_1_L (x)) = dC_3_2_L (dB_2_1_L (x))).

Context (cBC_DE: forall x: Y3,
  dB_3_0_L (dC_2_0_L (x)) = dC_3_1_L (dB_2_0_L (x))).

Context (cBC_ADE: forall x: Y2,
  dB_4_1_L (dC_3_1_L (x)) = dC_4_2_L (dB_3_1_L (x))).

Context (cBD_nil: forall x: X5,
  dB_1_0_U (dD_0_0_U (x)) = dD_1_1_U (dB_0_0_U (x))).

Context (cBD_A: forall x: X4,
  dB_2_1_U (dD_1_1_U (x)) = dD_2_2_U (dB_1_1_U (x))).

Context (cBD_C: forall x: X4,
  dB_2_0_U (dD_1_1_U (x)) = dD_2_2_U (dB_1_0_U (x))).

Context (cBD_E: forall x: Y4,
  dB_2_0_L (dD_1_0_L (x)) = dD_2_1_L (dB_1_0_L (x))).

Context (cBD_AC: forall x: X3,
  dB_3_1_U (dD_2_2_U (x)) = dD_3_3_U (dB_2_1_U (x))).

Context (cBD_AE: forall x: Y3,
  dB_3_1_L (dD_2_1_L (x)) = dD_3_2_L (dB_2_1_L (x))).

Context (cBD_CE: forall x: Y3,
  dB_3_0_L (dD_2_1_L (x)) = dD_3_2_L (dB_2_0_L (x))).

Context (cBD_ACE: forall x: Y2,
  dB_4_1_L (dD_3_2_L (x)) = dD_4_3_L (dB_3_1_L (x))).

Context (cBE_nil: forall x: X5,
  dB_1_0_L (dE_0_0_U (x)) = dE_1_1_U (dB_0_0_U (x))).

Context (cBE_A: forall x: X4,
  dB_2_1_L (dE_1_1_U (x)) = dE_2_2_U (dB_1_1_U (x))).

Context (cBE_C: forall x: X4,
  dB_2_0_L (dE_1_1_U (x)) = dE_2_2_U (dB_1_0_U (x))).

Context (cBE_D: forall x: X4,
  dB_2_0_L (dE_1_1_U (x)) = dE_2_2_U (dB_1_0_U (x))).

Context (cBE_AC: forall x: X3,
  dB_3_1_L (dE_2_2_U (x)) = dE_3_3_U (dB_2_1_U (x))).

Context (cBE_AD: forall x: X3,
  dB_3_1_L (dE_2_2_U (x)) = dE_3_3_U (dB_2_1_U (x))).

Context (cBE_CD: forall x: X3,
  dB_3_0_L (dE_2_2_U (x)) = dE_3_3_U (dB_2_0_U (x))).

Context (cBE_ACD: forall x: X2,
  dB_4_1_L (dE_3_3_U (x)) = dE_4_4_U (dB_3_1_U (x))).

Context (cCD_nil: forall x: X5,
  dC_1_0_U (dD_0_0_U (x)) = dD_1_1_U (dC_0_0_U (x))).

Context (cCD_A: forall x: X4,
  dC_2_1_U (dD_1_1_U (x)) = dD_2_2_U (dC_1_1_U (x))).

Context (cCD_B: forall x: X4,
  dC_2_1_U (dD_1_1_U (x)) = dD_2_2_U (dC_1_1_U (x))).

Context (cCD_E: forall x: Y4,
  dC_2_0_L (dD_1_0_L (x)) = dD_2_1_L (dC_1_0_L (x))).

Context (cCD_AB: forall x: X3,
  dC_3_2_U (dD_2_2_U (x)) = dD_3_3_U (dC_2_2_U (x))).

Context (cCD_AE: forall x: Y3,
  dC_3_1_L (dD_2_1_L (x)) = dD_3_2_L (dC_2_1_L (x))).

Context (cCD_BE: forall x: Y3,
  dC_3_1_L (dD_2_1_L (x)) = dD_3_2_L (dC_2_1_L (x))).

Context (cCD_ABE: forall x: Y2,
  dC_4_2_L (dD_3_2_L (x)) = dD_4_3_L (dC_3_2_L (x))).

Context (cCE_nil: forall x: X5,
  dC_1_0_L (dE_0_0_U (x)) = dE_1_1_U (dC_0_0_U (x))).

Context (cCE_A: forall x: X4,
  dC_2_1_L (dE_1_1_U (x)) = dE_2_2_U (dC_1_1_U (x))).

Context (cCE_B: forall x: X4,
  dC_2_1_L (dE_1_1_U (x)) = dE_2_2_U (dC_1_1_U (x))).

Context (cCE_D: forall x: X4,
  dC_2_0_L (dE_1_1_U (x)) = dE_2_2_U (dC_1_0_U (x))).

Context (cCE_AB: forall x: X3,
  dC_3_2_L (dE_2_2_U (x)) = dE_3_3_U (dC_2_2_U (x))).

Context (cCE_AD: forall x: X3,
  dC_3_1_L (dE_2_2_U (x)) = dE_3_3_U (dC_2_1_U (x))).

Context (cCE_BD: forall x: X3,
  dC_3_1_L (dE_2_2_U (x)) = dE_3_3_U (dC_2_1_U (x))).

Context (cCE_ABD: forall x: X2,
  dC_4_2_L (dE_3_3_U (x)) = dE_4_4_U (dC_3_2_U (x))).

Context (cDE_nil: forall x: X5,
  dD_1_0_L (dE_0_0_U (x)) = dE_1_1_U (dD_0_0_U (x))).

Context (cDE_A: forall x: X4,
  dD_2_1_L (dE_1_1_U (x)) = dE_2_2_U (dD_1_1_U (x))).

Context (cDE_B: forall x: X4,
  dD_2_1_L (dE_1_1_U (x)) = dE_2_2_U (dD_1_1_U (x))).

Context (cDE_C: forall x: X4,
  dD_2_1_L (dE_1_1_U (x)) = dE_2_2_U (dD_1_1_U (x))).

Context (cDE_AB: forall x: X3,
  dD_3_2_L (dE_2_2_U (x)) = dE_3_3_U (dD_2_2_U (x))).

Context (cDE_AC: forall x: X3,
  dD_3_2_L (dE_2_2_U (x)) = dE_3_3_U (dD_2_2_U (x))).

Context (cDE_BC: forall x: X3,
  dD_3_2_L (dE_2_2_U (x)) = dE_3_3_U (dD_2_2_U (x))).

Context (cDE_ABC: forall x: X2,
  dD_4_3_L (dE_3_3_U (x)) = dE_4_4_U (dD_3_3_U (x))).

Context (hABC_nil: forall x: X5,
  hexagonal_coherence
    (dA_2_0_U) (dC_2_2_U) (dB_2_1_U)
    (cBC_nil (x)) (cAB_nil (x)) (cAC_nil (x))
    (cAC_B (dB_0_0_U (x))) (cAB_C (dC_0_0_U (x))) (cBC_A (dA_0_0_U (x)))).

Context (hABC_D: forall x: X4,
  hexagonal_coherence
    (dA_3_0_U) (dC_3_2_U) (dB_3_1_U)
    (cBC_D (x)) (cAB_D (x)) (cAC_D (x))
    (cAC_BD (dB_1_0_U (x))) (cAB_CD (dC_1_0_U (x))) (cBC_AD (dA_1_0_U (x)))).

Context (hABC_E: forall x: Y4,
  hexagonal_coherence
    (dA_3_0_L) (dC_3_2_L) (dB_3_1_L)
    (cBC_E (x)) (cAB_E (x)) (cAC_E (x))
    (cAC_BE (dB_1_0_L (x))) (cAB_CE (dC_1_0_L (x))) (cBC_AE (dA_1_0_L (x)))).

Context (hABC_DE: forall x: Y3,
  hexagonal_coherence
    (dA_4_0_L) (dC_4_2_L) (dB_4_1_L)
    (cBC_DE (x)) (cAB_DE (x)) (cAC_DE (x))
    (cAC_BDE (dB_2_0_L (x))) (cAB_CDE (dC_2_0_L (x))) (cBC_ADE (dA_2_0_L (x)))).

Context (hABD_nil: forall x: X5,
  hexagonal_coherence
    (dA_2_0_U) (dD_2_2_U) (dB_2_1_U)
    (cBD_nil (x)) (cAB_nil (x)) (cAD_nil (x))
    (cAD_B (dB_0_0_U (x))) (cAB_D (dD_0_0_U (x))) (cBD_A (dA_0_0_U (x)))).

Context (hABD_C: forall x: X4,
  hexagonal_coherence
    (dA_3_0_U) (dD_3_3_U) (dB_3_1_U)
    (cBD_C (x)) (cAB_C (x)) (cAD_C (x))
    (cAD_BC (dB_1_0_U (x))) (cAB_CD (dD_1_1_U (x))) (cBD_AC (dA_1_0_U (x)))).

Context (hABD_E: forall x: Y4,
  hexagonal_coherence
    (dA_3_0_L) (dD_3_2_L) (dB_3_1_L)
    (cBD_E (x)) (cAB_E (x)) (cAD_E (x))
    (cAD_BE (dB_1_0_L (x))) (cAB_DE (dD_1_0_L (x))) (cBD_AE (dA_1_0_L (x)))).

Context (hABD_CE: forall x: Y3,
  hexagonal_coherence
    (dA_4_0_L) (dD_4_3_L) (dB_4_1_L)
    (cBD_CE (x)) (cAB_CE (x)) (cAD_CE (x))
    (cAD_BCE (dB_2_0_L (x))) (cAB_CDE (dD_2_1_L (x))) (cBD_ACE (dA_2_0_L (x)))).

Context (hABE_nil: forall x: X5,
  hexagonal_coherence
    (dA_2_0_L) (dE_2_2_U) (dB_2_1_L)
    (cBE_nil (x)) (cAB_nil (x)) (cAE_nil (x))
    (cAE_B (dB_0_0_U (x))) (cAB_E (dE_0_0_U (x))) (cBE_A (dA_0_0_U (x)))).

Context (hABE_C: forall x: X4,
  hexagonal_coherence
    (dA_3_0_L) (dE_3_3_U) (dB_3_1_L)
    (cBE_C (x)) (cAB_C (x)) (cAE_C (x))
    (cAE_BC (dB_1_0_U (x))) (cAB_CE (dE_1_1_U (x))) (cBE_AC (dA_1_0_U (x)))).

Context (hABE_D: forall x: X4,
  hexagonal_coherence
    (dA_3_0_L) (dE_3_3_U) (dB_3_1_L)
    (cBE_D (x)) (cAB_D (x)) (cAE_D (x))
    (cAE_BD (dB_1_0_U (x))) (cAB_DE (dE_1_1_U (x))) (cBE_AD (dA_1_0_U (x)))).

Context (hABE_CD: forall x: X3,
  hexagonal_coherence
    (dA_4_0_L) (dE_4_4_U) (dB_4_1_L)
    (cBE_CD (x)) (cAB_CD (x)) (cAE_CD (x))
    (cAE_BCD (dB_2_0_U (x))) (cAB_CDE (dE_2_2_U (x))) (cBE_ACD (dA_2_0_U (x)))).

Context (hACD_nil: forall x: X5,
  hexagonal_coherence
    (dA_2_0_U) (dD_2_2_U) (dC_2_1_U)
    (cCD_nil (x)) (cAC_nil (x)) (cAD_nil (x))
    (cAD_C (dC_0_0_U (x))) (cAC_D (dD_0_0_U (x))) (cCD_A (dA_0_0_U (x)))).

Context (hACD_B: forall x: X4,
  hexagonal_coherence
    (dA_3_0_U) (dD_3_3_U) (dC_3_2_U)
    (cCD_B (x)) (cAC_B (x)) (cAD_B (x))
    (cAD_BC (dC_1_1_U (x))) (cAC_BD (dD_1_1_U (x))) (cCD_AB (dA_1_0_U (x)))).

Context (hACD_E: forall x: Y4,
  hexagonal_coherence
    (dA_3_0_L) (dD_3_2_L) (dC_3_1_L)
    (cCD_E (x)) (cAC_E (x)) (cAD_E (x))
    (cAD_CE (dC_1_0_L (x))) (cAC_DE (dD_1_0_L (x))) (cCD_AE (dA_1_0_L (x)))).

Context (hACD_BE: forall x: Y3,
  hexagonal_coherence
    (dA_4_0_L) (dD_4_3_L) (dC_4_2_L)
    (cCD_BE (x)) (cAC_BE (x)) (cAD_BE (x))
    (cAD_BCE (dC_2_1_L (x))) (cAC_BDE (dD_2_1_L (x))) (cCD_ABE (dA_2_0_L (x)))).

Context (hACE_nil: forall x: X5,
  hexagonal_coherence
    (dA_2_0_L) (dE_2_2_U) (dC_2_1_L)
    (cCE_nil (x)) (cAC_nil (x)) (cAE_nil (x))
    (cAE_C (dC_0_0_U (x))) (cAC_E (dE_0_0_U (x))) (cCE_A (dA_0_0_U (x)))).

Context (hACE_B: forall x: X4,
  hexagonal_coherence
    (dA_3_0_L) (dE_3_3_U) (dC_3_2_L)
    (cCE_B (x)) (cAC_B (x)) (cAE_B (x))
    (cAE_BC (dC_1_1_U (x))) (cAC_BE (dE_1_1_U (x))) (cCE_AB (dA_1_0_U (x)))).

Context (hACE_D: forall x: X4,
  hexagonal_coherence
    (dA_3_0_L) (dE_3_3_U) (dC_3_1_L)
    (cCE_D (x)) (cAC_D (x)) (cAE_D (x))
    (cAE_CD (dC_1_0_U (x))) (cAC_DE (dE_1_1_U (x))) (cCE_AD (dA_1_0_U (x)))).

Context (hACE_BD: forall x: X3,
  hexagonal_coherence
    (dA_4_0_L) (dE_4_4_U) (dC_4_2_L)
    (cCE_BD (x)) (cAC_BD (x)) (cAE_BD (x))
    (cAE_BCD (dC_2_1_U (x))) (cAC_BDE (dE_2_2_U (x))) (cCE_ABD (dA_2_0_U (x)))).

Context (hADE_nil: forall x: X5,
  hexagonal_coherence
    (dA_2_0_L) (dE_2_2_U) (dD_2_1_L)
    (cDE_nil (x)) (cAD_nil (x)) (cAE_nil (x))
    (cAE_D (dD_0_0_U (x))) (cAD_E (dE_0_0_U (x))) (cDE_A (dA_0_0_U (x)))).

Context (hADE_B: forall x: X4,
  hexagonal_coherence
    (dA_3_0_L) (dE_3_3_U) (dD_3_2_L)
    (cDE_B (x)) (cAD_B (x)) (cAE_B (x))
    (cAE_BD (dD_1_1_U (x))) (cAD_BE (dE_1_1_U (x))) (cDE_AB (dA_1_0_U (x)))).

Context (hADE_C: forall x: X4,
  hexagonal_coherence
    (dA_3_0_L) (dE_3_3_U) (dD_3_2_L)
    (cDE_C (x)) (cAD_C (x)) (cAE_C (x))
    (cAE_CD (dD_1_1_U (x))) (cAD_CE (dE_1_1_U (x))) (cDE_AC (dA_1_0_U (x)))).

Context (hADE_BC: forall x: X3,
  hexagonal_coherence
    (dA_4_0_L) (dE_4_4_U) (dD_4_3_L)
    (cDE_BC (x)) (cAD_BC (x)) (cAE_BC (x))
    (cAE_BCD (dD_2_2_U (x))) (cAD_BCE (dE_2_2_U (x))) (cDE_ABC (dA_2_0_U (x)))).

Context (hBCD_nil: forall x: X5,
  hexagonal_coherence
    (dB_2_0_U) (dD_2_2_U) (dC_2_1_U)
    (cCD_nil (x)) (cBC_nil (x)) (cBD_nil (x))
    (cBD_C (dC_0_0_U (x))) (cBC_D (dD_0_0_U (x))) (cCD_B (dB_0_0_U (x)))).

Context (hBCD_A: forall x: X4,
  hexagonal_coherence
    (dB_3_1_U) (dD_3_3_U) (dC_3_2_U)
    (cCD_A (x)) (cBC_A (x)) (cBD_A (x))
    (cBD_AC (dC_1_1_U (x))) (cBC_AD (dD_1_1_U (x))) (cCD_AB (dB_1_1_U (x)))).

Context (hBCD_E: forall x: Y4,
  hexagonal_coherence
    (dB_3_0_L) (dD_3_2_L) (dC_3_1_L)
    (cCD_E (x)) (cBC_E (x)) (cBD_E (x))
    (cBD_CE (dC_1_0_L (x))) (cBC_DE (dD_1_0_L (x))) (cCD_BE (dB_1_0_L (x)))).

Context (hBCD_AE: forall x: Y3,
  hexagonal_coherence
    (dB_4_1_L) (dD_4_3_L) (dC_4_2_L)
    (cCD_AE (x)) (cBC_AE (x)) (cBD_AE (x))
    (cBD_ACE (dC_2_1_L (x))) (cBC_ADE (dD_2_1_L (x))) (cCD_ABE (dB_2_1_L (x)))).

Context (hBCE_nil: forall x: X5,
  hexagonal_coherence
    (dB_2_0_L) (dE_2_2_U) (dC_2_1_L)
    (cCE_nil (x)) (cBC_nil (x)) (cBE_nil (x))
    (cBE_C (dC_0_0_U (x))) (cBC_E (dE_0_0_U (x))) (cCE_B (dB_0_0_U (x)))).

Context (hBCE_A: forall x: X4,
  hexagonal_coherence
    (dB_3_1_L) (dE_3_3_U) (dC_3_2_L)
    (cCE_A (x)) (cBC_A (x)) (cBE_A (x))
    (cBE_AC (dC_1_1_U (x))) (cBC_AE (dE_1_1_U (x))) (cCE_AB (dB_1_1_U (x)))).

Context (hBCE_D: forall x: X4,
  hexagonal_coherence
    (dB_3_0_L) (dE_3_3_U) (dC_3_1_L)
    (cCE_D (x)) (cBC_D (x)) (cBE_D (x))
    (cBE_CD (dC_1_0_U (x))) (cBC_DE (dE_1_1_U (x))) (cCE_BD (dB_1_0_U (x)))).

Context (hBCE_AD: forall x: X3,
  hexagonal_coherence
    (dB_4_1_L) (dE_4_4_U) (dC_4_2_L)
    (cCE_AD (x)) (cBC_AD (x)) (cBE_AD (x))
    (cBE_ACD (dC_2_1_U (x))) (cBC_ADE (dE_2_2_U (x))) (cCE_ABD (dB_2_1_U (x)))).

Context (hBDE_nil: forall x: X5,
  hexagonal_coherence
    (dB_2_0_L) (dE_2_2_U) (dD_2_1_L)
    (cDE_nil (x)) (cBD_nil (x)) (cBE_nil (x))
    (cBE_D (dD_0_0_U (x))) (cBD_E (dE_0_0_U (x))) (cDE_B (dB_0_0_U (x)))).

Context (hBDE_A: forall x: X4,
  hexagonal_coherence
    (dB_3_1_L) (dE_3_3_U) (dD_3_2_L)
    (cDE_A (x)) (cBD_A (x)) (cBE_A (x))
    (cBE_AD (dD_1_1_U (x))) (cBD_AE (dE_1_1_U (x))) (cDE_AB (dB_1_1_U (x)))).

Context (hBDE_C: forall x: X4,
  hexagonal_coherence
    (dB_3_0_L) (dE_3_3_U) (dD_3_2_L)
    (cDE_C (x)) (cBD_C (x)) (cBE_C (x))
    (cBE_CD (dD_1_1_U (x))) (cBD_CE (dE_1_1_U (x))) (cDE_BC (dB_1_0_U (x)))).

Context (hBDE_AC: forall x: X3,
  hexagonal_coherence
    (dB_4_1_L) (dE_4_4_U) (dD_4_3_L)
    (cDE_AC (x)) (cBD_AC (x)) (cBE_AC (x))
    (cBE_ACD (dD_2_2_U (x))) (cBD_ACE (dE_2_2_U (x))) (cDE_ABC (dB_2_1_U (x)))).

Context (hCDE_nil: forall x: X5,
  hexagonal_coherence
    (dC_2_0_L) (dE_2_2_U) (dD_2_1_L)
    (cDE_nil (x)) (cCD_nil (x)) (cCE_nil (x))
    (cCE_D (dD_0_0_U (x))) (cCD_E (dE_0_0_U (x))) (cDE_C (dC_0_0_U (x)))).

Context (hCDE_A: forall x: X4,
  hexagonal_coherence
    (dC_3_1_L) (dE_3_3_U) (dD_3_2_L)
    (cDE_A (x)) (cCD_A (x)) (cCE_A (x))
    (cCE_AD (dD_1_1_U (x))) (cCD_AE (dE_1_1_U (x))) (cDE_AC (dC_1_1_U (x)))).

Context (hCDE_B: forall x: X4,
  hexagonal_coherence
    (dC_3_1_L) (dE_3_3_U) (dD_3_2_L)
    (cDE_B (x)) (cCD_B (x)) (cCE_B (x))
    (cCE_BD (dD_1_1_U (x))) (cCD_BE (dE_1_1_U (x))) (cDE_BC (dC_1_1_U (x)))).

Context (hCDE_AB: forall x: X3,
  hexagonal_coherence
    (dC_4_2_L) (dE_4_4_U) (dD_4_3_L)
    (cDE_AB (x)) (cCD_AB (x)) (cCE_AB (x))
    (cCE_ABD (dD_2_2_U (x))) (cCD_ABE (dE_2_2_U (x))) (cDE_ABC (dC_2_2_U (x)))).

Context (kABCD_nil: forall x: X5,
  @permutahedral_coherence
    (X3) (X2) (X1)
    (X3) (X2) (dD_2_2_U)
    (dD_3_3_U) (dA_2_0_U) (dC_2_2_U)
    (dB_2_1_U) (dA_3_0_U) (dC_3_2_U)
    (dB_3_1_U) (cAD_BC) (cCD_AB)
    (cBD_AC) (dB_2_0_U) (dC_2_1_U)
    (dA_2_0_U) (dB_2_1_U) (cAC_BD)
    (cAB_CD) (cBC_AD) (dB_1_0_U (dC_0_0_U (x)))
    (dC_1_1_U (dB_0_0_U (x))) (dA_1_0_U (dB_0_0_U (x))) (dB_1_1_U (dA_0_0_U (x)))
    (dA_1_0_U (dC_0_0_U (x))) (dC_1_1_U (dA_0_0_U (x))) (cBC_nil (x))
    (cAB_nil (x)) (cAC_nil (x)) (cAC_B (dB_0_0_U (x)))
    (cAB_C (dC_0_0_U (x))) (cBC_A (dA_0_0_U (x))) (dC_1_0_U (dD_0_0_U (x)))
    (dD_1_1_U (dC_0_0_U (x))) (dB_1_0_U (dD_0_0_U (x))) (dD_1_1_U (dB_0_0_U (x)))
    (dA_1_0_U (dD_0_0_U (x))) (dD_1_1_U (dA_0_0_U (x))) (cCD_nil (x))
    (cBD_nil (x)) (cAD_nil (x)) (cBD_C (dC_0_0_U (x)))
    (cCD_B (dB_0_0_U (x))) (cAD_B (dB_0_0_U (x))) (cBD_A (dA_0_0_U (x)))
    (cAD_C (dC_0_0_U (x))) (cCD_A (dA_0_0_U (x))) (cBC_D (dD_0_0_U (x)))
    (cAB_D (dD_0_0_U (x))) (cAC_D (dD_0_0_U (x))) (hBCD_nil (x))
    (hABD_nil (x)) (hACD_nil (x)) (hABC_nil (x))
    (hACD_B (dB_0_0_U (x))) (hABD_C (dC_0_0_U (x))) (hBCD_A (dA_0_0_U (x)))
    (hABC_D (dD_0_0_U (x)))).

Context (kABCD_E: forall x: Y4,
  @permutahedral_coherence
    (Y2) (Y1) (Y0)
    (Y2) (Y1) (dD_3_2_L)
    (dD_4_3_L) (dA_3_0_L) (dC_3_2_L)
    (dB_3_1_L) (dA_4_0_L) (dC_4_2_L)
    (dB_4_1_L) (cAD_BCE) (cCD_ABE)
    (cBD_ACE) (dB_3_0_L) (dC_3_1_L)
    (dA_3_0_L) (dB_3_1_L) (cAC_BDE)
    (cAB_CDE) (cBC_ADE) (dB_2_0_L (dC_1_0_L (x)))
    (dC_2_1_L (dB_1_0_L (x))) (dA_2_0_L (dB_1_0_L (x))) (dB_2_1_L (dA_1_0_L (x)))
    (dA_2_0_L (dC_1_0_L (x))) (dC_2_1_L (dA_1_0_L (x))) (cBC_E (x))
    (cAB_E (x)) (cAC_E (x)) (cAC_BE (dB_1_0_L (x)))
    (cAB_CE (dC_1_0_L (x))) (cBC_AE (dA_1_0_L (x))) (dC_2_0_L (dD_1_0_L (x)))
    (dD_2_1_L (dC_1_0_L (x))) (dB_2_0_L (dD_1_0_L (x))) (dD_2_1_L (dB_1_0_L (x)))
    (dA_2_0_L (dD_1_0_L (x))) (dD_2_1_L (dA_1_0_L (x))) (cCD_E (x))
    (cBD_E (x)) (cAD_E (x)) (cBD_CE (dC_1_0_L (x)))
    (cCD_BE (dB_1_0_L (x))) (cAD_BE (dB_1_0_L (x))) (cBD_AE (dA_1_0_L (x)))
    (cAD_CE (dC_1_0_L (x))) (cCD_AE (dA_1_0_L (x))) (cBC_DE (dD_1_0_L (x)))
    (cAB_DE (dD_1_0_L (x))) (cAC_DE (dD_1_0_L (x))) (hBCD_E (x))
    (hABD_E (x)) (hACD_E (x)) (hABC_E (x))
    (hACD_BE (dB_1_0_L (x))) (hABD_CE (dC_1_0_L (x))) (hBCD_AE (dA_1_0_L (x)))
    (hABC_DE (dD_1_0_L (x)))).

Context (kABCE_nil: forall x: X5,
  @permutahedral_coherence
    (Y3) (Y2) (Y1)
    (X3) (X2) (dE_2_2_U)
    (dE_3_3_U) (dA_2_0_U) (dC_2_2_U)
    (dB_2_1_U) (dA_3_0_L) (dC_3_2_L)
    (dB_3_1_L) (cAE_BC) (cCE_AB)
    (cBE_AC) (dB_2_0_L) (dC_2_1_L)
    (dA_2_0_L) (dB_2_1_L) (cAC_BE)
    (cAB_CE) (cBC_AE) (dB_1_0_U (dC_0_0_U (x)))
    (dC_1_1_U (dB_0_0_U (x))) (dA_1_0_U (dB_0_0_U (x))) (dB_1_1_U (dA_0_0_U (x)))
    (dA_1_0_U (dC_0_0_U (x))) (dC_1_1_U (dA_0_0_U (x))) (cBC_nil (x))
    (cAB_nil (x)) (cAC_nil (x)) (cAC_B (dB_0_0_U (x)))
    (cAB_C (dC_0_0_U (x))) (cBC_A (dA_0_0_U (x))) (dC_1_0_L (dE_0_0_U (x)))
    (dE_1_1_U (dC_0_0_U (x))) (dB_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dB_0_0_U (x)))
    (dA_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dA_0_0_U (x))) (cCE_nil (x))
    (cBE_nil (x)) (cAE_nil (x)) (cBE_C (dC_0_0_U (x)))
    (cCE_B (dB_0_0_U (x))) (cAE_B (dB_0_0_U (x))) (cBE_A (dA_0_0_U (x)))
    (cAE_C (dC_0_0_U (x))) (cCE_A (dA_0_0_U (x))) (cBC_E (dE_0_0_U (x)))
    (cAB_E (dE_0_0_U (x))) (cAC_E (dE_0_0_U (x))) (hBCE_nil (x))
    (hABE_nil (x)) (hACE_nil (x)) (hABC_nil (x))
    (hACE_B (dB_0_0_U (x))) (hABE_C (dC_0_0_U (x))) (hBCE_A (dA_0_0_U (x)))
    (hABC_E (dE_0_0_U (x)))).

Context (kABCE_D: forall x: X4,
  @permutahedral_coherence
    (Y2) (Y1) (Y0)
    (X2) (X1) (dE_3_3_U)
    (dE_4_4_U) (dA_3_0_U) (dC_3_2_U)
    (dB_3_1_U) (dA_4_0_L) (dC_4_2_L)
    (dB_4_1_L) (cAE_BCD) (cCE_ABD)
    (cBE_ACD) (dB_3_0_L) (dC_3_1_L)
    (dA_3_0_L) (dB_3_1_L) (cAC_BDE)
    (cAB_CDE) (cBC_ADE) (dB_2_0_U (dC_1_0_U (x)))
    (dC_2_1_U (dB_1_0_U (x))) (dA_2_0_U (dB_1_0_U (x))) (dB_2_1_U (dA_1_0_U (x)))
    (dA_2_0_U (dC_1_0_U (x))) (dC_2_1_U (dA_1_0_U (x))) (cBC_D (x))
    (cAB_D (x)) (cAC_D (x)) (cAC_BD (dB_1_0_U (x)))
    (cAB_CD (dC_1_0_U (x))) (cBC_AD (dA_1_0_U (x))) (dC_2_0_L (dE_1_1_U (x)))
    (dE_2_2_U (dC_1_0_U (x))) (dB_2_0_L (dE_1_1_U (x))) (dE_2_2_U (dB_1_0_U (x)))
    (dA_2_0_L (dE_1_1_U (x))) (dE_2_2_U (dA_1_0_U (x))) (cCE_D (x))
    (cBE_D (x)) (cAE_D (x)) (cBE_CD (dC_1_0_U (x)))
    (cCE_BD (dB_1_0_U (x))) (cAE_BD (dB_1_0_U (x))) (cBE_AD (dA_1_0_U (x)))
    (cAE_CD (dC_1_0_U (x))) (cCE_AD (dA_1_0_U (x))) (cBC_DE (dE_1_1_U (x)))
    (cAB_DE (dE_1_1_U (x))) (cAC_DE (dE_1_1_U (x))) (hBCE_D (x))
    (hABE_D (x)) (hACE_D (x)) (hABC_D (x))
    (hACE_BD (dB_1_0_U (x))) (hABE_CD (dC_1_0_U (x))) (hBCE_AD (dA_1_0_U (x)))
    (hABC_DE (dE_1_1_U (x)))).

Context (kABDE_nil: forall x: X5,
  @permutahedral_coherence
    (Y3) (Y2) (Y1)
    (X3) (X2) (dE_2_2_U)
    (dE_3_3_U) (dA_2_0_U) (dD_2_2_U)
    (dB_2_1_U) (dA_3_0_L) (dD_3_2_L)
    (dB_3_1_L) (cAE_BD) (cDE_AB)
    (cBE_AD) (dB_2_0_L) (dD_2_1_L)
    (dA_2_0_L) (dB_2_1_L) (cAD_BE)
    (cAB_DE) (cBD_AE) (dB_1_0_U (dD_0_0_U (x)))
    (dD_1_1_U (dB_0_0_U (x))) (dA_1_0_U (dB_0_0_U (x))) (dB_1_1_U (dA_0_0_U (x)))
    (dA_1_0_U (dD_0_0_U (x))) (dD_1_1_U (dA_0_0_U (x))) (cBD_nil (x))
    (cAB_nil (x)) (cAD_nil (x)) (cAD_B (dB_0_0_U (x)))
    (cAB_D (dD_0_0_U (x))) (cBD_A (dA_0_0_U (x))) (dD_1_0_L (dE_0_0_U (x)))
    (dE_1_1_U (dD_0_0_U (x))) (dB_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dB_0_0_U (x)))
    (dA_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dA_0_0_U (x))) (cDE_nil (x))
    (cBE_nil (x)) (cAE_nil (x)) (cBE_D (dD_0_0_U (x)))
    (cDE_B (dB_0_0_U (x))) (cAE_B (dB_0_0_U (x))) (cBE_A (dA_0_0_U (x)))
    (cAE_D (dD_0_0_U (x))) (cDE_A (dA_0_0_U (x))) (cBD_E (dE_0_0_U (x)))
    (cAB_E (dE_0_0_U (x))) (cAD_E (dE_0_0_U (x))) (hBDE_nil (x))
    (hABE_nil (x)) (hADE_nil (x)) (hABD_nil (x))
    (hADE_B (dB_0_0_U (x))) (hABE_D (dD_0_0_U (x))) (hBDE_A (dA_0_0_U (x)))
    (hABD_E (dE_0_0_U (x)))).

Context (kABDE_C: forall x: X4,
  @permutahedral_coherence
    (Y2) (Y1) (Y0)
    (X2) (X1) (dE_3_3_U)
    (dE_4_4_U) (dA_3_0_U) (dD_3_3_U)
    (dB_3_1_U) (dA_4_0_L) (dD_4_3_L)
    (dB_4_1_L) (cAE_BCD) (cDE_ABC)
    (cBE_ACD) (dB_3_0_L) (dD_3_2_L)
    (dA_3_0_L) (dB_3_1_L) (cAD_BCE)
    (cAB_CDE) (cBD_ACE) (dB_2_0_U (dD_1_1_U (x)))
    (dD_2_2_U (dB_1_0_U (x))) (dA_2_0_U (dB_1_0_U (x))) (dB_2_1_U (dA_1_0_U (x)))
    (dA_2_0_U (dD_1_1_U (x))) (dD_2_2_U (dA_1_0_U (x))) (cBD_C (x))
    (cAB_C (x)) (cAD_C (x)) (cAD_BC (dB_1_0_U (x)))
    (cAB_CD (dD_1_1_U (x))) (cBD_AC (dA_1_0_U (x))) (dD_2_1_L (dE_1_1_U (x)))
    (dE_2_2_U (dD_1_1_U (x))) (dB_2_0_L (dE_1_1_U (x))) (dE_2_2_U (dB_1_0_U (x)))
    (dA_2_0_L (dE_1_1_U (x))) (dE_2_2_U (dA_1_0_U (x))) (cDE_C (x))
    (cBE_C (x)) (cAE_C (x)) (cBE_CD (dD_1_1_U (x)))
    (cDE_BC (dB_1_0_U (x))) (cAE_BC (dB_1_0_U (x))) (cBE_AC (dA_1_0_U (x)))
    (cAE_CD (dD_1_1_U (x))) (cDE_AC (dA_1_0_U (x))) (cBD_CE (dE_1_1_U (x)))
    (cAB_CE (dE_1_1_U (x))) (cAD_CE (dE_1_1_U (x))) (hBDE_C (x))
    (hABE_C (x)) (hADE_C (x)) (hABD_C (x))
    (hADE_BC (dB_1_0_U (x))) (hABE_CD (dD_1_1_U (x))) (hBDE_AC (dA_1_0_U (x)))
    (hABD_CE (dE_1_1_U (x)))).

Context (kACDE_nil: forall x: X5,
  @permutahedral_coherence
    (Y3) (Y2) (Y1)
    (X3) (X2) (dE_2_2_U)
    (dE_3_3_U) (dA_2_0_U) (dD_2_2_U)
    (dC_2_1_U) (dA_3_0_L) (dD_3_2_L)
    (dC_3_1_L) (cAE_CD) (cDE_AC)
    (cCE_AD) (dC_2_0_L) (dD_2_1_L)
    (dA_2_0_L) (dC_2_1_L) (cAD_CE)
    (cAC_DE) (cCD_AE) (dC_1_0_U (dD_0_0_U (x)))
    (dD_1_1_U (dC_0_0_U (x))) (dA_1_0_U (dC_0_0_U (x))) (dC_1_1_U (dA_0_0_U (x)))
    (dA_1_0_U (dD_0_0_U (x))) (dD_1_1_U (dA_0_0_U (x))) (cCD_nil (x))
    (cAC_nil (x)) (cAD_nil (x)) (cAD_C (dC_0_0_U (x)))
    (cAC_D (dD_0_0_U (x))) (cCD_A (dA_0_0_U (x))) (dD_1_0_L (dE_0_0_U (x)))
    (dE_1_1_U (dD_0_0_U (x))) (dC_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dC_0_0_U (x)))
    (dA_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dA_0_0_U (x))) (cDE_nil (x))
    (cCE_nil (x)) (cAE_nil (x)) (cCE_D (dD_0_0_U (x)))
    (cDE_C (dC_0_0_U (x))) (cAE_C (dC_0_0_U (x))) (cCE_A (dA_0_0_U (x)))
    (cAE_D (dD_0_0_U (x))) (cDE_A (dA_0_0_U (x))) (cCD_E (dE_0_0_U (x)))
    (cAC_E (dE_0_0_U (x))) (cAD_E (dE_0_0_U (x))) (hCDE_nil (x))
    (hACE_nil (x)) (hADE_nil (x)) (hACD_nil (x))
    (hADE_C (dC_0_0_U (x))) (hACE_D (dD_0_0_U (x))) (hCDE_A (dA_0_0_U (x)))
    (hACD_E (dE_0_0_U (x)))).

Context (kACDE_B: forall x: X4,
  @permutahedral_coherence
    (Y2) (Y1) (Y0)
    (X2) (X1) (dE_3_3_U)
    (dE_4_4_U) (dA_3_0_U) (dD_3_3_U)
    (dC_3_2_U) (dA_4_0_L) (dD_4_3_L)
    (dC_4_2_L) (cAE_BCD) (cDE_ABC)
    (cCE_ABD) (dC_3_1_L) (dD_3_2_L)
    (dA_3_0_L) (dC_3_2_L) (cAD_BCE)
    (cAC_BDE) (cCD_ABE) (dC_2_1_U (dD_1_1_U (x)))
    (dD_2_2_U (dC_1_1_U (x))) (dA_2_0_U (dC_1_1_U (x))) (dC_2_2_U (dA_1_0_U (x)))
    (dA_2_0_U (dD_1_1_U (x))) (dD_2_2_U (dA_1_0_U (x))) (cCD_B (x))
    (cAC_B (x)) (cAD_B (x)) (cAD_BC (dC_1_1_U (x)))
    (cAC_BD (dD_1_1_U (x))) (cCD_AB (dA_1_0_U (x))) (dD_2_1_L (dE_1_1_U (x)))
    (dE_2_2_U (dD_1_1_U (x))) (dC_2_1_L (dE_1_1_U (x))) (dE_2_2_U (dC_1_1_U (x)))
    (dA_2_0_L (dE_1_1_U (x))) (dE_2_2_U (dA_1_0_U (x))) (cDE_B (x))
    (cCE_B (x)) (cAE_B (x)) (cCE_BD (dD_1_1_U (x)))
    (cDE_BC (dC_1_1_U (x))) (cAE_BC (dC_1_1_U (x))) (cCE_AB (dA_1_0_U (x)))
    (cAE_BD (dD_1_1_U (x))) (cDE_AB (dA_1_0_U (x))) (cCD_BE (dE_1_1_U (x)))
    (cAC_BE (dE_1_1_U (x))) (cAD_BE (dE_1_1_U (x))) (hCDE_B (x))
    (hACE_B (x)) (hADE_B (x)) (hACD_B (x))
    (hADE_BC (dC_1_1_U (x))) (hACE_BD (dD_1_1_U (x))) (hCDE_AB (dA_1_0_U (x)))
    (hACD_BE (dE_1_1_U (x)))).

Context (kBCDE_nil: forall x: X5,
  @permutahedral_coherence
    (Y3) (Y2) (Y1)
    (X3) (X2) (dE_2_2_U)
    (dE_3_3_U) (dB_2_0_U) (dD_2_2_U)
    (dC_2_1_U) (dB_3_0_L) (dD_3_2_L)
    (dC_3_1_L) (cBE_CD) (cDE_BC)
    (cCE_BD) (dC_2_0_L) (dD_2_1_L)
    (dB_2_0_L) (dC_2_1_L) (cBD_CE)
    (cBC_DE) (cCD_BE) (dC_1_0_U (dD_0_0_U (x)))
    (dD_1_1_U (dC_0_0_U (x))) (dB_1_0_U (dC_0_0_U (x))) (dC_1_1_U (dB_0_0_U (x)))
    (dB_1_0_U (dD_0_0_U (x))) (dD_1_1_U (dB_0_0_U (x))) (cCD_nil (x))
    (cBC_nil (x)) (cBD_nil (x)) (cBD_C (dC_0_0_U (x)))
    (cBC_D (dD_0_0_U (x))) (cCD_B (dB_0_0_U (x))) (dD_1_0_L (dE_0_0_U (x)))
    (dE_1_1_U (dD_0_0_U (x))) (dC_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dC_0_0_U (x)))
    (dB_1_0_L (dE_0_0_U (x))) (dE_1_1_U (dB_0_0_U (x))) (cDE_nil (x))
    (cCE_nil (x)) (cBE_nil (x)) (cCE_D (dD_0_0_U (x)))
    (cDE_C (dC_0_0_U (x))) (cBE_C (dC_0_0_U (x))) (cCE_B (dB_0_0_U (x)))
    (cBE_D (dD_0_0_U (x))) (cDE_B (dB_0_0_U (x))) (cCD_E (dE_0_0_U (x)))
    (cBC_E (dE_0_0_U (x))) (cBD_E (dE_0_0_U (x))) (hCDE_nil (x))
    (hBCE_nil (x)) (hBDE_nil (x)) (hBCD_nil (x))
    (hBDE_C (dC_0_0_U (x))) (hBCE_D (dD_0_0_U (x))) (hCDE_B (dB_0_0_U (x)))
    (hBCD_E (dE_0_0_U (x)))).

Context (kBCDE_A: forall x: X4,
  @permutahedral_coherence
    (Y2) (Y1) (Y0)
    (X2) (X1) (dE_3_3_U)
    (dE_4_4_U) (dB_3_1_U) (dD_3_3_U)
    (dC_3_2_U) (dB_4_1_L) (dD_4_3_L)
    (dC_4_2_L) (cBE_ACD) (cDE_ABC)
    (cCE_ABD) (dC_3_1_L) (dD_3_2_L)
    (dB_3_1_L) (dC_3_2_L) (cBD_ACE)
    (cBC_ADE) (cCD_ABE) (dC_2_1_U (dD_1_1_U (x)))
    (dD_2_2_U (dC_1_1_U (x))) (dB_2_1_U (dC_1_1_U (x))) (dC_2_2_U (dB_1_1_U (x)))
    (dB_2_1_U (dD_1_1_U (x))) (dD_2_2_U (dB_1_1_U (x))) (cCD_A (x))
    (cBC_A (x)) (cBD_A (x)) (cBD_AC (dC_1_1_U (x)))
    (cBC_AD (dD_1_1_U (x))) (cCD_AB (dB_1_1_U (x))) (dD_2_1_L (dE_1_1_U (x)))
    (dE_2_2_U (dD_1_1_U (x))) (dC_2_1_L (dE_1_1_U (x))) (dE_2_2_U (dC_1_1_U (x)))
    (dB_2_1_L (dE_1_1_U (x))) (dE_2_2_U (dB_1_1_U (x))) (cDE_A (x))
    (cCE_A (x)) (cBE_A (x)) (cCE_AD (dD_1_1_U (x)))
    (cDE_AC (dC_1_1_U (x))) (cBE_AC (dC_1_1_U (x))) (cCE_AB (dB_1_1_U (x)))
    (cBE_AD (dD_1_1_U (x))) (cDE_AB (dB_1_1_U (x))) (cCD_AE (dE_1_1_U (x)))
    (cBC_AE (dE_1_1_U (x))) (cBD_AE (dE_1_1_U (x))) (hCDE_A (x))
    (hBCE_A (x)) (hBDE_A (x)) (hBCD_A (x))
    (hBDE_AC (dC_1_1_U (x))) (hBCE_AD (dD_1_1_U (x))) (hCDE_AB (dB_1_1_U (x)))
    (hBCD_AE (dE_1_1_U (x)))).

(** The ten permutahedral faces use the supplied P4 coherences. The twenty
    prism faces use the canonical map and naturality fillers. *)
Context (x: X5).

Definition facet_BCDE_A :=
  kBCDE_A (dA_0_0_U (x)).

Definition facet_A_BCDE :=
  square_cube_map dA_4_0_L (kBCDE_nil x).

Definition facet_ACDE_B :=
  kACDE_B (dB_0_0_U (x)).

Definition facet_B_ACDE :=
  square_cube_map dB_4_1_L (kACDE_nil x).

Definition facet_ABDE_C :=
  kABDE_C (dC_0_0_U (x)).

Definition facet_C_ABDE :=
  square_cube_map dC_4_2_L (kABDE_nil x).

Definition facet_ABCE_D :=
  kABCE_D (dD_0_0_U (x)).

Definition facet_D_ABCE :=
  square_cube_map dD_4_3_L (kABCE_nil x).

Definition facet_ABCD_E :=
  kABCD_E (dE_0_0_U (x)).

Definition facet_E_ABCD :=
  square_cube_map dE_4_4_U (kABCD_nil x).

Definition facet_CDE_AB :=
  hexagonal_prism_coherence_nat_fill (dC_4_2_L) (dE_4_4_U) (dD_4_3_L)
    (fun z => dD_3_2_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dD_2_2_U (z)))
    (fun z => dC_3_2_U (dD_2_2_U (z))) (fun z => dD_3_3_U (dC_2_2_U (z)))
    (fun z => dC_3_2_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dC_2_2_U (z))) (cDE_AB)
    (cCD_AB) (cCE_AB) (fun z => cCE_ABD (dD_2_2_U (z))) (fun z => cCD_ABE (dE_2_2_U (z)))
    (fun z => cDE_ABC (dC_2_2_U (z))) (hCDE_AB) (cAB_nil (x)).

Definition facet_AB_CDE :=
  hexagonal_prism_coherence_map_fill (dC_2_0_L) (dE_2_2_U) (dD_2_1_L) (dB_3_0_L)
    (dA_3_0_L) (dA_4_0_L) (dB_4_1_L) (cAB_CDE) (cDE_nil (x)) (cCD_nil (x)) (cCE_nil (x))
    (cCE_D (dD_0_0_U (x))) (cCD_E (dE_0_0_U (x))) (cDE_C (dC_0_0_U (x))) (hCDE_nil (x)).

Definition facet_BDE_AC :=
  hexagonal_prism_coherence_nat_fill (dB_4_1_L) (dE_4_4_U) (dD_4_3_L)
    (fun z => dD_3_2_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dD_2_2_U (z)))
    (fun z => dB_3_1_U (dD_2_2_U (z))) (fun z => dD_3_3_U (dB_2_1_U (z)))
    (fun z => dB_3_1_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dB_2_1_U (z))) (cDE_AC)
    (cBD_AC) (cBE_AC) (fun z => cBE_ACD (dD_2_2_U (z))) (fun z => cBD_ACE (dE_2_2_U (z)))
    (fun z => cDE_ABC (dB_2_1_U (z))) (hBDE_AC) (cAC_nil (x)).

Definition facet_AC_BDE :=
  hexagonal_prism_coherence_map_fill (dB_2_0_L) (dE_2_2_U) (dD_2_1_L) (dC_3_1_L)
    (dA_3_0_L) (dA_4_0_L) (dC_4_2_L) (cAC_BDE) (cDE_nil (x)) (cBD_nil (x)) (cBE_nil (x))
    (cBE_D (dD_0_0_U (x))) (cBD_E (dE_0_0_U (x))) (cDE_B (dB_0_0_U (x))) (hBDE_nil (x)).

Definition facet_BCE_AD :=
  hexagonal_prism_coherence_nat_fill (dB_4_1_L) (dE_4_4_U) (dC_4_2_L)
    (fun z => dC_3_1_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dC_2_1_U (z)))
    (fun z => dB_3_1_U (dC_2_1_U (z))) (fun z => dC_3_2_U (dB_2_1_U (z)))
    (fun z => dB_3_1_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dB_2_1_U (z))) (cCE_AD)
    (cBC_AD) (cBE_AD) (fun z => cBE_ACD (dC_2_1_U (z))) (fun z => cBC_ADE (dE_2_2_U (z)))
    (fun z => cCE_ABD (dB_2_1_U (z))) (hBCE_AD) (cAD_nil (x)).

Definition facet_AD_BCE :=
  hexagonal_prism_coherence_map_fill (dB_2_0_L) (dE_2_2_U) (dC_2_1_L) (dD_3_2_L)
    (dA_3_0_L) (dA_4_0_L) (dD_4_3_L) (cAD_BCE) (cCE_nil (x)) (cBC_nil (x)) (cBE_nil (x))
    (cBE_C (dC_0_0_U (x))) (cBC_E (dE_0_0_U (x))) (cCE_B (dB_0_0_U (x))) (hBCE_nil (x)).

Definition facet_BCD_AE :=
  hexagonal_prism_coherence_nat_fill (dB_4_1_L) (dD_4_3_L) (dC_4_2_L)
    (fun z => dC_3_1_L (dD_2_1_L (z))) (fun z => dD_3_2_L (dC_2_1_L (z)))
    (fun z => dB_3_1_L (dC_2_1_L (z))) (fun z => dC_3_2_L (dB_2_1_L (z)))
    (fun z => dB_3_1_L (dD_2_1_L (z))) (fun z => dD_3_2_L (dB_2_1_L (z))) (cCD_AE)
    (cBC_AE) (cBD_AE) (fun z => cBD_ACE (dC_2_1_L (z))) (fun z => cBC_ADE (dD_2_1_L (z)))
    (fun z => cCD_ABE (dB_2_1_L (z))) (hBCD_AE) (cAE_nil (x)).

Definition facet_AE_BCD :=
  hexagonal_prism_coherence_map_fill (dB_2_0_U) (dD_2_2_U) (dC_2_1_U) (dE_3_3_U)
    (dA_3_0_U) (dA_4_0_L) (dE_4_4_U) (cAE_BCD) (cCD_nil (x)) (cBC_nil (x)) (cBD_nil (x))
    (cBD_C (dC_0_0_U (x))) (cBC_D (dD_0_0_U (x))) (cCD_B (dB_0_0_U (x))) (hBCD_nil (x)).

Definition facet_ADE_BC :=
  hexagonal_prism_coherence_nat_fill (dA_4_0_L) (dE_4_4_U) (dD_4_3_L)
    (fun z => dD_3_2_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dD_2_2_U (z)))
    (fun z => dA_3_0_U (dD_2_2_U (z))) (fun z => dD_3_3_U (dA_2_0_U (z)))
    (fun z => dA_3_0_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dA_2_0_U (z))) (cDE_BC)
    (cAD_BC) (cAE_BC) (fun z => cAE_BCD (dD_2_2_U (z))) (fun z => cAD_BCE (dE_2_2_U (z)))
    (fun z => cDE_ABC (dA_2_0_U (z))) (hADE_BC) (cBC_nil (x)).

Definition facet_BC_ADE :=
  hexagonal_prism_coherence_map_fill (dA_2_0_L) (dE_2_2_U) (dD_2_1_L) (dC_3_1_L)
    (dB_3_1_L) (dB_4_1_L) (dC_4_2_L) (cBC_ADE) (cDE_nil (x)) (cAD_nil (x)) (cAE_nil (x))
    (cAE_D (dD_0_0_U (x))) (cAD_E (dE_0_0_U (x))) (cDE_A (dA_0_0_U (x))) (hADE_nil (x)).

Definition facet_ACE_BD :=
  hexagonal_prism_coherence_nat_fill (dA_4_0_L) (dE_4_4_U) (dC_4_2_L)
    (fun z => dC_3_1_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dC_2_1_U (z)))
    (fun z => dA_3_0_U (dC_2_1_U (z))) (fun z => dC_3_2_U (dA_2_0_U (z)))
    (fun z => dA_3_0_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dA_2_0_U (z))) (cCE_BD)
    (cAC_BD) (cAE_BD) (fun z => cAE_BCD (dC_2_1_U (z))) (fun z => cAC_BDE (dE_2_2_U (z)))
    (fun z => cCE_ABD (dA_2_0_U (z))) (hACE_BD) (cBD_nil (x)).

Definition facet_BD_ACE :=
  hexagonal_prism_coherence_map_fill (dA_2_0_L) (dE_2_2_U) (dC_2_1_L) (dD_3_2_L)
    (dB_3_1_L) (dB_4_1_L) (dD_4_3_L) (cBD_ACE) (cCE_nil (x)) (cAC_nil (x)) (cAE_nil (x))
    (cAE_C (dC_0_0_U (x))) (cAC_E (dE_0_0_U (x))) (cCE_A (dA_0_0_U (x))) (hACE_nil (x)).

Definition facet_ACD_BE :=
  hexagonal_prism_coherence_nat_fill (dA_4_0_L) (dD_4_3_L) (dC_4_2_L)
    (fun z => dC_3_1_L (dD_2_1_L (z))) (fun z => dD_3_2_L (dC_2_1_L (z)))
    (fun z => dA_3_0_L (dC_2_1_L (z))) (fun z => dC_3_2_L (dA_2_0_L (z)))
    (fun z => dA_3_0_L (dD_2_1_L (z))) (fun z => dD_3_2_L (dA_2_0_L (z))) (cCD_BE)
    (cAC_BE) (cAD_BE) (fun z => cAD_BCE (dC_2_1_L (z))) (fun z => cAC_BDE (dD_2_1_L (z)))
    (fun z => cCD_ABE (dA_2_0_L (z))) (hACD_BE) (cBE_nil (x)).

Definition facet_BE_ACD :=
  hexagonal_prism_coherence_map_fill (dA_2_0_U) (dD_2_2_U) (dC_2_1_U) (dE_3_3_U)
    (dB_3_1_U) (dB_4_1_L) (dE_4_4_U) (cBE_ACD) (cCD_nil (x)) (cAC_nil (x)) (cAD_nil (x))
    (cAD_C (dC_0_0_U (x))) (cAC_D (dD_0_0_U (x))) (cCD_A (dA_0_0_U (x))) (hACD_nil (x)).

Definition facet_ABE_CD :=
  hexagonal_prism_coherence_nat_fill (dA_4_0_L) (dE_4_4_U) (dB_4_1_L)
    (fun z => dB_3_0_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dB_2_0_U (z)))
    (fun z => dA_3_0_U (dB_2_0_U (z))) (fun z => dB_3_1_U (dA_2_0_U (z)))
    (fun z => dA_3_0_L (dE_2_2_U (z))) (fun z => dE_3_3_U (dA_2_0_U (z))) (cBE_CD)
    (cAB_CD) (cAE_CD) (fun z => cAE_BCD (dB_2_0_U (z))) (fun z => cAB_CDE (dE_2_2_U (z)))
    (fun z => cBE_ACD (dA_2_0_U (z))) (hABE_CD) (cCD_nil (x)).

Definition facet_CD_ABE :=
  hexagonal_prism_coherence_map_fill (dA_2_0_L) (dE_2_2_U) (dB_2_1_L) (dD_3_2_L)
    (dC_3_2_L) (dC_4_2_L) (dD_4_3_L) (cCD_ABE) (cBE_nil (x)) (cAB_nil (x)) (cAE_nil (x))
    (cAE_B (dB_0_0_U (x))) (cAB_E (dE_0_0_U (x))) (cBE_A (dA_0_0_U (x))) (hABE_nil (x)).

Definition facet_ABD_CE :=
  hexagonal_prism_coherence_nat_fill (dA_4_0_L) (dD_4_3_L) (dB_4_1_L)
    (fun z => dB_3_0_L (dD_2_1_L (z))) (fun z => dD_3_2_L (dB_2_0_L (z)))
    (fun z => dA_3_0_L (dB_2_0_L (z))) (fun z => dB_3_1_L (dA_2_0_L (z)))
    (fun z => dA_3_0_L (dD_2_1_L (z))) (fun z => dD_3_2_L (dA_2_0_L (z))) (cBD_CE)
    (cAB_CE) (cAD_CE) (fun z => cAD_BCE (dB_2_0_L (z))) (fun z => cAB_CDE (dD_2_1_L (z)))
    (fun z => cBD_ACE (dA_2_0_L (z))) (hABD_CE) (cCE_nil (x)).

Definition facet_CE_ABD :=
  hexagonal_prism_coherence_map_fill (dA_2_0_U) (dD_2_2_U) (dB_2_1_U) (dE_3_3_U)
    (dC_3_2_U) (dC_4_2_L) (dE_4_4_U) (cCE_ABD) (cBD_nil (x)) (cAB_nil (x)) (cAD_nil (x))
    (cAD_B (dB_0_0_U (x))) (cAB_D (dD_0_0_U (x))) (cBD_A (dA_0_0_U (x))) (hABD_nil (x)).

Definition facet_ABC_DE :=
  hexagonal_prism_coherence_nat_fill (dA_4_0_L) (dC_4_2_L) (dB_4_1_L)
    (fun z => dB_3_0_L (dC_2_0_L (z))) (fun z => dC_3_1_L (dB_2_0_L (z)))
    (fun z => dA_3_0_L (dB_2_0_L (z))) (fun z => dB_3_1_L (dA_2_0_L (z)))
    (fun z => dA_3_0_L (dC_2_0_L (z))) (fun z => dC_3_1_L (dA_2_0_L (z))) (cBC_DE)
    (cAB_DE) (cAC_DE) (fun z => cAC_BDE (dB_2_0_L (z))) (fun z => cAB_CDE (dC_2_0_L (z)))
    (fun z => cBC_ADE (dA_2_0_L (z))) (hABC_DE) (cDE_nil (x)).

Definition facet_DE_ABC :=
  hexagonal_prism_coherence_map_fill (dA_2_0_U) (dC_2_2_U) (dB_2_1_U) (dE_3_3_U)
    (dD_3_3_U) (dD_4_3_L) (dE_4_4_U) (cDE_ABC) (cBC_nil (x)) (cAB_nil (x)) (cAC_nil (x))
    (cAC_B (dB_0_0_U (x))) (cAB_C (dC_0_0_U (x))) (cBC_A (dA_0_0_U (x))) (hABC_nil (x)).

(** Whole-route views of the four outer map-prism facets. *)
Local Definition facet_AE_BCD_route :=
  hexagonal_prism_map_route_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD (hBCD_nil x).

Local Definition facet_CE_ABD_route :=
  hexagonal_prism_map_route_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD (hABD_nil x).

Local Definition facet_BE_ACD_route :=
  hexagonal_prism_map_route_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD (hACD_nil x).

Local Definition facet_DE_ABC_route :=
  hexagonal_prism_map_route_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC (hABC_nil x).

(** Moving [E] past a word gives its vertical comparison path. The
    squares [n_w_i] transport the adjacent swap at position [i] in [w],
    counting positions from the left starting at one. *)
Local Definition v_ABCD:
  dA_4_0_L (dB_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dA_3_0_U (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))) :=
  (f_equal dA_4_0_L
    ((f_equal dB_3_0_L ((f_equal dC_2_0_L (cDE_nil x)) • (cCE_D (dD_0_0_U x))))
    • (cBE_CD (dC_1_0_U (dD_0_0_U x)))))
  • (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))).

Local Definition v_ABDC:
  dA_4_0_L (dB_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dA_3_0_U (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))) :=
  (f_equal dA_4_0_L
    ((f_equal dB_3_0_L ((f_equal dD_2_1_L (cCE_nil x)) • (cDE_C (dC_0_0_U x))))
    • (cBE_CD (dD_1_1_U (dC_0_0_U x)))))
  • (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))).

Local Definition v_ACBD:
  dA_4_0_L (dC_3_1_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dA_3_0_U (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))) :=
  (f_equal dA_4_0_L
    ((f_equal dC_3_1_L ((f_equal dB_2_0_L (cDE_nil x)) • (cBE_D (dD_0_0_U x))))
    • (cCE_BD (dB_1_0_U (dD_0_0_U x)))))
  • (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))).

Local Definition v_ACDB:
  dA_4_0_L (dC_3_1_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dA_3_0_U (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))) :=
  (f_equal dA_4_0_L
    ((f_equal dC_3_1_L ((f_equal dD_2_1_L (cBE_nil x)) • (cDE_B (dB_0_0_U x))))
    • (cCE_BD (dD_1_1_U (dB_0_0_U x)))))
  • (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))).

Local Definition v_ADBC:
  dA_4_0_L (dD_3_2_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dA_3_0_U (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))) :=
  (f_equal dA_4_0_L
    ((f_equal dD_3_2_L ((f_equal dB_2_0_L (cCE_nil x)) • (cBE_C (dC_0_0_U x))))
    • (cDE_BC (dB_1_0_U (dC_0_0_U x)))))
  • (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))).

Local Definition v_ADCB:
  dA_4_0_L (dD_3_2_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dA_3_0_U (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))) :=
  (f_equal dA_4_0_L
    ((f_equal dD_3_2_L ((f_equal dC_2_1_L (cBE_nil x)) • (cCE_B (dB_0_0_U x))))
    • (cDE_BC (dC_1_1_U (dB_0_0_U x)))))
  • (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))).

Local Definition v_BACD:
  dB_4_1_L (dA_3_0_L (dC_2_0_L (dD_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dB_3_1_U (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))) :=
  (f_equal dB_4_1_L
    ((f_equal dA_3_0_L ((f_equal dC_2_0_L (cDE_nil x)) • (cCE_D (dD_0_0_U x))))
    • (cAE_CD (dC_1_0_U (dD_0_0_U x)))))
  • (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))).

Local Definition v_BADC:
  dB_4_1_L (dA_3_0_L (dD_2_1_L (dC_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dB_3_1_U (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))) :=
  (f_equal dB_4_1_L
    ((f_equal dA_3_0_L ((f_equal dD_2_1_L (cCE_nil x)) • (cDE_C (dC_0_0_U x))))
    • (cAE_CD (dD_1_1_U (dC_0_0_U x)))))
  • (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))).

Local Definition v_BCAD:
  dB_4_1_L (dC_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dB_3_1_U (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))) :=
  (f_equal dB_4_1_L
    ((f_equal dC_3_1_L ((f_equal dA_2_0_L (cDE_nil x)) • (cAE_D (dD_0_0_U x))))
    • (cCE_AD (dA_1_0_U (dD_0_0_U x)))))
  • (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))).

Local Definition v_BCDA:
  dB_4_1_L (dC_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dB_3_1_U (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))) :=
  (f_equal dB_4_1_L
    ((f_equal dC_3_1_L ((f_equal dD_2_1_L (cAE_nil x)) • (cDE_A (dA_0_0_U x))))
    • (cCE_AD (dD_1_1_U (dA_0_0_U x)))))
  • (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))).

Local Definition v_BDAC:
  dB_4_1_L (dD_3_2_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dB_3_1_U (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))) :=
  (f_equal dB_4_1_L
    ((f_equal dD_3_2_L ((f_equal dA_2_0_L (cCE_nil x)) • (cAE_C (dC_0_0_U x))))
    • (cDE_AC (dA_1_0_U (dC_0_0_U x)))))
  • (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))).

Local Definition v_BDCA:
  dB_4_1_L (dD_3_2_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dB_3_1_U (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))) :=
  (f_equal dB_4_1_L
    ((f_equal dD_3_2_L ((f_equal dC_2_1_L (cAE_nil x)) • (cCE_A (dA_0_0_U x))))
    • (cDE_AC (dC_1_1_U (dA_0_0_U x)))))
  • (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))).

Local Definition v_CABD:
  dC_4_2_L (dA_3_0_L (dB_2_0_L (dD_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dC_3_2_U (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))) :=
  (f_equal dC_4_2_L
    ((f_equal dA_3_0_L ((f_equal dB_2_0_L (cDE_nil x)) • (cBE_D (dD_0_0_U x))))
    • (cAE_BD (dB_1_0_U (dD_0_0_U x)))))
  • (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))).

Local Definition v_CADB:
  dC_4_2_L (dA_3_0_L (dD_2_1_L (dB_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dC_3_2_U (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))) :=
  (f_equal dC_4_2_L
    ((f_equal dA_3_0_L ((f_equal dD_2_1_L (cBE_nil x)) • (cDE_B (dB_0_0_U x))))
    • (cAE_BD (dD_1_1_U (dB_0_0_U x)))))
  • (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))).

Local Definition v_CBAD:
  dC_4_2_L (dB_3_1_L (dA_2_0_L (dD_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dC_3_2_U (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))) :=
  (f_equal dC_4_2_L
    ((f_equal dB_3_1_L ((f_equal dA_2_0_L (cDE_nil x)) • (cAE_D (dD_0_0_U x))))
    • (cBE_AD (dA_1_0_U (dD_0_0_U x)))))
  • (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))).

Local Definition v_CBDA:
  dC_4_2_L (dB_3_1_L (dD_2_1_L (dA_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dC_3_2_U (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))) :=
  (f_equal dC_4_2_L
    ((f_equal dB_3_1_L ((f_equal dD_2_1_L (cAE_nil x)) • (cDE_A (dA_0_0_U x))))
    • (cBE_AD (dD_1_1_U (dA_0_0_U x)))))
  • (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))).

Local Definition v_CDAB:
  dC_4_2_L (dD_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dC_3_2_U (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))) :=
  (f_equal dC_4_2_L
    ((f_equal dD_3_2_L ((f_equal dA_2_0_L (cBE_nil x)) • (cAE_B (dB_0_0_U x))))
    • (cDE_AB (dA_1_0_U (dB_0_0_U x)))))
  • (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))).

Local Definition v_CDBA:
  dC_4_2_L (dD_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dC_3_2_U (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))) :=
  (f_equal dC_4_2_L
    ((f_equal dD_3_2_L ((f_equal dB_2_1_L (cAE_nil x)) • (cBE_A (dA_0_0_U x))))
    • (cDE_AB (dB_1_1_U (dA_0_0_U x)))))
  • (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))).

Local Definition v_DABC:
  dD_4_3_L (dA_3_0_L (dB_2_0_L (dC_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dD_3_3_U (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))) :=
  (f_equal dD_4_3_L
    ((f_equal dA_3_0_L ((f_equal dB_2_0_L (cCE_nil x)) • (cBE_C (dC_0_0_U x))))
    • (cAE_BC (dB_1_0_U (dC_0_0_U x)))))
  • (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))).

Local Definition v_DACB:
  dD_4_3_L (dA_3_0_L (dC_2_1_L (dB_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dD_3_3_U (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))) :=
  (f_equal dD_4_3_L
    ((f_equal dA_3_0_L ((f_equal dC_2_1_L (cBE_nil x)) • (cCE_B (dB_0_0_U x))))
    • (cAE_BC (dC_1_1_U (dB_0_0_U x)))))
  • (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))).

Local Definition v_DBAC:
  dD_4_3_L (dB_3_1_L (dA_2_0_L (dC_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dD_3_3_U (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))) :=
  (f_equal dD_4_3_L
    ((f_equal dB_3_1_L ((f_equal dA_2_0_L (cCE_nil x)) • (cAE_C (dC_0_0_U x))))
    • (cBE_AC (dA_1_0_U (dC_0_0_U x)))))
  • (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))).

Local Definition v_DBCA:
  dD_4_3_L (dB_3_1_L (dC_2_1_L (dA_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dD_3_3_U (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))) :=
  (f_equal dD_4_3_L
    ((f_equal dB_3_1_L ((f_equal dC_2_1_L (cAE_nil x)) • (cCE_A (dA_0_0_U x))))
    • (cBE_AC (dC_1_1_U (dA_0_0_U x)))))
  • (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))).

Local Definition v_DCAB:
  dD_4_3_L (dC_3_2_L (dA_2_0_L (dB_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dD_3_3_U (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))) :=
  (f_equal dD_4_3_L
    ((f_equal dC_3_2_L ((f_equal dA_2_0_L (cBE_nil x)) • (cAE_B (dB_0_0_U x))))
    • (cCE_AB (dA_1_0_U (dB_0_0_U x)))))
  • (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))).

Local Definition v_DCBA:
  dD_4_3_L (dC_3_2_L (dB_2_1_L (dA_1_0_L (dE_0_0_U x))))
  = dE_4_4_U (dD_3_3_U (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))) :=
  (f_equal dD_4_3_L
    ((f_equal dC_3_2_L ((f_equal dB_2_1_L (cAE_nil x)) • (cBE_A (dA_0_0_U x))))
    • (cCE_AB (dB_1_1_U (dA_0_0_U x)))))
  • (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))).

Local Definition n_ABCD_1:
  v_ABCD • f_equal dE_4_4_U (cAB_CD (dC_1_0_U (dD_0_0_U x)))
  = (cAB_CDE (dC_2_0_L (dD_1_0_L (dE_0_0_U x)))) • v_BACD :=
  layer_square_nat dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U cAB_CDE
    ((f_equal dC_2_0_L (cDE_nil x)) • (cCE_D (dD_0_0_U x)))
    (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cAE_CD (dC_1_0_U (dD_0_0_U x)))
    (cAB_CD (dC_1_0_U (dD_0_0_U x)))
    (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x))))
    (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x))))
    (hABE_CD (dC_1_0_U (dD_0_0_U x)))
    (square_coherence_fill dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L cAB_CDE
      ((f_equal dC_2_0_L (cDE_nil x)) • (cCE_D (dD_0_0_U x)))).

Local Definition n_ABCD_2:
  v_ABCD • f_equal dE_4_4_U (f_equal dA_3_0_U (cBC_D (dD_0_0_U x)))
  = (f_equal dA_4_0_L (cBC_DE (dD_1_0_L (dE_0_0_U x)))) • v_ACBD :=
  square_stack
    (square_map dA_4_0_L
      (layer_square_nat dC_2_0_L dB_2_0_L dB_3_0_L dC_3_1_L dE_3_3_U cBC_DE (cDE_nil x)
        (cCE_D (dD_0_0_U x)) (cBE_D (dD_0_0_U x)) (cBC_D (dD_0_0_U x))
        (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_BD (dB_1_0_U (dD_0_0_U x)))
        (hBCE_D (dD_0_0_U x))
        (square_coherence_fill dC_2_0_L dB_2_0_L dB_3_0_L dC_3_1_L cBC_DE (cDE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
        (cBC_D (dD_0_0_U x)))).

Local Definition n_ABCD_3:
  v_ABCD • f_equal dE_4_4_U (f_equal dA_3_0_U (f_equal dB_2_0_U (cCD_nil x)))
  = (f_equal dA_4_0_L (f_equal dB_3_0_L (cCD_E (dE_0_0_U x)))) • v_ABDC :=
  square_stack
    (square_map dA_4_0_L
      (square_stack (square_map dB_3_0_L (hCDE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dB_2_0_U dB_3_0_L dE_3_3_U cBE_CD (cCD_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
        (f_equal dB_2_0_U (cCD_nil x)))).

Local Definition n_ABDC_1:
  v_ABDC • f_equal dE_4_4_U (cAB_CD (dD_1_1_U (dC_0_0_U x)))
  = (cAB_CDE (dD_2_1_L (dC_1_0_L (dE_0_0_U x)))) • v_BADC :=
  layer_square_nat dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U cAB_CDE
    ((f_equal dD_2_1_L (cCE_nil x)) • (cDE_C (dC_0_0_U x)))
    (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cAE_CD (dD_1_1_U (dC_0_0_U x)))
    (cAB_CD (dD_1_1_U (dC_0_0_U x)))
    (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x))))
    (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x))))
    (hABE_CD (dD_1_1_U (dC_0_0_U x)))
    (square_coherence_fill dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L cAB_CDE
      ((f_equal dD_2_1_L (cCE_nil x)) • (cDE_C (dC_0_0_U x)))).

Local Definition n_ABDC_2:
  v_ABDC • f_equal dE_4_4_U (f_equal dA_3_0_U (cBD_C (dC_0_0_U x)))
  = (f_equal dA_4_0_L (cBD_CE (dC_1_0_L (dE_0_0_U x)))) • v_ADBC :=
  square_stack
    (square_map dA_4_0_L
      (layer_square_nat dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L dE_3_3_U cBD_CE (cCE_nil x)
        (cDE_C (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cBD_C (dC_0_0_U x))
        (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_BC (dB_1_0_U (dC_0_0_U x)))
        (hBDE_C (dC_0_0_U x))
        (square_coherence_fill dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L cBD_CE (cCE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
        (cBD_C (dC_0_0_U x)))).

Local Definition n_ACBD_1:
  v_ACBD • f_equal dE_4_4_U (cAC_BD (dB_1_0_U (dD_0_0_U x)))
  = (cAC_BDE (dB_2_0_L (dD_1_0_L (dE_0_0_U x)))) • v_CABD :=
  layer_square_nat dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U cAC_BDE
    ((f_equal dB_2_0_L (cDE_nil x)) • (cBE_D (dD_0_0_U x)))
    (cCE_BD (dB_1_0_U (dD_0_0_U x))) (cAE_BD (dB_1_0_U (dD_0_0_U x)))
    (cAC_BD (dB_1_0_U (dD_0_0_U x)))
    (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
    (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x))))
    (hACE_BD (dB_1_0_U (dD_0_0_U x)))
    (square_coherence_fill dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L cAC_BDE
      ((f_equal dB_2_0_L (cDE_nil x)) • (cBE_D (dD_0_0_U x)))).

Local Definition n_ACBD_3:
  v_ACBD • f_equal dE_4_4_U (f_equal dA_3_0_U (f_equal dC_2_1_U (cBD_nil x)))
  = (f_equal dA_4_0_L (f_equal dC_3_1_L (cBD_E (dE_0_0_U x)))) • v_ACDB :=
  square_stack
    (square_map dA_4_0_L
      (square_stack (square_map dC_3_1_L (hBDE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dC_2_1_U dC_3_1_L dE_3_3_U cCE_BD (cBD_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
        (f_equal dC_2_1_U (cBD_nil x)))).

Local Definition n_ACDB_1:
  v_ACDB • f_equal dE_4_4_U (cAC_BD (dD_1_1_U (dB_0_0_U x)))
  = (cAC_BDE (dD_2_1_L (dB_1_0_L (dE_0_0_U x)))) • v_CADB :=
  layer_square_nat dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U cAC_BDE
    ((f_equal dD_2_1_L (cBE_nil x)) • (cDE_B (dB_0_0_U x)))
    (cCE_BD (dD_1_1_U (dB_0_0_U x))) (cAE_BD (dD_1_1_U (dB_0_0_U x)))
    (cAC_BD (dD_1_1_U (dB_0_0_U x)))
    (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x))))
    (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x))))
    (hACE_BD (dD_1_1_U (dB_0_0_U x)))
    (square_coherence_fill dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L cAC_BDE
      ((f_equal dD_2_1_L (cBE_nil x)) • (cDE_B (dB_0_0_U x)))).

Local Definition n_ACDB_2:
  v_ACDB • f_equal dE_4_4_U (f_equal dA_3_0_U (cCD_B (dB_0_0_U x)))
  = (f_equal dA_4_0_L (cCD_BE (dB_1_0_L (dE_0_0_U x)))) • v_ADCB :=
  square_stack
    (square_map dA_4_0_L
      (layer_square_nat dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_BE (cBE_nil x)
        (cDE_B (dB_0_0_U x)) (cCE_B (dB_0_0_U x)) (cCD_B (dB_0_0_U x))
        (cCE_BD (dD_1_1_U (dB_0_0_U x))) (cDE_BC (dC_1_1_U (dB_0_0_U x)))
        (hCDE_B (dB_0_0_U x))
        (square_coherence_fill dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L cCD_BE (cBE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
        (cCD_B (dB_0_0_U x)))).

Local Definition n_ADBC_1:
  v_ADBC • f_equal dE_4_4_U (cAD_BC (dB_1_0_U (dC_0_0_U x)))
  = (cAD_BCE (dB_2_0_L (dC_1_0_L (dE_0_0_U x)))) • v_DABC :=
  layer_square_nat dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U cAD_BCE
    ((f_equal dB_2_0_L (cCE_nil x)) • (cBE_C (dC_0_0_U x)))
    (cDE_BC (dB_1_0_U (dC_0_0_U x))) (cAE_BC (dB_1_0_U (dC_0_0_U x)))
    (cAD_BC (dB_1_0_U (dC_0_0_U x)))
    (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
    (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x))))
    (hADE_BC (dB_1_0_U (dC_0_0_U x)))
    (square_coherence_fill dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L cAD_BCE
      ((f_equal dB_2_0_L (cCE_nil x)) • (cBE_C (dC_0_0_U x)))).

Local Definition n_ADBC_3:
  v_ADBC • f_equal dE_4_4_U (f_equal dA_3_0_U (f_equal dD_2_2_U (cBC_nil x)))
  = (f_equal dA_4_0_L (f_equal dD_3_2_L (cBC_E (dE_0_0_U x)))) • v_ADCB :=
  square_stack
    (square_map dA_4_0_L
      (square_stack (square_map dD_3_2_L (hBCE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dD_2_2_U dD_3_2_L dE_3_3_U cDE_BC (cBC_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
        (f_equal dD_2_2_U (cBC_nil x)))).

Local Definition n_ADCB_1:
  v_ADCB • f_equal dE_4_4_U (cAD_BC (dC_1_1_U (dB_0_0_U x)))
  = (cAD_BCE (dC_2_1_L (dB_1_0_L (dE_0_0_U x)))) • v_DACB :=
  layer_square_nat dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U cAD_BCE
    ((f_equal dC_2_1_L (cBE_nil x)) • (cCE_B (dB_0_0_U x)))
    (cDE_BC (dC_1_1_U (dB_0_0_U x))) (cAE_BC (dC_1_1_U (dB_0_0_U x)))
    (cAD_BC (dC_1_1_U (dB_0_0_U x)))
    (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
    (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x))))
    (hADE_BC (dC_1_1_U (dB_0_0_U x)))
    (square_coherence_fill dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L cAD_BCE
      ((f_equal dC_2_1_L (cBE_nil x)) • (cCE_B (dB_0_0_U x)))).

Local Definition n_BACD_2:
  v_BACD • f_equal dE_4_4_U (f_equal dB_3_1_U (cAC_D (dD_0_0_U x)))
  = (f_equal dB_4_1_L (cAC_DE (dD_1_0_L (dE_0_0_U x)))) • v_BCAD :=
  square_stack
    (square_map dB_4_1_L
      (layer_square_nat dC_2_0_L dA_2_0_L dA_3_0_L dC_3_1_L dE_3_3_U cAC_DE (cDE_nil x)
        (cCE_D (dD_0_0_U x)) (cAE_D (dD_0_0_U x)) (cAC_D (dD_0_0_U x))
        (cAE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
        (hACE_D (dD_0_0_U x))
        (square_coherence_fill dC_2_0_L dA_2_0_L dA_3_0_L dC_3_1_L cAC_DE (cDE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
        (cAC_D (dD_0_0_U x)))).

Local Definition n_BACD_3:
  v_BACD • f_equal dE_4_4_U (f_equal dB_3_1_U (f_equal dA_2_0_U (cCD_nil x)))
  = (f_equal dB_4_1_L (f_equal dA_3_0_L (cCD_E (dE_0_0_U x)))) • v_BADC :=
  square_stack
    (square_map dB_4_1_L
      (square_stack (square_map dA_3_0_L (hCDE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U cAE_CD (cCD_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
        (f_equal dA_2_0_U (cCD_nil x)))).

Local Definition n_BADC_2:
  v_BADC • f_equal dE_4_4_U (f_equal dB_3_1_U (cAD_C (dC_0_0_U x)))
  = (f_equal dB_4_1_L (cAD_CE (dC_1_0_L (dE_0_0_U x)))) • v_BDAC :=
  square_stack
    (square_map dB_4_1_L
      (layer_square_nat dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_CE (cCE_nil x)
        (cDE_C (dC_0_0_U x)) (cAE_C (dC_0_0_U x)) (cAD_C (dC_0_0_U x))
        (cAE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AC (dA_1_0_U (dC_0_0_U x)))
        (hADE_C (dC_0_0_U x))
        (square_coherence_fill dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L cAD_CE (cCE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
        (cAD_C (dC_0_0_U x)))).

Local Definition n_BCAD_1:
  v_BCAD • f_equal dE_4_4_U (cBC_AD (dA_1_0_U (dD_0_0_U x)))
  = (cBC_ADE (dA_2_0_L (dD_1_0_L (dE_0_0_U x)))) • v_CBAD :=
  layer_square_nat dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U cBC_ADE
    ((f_equal dA_2_0_L (cDE_nil x)) • (cAE_D (dD_0_0_U x)))
    (cCE_AD (dA_1_0_U (dD_0_0_U x))) (cBE_AD (dA_1_0_U (dD_0_0_U x)))
    (cBC_AD (dA_1_0_U (dD_0_0_U x)))
    (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
    (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x))))
    (hBCE_AD (dA_1_0_U (dD_0_0_U x)))
    (square_coherence_fill dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L cBC_ADE
      ((f_equal dA_2_0_L (cDE_nil x)) • (cAE_D (dD_0_0_U x)))).

Local Definition n_BCAD_3:
  v_BCAD • f_equal dE_4_4_U (f_equal dB_3_1_U (f_equal dC_2_1_U (cAD_nil x)))
  = (f_equal dB_4_1_L (f_equal dC_3_1_L (cAD_E (dE_0_0_U x)))) • v_BCDA :=
  square_stack
    (square_map dB_4_1_L
      (square_stack (square_map dC_3_1_L (hADE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dC_2_1_U dC_3_1_L dE_3_3_U cCE_AD (cAD_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
        (f_equal dC_2_1_U (cAD_nil x)))).

Local Definition n_BCDA_1:
  v_BCDA • f_equal dE_4_4_U (cBC_AD (dD_1_1_U (dA_0_0_U x)))
  = (cBC_ADE (dD_2_1_L (dA_1_0_L (dE_0_0_U x)))) • v_CBDA :=
  layer_square_nat dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U cBC_ADE
    ((f_equal dD_2_1_L (cAE_nil x)) • (cDE_A (dA_0_0_U x)))
    (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cBE_AD (dD_1_1_U (dA_0_0_U x)))
    (cBC_AD (dD_1_1_U (dA_0_0_U x)))
    (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x))))
    (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x))))
    (hBCE_AD (dD_1_1_U (dA_0_0_U x)))
    (square_coherence_fill dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L cBC_ADE
      ((f_equal dD_2_1_L (cAE_nil x)) • (cDE_A (dA_0_0_U x)))).

Local Definition n_BCDA_2:
  v_BCDA • f_equal dE_4_4_U (f_equal dB_3_1_U (cCD_A (dA_0_0_U x)))
  = (f_equal dB_4_1_L (cCD_AE (dA_1_0_L (dE_0_0_U x)))) • v_BDCA :=
  square_stack
    (square_map dB_4_1_L
      (layer_square_nat dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_AE (cAE_nil x)
        (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cCD_A (dA_0_0_U x))
        (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AC (dC_1_1_U (dA_0_0_U x)))
        (hCDE_A (dA_0_0_U x))
        (square_coherence_fill dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L cCD_AE (cAE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
        (cCD_A (dA_0_0_U x)))).

Local Definition n_BDAC_1:
  v_BDAC • f_equal dE_4_4_U (cBD_AC (dA_1_0_U (dC_0_0_U x)))
  = (cBD_ACE (dA_2_0_L (dC_1_0_L (dE_0_0_U x)))) • v_DBAC :=
  layer_square_nat dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U cBD_ACE
    ((f_equal dA_2_0_L (cCE_nil x)) • (cAE_C (dC_0_0_U x)))
    (cDE_AC (dA_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
    (cBD_AC (dA_1_0_U (dC_0_0_U x)))
    (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
    (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x))))
    (hBDE_AC (dA_1_0_U (dC_0_0_U x)))
    (square_coherence_fill dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L cBD_ACE
      ((f_equal dA_2_0_L (cCE_nil x)) • (cAE_C (dC_0_0_U x)))).

Local Definition n_BDAC_3:
  v_BDAC • f_equal dE_4_4_U (f_equal dB_3_1_U (f_equal dD_2_2_U (cAC_nil x)))
  = (f_equal dB_4_1_L (f_equal dD_3_2_L (cAC_E (dE_0_0_U x)))) • v_BDCA :=
  square_stack
    (square_map dB_4_1_L
      (square_stack (square_map dD_3_2_L (hACE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dD_2_2_U dD_3_2_L dE_3_3_U cDE_AC (cAC_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
        (f_equal dD_2_2_U (cAC_nil x)))).

Local Definition n_BDCA_1:
  v_BDCA • f_equal dE_4_4_U (cBD_AC (dC_1_1_U (dA_0_0_U x)))
  = (cBD_ACE (dC_2_1_L (dA_1_0_L (dE_0_0_U x)))) • v_DBCA :=
  layer_square_nat dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U cBD_ACE
    ((f_equal dC_2_1_L (cAE_nil x)) • (cCE_A (dA_0_0_U x)))
    (cDE_AC (dC_1_1_U (dA_0_0_U x))) (cBE_AC (dC_1_1_U (dA_0_0_U x)))
    (cBD_AC (dC_1_1_U (dA_0_0_U x)))
    (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
    (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x))))
    (hBDE_AC (dC_1_1_U (dA_0_0_U x)))
    (square_coherence_fill dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L cBD_ACE
      ((f_equal dC_2_1_L (cAE_nil x)) • (cCE_A (dA_0_0_U x)))).

Local Definition n_CABD_2:
  v_CABD • f_equal dE_4_4_U (f_equal dC_3_2_U (cAB_D (dD_0_0_U x)))
  = (f_equal dC_4_2_L (cAB_DE (dD_1_0_L (dE_0_0_U x)))) • v_CBAD :=
  square_stack
    (square_map dC_4_2_L
      (layer_square_nat dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_DE (cDE_nil x)
        (cBE_D (dD_0_0_U x)) (cAE_D (dD_0_0_U x)) (cAB_D (dD_0_0_U x))
        (cAE_BD (dB_1_0_U (dD_0_0_U x))) (cBE_AD (dA_1_0_U (dD_0_0_U x)))
        (hABE_D (dD_0_0_U x))
        (square_coherence_fill dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L cAB_DE (cDE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
        (cAB_D (dD_0_0_U x)))).

Local Definition n_CABD_3:
  v_CABD • f_equal dE_4_4_U (f_equal dC_3_2_U (f_equal dA_2_0_U (cBD_nil x)))
  = (f_equal dC_4_2_L (f_equal dA_3_0_L (cBD_E (dE_0_0_U x)))) • v_CADB :=
  square_stack
    (square_map dC_4_2_L
      (square_stack (square_map dA_3_0_L (hBDE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U cAE_BD (cBD_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
        (f_equal dA_2_0_U (cBD_nil x)))).

Local Definition n_CADB_2:
  v_CADB • f_equal dE_4_4_U (f_equal dC_3_2_U (cAD_B (dB_0_0_U x)))
  = (f_equal dC_4_2_L (cAD_BE (dB_1_0_L (dE_0_0_U x)))) • v_CDAB :=
  square_stack
    (square_map dC_4_2_L
      (layer_square_nat dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_BE (cBE_nil x)
        (cDE_B (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x))
        (cAE_BD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
        (hADE_B (dB_0_0_U x))
        (square_coherence_fill dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L cAD_BE (cBE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
        (cAD_B (dB_0_0_U x)))).

Local Definition n_CBAD_3:
  v_CBAD • f_equal dE_4_4_U (f_equal dC_3_2_U (f_equal dB_2_1_U (cAD_nil x)))
  = (f_equal dC_4_2_L (f_equal dB_3_1_L (cAD_E (dE_0_0_U x)))) • v_CBDA :=
  square_stack
    (square_map dC_4_2_L
      (square_stack (square_map dB_3_1_L (hADE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dB_2_1_U dB_3_1_L dE_3_3_U cBE_AD (cAD_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
        (f_equal dB_2_1_U (cAD_nil x)))).

Local Definition n_CBDA_2:
  v_CBDA • f_equal dE_4_4_U (f_equal dC_3_2_U (cBD_A (dA_0_0_U x)))
  = (f_equal dC_4_2_L (cBD_AE (dA_1_0_L (dE_0_0_U x)))) • v_CDBA :=
  square_stack
    (square_map dC_4_2_L
      (layer_square_nat dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U cBD_AE (cAE_nil x)
        (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x))
        (cBE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
        (hBDE_A (dA_0_0_U x))
        (square_coherence_fill dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L cBD_AE (cAE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
        (cBD_A (dA_0_0_U x)))).

Local Definition n_CDAB_1:
  v_CDAB • f_equal dE_4_4_U (cCD_AB (dA_1_0_U (dB_0_0_U x)))
  = (cCD_ABE (dA_2_0_L (dB_1_0_L (dE_0_0_U x)))) • v_DCAB :=
  layer_square_nat dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U cCD_ABE
    ((f_equal dA_2_0_L (cBE_nil x)) • (cAE_B (dB_0_0_U x)))
    (cDE_AB (dA_1_0_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
    (cCD_AB (dA_1_0_U (dB_0_0_U x)))
    (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
    (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x))))
    (hCDE_AB (dA_1_0_U (dB_0_0_U x)))
    (square_coherence_fill dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L cCD_ABE
      ((f_equal dA_2_0_L (cBE_nil x)) • (cAE_B (dB_0_0_U x)))).

Local Definition n_CDAB_3:
  v_CDAB • f_equal dE_4_4_U (f_equal dC_3_2_U (f_equal dD_2_2_U (cAB_nil x)))
  = (f_equal dC_4_2_L (f_equal dD_3_2_L (cAB_E (dE_0_0_U x)))) • v_CDBA :=
  square_stack
    (square_map dC_4_2_L
      (square_stack (square_map dD_3_2_L (hABE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dD_2_2_U dD_3_2_L dE_3_3_U cDE_AB (cAB_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
        (f_equal dD_2_2_U (cAB_nil x)))).

Local Definition n_CDBA_1:
  v_CDBA • f_equal dE_4_4_U (cCD_AB (dB_1_1_U (dA_0_0_U x)))
  = (cCD_ABE (dB_2_1_L (dA_1_0_L (dE_0_0_U x)))) • v_DCBA :=
  layer_square_nat dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U cCD_ABE
    ((f_equal dB_2_1_L (cAE_nil x)) • (cBE_A (dA_0_0_U x)))
    (cDE_AB (dB_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
    (cCD_AB (dB_1_1_U (dA_0_0_U x)))
    (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
    (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))
    (hCDE_AB (dB_1_1_U (dA_0_0_U x)))
    (square_coherence_fill dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L cCD_ABE
      ((f_equal dB_2_1_L (cAE_nil x)) • (cBE_A (dA_0_0_U x)))).

Local Definition n_DABC_2:
  v_DABC • f_equal dE_4_4_U (f_equal dD_3_3_U (cAB_C (dC_0_0_U x)))
  = (f_equal dD_4_3_L (cAB_CE (dC_1_0_L (dE_0_0_U x)))) • v_DBAC :=
  square_stack
    (square_map dD_4_3_L
      (layer_square_nat dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_CE (cCE_nil x)
        (cBE_C (dC_0_0_U x)) (cAE_C (dC_0_0_U x)) (cAB_C (dC_0_0_U x))
        (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
        (hABE_C (dC_0_0_U x))
        (square_coherence_fill dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L cAB_CE (cCE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (cAB_C (dC_0_0_U x)))).

Local Definition n_DABC_3:
  v_DABC • f_equal dE_4_4_U (f_equal dD_3_3_U (f_equal dA_2_0_U (cBC_nil x)))
  = (f_equal dD_4_3_L (f_equal dA_3_0_L (cBC_E (dE_0_0_U x)))) • v_DACB :=
  square_stack
    (square_map dD_4_3_L
      (square_stack (square_map dA_3_0_L (hBCE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U cAE_BC (cBC_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (f_equal dA_2_0_U (cBC_nil x)))).

Local Definition n_DACB_2:
  v_DACB • f_equal dE_4_4_U (f_equal dD_3_3_U (cAC_B (dB_0_0_U x)))
  = (f_equal dD_4_3_L (cAC_BE (dB_1_0_L (dE_0_0_U x)))) • v_DCAB :=
  square_stack
    (square_map dD_4_3_L
      (layer_square_nat dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L dE_3_3_U cAC_BE (cBE_nil x)
        (cCE_B (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAC_B (dB_0_0_U x))
        (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
        (hACE_B (dB_0_0_U x))
        (square_coherence_fill dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L cAC_BE (cBE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (cAC_B (dB_0_0_U x)))).

Local Definition n_DBAC_3:
  v_DBAC • f_equal dE_4_4_U (f_equal dD_3_3_U (f_equal dB_2_1_U (cAC_nil x)))
  = (f_equal dD_4_3_L (f_equal dB_3_1_L (cAC_E (dE_0_0_U x)))) • v_DBCA :=
  square_stack
    (square_map dD_4_3_L
      (square_stack (square_map dB_3_1_L (hACE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dB_2_1_U dB_3_1_L dE_3_3_U cBE_AC (cAC_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (f_equal dB_2_1_U (cAC_nil x)))).

Local Definition n_DBCA_2:
  v_DBCA • f_equal dE_4_4_U (f_equal dD_3_3_U (cBC_A (dA_0_0_U x)))
  = (f_equal dD_4_3_L (cBC_AE (dA_1_0_L (dE_0_0_U x)))) • v_DCBA :=
  square_stack
    (square_map dD_4_3_L
      (layer_square_nat dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L dE_3_3_U cBC_AE (cAE_nil x)
        (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBC_A (dA_0_0_U x))
        (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
        (hBCE_A (dA_0_0_U x))
        (square_coherence_fill dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L cBC_AE (cAE_nil x))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (cBC_A (dA_0_0_U x)))).

Local Definition n_DCAB_3:
  v_DCAB • f_equal dE_4_4_U (f_equal dD_3_3_U (f_equal dC_2_2_U (cAB_nil x)))
  = (f_equal dD_4_3_L (f_equal dC_3_2_L (cAB_E (dE_0_0_U x)))) • v_DCBA :=
  square_stack
    (square_map dD_4_3_L
      (square_stack (square_map dC_3_2_L (hABE_nil x))
        (eq_sym
          (square_coherence_fill dE_2_2_U dC_2_2_U dC_3_2_L dE_3_3_U cCE_AB (cAB_nil x)))))
    (eq_sym
      (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (f_equal dC_2_2_U (cAB_nil x)))).

(** The four hexagons with a source operation use the naturality
    prism filler through [layer_cube_nat]. Normalize their side squares
    to the same vertical paths as the adjacent-swap squares above. *)
Local Definition raw_nat_BCD_A :=
  @layer_cube_nat Y2 Y1 Y0 X2 X1 dE_3_3_U dE_4_4_U dB_3_1_U dD_3_3_U dC_3_2_U dB_4_1_L
    dD_4_3_L dC_4_2_L cBE_ACD cDE_ABC cCE_ABD dC_3_1_L dD_3_2_L dB_3_1_L dC_3_2_L cBD_ACE
    cBC_ADE cCD_ABE Y3 dD_2_1_L dC_2_1_L dB_2_1_L cCD_AE cBC_AE cBD_AE hBCD_AE
    (dA_1_0_L (dE_0_0_U x)) (dE_1_1_U (dA_0_0_U x)) (cAE_nil x)
    (dC_2_1_U (dD_1_1_U (dA_0_0_U x))) (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))
    (dB_2_1_U (dC_1_1_U (dA_0_0_U x))) (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))
    (dB_2_1_U (dD_1_1_U (dA_0_0_U x))) (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))
    (cCD_A (dA_0_0_U x)) (cBC_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x))
    (cBD_AC (dC_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x)))
    (cCD_AB (dB_1_1_U (dA_0_0_U x))) (dE_2_2_U (dD_1_1_U (dA_0_0_U x)))
    (dE_2_2_U (dC_1_1_U (dA_0_0_U x))) (dE_2_2_U (dB_1_1_U (dA_0_0_U x)))
    (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x))
    (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AC (dC_1_1_U (dA_0_0_U x)))
    (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
    (cBE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
    (hCDE_A (dA_0_0_U x)) (hBCE_A (dA_0_0_U x)) (hBDE_A (dA_0_0_U x))
    (hBCD_A (dA_0_0_U x)) (hBDE_AC (dC_1_1_U (dA_0_0_U x)))
    (hBCE_AD (dD_1_1_U (dA_0_0_U x))) (hCDE_AB (dB_1_1_U (dA_0_0_U x)))
    (kBCDE_A (dA_0_0_U x))
    (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
      (fun z => dD_3_2_L (dC_2_1_L z)) dB_4_1_L dB_4_1_L
      (fun z => f_equal dB_4_1_L (cCD_AE z)) (cAE_nil x))
    (square_coherence_fill (fun z => dD_3_2_L (dC_2_1_L z))
      (fun z => dB_3_1_L (dC_2_1_L z)) dB_4_1_L dD_4_3_L (fun z => cBD_ACE (dC_2_1_L z))
      (cAE_nil x))
    (square_coherence_fill (fun z => dB_3_1_L (dC_2_1_L z))
      (fun z => dC_3_2_L (dB_2_1_L z)) dD_4_3_L dD_4_3_L
      (fun z => f_equal dD_4_3_L (cBC_AE z)) (cAE_nil x))
    (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
      (fun z => dB_3_1_L (dD_2_1_L z)) dB_4_1_L dC_4_2_L (fun z => cBC_ADE (dD_2_1_L z))
      (cAE_nil x))
    (square_coherence_fill (fun z => dB_3_1_L (dD_2_1_L z))
      (fun z => dD_3_2_L (dB_2_1_L z)) dC_4_2_L dC_4_2_L
      (fun z => f_equal dC_4_2_L (cBD_AE z)) (cAE_nil x))
    (square_coherence_fill (fun z => dD_3_2_L (dB_2_1_L z))
      (fun z => dC_3_2_L (dB_2_1_L z)) dC_4_2_L dD_4_3_L (fun z => cCD_ABE (dB_2_1_L z))
      (cAE_nil x))
    facet_BCD_AE.

Local Definition hcube_BCD_A:
  square_cube
    (square_compose_map dE_4_4_U (square_compose_map dE_4_4_U n_BCDA_2 n_BDCA_1) n_DBCA_2)
    (square_compose_map dE_4_4_U n_BCDA_1 (square_compose_map dE_4_4_U n_CBDA_2 n_CDBA_1))
    (f_equal (fun e => f_equal dE_4_4_U e) (hBCD_A (dA_0_0_U x)))
    (hBCD_AE (dA_1_0_L (dE_0_0_U x))) :=
  square_cube_change_faces
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_AE
            dB_4_1_L dB_3_1_U dE_4_4_U cBE_ACD (cAE_nil x) (cDE_A (dA_0_0_U x))
            (cCE_A (dA_0_0_U x)) (cCD_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
            (cDE_AC (dC_1_1_U (dA_0_0_U x))) (hCDE_A (dA_0_0_U x)))
          (layer_square_nat_source dC_2_1_L dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U
            cBD_ACE (cAE_nil x) (cCE_A (dA_0_0_U x)) (cDE_AC (dC_1_1_U (dA_0_0_U x)))
            (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
            (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
            (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x))))
            (hBDE_AC (dC_1_1_U (dA_0_0_U x)))))
        (layer_square_map_source dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L dE_3_3_U cBC_AE
          dD_4_3_L dD_3_3_U dE_4_4_U cDE_ABC (cAE_nil x) (cCE_A (dA_0_0_U x))
          (cBE_A (dA_0_0_U x)) (cBC_A (dA_0_0_U x)) (cBE_AC (dC_1_1_U (dA_0_0_U x)))
          (cCE_AB (dB_1_1_U (dA_0_0_U x))) (hBCE_A (dA_0_0_U x))))
      (square_nat_route_left dE_4_4_U
        (layer_cube_nat_side dD_2_1_L dC_3_1_L dB_4_1_L (cAE_nil x) (cDE_A (dA_0_0_U x))
          (cCE_AD (dD_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))))
        (layer_cube_nat_side dC_2_1_L dD_3_2_L dB_4_1_L (cAE_nil x) (cCE_A (dA_0_0_U x))
          (cDE_AC (dC_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x)))))
        (layer_cube_nat_side dC_2_1_L dB_3_1_L dD_4_3_L (cAE_nil x) (cCE_A (dA_0_0_U x))
          (cBE_AC (dC_1_1_U (dA_0_0_U x)))
          (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x)))))
        (layer_cube_nat_side dB_2_1_L dC_3_2_L dD_4_3_L (cAE_nil x) (cBE_A (dA_0_0_U x))
          (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))))
        (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
          (fun z => dD_3_2_L (dC_2_1_L z)) dB_4_1_L dB_4_1_L
          (fun z => f_equal dB_4_1_L (cCD_AE z)) (cAE_nil x))
        (square_coherence_fill (fun z => dD_3_2_L (dC_2_1_L z))
          (fun z => dB_3_1_L (dC_2_1_L z)) dB_4_1_L dD_4_3_L
          (fun z => cBD_ACE (dC_2_1_L z)) (cAE_nil x))
        (square_coherence_fill (fun z => dB_3_1_L (dC_2_1_L z))
          (fun z => dC_3_2_L (dB_2_1_L z)) dD_4_3_L dD_4_3_L
          (fun z => f_equal dD_4_3_L (cBC_AE z)) (cAE_nil x))
        (square_stack
          (square_map dB_4_1_L ((hCDE_A (dA_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
              (cCD_A (dA_0_0_U x)))))
        (layer_square_nat dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U cBD_ACE
          (cCE_A (dA_0_0_U x)) (cDE_AC (dC_1_1_U (dA_0_0_U x)))
          (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cBD_AC (dC_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dC_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dC_1_1_U (dA_0_0_U x))))
          (hBDE_AC (dC_1_1_U (dA_0_0_U x)))
          (square_coherence_fill dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L cBD_ACE
            (cCE_A (dA_0_0_U x))))
        (square_stack
          (square_map dD_4_3_L ((hBCE_A (dA_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
              (cBC_A (dA_0_0_U x)))))))
    raw_nat_BCD_A
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_nat_source dD_2_1_L dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U
          cBC_ADE (cAE_nil x) (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
          (cBE_AD (dD_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x))))
          (hBCE_AD (dD_1_1_U (dA_0_0_U x))))
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U cBD_AE
            dC_4_2_L dC_3_2_U dE_4_4_U cCE_ABD (cAE_nil x) (cDE_A (dA_0_0_U x))
            (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x)) (cBE_AD (dD_1_1_U (dA_0_0_U x)))
            (cDE_AB (dB_1_1_U (dA_0_0_U x))) (hBDE_A (dA_0_0_U x)))
          (layer_square_nat_source dB_2_1_L dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U
            cCD_ABE (cAE_nil x) (cBE_A (dA_0_0_U x)) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
            (cCE_AB (dB_1_1_U (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x)))
            (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
            (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))
            (hCDE_AB (dB_1_1_U (dA_0_0_U x))))))
      (square_nat_route dE_4_4_U
        (layer_cube_nat_side dD_2_1_L dC_3_1_L dB_4_1_L (cAE_nil x) (cDE_A (dA_0_0_U x))
          (cCE_AD (dD_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x)))))
        (layer_cube_nat_side dD_2_1_L dB_3_1_L dC_4_2_L (cAE_nil x) (cDE_A (dA_0_0_U x))
          (cBE_AD (dD_1_1_U (dA_0_0_U x)))
          (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x)))))
        (layer_cube_nat_side dB_2_1_L dD_3_2_L dC_4_2_L (cAE_nil x) (cBE_A (dA_0_0_U x))
          (cDE_AB (dB_1_1_U (dA_0_0_U x)))
          (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x)))))
        (layer_cube_nat_side dB_2_1_L dC_3_2_L dD_4_3_L (cAE_nil x) (cBE_A (dA_0_0_U x))
          (cCE_AB (dB_1_1_U (dA_0_0_U x)))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x)))))
        (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
          (fun z => dB_3_1_L (dD_2_1_L z)) dB_4_1_L dC_4_2_L
          (fun z => cBC_ADE (dD_2_1_L z)) (cAE_nil x))
        (square_coherence_fill (fun z => dB_3_1_L (dD_2_1_L z))
          (fun z => dD_3_2_L (dB_2_1_L z)) dC_4_2_L dC_4_2_L
          (fun z => f_equal dC_4_2_L (cBD_AE z)) (cAE_nil x))
        (square_coherence_fill (fun z => dD_3_2_L (dB_2_1_L z))
          (fun z => dC_3_2_L (dB_2_1_L z)) dC_4_2_L dD_4_3_L
          (fun z => cCD_ABE (dB_2_1_L z)) (cAE_nil x))
        (layer_square_nat dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U cBC_ADE
          (cDE_A (dA_0_0_U x)) (cCE_AD (dD_1_1_U (dA_0_0_U x)))
          (cBE_AD (dD_1_1_U (dA_0_0_U x))) (cBC_AD (dD_1_1_U (dA_0_0_U x)))
          (cBE_ACD (dC_2_1_U (dD_1_1_U (dA_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dD_1_1_U (dA_0_0_U x))))
          (hBCE_AD (dD_1_1_U (dA_0_0_U x)))
          (square_coherence_fill dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L cBC_ADE
            (cDE_A (dA_0_0_U x))))
        (square_stack
          (square_map dC_4_2_L ((hBDE_A (dA_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
              (cBD_A (dA_0_0_U x)))))
        (layer_square_nat dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U cCD_ABE
          (cBE_A (dA_0_0_U x)) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
          (cCE_AB (dB_1_1_U (dA_0_0_U x))) (cCD_AB (dB_1_1_U (dA_0_0_U x)))
          (cCE_ABD (dD_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dB_1_1_U (dA_0_0_U x))))
          (hCDE_AB (dB_1_1_U (dA_0_0_U x)))
          (square_coherence_fill dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L cCD_ABE
            (cBE_A (dA_0_0_U x)))))).

Local Definition raw_nat_ACD_B :=
  @layer_cube_nat Y2 Y1 Y0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dD_3_3_U dC_3_2_U dA_4_0_L
    dD_4_3_L dC_4_2_L cAE_BCD cDE_ABC cCE_ABD dC_3_1_L dD_3_2_L dA_3_0_L dC_3_2_L cAD_BCE
    cAC_BDE cCD_ABE Y3 dD_2_1_L dC_2_1_L dA_2_0_L cCD_BE cAC_BE cAD_BE hACD_BE
    (dB_1_0_L (dE_0_0_U x)) (dE_1_1_U (dB_0_0_U x)) (cBE_nil x)
    (dC_2_1_U (dD_1_1_U (dB_0_0_U x))) (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))
    (dA_2_0_U (dC_1_1_U (dB_0_0_U x))) (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))
    (dA_2_0_U (dD_1_1_U (dB_0_0_U x))) (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))
    (cCD_B (dB_0_0_U x)) (cAC_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x))
    (cAD_BC (dC_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x)))
    (cCD_AB (dA_1_0_U (dB_0_0_U x))) (dE_2_2_U (dD_1_1_U (dB_0_0_U x)))
    (dE_2_2_U (dC_1_1_U (dB_0_0_U x))) (dE_2_2_U (dA_1_0_U (dB_0_0_U x)))
    (cDE_B (dB_0_0_U x)) (cCE_B (dB_0_0_U x)) (cAE_B (dB_0_0_U x))
    (cCE_BD (dD_1_1_U (dB_0_0_U x))) (cDE_BC (dC_1_1_U (dB_0_0_U x)))
    (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
    (cAE_BD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
    (hCDE_B (dB_0_0_U x)) (hACE_B (dB_0_0_U x)) (hADE_B (dB_0_0_U x))
    (hACD_B (dB_0_0_U x)) (hADE_BC (dC_1_1_U (dB_0_0_U x)))
    (hACE_BD (dD_1_1_U (dB_0_0_U x))) (hCDE_AB (dA_1_0_U (dB_0_0_U x)))
    (kACDE_B (dB_0_0_U x))
    (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
      (fun z => dD_3_2_L (dC_2_1_L z)) dA_4_0_L dA_4_0_L
      (fun z => f_equal dA_4_0_L (cCD_BE z)) (cBE_nil x))
    (square_coherence_fill (fun z => dD_3_2_L (dC_2_1_L z))
      (fun z => dA_3_0_L (dC_2_1_L z)) dA_4_0_L dD_4_3_L (fun z => cAD_BCE (dC_2_1_L z))
      (cBE_nil x))
    (square_coherence_fill (fun z => dA_3_0_L (dC_2_1_L z))
      (fun z => dC_3_2_L (dA_2_0_L z)) dD_4_3_L dD_4_3_L
      (fun z => f_equal dD_4_3_L (cAC_BE z)) (cBE_nil x))
    (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
      (fun z => dA_3_0_L (dD_2_1_L z)) dA_4_0_L dC_4_2_L (fun z => cAC_BDE (dD_2_1_L z))
      (cBE_nil x))
    (square_coherence_fill (fun z => dA_3_0_L (dD_2_1_L z))
      (fun z => dD_3_2_L (dA_2_0_L z)) dC_4_2_L dC_4_2_L
      (fun z => f_equal dC_4_2_L (cAD_BE z)) (cBE_nil x))
    (square_coherence_fill (fun z => dD_3_2_L (dA_2_0_L z))
      (fun z => dC_3_2_L (dA_2_0_L z)) dC_4_2_L dD_4_3_L (fun z => cCD_ABE (dA_2_0_L z))
      (cBE_nil x))
    facet_ACD_BE.

Local Definition hcube_ACD_B:
  square_cube
    (square_compose_map dE_4_4_U (square_compose_map dE_4_4_U n_ACDB_2 n_ADCB_1) n_DACB_2)
    (square_compose_map dE_4_4_U n_ACDB_1 (square_compose_map dE_4_4_U n_CADB_2 n_CDAB_1))
    (f_equal (fun e => f_equal dE_4_4_U e) (hACD_B (dB_0_0_U x)))
    (hACD_BE (dB_1_0_L (dE_0_0_U x))) :=
  square_cube_change_faces
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_BE
            dA_4_0_L dA_3_0_U dE_4_4_U cAE_BCD (cBE_nil x) (cDE_B (dB_0_0_U x))
            (cCE_B (dB_0_0_U x)) (cCD_B (dB_0_0_U x)) (cCE_BD (dD_1_1_U (dB_0_0_U x)))
            (cDE_BC (dC_1_1_U (dB_0_0_U x))) (hCDE_B (dB_0_0_U x)))
          (layer_square_nat_source dC_2_1_L dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U
            cAD_BCE (cBE_nil x) (cCE_B (dB_0_0_U x)) (cDE_BC (dC_1_1_U (dB_0_0_U x)))
            (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
            (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
            (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x))))
            (hADE_BC (dC_1_1_U (dB_0_0_U x)))))
        (layer_square_map_source dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L dE_3_3_U cAC_BE
          dD_4_3_L dD_3_3_U dE_4_4_U cDE_ABC (cBE_nil x) (cCE_B (dB_0_0_U x))
          (cAE_B (dB_0_0_U x)) (cAC_B (dB_0_0_U x)) (cAE_BC (dC_1_1_U (dB_0_0_U x)))
          (cCE_AB (dA_1_0_U (dB_0_0_U x))) (hACE_B (dB_0_0_U x))))
      (square_nat_route_left dE_4_4_U
        (layer_cube_nat_side dD_2_1_L dC_3_1_L dA_4_0_L (cBE_nil x) (cDE_B (dB_0_0_U x))
          (cCE_BD (dD_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))))
        (layer_cube_nat_side dC_2_1_L dD_3_2_L dA_4_0_L (cBE_nil x) (cCE_B (dB_0_0_U x))
          (cDE_BC (dC_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x)))))
        (layer_cube_nat_side dC_2_1_L dA_3_0_L dD_4_3_L (cBE_nil x) (cCE_B (dB_0_0_U x))
          (cAE_BC (dC_1_1_U (dB_0_0_U x)))
          (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dC_3_2_L dD_4_3_L (cBE_nil x) (cAE_B (dB_0_0_U x))
          (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))))
        (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
          (fun z => dD_3_2_L (dC_2_1_L z)) dA_4_0_L dA_4_0_L
          (fun z => f_equal dA_4_0_L (cCD_BE z)) (cBE_nil x))
        (square_coherence_fill (fun z => dD_3_2_L (dC_2_1_L z))
          (fun z => dA_3_0_L (dC_2_1_L z)) dA_4_0_L dD_4_3_L
          (fun z => cAD_BCE (dC_2_1_L z)) (cBE_nil x))
        (square_coherence_fill (fun z => dA_3_0_L (dC_2_1_L z))
          (fun z => dC_3_2_L (dA_2_0_L z)) dD_4_3_L dD_4_3_L
          (fun z => f_equal dD_4_3_L (cAC_BE z)) (cBE_nil x))
        (square_stack
          (square_map dA_4_0_L ((hCDE_B (dB_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
              (cCD_B (dB_0_0_U x)))))
        (layer_square_nat dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U cAD_BCE
          (cCE_B (dB_0_0_U x)) (cDE_BC (dC_1_1_U (dB_0_0_U x)))
          (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cAD_BC (dC_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dC_1_1_U (dB_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dC_1_1_U (dB_0_0_U x))))
          (hADE_BC (dC_1_1_U (dB_0_0_U x)))
          (square_coherence_fill dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L cAD_BCE
            (cCE_B (dB_0_0_U x))))
        (square_stack
          (square_map dD_4_3_L ((hACE_B (dB_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
              (cAC_B (dB_0_0_U x)))))))
    raw_nat_ACD_B
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_nat_source dD_2_1_L dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U
          cAC_BDE (cBE_nil x) (cDE_B (dB_0_0_U x)) (cCE_BD (dD_1_1_U (dB_0_0_U x)))
          (cAE_BD (dD_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x))))
          (hACE_BD (dD_1_1_U (dB_0_0_U x))))
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_BE
            dC_4_2_L dC_3_2_U dE_4_4_U cCE_ABD (cBE_nil x) (cDE_B (dB_0_0_U x))
            (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x)) (cAE_BD (dD_1_1_U (dB_0_0_U x)))
            (cDE_AB (dA_1_0_U (dB_0_0_U x))) (hADE_B (dB_0_0_U x)))
          (layer_square_nat_source dA_2_0_L dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U
            cCD_ABE (cBE_nil x) (cAE_B (dB_0_0_U x)) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
            (cCE_AB (dA_1_0_U (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x)))
            (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
            (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x))))
            (hCDE_AB (dA_1_0_U (dB_0_0_U x))))))
      (square_nat_route dE_4_4_U
        (layer_cube_nat_side dD_2_1_L dC_3_1_L dA_4_0_L (cBE_nil x) (cDE_B (dB_0_0_U x))
          (cCE_BD (dD_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x)))))
        (layer_cube_nat_side dD_2_1_L dA_3_0_L dC_4_2_L (cBE_nil x) (cDE_B (dB_0_0_U x))
          (cAE_BD (dD_1_1_U (dB_0_0_U x)))
          (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dD_3_2_L dC_4_2_L (cBE_nil x) (cAE_B (dB_0_0_U x))
          (cDE_AB (dA_1_0_U (dB_0_0_U x)))
          (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dC_3_2_L dD_4_3_L (cBE_nil x) (cAE_B (dB_0_0_U x))
          (cCE_AB (dA_1_0_U (dB_0_0_U x)))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x)))))
        (square_coherence_fill (fun z => dC_3_1_L (dD_2_1_L z))
          (fun z => dA_3_0_L (dD_2_1_L z)) dA_4_0_L dC_4_2_L
          (fun z => cAC_BDE (dD_2_1_L z)) (cBE_nil x))
        (square_coherence_fill (fun z => dA_3_0_L (dD_2_1_L z))
          (fun z => dD_3_2_L (dA_2_0_L z)) dC_4_2_L dC_4_2_L
          (fun z => f_equal dC_4_2_L (cAD_BE z)) (cBE_nil x))
        (square_coherence_fill (fun z => dD_3_2_L (dA_2_0_L z))
          (fun z => dC_3_2_L (dA_2_0_L z)) dC_4_2_L dD_4_3_L
          (fun z => cCD_ABE (dA_2_0_L z)) (cBE_nil x))
        (layer_square_nat dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U cAC_BDE
          (cDE_B (dB_0_0_U x)) (cCE_BD (dD_1_1_U (dB_0_0_U x)))
          (cAE_BD (dD_1_1_U (dB_0_0_U x))) (cAC_BD (dD_1_1_U (dB_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dD_1_1_U (dB_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dD_1_1_U (dB_0_0_U x))))
          (hACE_BD (dD_1_1_U (dB_0_0_U x)))
          (square_coherence_fill dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L cAC_BDE
            (cDE_B (dB_0_0_U x))))
        (square_stack
          (square_map dC_4_2_L ((hADE_B (dB_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
              (cAD_B (dB_0_0_U x)))))
        (layer_square_nat dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L dE_4_4_U cCD_ABE
          (cAE_B (dB_0_0_U x)) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
          (cCE_AB (dA_1_0_U (dB_0_0_U x))) (cCD_AB (dA_1_0_U (dB_0_0_U x)))
          (cCE_ABD (dD_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (cDE_ABC (dC_2_2_U (dA_1_0_U (dB_0_0_U x))))
          (hCDE_AB (dA_1_0_U (dB_0_0_U x)))
          (square_coherence_fill dD_3_2_L dC_3_2_L dC_4_2_L dD_4_3_L cCD_ABE
            (cAE_B (dB_0_0_U x)))))).

Local Definition raw_nat_ABD_C :=
  @layer_cube_nat Y2 Y1 Y0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dD_3_3_U dB_3_1_U dA_4_0_L
    dD_4_3_L dB_4_1_L cAE_BCD cDE_ABC cBE_ACD dB_3_0_L dD_3_2_L dA_3_0_L dB_3_1_L cAD_BCE
    cAB_CDE cBD_ACE Y3 dD_2_1_L dB_2_0_L dA_2_0_L cBD_CE cAB_CE cAD_CE hABD_CE
    (dC_1_0_L (dE_0_0_U x)) (dE_1_1_U (dC_0_0_U x)) (cCE_nil x)
    (dB_2_0_U (dD_1_1_U (dC_0_0_U x))) (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))
    (dA_2_0_U (dB_1_0_U (dC_0_0_U x))) (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))
    (dA_2_0_U (dD_1_1_U (dC_0_0_U x))) (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))
    (cBD_C (dC_0_0_U x)) (cAB_C (dC_0_0_U x)) (cAD_C (dC_0_0_U x))
    (cAD_BC (dB_1_0_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x)))
    (cBD_AC (dA_1_0_U (dC_0_0_U x))) (dE_2_2_U (dD_1_1_U (dC_0_0_U x)))
    (dE_2_2_U (dB_1_0_U (dC_0_0_U x))) (dE_2_2_U (dA_1_0_U (dC_0_0_U x)))
    (cDE_C (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cAE_C (dC_0_0_U x))
    (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_BC (dB_1_0_U (dC_0_0_U x)))
    (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
    (cAE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AC (dA_1_0_U (dC_0_0_U x)))
    (hBDE_C (dC_0_0_U x)) (hABE_C (dC_0_0_U x)) (hADE_C (dC_0_0_U x))
    (hABD_C (dC_0_0_U x)) (hADE_BC (dB_1_0_U (dC_0_0_U x)))
    (hABE_CD (dD_1_1_U (dC_0_0_U x))) (hBDE_AC (dA_1_0_U (dC_0_0_U x)))
    (kABDE_C (dC_0_0_U x))
    (square_coherence_fill (fun z => dB_3_0_L (dD_2_1_L z))
      (fun z => dD_3_2_L (dB_2_0_L z)) dA_4_0_L dA_4_0_L
      (fun z => f_equal dA_4_0_L (cBD_CE z)) (cCE_nil x))
    (square_coherence_fill (fun z => dD_3_2_L (dB_2_0_L z))
      (fun z => dA_3_0_L (dB_2_0_L z)) dA_4_0_L dD_4_3_L (fun z => cAD_BCE (dB_2_0_L z))
      (cCE_nil x))
    (square_coherence_fill (fun z => dA_3_0_L (dB_2_0_L z))
      (fun z => dB_3_1_L (dA_2_0_L z)) dD_4_3_L dD_4_3_L
      (fun z => f_equal dD_4_3_L (cAB_CE z)) (cCE_nil x))
    (square_coherence_fill (fun z => dB_3_0_L (dD_2_1_L z))
      (fun z => dA_3_0_L (dD_2_1_L z)) dA_4_0_L dB_4_1_L (fun z => cAB_CDE (dD_2_1_L z))
      (cCE_nil x))
    (square_coherence_fill (fun z => dA_3_0_L (dD_2_1_L z))
      (fun z => dD_3_2_L (dA_2_0_L z)) dB_4_1_L dB_4_1_L
      (fun z => f_equal dB_4_1_L (cAD_CE z)) (cCE_nil x))
    (square_coherence_fill (fun z => dD_3_2_L (dA_2_0_L z))
      (fun z => dB_3_1_L (dA_2_0_L z)) dB_4_1_L dD_4_3_L (fun z => cBD_ACE (dA_2_0_L z))
      (cCE_nil x))
    facet_ABD_CE.

Local Definition hcube_ABD_C:
  square_cube
    (square_compose_map dE_4_4_U (square_compose_map dE_4_4_U n_ABDC_2 n_ADBC_1) n_DABC_2)
    (square_compose_map dE_4_4_U n_ABDC_1 (square_compose_map dE_4_4_U n_BADC_2 n_BDAC_1))
    (f_equal (fun e => f_equal dE_4_4_U e) (hABD_C (dC_0_0_U x)))
    (hABD_CE (dC_1_0_L (dE_0_0_U x))) :=
  square_cube_change_faces
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L dE_3_3_U cBD_CE
            dA_4_0_L dA_3_0_U dE_4_4_U cAE_BCD (cCE_nil x) (cDE_C (dC_0_0_U x))
            (cBE_C (dC_0_0_U x)) (cBD_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
            (cDE_BC (dB_1_0_U (dC_0_0_U x))) (hBDE_C (dC_0_0_U x)))
          (layer_square_nat_source dB_2_0_L dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U
            cAD_BCE (cCE_nil x) (cBE_C (dC_0_0_U x)) (cDE_BC (dB_1_0_U (dC_0_0_U x)))
            (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
            (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
            (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x))))
            (hADE_BC (dB_1_0_U (dC_0_0_U x)))))
        (layer_square_map_source dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_CE
          dD_4_3_L dD_3_3_U dE_4_4_U cDE_ABC (cCE_nil x) (cBE_C (dC_0_0_U x))
          (cAE_C (dC_0_0_U x)) (cAB_C (dC_0_0_U x)) (cAE_BC (dB_1_0_U (dC_0_0_U x)))
          (cBE_AC (dA_1_0_U (dC_0_0_U x))) (hABE_C (dC_0_0_U x))))
      (square_nat_route_left dE_4_4_U
        (layer_cube_nat_side dD_2_1_L dB_3_0_L dA_4_0_L (cCE_nil x) (cDE_C (dC_0_0_U x))
          (cBE_CD (dD_1_1_U (dC_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))))
        (layer_cube_nat_side dB_2_0_L dD_3_2_L dA_4_0_L (cCE_nil x) (cBE_C (dC_0_0_U x))
          (cDE_BC (dB_1_0_U (dC_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x)))))
        (layer_cube_nat_side dB_2_0_L dA_3_0_L dD_4_3_L (cCE_nil x) (cBE_C (dC_0_0_U x))
          (cAE_BC (dB_1_0_U (dC_0_0_U x)))
          (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dB_3_1_L dD_4_3_L (cCE_nil x) (cAE_C (dC_0_0_U x))
          (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))))
        (square_coherence_fill (fun z => dB_3_0_L (dD_2_1_L z))
          (fun z => dD_3_2_L (dB_2_0_L z)) dA_4_0_L dA_4_0_L
          (fun z => f_equal dA_4_0_L (cBD_CE z)) (cCE_nil x))
        (square_coherence_fill (fun z => dD_3_2_L (dB_2_0_L z))
          (fun z => dA_3_0_L (dB_2_0_L z)) dA_4_0_L dD_4_3_L
          (fun z => cAD_BCE (dB_2_0_L z)) (cCE_nil x))
        (square_coherence_fill (fun z => dA_3_0_L (dB_2_0_L z))
          (fun z => dB_3_1_L (dA_2_0_L z)) dD_4_3_L dD_4_3_L
          (fun z => f_equal dD_4_3_L (cAB_CE z)) (cCE_nil x))
        (square_stack
          (square_map dA_4_0_L ((hBDE_C (dC_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
              (cBD_C (dC_0_0_U x)))))
        (layer_square_nat dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L dE_4_4_U cAD_BCE
          (cBE_C (dC_0_0_U x)) (cDE_BC (dB_1_0_U (dC_0_0_U x)))
          (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cAD_BC (dB_1_0_U (dC_0_0_U x)))
          (cAE_BCD (dD_2_2_U (dB_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dA_2_0_U (dB_1_0_U (dC_0_0_U x))))
          (hADE_BC (dB_1_0_U (dC_0_0_U x)))
          (square_coherence_fill dD_3_2_L dA_3_0_L dA_4_0_L dD_4_3_L cAD_BCE
            (cBE_C (dC_0_0_U x))))
        (square_stack
          (square_map dD_4_3_L ((hABE_C (dC_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
              (cAB_C (dC_0_0_U x)))))))
    raw_nat_ABD_C
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_nat_source dD_2_1_L dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U
          cAB_CDE (cCE_nil x) (cDE_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
          (cAE_CD (dD_1_1_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x))))
          (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x))))
          (hABE_CD (dD_1_1_U (dC_0_0_U x))))
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_CE
            dB_4_1_L dB_3_1_U dE_4_4_U cBE_ACD (cCE_nil x) (cDE_C (dC_0_0_U x))
            (cAE_C (dC_0_0_U x)) (cAD_C (dC_0_0_U x)) (cAE_CD (dD_1_1_U (dC_0_0_U x)))
            (cDE_AC (dA_1_0_U (dC_0_0_U x))) (hADE_C (dC_0_0_U x)))
          (layer_square_nat_source dA_2_0_L dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U
            cBD_ACE (cCE_nil x) (cAE_C (dC_0_0_U x)) (cDE_AC (dA_1_0_U (dC_0_0_U x)))
            (cBE_AC (dA_1_0_U (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x)))
            (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
            (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x))))
            (hBDE_AC (dA_1_0_U (dC_0_0_U x))))))
      (square_nat_route dE_4_4_U
        (layer_cube_nat_side dD_2_1_L dB_3_0_L dA_4_0_L (cCE_nil x) (cDE_C (dC_0_0_U x))
          (cBE_CD (dD_1_1_U (dC_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x)))))
        (layer_cube_nat_side dD_2_1_L dA_3_0_L dB_4_1_L (cCE_nil x) (cDE_C (dC_0_0_U x))
          (cAE_CD (dD_1_1_U (dC_0_0_U x)))
          (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dD_3_2_L dB_4_1_L (cCE_nil x) (cAE_C (dC_0_0_U x))
          (cDE_AC (dA_1_0_U (dC_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dB_3_1_L dD_4_3_L (cCE_nil x) (cAE_C (dC_0_0_U x))
          (cBE_AC (dA_1_0_U (dC_0_0_U x)))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x)))))
        (square_coherence_fill (fun z => dB_3_0_L (dD_2_1_L z))
          (fun z => dA_3_0_L (dD_2_1_L z)) dA_4_0_L dB_4_1_L
          (fun z => cAB_CDE (dD_2_1_L z)) (cCE_nil x))
        (square_coherence_fill (fun z => dA_3_0_L (dD_2_1_L z))
          (fun z => dD_3_2_L (dA_2_0_L z)) dB_4_1_L dB_4_1_L
          (fun z => f_equal dB_4_1_L (cAD_CE z)) (cCE_nil x))
        (square_coherence_fill (fun z => dD_3_2_L (dA_2_0_L z))
          (fun z => dB_3_1_L (dA_2_0_L z)) dB_4_1_L dD_4_3_L
          (fun z => cBD_ACE (dA_2_0_L z)) (cCE_nil x))
        (layer_square_nat dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U cAB_CDE
          (cDE_C (dC_0_0_U x)) (cBE_CD (dD_1_1_U (dC_0_0_U x)))
          (cAE_CD (dD_1_1_U (dC_0_0_U x))) (cAB_CD (dD_1_1_U (dC_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dD_1_1_U (dC_0_0_U x))))
          (cBE_ACD (dA_2_0_U (dD_1_1_U (dC_0_0_U x))))
          (hABE_CD (dD_1_1_U (dC_0_0_U x)))
          (square_coherence_fill dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L cAB_CDE
            (cDE_C (dC_0_0_U x))))
        (square_stack
          (square_map dB_4_1_L ((hADE_C (dC_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
              (cAD_C (dC_0_0_U x)))))
        (layer_square_nat dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L dE_4_4_U cBD_ACE
          (cAE_C (dC_0_0_U x)) (cDE_AC (dA_1_0_U (dC_0_0_U x)))
          (cBE_AC (dA_1_0_U (dC_0_0_U x))) (cBD_AC (dA_1_0_U (dC_0_0_U x)))
          (cBE_ACD (dD_2_2_U (dA_1_0_U (dC_0_0_U x))))
          (cDE_ABC (dB_2_1_U (dA_1_0_U (dC_0_0_U x))))
          (hBDE_AC (dA_1_0_U (dC_0_0_U x)))
          (square_coherence_fill dD_3_2_L dB_3_1_L dB_4_1_L dD_4_3_L cBD_ACE
            (cAE_C (dC_0_0_U x)))))).

Local Definition raw_nat_ABC_D :=
  @layer_cube_nat Y2 Y1 Y0 X2 X1 dE_3_3_U dE_4_4_U dA_3_0_U dC_3_2_U dB_3_1_U dA_4_0_L
    dC_4_2_L dB_4_1_L cAE_BCD cCE_ABD cBE_ACD dB_3_0_L dC_3_1_L dA_3_0_L dB_3_1_L cAC_BDE
    cAB_CDE cBC_ADE Y3 dC_2_0_L dB_2_0_L dA_2_0_L cBC_DE cAB_DE cAC_DE hABC_DE
    (dD_1_0_L (dE_0_0_U x)) (dE_1_1_U (dD_0_0_U x)) (cDE_nil x)
    (dB_2_0_U (dC_1_0_U (dD_0_0_U x))) (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))
    (dA_2_0_U (dB_1_0_U (dD_0_0_U x))) (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))
    (dA_2_0_U (dC_1_0_U (dD_0_0_U x))) (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))
    (cBC_D (dD_0_0_U x)) (cAB_D (dD_0_0_U x)) (cAC_D (dD_0_0_U x))
    (cAC_BD (dB_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x)))
    (cBC_AD (dA_1_0_U (dD_0_0_U x))) (dE_2_2_U (dC_1_0_U (dD_0_0_U x)))
    (dE_2_2_U (dB_1_0_U (dD_0_0_U x))) (dE_2_2_U (dA_1_0_U (dD_0_0_U x)))
    (cCE_D (dD_0_0_U x)) (cBE_D (dD_0_0_U x)) (cAE_D (dD_0_0_U x))
    (cBE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_BD (dB_1_0_U (dD_0_0_U x)))
    (cAE_BD (dB_1_0_U (dD_0_0_U x))) (cBE_AD (dA_1_0_U (dD_0_0_U x)))
    (cAE_CD (dC_1_0_U (dD_0_0_U x))) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
    (hBCE_D (dD_0_0_U x)) (hABE_D (dD_0_0_U x)) (hACE_D (dD_0_0_U x))
    (hABC_D (dD_0_0_U x)) (hACE_BD (dB_1_0_U (dD_0_0_U x)))
    (hABE_CD (dC_1_0_U (dD_0_0_U x))) (hBCE_AD (dA_1_0_U (dD_0_0_U x)))
    (kABCE_D (dD_0_0_U x))
    (square_coherence_fill (fun z => dB_3_0_L (dC_2_0_L z))
      (fun z => dC_3_1_L (dB_2_0_L z)) dA_4_0_L dA_4_0_L
      (fun z => f_equal dA_4_0_L (cBC_DE z)) (cDE_nil x))
    (square_coherence_fill (fun z => dC_3_1_L (dB_2_0_L z))
      (fun z => dA_3_0_L (dB_2_0_L z)) dA_4_0_L dC_4_2_L (fun z => cAC_BDE (dB_2_0_L z))
      (cDE_nil x))
    (square_coherence_fill (fun z => dA_3_0_L (dB_2_0_L z))
      (fun z => dB_3_1_L (dA_2_0_L z)) dC_4_2_L dC_4_2_L
      (fun z => f_equal dC_4_2_L (cAB_DE z)) (cDE_nil x))
    (square_coherence_fill (fun z => dB_3_0_L (dC_2_0_L z))
      (fun z => dA_3_0_L (dC_2_0_L z)) dA_4_0_L dB_4_1_L (fun z => cAB_CDE (dC_2_0_L z))
      (cDE_nil x))
    (square_coherence_fill (fun z => dA_3_0_L (dC_2_0_L z))
      (fun z => dC_3_1_L (dA_2_0_L z)) dB_4_1_L dB_4_1_L
      (fun z => f_equal dB_4_1_L (cAC_DE z)) (cDE_nil x))
    (square_coherence_fill (fun z => dC_3_1_L (dA_2_0_L z))
      (fun z => dB_3_1_L (dA_2_0_L z)) dB_4_1_L dC_4_2_L (fun z => cBC_ADE (dA_2_0_L z))
      (cDE_nil x))
    facet_ABC_DE.

Local Definition hcube_ABC_D:
  square_cube
    (square_compose_map dE_4_4_U (square_compose_map dE_4_4_U n_ABCD_2 n_ACBD_1) n_CABD_2)
    (square_compose_map dE_4_4_U n_ABCD_1 (square_compose_map dE_4_4_U n_BACD_2 n_BCAD_1))
    (f_equal (fun e => f_equal dE_4_4_U e) (hABC_D (dD_0_0_U x)))
    (hABC_DE (dD_1_0_L (dE_0_0_U x))) :=
  square_cube_change_faces
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dC_2_0_L dB_2_0_L dB_3_0_L dC_3_1_L dE_3_3_U cBC_DE
            dA_4_0_L dA_3_0_U dE_4_4_U cAE_BCD (cDE_nil x) (cCE_D (dD_0_0_U x))
            (cBE_D (dD_0_0_U x)) (cBC_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
            (cCE_BD (dB_1_0_U (dD_0_0_U x))) (hBCE_D (dD_0_0_U x)))
          (layer_square_nat_source dB_2_0_L dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U
            cAC_BDE (cDE_nil x) (cBE_D (dD_0_0_U x)) (cCE_BD (dB_1_0_U (dD_0_0_U x)))
            (cAE_BD (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
            (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
            (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x))))
            (hACE_BD (dB_1_0_U (dD_0_0_U x)))))
        (layer_square_map_source dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_DE
          dC_4_2_L dC_3_2_U dE_4_4_U cCE_ABD (cDE_nil x) (cBE_D (dD_0_0_U x))
          (cAE_D (dD_0_0_U x)) (cAB_D (dD_0_0_U x)) (cAE_BD (dB_1_0_U (dD_0_0_U x)))
          (cBE_AD (dA_1_0_U (dD_0_0_U x))) (hABE_D (dD_0_0_U x))))
      (square_nat_route_left dE_4_4_U
        (layer_cube_nat_side dC_2_0_L dB_3_0_L dA_4_0_L (cDE_nil x) (cCE_D (dD_0_0_U x))
          (cBE_CD (dC_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))))
        (layer_cube_nat_side dB_2_0_L dC_3_1_L dA_4_0_L (cDE_nil x) (cBE_D (dD_0_0_U x))
          (cCE_BD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x)))))
        (layer_cube_nat_side dB_2_0_L dA_3_0_L dC_4_2_L (cDE_nil x) (cBE_D (dD_0_0_U x))
          (cAE_BD (dB_1_0_U (dD_0_0_U x)))
          (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dB_3_1_L dC_4_2_L (cDE_nil x) (cAE_D (dD_0_0_U x))
          (cBE_AD (dA_1_0_U (dD_0_0_U x)))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))))
        (square_coherence_fill (fun z => dB_3_0_L (dC_2_0_L z))
          (fun z => dC_3_1_L (dB_2_0_L z)) dA_4_0_L dA_4_0_L
          (fun z => f_equal dA_4_0_L (cBC_DE z)) (cDE_nil x))
        (square_coherence_fill (fun z => dC_3_1_L (dB_2_0_L z))
          (fun z => dA_3_0_L (dB_2_0_L z)) dA_4_0_L dC_4_2_L
          (fun z => cAC_BDE (dB_2_0_L z)) (cDE_nil x))
        (square_coherence_fill (fun z => dA_3_0_L (dB_2_0_L z))
          (fun z => dB_3_1_L (dA_2_0_L z)) dC_4_2_L dC_4_2_L
          (fun z => f_equal dC_4_2_L (cAB_DE z)) (cDE_nil x))
        (square_stack
          (square_map dA_4_0_L ((hBCE_D (dD_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
              (cBC_D (dD_0_0_U x)))))
        (layer_square_nat dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L dE_4_4_U cAC_BDE
          (cBE_D (dD_0_0_U x)) (cCE_BD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BD (dB_1_0_U (dD_0_0_U x))) (cAC_BD (dB_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dC_2_1_U (dB_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dA_2_0_U (dB_1_0_U (dD_0_0_U x))))
          (hACE_BD (dB_1_0_U (dD_0_0_U x)))
          (square_coherence_fill dC_3_1_L dA_3_0_L dA_4_0_L dC_4_2_L cAC_BDE
            (cBE_D (dD_0_0_U x))))
        (square_stack
          (square_map dC_4_2_L ((hABE_D (dD_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
              (cAB_D (dD_0_0_U x)))))))
    raw_nat_ABC_D
    (eq_trans
      (path_map2
        (fun H K => square_compose_map dE_4_4_U H K)
        (layer_square_nat_source dC_2_0_L dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U
          cAB_CDE (cDE_nil x) (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
          (cAE_CD (dC_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x))))
          (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x))))
          (hABE_CD (dC_1_0_U (dD_0_0_U x))))
        (path_map2
          (fun H K => square_compose_map dE_4_4_U H K)
          (layer_square_map_source dC_2_0_L dA_2_0_L dA_3_0_L dC_3_1_L dE_3_3_U cAC_DE
            dB_4_1_L dB_3_1_U dE_4_4_U cBE_ACD (cDE_nil x) (cCE_D (dD_0_0_U x))
            (cAE_D (dD_0_0_U x)) (cAC_D (dD_0_0_U x)) (cAE_CD (dC_1_0_U (dD_0_0_U x)))
            (cCE_AD (dA_1_0_U (dD_0_0_U x))) (hACE_D (dD_0_0_U x)))
          (layer_square_nat_source dA_2_0_L dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U
            cBC_ADE (cDE_nil x) (cAE_D (dD_0_0_U x)) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
            (cBE_AD (dA_1_0_U (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x)))
            (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
            (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x))))
            (hBCE_AD (dA_1_0_U (dD_0_0_U x))))))
      (square_nat_route dE_4_4_U
        (layer_cube_nat_side dC_2_0_L dB_3_0_L dA_4_0_L (cDE_nil x) (cCE_D (dD_0_0_U x))
          (cBE_CD (dC_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x)))))
        (layer_cube_nat_side dC_2_0_L dA_3_0_L dB_4_1_L (cDE_nil x) (cCE_D (dD_0_0_U x))
          (cAE_CD (dC_1_0_U (dD_0_0_U x)))
          (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dC_3_1_L dB_4_1_L (cDE_nil x) (cAE_D (dD_0_0_U x))
          (cCE_AD (dA_1_0_U (dD_0_0_U x)))
          (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x)))))
        (layer_cube_nat_side dA_2_0_L dB_3_1_L dC_4_2_L (cDE_nil x) (cAE_D (dD_0_0_U x))
          (cBE_AD (dA_1_0_U (dD_0_0_U x)))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x)))))
        (square_coherence_fill (fun z => dB_3_0_L (dC_2_0_L z))
          (fun z => dA_3_0_L (dC_2_0_L z)) dA_4_0_L dB_4_1_L
          (fun z => cAB_CDE (dC_2_0_L z)) (cDE_nil x))
        (square_coherence_fill (fun z => dA_3_0_L (dC_2_0_L z))
          (fun z => dC_3_1_L (dA_2_0_L z)) dB_4_1_L dB_4_1_L
          (fun z => f_equal dB_4_1_L (cAC_DE z)) (cDE_nil x))
        (square_coherence_fill (fun z => dC_3_1_L (dA_2_0_L z))
          (fun z => dB_3_1_L (dA_2_0_L z)) dB_4_1_L dC_4_2_L
          (fun z => cBC_ADE (dA_2_0_L z)) (cDE_nil x))
        (layer_square_nat dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L dE_4_4_U cAB_CDE
          (cCE_D (dD_0_0_U x)) (cBE_CD (dC_1_0_U (dD_0_0_U x)))
          (cAE_CD (dC_1_0_U (dD_0_0_U x))) (cAB_CD (dC_1_0_U (dD_0_0_U x)))
          (cAE_BCD (dB_2_0_U (dC_1_0_U (dD_0_0_U x))))
          (cBE_ACD (dA_2_0_U (dC_1_0_U (dD_0_0_U x))))
          (hABE_CD (dC_1_0_U (dD_0_0_U x)))
          (square_coherence_fill dB_3_0_L dA_3_0_L dA_4_0_L dB_4_1_L cAB_CDE
            (cCE_D (dD_0_0_U x))))
        (square_stack
          (square_map dB_4_1_L ((hACE_D (dD_0_0_U x))))
          (eq_sym
            (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
              (cAC_D (dD_0_0_U x)))))
        (layer_square_nat dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L dE_4_4_U cBC_ADE
          (cAE_D (dD_0_0_U x)) (cCE_AD (dA_1_0_U (dD_0_0_U x)))
          (cBE_AD (dA_1_0_U (dD_0_0_U x))) (cBC_AD (dA_1_0_U (dD_0_0_U x)))
          (cBE_ACD (dC_2_1_U (dA_1_0_U (dD_0_0_U x))))
          (cCE_ABD (dB_2_1_U (dA_1_0_U (dD_0_0_U x))))
          (hBCE_AD (dA_1_0_U (dD_0_0_U x)))
          (square_coherence_fill dC_3_1_L dB_3_1_L dB_4_1_L dC_4_2_L cBC_ADE
            (cAE_D (dD_0_0_U x)))))).

(** Each square face transports by pasting two prisms: naturality of
    the comparison hexagon and mapping of the source hexagon. The six
    choices below cover the ordered partitions of [A, B, C, D] into
    two two-letter blocks. *)
Local Definition positive_square_AB_CD :=
  hexagonal_prism_pair_cube (dC_2_0_L) (dE_2_2_U) (dD_2_1_L) (dB_2_0_U) (dA_2_0_U)
    (dB_3_0_L) (dA_3_0_L) (dE_3_3_U) (dE_3_3_U) (dA_4_0_L) (dB_4_1_L) (dA_3_0_U)
    (dB_3_1_U) (dE_4_4_U) (cBE_CD) (cAE_CD) (cAE_BCD) (cBE_ACD) (cAB_CDE) (cAB_CD)
    (hABE_CD) (cDE_nil (x)) (cCD_nil (x)) (cCE_nil (x)) (cCE_D (dD_0_0_U (x)))
    (cCD_E (dE_0_0_U (x))) (cDE_C (dC_0_0_U (x))) (hCDE_nil (x)) (facet_AB_CDE)
    (facet_ABE_CD).

Local Definition positive_square_AC_BD :=
  hexagonal_prism_pair_cube (dB_2_0_L) (dE_2_2_U) (dD_2_1_L) (dC_2_1_U) (dA_2_0_U)
    (dC_3_1_L) (dA_3_0_L) (dE_3_3_U) (dE_3_3_U) (dA_4_0_L) (dC_4_2_L) (dA_3_0_U)
    (dC_3_2_U) (dE_4_4_U) (cCE_BD) (cAE_BD) (cAE_BCD) (cCE_ABD) (cAC_BDE) (cAC_BD)
    (hACE_BD) (cDE_nil (x)) (cBD_nil (x)) (cBE_nil (x)) (cBE_D (dD_0_0_U (x)))
    (cBD_E (dE_0_0_U (x))) (cDE_B (dB_0_0_U (x))) (hBDE_nil (x)) (facet_AC_BDE)
    (facet_ACE_BD).

Local Definition positive_square_AD_BC :=
  hexagonal_prism_pair_cube (dB_2_0_L) (dE_2_2_U) (dC_2_1_L) (dD_2_2_U) (dA_2_0_U)
    (dD_3_2_L) (dA_3_0_L) (dE_3_3_U) (dE_3_3_U) (dA_4_0_L) (dD_4_3_L) (dA_3_0_U)
    (dD_3_3_U) (dE_4_4_U) (cDE_BC) (cAE_BC) (cAE_BCD) (cDE_ABC) (cAD_BCE) (cAD_BC)
    (hADE_BC) (cCE_nil (x)) (cBC_nil (x)) (cBE_nil (x)) (cBE_C (dC_0_0_U (x)))
    (cBC_E (dE_0_0_U (x))) (cCE_B (dB_0_0_U (x))) (hBCE_nil (x)) (facet_AD_BCE)
    (facet_ADE_BC).

Local Definition positive_square_BC_AD :=
  hexagonal_prism_pair_cube (dA_2_0_L) (dE_2_2_U) (dD_2_1_L) (dC_2_1_U) (dB_2_1_U)
    (dC_3_1_L) (dB_3_1_L) (dE_3_3_U) (dE_3_3_U) (dB_4_1_L) (dC_4_2_L) (dB_3_1_U)
    (dC_3_2_U) (dE_4_4_U) (cCE_AD) (cBE_AD) (cBE_ACD) (cCE_ABD) (cBC_ADE) (cBC_AD)
    (hBCE_AD) (cDE_nil (x)) (cAD_nil (x)) (cAE_nil (x)) (cAE_D (dD_0_0_U (x)))
    (cAD_E (dE_0_0_U (x))) (cDE_A (dA_0_0_U (x))) (hADE_nil (x)) (facet_BC_ADE)
    (facet_BCE_AD).

Local Definition positive_square_BD_AC :=
  hexagonal_prism_pair_cube (dA_2_0_L) (dE_2_2_U) (dC_2_1_L) (dD_2_2_U) (dB_2_1_U)
    (dD_3_2_L) (dB_3_1_L) (dE_3_3_U) (dE_3_3_U) (dB_4_1_L) (dD_4_3_L) (dB_3_1_U)
    (dD_3_3_U) (dE_4_4_U) (cDE_AC) (cBE_AC) (cBE_ACD) (cDE_ABC) (cBD_ACE) (cBD_AC)
    (hBDE_AC) (cCE_nil (x)) (cAC_nil (x)) (cAE_nil (x)) (cAE_C (dC_0_0_U (x)))
    (cAC_E (dE_0_0_U (x))) (cCE_A (dA_0_0_U (x))) (hACE_nil (x)) (facet_BD_ACE)
    (facet_BDE_AC).

Local Definition positive_square_CD_AB :=
  hexagonal_prism_pair_cube (dA_2_0_L) (dE_2_2_U) (dB_2_1_L) (dD_2_2_U) (dC_2_2_U)
    (dD_3_2_L) (dC_3_2_L) (dE_3_3_U) (dE_3_3_U) (dC_4_2_L) (dD_4_3_L) (dC_3_2_U)
    (dD_3_3_U) (dE_4_4_U) (cDE_AB) (cCE_AB) (cCE_ABD) (cDE_ABC) (cCD_ABE) (cCD_AB)
    (hCDE_AB) (cBE_nil (x)) (cAB_nil (x)) (cAE_nil (x)) (cAE_B (dB_0_0_U (x)))
    (cAB_E (dE_0_0_U (x))) (cBE_A (dA_0_0_U (x))) (hABE_nil (x)) (facet_CD_ABE)
    (facet_CDE_AB).

Local Definition n_BCD_2 :=
  square_stack (square_map dB_3_0_L (hCDE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dB_2_0_U dB_3_0_L dE_3_3_U cBE_CD (cCD_nil x))).

Local Definition n_BDC_1 :=
  layer_square_nat dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L dE_3_3_U cBD_CE (cCE_nil x)
    (cDE_C (dC_0_0_U x)) (cBE_C (dC_0_0_U x)) (cBD_C (dC_0_0_U x))
    (cBE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_BC (dB_1_0_U (dC_0_0_U x)))
    (hBDE_C (dC_0_0_U x))
    (square_coherence_fill dD_2_1_L dB_2_0_L dB_3_0_L dD_3_2_L cBD_CE (cCE_nil x)).

Local Definition n_DBC_2 :=
  square_stack (square_map dD_3_2_L (hBCE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dD_2_2_U dD_3_2_L dE_3_3_U cDE_BC (cBC_nil x))).

Local Definition n_CBD_2 :=
  square_stack (square_map dC_3_1_L (hBDE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dC_2_1_U dC_3_1_L dE_3_3_U cCE_BD (cBD_nil x))).

Local Definition n_CDB_1 :=
  layer_square_nat dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_BE (cBE_nil x)
    (cDE_B (dB_0_0_U x)) (cCE_B (dB_0_0_U x)) (cCD_B (dB_0_0_U x))
    (cCE_BD (dD_1_1_U (dB_0_0_U x))) (cDE_BC (dC_1_1_U (dB_0_0_U x)))
    (hCDE_B (dB_0_0_U x))
    (square_coherence_fill dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L cCD_BE (cBE_nil x)).

Local Definition n_ABD_2 :=
  square_stack (square_map dA_3_0_L (hBDE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U cAE_BD (cBD_nil x))).

Local Definition n_ADB_1 :=
  layer_square_nat dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_BE (cBE_nil x)
    (cDE_B (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAD_B (dB_0_0_U x))
    (cAE_BD (dD_1_1_U (dB_0_0_U x))) (cDE_AB (dA_1_0_U (dB_0_0_U x)))
    (hADE_B (dB_0_0_U x))
    (square_coherence_fill dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L cAD_BE (cBE_nil x)).

Local Definition n_DAB_2 :=
  square_stack (square_map dD_3_2_L (hABE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dD_2_2_U dD_3_2_L dE_3_3_U cDE_AB (cAB_nil x))).

Local Definition n_ACD_2 :=
  square_stack (square_map dA_3_0_L (hCDE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U cAE_CD (cCD_nil x))).

Local Definition n_ADC_1 :=
  layer_square_nat dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L dE_3_3_U cAD_CE (cCE_nil x)
    (cDE_C (dC_0_0_U x)) (cAE_C (dC_0_0_U x)) (cAD_C (dC_0_0_U x))
    (cAE_CD (dD_1_1_U (dC_0_0_U x))) (cDE_AC (dA_1_0_U (dC_0_0_U x)))
    (hADE_C (dC_0_0_U x))
    (square_coherence_fill dD_2_1_L dA_2_0_L dA_3_0_L dD_3_2_L cAD_CE (cCE_nil x)).

Local Definition n_DAC_2 :=
  square_stack (square_map dD_3_2_L (hACE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dD_2_2_U dD_3_2_L dE_3_3_U cDE_AC (cAC_nil x))).

Local Definition n_CAD_2 :=
  square_stack (square_map dC_3_1_L (hADE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dC_2_1_U dC_3_1_L dE_3_3_U cCE_AD (cAD_nil x))).

Local Definition n_CDA_1 :=
  layer_square_nat dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L dE_3_3_U cCD_AE (cAE_nil x)
    (cDE_A (dA_0_0_U x)) (cCE_A (dA_0_0_U x)) (cCD_A (dA_0_0_U x))
    (cCE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AC (dC_1_1_U (dA_0_0_U x)))
    (hCDE_A (dA_0_0_U x))
    (square_coherence_fill dD_2_1_L dC_2_1_L dC_3_1_L dD_3_2_L cCD_AE (cAE_nil x)).

Local Definition n_BAD_2 :=
  square_stack (square_map dB_3_1_L (hADE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dB_2_1_U dB_3_1_L dE_3_3_U cBE_AD (cAD_nil x))).

Local Definition n_BDA_1 :=
  layer_square_nat dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L dE_3_3_U cBD_AE (cAE_nil x)
    (cDE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBD_A (dA_0_0_U x))
    (cBE_AD (dD_1_1_U (dA_0_0_U x))) (cDE_AB (dB_1_1_U (dA_0_0_U x)))
    (hBDE_A (dA_0_0_U x))
    (square_coherence_fill dD_2_1_L dB_2_1_L dB_3_1_L dD_3_2_L cBD_AE (cAE_nil x)).

Local Definition n_ABC_2 :=
  square_stack (square_map dA_3_0_L (hBCE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dA_2_0_U dA_3_0_L dE_3_3_U cAE_BC (cBC_nil x))).

Local Definition n_ACB_1 :=
  layer_square_nat dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L dE_3_3_U cAC_BE (cBE_nil x)
    (cCE_B (dB_0_0_U x)) (cAE_B (dB_0_0_U x)) (cAC_B (dB_0_0_U x))
    (cAE_BC (dC_1_1_U (dB_0_0_U x))) (cCE_AB (dA_1_0_U (dB_0_0_U x)))
    (hACE_B (dB_0_0_U x))
    (square_coherence_fill dC_2_1_L dA_2_0_L dA_3_0_L dC_3_2_L cAC_BE (cBE_nil x)).

Local Definition n_CAB_2 :=
  square_stack (square_map dC_3_2_L (hABE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dC_2_2_U dC_3_2_L dE_3_3_U cCE_AB (cAB_nil x))).

Local Definition n_ABC_1 :=
  layer_square_nat dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L dE_3_3_U cAB_CE (cCE_nil x)
    (cBE_C (dC_0_0_U x)) (cAE_C (dC_0_0_U x)) (cAB_C (dC_0_0_U x))
    (cAE_BC (dB_1_0_U (dC_0_0_U x))) (cBE_AC (dA_1_0_U (dC_0_0_U x)))
    (hABE_C (dC_0_0_U x))
    (square_coherence_fill dB_2_0_L dA_2_0_L dA_3_0_L dB_3_1_L cAB_CE (cCE_nil x)).

Local Definition n_BAC_2 :=
  square_stack (square_map dB_3_1_L (hACE_nil x))
    (eq_sym
      (square_coherence_fill dE_2_2_U dB_2_1_U dB_3_1_L dE_3_3_U cBE_AC (cAC_nil x))).

Local Definition n_BCA_1 :=
  layer_square_nat dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L dE_3_3_U cBC_AE (cAE_nil x)
    (cCE_A (dA_0_0_U x)) (cBE_A (dA_0_0_U x)) (cBC_A (dA_0_0_U x))
    (cBE_AC (dC_1_1_U (dA_0_0_U x))) (cCE_AB (dB_1_1_U (dA_0_0_U x)))
    (hBCE_A (dA_0_0_U x))
    (square_coherence_fill dC_2_1_L dB_2_1_L dB_3_1_L dC_3_2_L cBC_AE (cAE_nil x)).

(** Lift the six side pastings of [permutahedral_coherence], preserving
    their association. The remaining two hexagons close these routes. *)
Local Definition p5_left_map_BCD :=
  square_stack_cube dE_4_4_U
    (square_map_cube dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD (kBCDE_nil x)
      (facet_AE_BCD_route))
    (square_cube_inverse_map dE_4_4_U positive_square_AD_BC).

Local Definition p5_left_nat_ACD :=
  square_change_sides_cube dE_4_4_U
    (square_cube_trans_map dE_4_4_U
      (square_cube_whisker_r dE_4_4_U n_ADCB_1
        (square_map_along_compose dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
          (f_equal dC_2_1_U (cBD_nil x)) (cCD_B (dB_0_0_U x)) n_CBD_2 n_CDB_1))
      (square_cube_inverse_map dE_4_4_U
        (square_compose_map_assoc dE_4_4_U n_ACBD_3 n_ACDB_2 n_ADCB_1)))
    (square_stack_cube dE_4_4_U positive_square_AC_BD hcube_ACD_B)
    (square_cube_trans_map dE_4_4_U
      (square_cube_whisker_r dE_4_4_U n_CDAB_1
        (square_map_along_compose dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
          (f_equal dA_2_0_U (cBD_nil x)) (cAD_B (dB_0_0_U x)) n_ABD_2 n_ADB_1))
      (square_cube_inverse_map dE_4_4_U
        (square_compose_map_assoc dE_4_4_U n_CABD_3 n_CADB_2 n_CDAB_1))).

Local Definition p5_left_map_ABD :=
  square_stack_cube dE_4_4_U
    (square_map_cube dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD (kABDE_nil x)
      (facet_CE_ABD_route))
    (square_cube_inverse_map dE_4_4_U positive_square_CD_AB).

Local Definition p5_right_nat_ABD :=
  square_change_sides_cube dE_4_4_U
    (square_cube_trans_map dE_4_4_U
      (square_cube_whisker_r dE_4_4_U n_ADBC_1
        (square_map_along_compose dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
          (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)) n_BCD_2 n_BDC_1))
      (square_cube_inverse_map dE_4_4_U
        (square_compose_map_assoc dE_4_4_U n_ABCD_3 n_ABDC_2 n_ADBC_1)))
    (square_stack_cube dE_4_4_U positive_square_AB_CD hcube_ABD_C)
    (square_cube_trans_map dE_4_4_U
      (square_cube_whisker_r dE_4_4_U n_BDAC_1
        (square_map_along_compose dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
          (f_equal dA_2_0_U (cCD_nil x)) (cAD_C (dC_0_0_U x)) n_ACD_2 n_ADC_1))
      (square_cube_inverse_map dE_4_4_U
        (square_compose_map_assoc dE_4_4_U n_BACD_3 n_BADC_2 n_BDAC_1))).

Local Definition p5_right_map_ACD :=
  square_stack_cube dE_4_4_U
    (square_map_cube dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD (kACDE_nil x)
      (facet_BE_ACD_route))
    (square_cube_inverse_map dE_4_4_U positive_square_BD_AC).

Local Definition p5_right_nat_BCD :=
  square_change_sides_cube dE_4_4_U
    (square_cube_trans_map dE_4_4_U
      (square_cube_whisker_r dE_4_4_U n_BDCA_1
        (square_map_along_compose dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
          (f_equal dC_2_1_U (cAD_nil x)) (cCD_A (dA_0_0_U x)) n_CAD_2 n_CDA_1))
      (square_cube_inverse_map dE_4_4_U
        (square_compose_map_assoc dE_4_4_U n_BCAD_3 n_BCDA_2 n_BDCA_1)))
    (square_stack_cube dE_4_4_U positive_square_BC_AD hcube_BCD_A)
    (square_cube_trans_map dE_4_4_U
      (square_cube_whisker_r dE_4_4_U n_CDBA_1
        (square_map_along_compose dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
          (f_equal dB_2_1_U (cAD_nil x)) (cBD_A (dA_0_0_U x)) n_BAD_2 n_BDA_1))
      (square_cube_inverse_map dE_4_4_U
        (square_compose_map_assoc dE_4_4_U n_CBAD_3 n_CBDA_2 n_CDBA_1))).

Local Definition p5_left_sides :=
  let prefix :=
    (square_compose_map dE_4_4_U
      (square_map_along dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD _
        (square_compose_map dE_3_3_U n_BCD_2 n_BDC_1)
        (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
          (eq_trans (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)))))
      n_ADBC_1)
    in square_cube_trans_map dE_4_4_U
    (square_cube_whisker_l dE_4_4_U prefix
      (square_map_along_compose dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (eq_trans (f_equal dA_2_0_U (cBC_nil x)) (cAC_B (dB_0_0_U x)))
        (f_equal dC_2_2_U (cAB_nil x))
        (square_compose_map dE_3_3_U n_ABC_2 n_ACB_1)
        n_CAB_2))
    (square_compose_cube dE_4_4_U
      (square_cube_trans_map dE_4_4_U
        (square_cube_whisker_l dE_4_4_U prefix
          (square_map_along_compose dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
            (f_equal dA_2_0_U (cBC_nil x)) (cAC_B (dB_0_0_U x)) n_ABC_2 n_ACB_1))
        (square_compose_cube dE_4_4_U p5_left_map_BCD p5_left_nat_ACD))
      p5_left_map_ABD).

Local Definition p5_right_sides :=
  square_cube_trans_map dE_4_4_U
    (square_cube_whisker_l dE_4_4_U
      (square_compose_map dE_4_4_U
        (square_map_along dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD _
          (square_compose_map dE_3_3_U n_BCD_2 n_BDC_1)
          (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
            (eq_trans (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)))))
        n_ADBC_1)
      (square_map_along_compose dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
        (cAB_C (dC_0_0_U x))
        (eq_trans (f_equal dB_2_1_U (cAC_nil x)) (cBC_A (dA_0_0_U x)))
        n_ABC_1
        (square_compose_map dE_3_3_U n_BAC_2 n_BCA_1)))
    (square_compose_cube dE_4_4_U p5_right_nat_ABD
      (square_cube_trans_map dE_4_4_U
        (square_cube_whisker_l dE_4_4_U
          (square_compose_map dE_4_4_U
            (square_map_along dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD _
              (square_compose_map dE_3_3_U n_ACD_2 n_ADC_1)
              (square_coherence_fill dE_3_3_U dB_3_1_U dB_4_1_L dE_4_4_U cBE_ACD
                (eq_trans (f_equal dA_2_0_U (cCD_nil x)) (cAD_C (dC_0_0_U x)))))
            n_BDAC_1)
          (square_map_along_compose dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC
            (f_equal dB_2_1_U (cAC_nil x)) (cBC_A (dA_0_0_U x)) n_BAC_2 n_BCA_1))
        (square_compose_cube dE_4_4_U p5_right_map_ACD p5_right_nat_BCD))).

Local Definition p5_left_boundary :=
  square_cube_trans_map dE_4_4_U p5_left_sides
    (square_cube_whisker_r dE_4_4_U
      (square_compose_map dE_4_4_U
        (square_map_along dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD _
          (square_compose_map dE_3_3_U n_BAD_2 n_BDA_1)
          (square_coherence_fill dE_3_3_U dC_3_2_U dC_4_2_L dE_4_4_U cCE_ABD
            (eq_trans (f_equal dB_2_1_U (cAD_nil x)) (cBD_A (dA_0_0_U x)))))
        n_CDBA_1)
      hcube_ABC_D).

Local Definition p5_right_boundary :=
  square_cube_trans_map dE_4_4_U
    (square_cube_whisker_l dE_4_4_U
      (square_compose_map dE_4_4_U
        (square_map_along dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD _
          (square_compose_map dE_3_3_U n_BCD_2 n_BDC_1)
          (square_coherence_fill dE_3_3_U dA_3_0_U dA_4_0_L dE_4_4_U cAE_BCD
            (eq_trans (f_equal dB_2_0_U (cCD_nil x)) (cBD_C (dC_0_0_U x)))))
        n_ADBC_1)
      (square_cube_map_along dE_3_3_U dD_3_3_U dD_4_3_L dE_4_4_U cDE_ABC (kABCE_nil x)
        (facet_DE_ABC_route)))
    p5_right_sides.

(** The two pastings of the P5 boundary. Each has five permutahedral
    and ten hexagonal-prism facets. *)
Definition perm5_coherence : Prop :=
  square_cube p5_left_boundary p5_right_boundary
    (f_equal (fun H => whisker_r H v_DCBA) (kABCD_E (dE_0_0_U x)))
    (f_equal
      (fun H => whisker_l v_ABCD (f_equal (fun e => f_equal dE_4_4_U e) H))
      (kABCD_nil x)).

End FiveOperations.
