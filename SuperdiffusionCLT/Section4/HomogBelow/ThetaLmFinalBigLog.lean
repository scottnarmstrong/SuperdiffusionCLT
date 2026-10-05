/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.M0ThresholdB
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmP2Prime
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmThetaZero
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmThetaZeroGe1
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmAssemblyGammaOne

/-!
**The match** between the generic (`D, H, KPsiS, pPsiS`-parametrized) "big-log ≤ m0"
hypothesis of `ThetaLmAssemblyAKHCApp.lean` (the third premise of `homogBelow_akhcApplication`,
which must be discharged before its `hStep` can be applied) and `homogBelowM0_threshold_corrected`
of `M0ThresholdB.lean` (hardwired at the paper's own choice `D=1, K_{Ψ_S}=2, p_{Ψ_S}=2d`, and
with `Θ₀` replaced by its *proved upper bound*).

Two gaps are bridged, beyond the pure copy of the conclusion of `M0Threshold`:

1. **`Θ₀` actual vs. bound.** `homogBelowM0_threshold_corrected` is proved at
   `Θ₀ := (2C_env(d)+4C_env(d)²)ν⁻²L` (the proved upper bound,
   `ThetaLmThetaZero.lean`'s `homogBelow_thetaCutoff_zero_le`), not at the
   *actual* `Θ₀ = thetaCutoff nu L P 0` that the hypothesis from [AK, Theorem 6.1] needs.
   This is bridged via `homogBelowM0_monotone_in_Theta0` of `M0ThresholdB.lean`
   (the whole left side is monotone increasing in `Θ₀` once `Θ₀ ≥ 1`), fed
   the *actual* `1 ≤ Θ₀` from `homogBelow_one_le_thetaCutoff_zero` of
   `ThetaLmThetaZeroGe1.lean` (the bound `Θ_n ≥ 1`, needing only
   `0 < nu`, `ShellLawJ4`, and the (P2′) witness -- no `ShellLawPrefix`/`J2`/`J3`).
2. **Symbolic `D, H, KPsiS, pPsiS` vs. the paper's hardwired numerals.**
   `homogBelow_akhcApplication`'s conclusion keeps these as whatever witness
   the caller supplied to (P2′); they equal `1`, `8·Cellip·ν⁻²`, `2`,
   `2d` only because of how the proof of `homogBelow_P2prime_verified` constructs them,
   which is invisible to a caller who merely `obtain`s the existential.
   `ThetaLmP2Prime.lean` therefore carries three further equational conjuncts (`D = 1`,
   `KPsiS = gammaGrowthConst 1`, `pPsiS = 2 * (d:ℝ)`, alongside `H = 4·Cellip·γ⁻¹·ν^(-2)`)
   exposing exactly this, as it does for `4 * m2 ≤ L + 3`. A further
   small gap: `homogBelow_akhcApplication`'s `gammaGrowthConst (1/3) ^ (4*d^2)`
   elaborates with a **natural-number** exponent (`Monoid.npow`, since `d : ℕ`
   and no cast forces `Real.rpow`), while `M0ThresholdB.lean` is stated with
   the exponent explicitly cast to `ℝ` (`Real.rpow`); this is bridged by `hPowEq`
   below via `Real.rpow_natCast`.

Once these are in hand, the two sides differ only by pure field arithmetic
inside the (untouched, syntactically identical) `Real.log`/`Real.exp` atoms:
`ring` closes each piece once `congr`-adjacent atoms are isolated by `rw`, so no
new mathematics is needed beyond the wiring.

`homogBelow_bigLog_le_m0` is deliberately generic in `m0` (taking the M0Threshold
conclusion as a hypothesis `hM0`, not re-deriving it): it serves **both**
branches of the final assembly — `homogBelowM0_threshold_corrected` (`m ≤ L²`,
`m0 := ⌈Cprime·log²L⌉₊`) and `homogBelowM0_threshold_large_m` (`L² ≤ m`, `m0 := ⌈Cprime·log²m⌉₊`,
`Section4/HomogBelow/M0ThresholdC.lean`) — since both produce a proof of the
same `hM0` shape at their own `m0`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- **The big-log hypothesis, discharged.** Given the (P2′) witness (with its
`sc3`-added equational conjuncts pinning `D, KPsiS, pPsiS, H` to the paper's
concrete values) and a pre-specialized M0-threshold fact `hM0` (from either
`homogBelowM0_threshold_corrected` or `homogBelowM0_threshold_large_m`) at
the SAME `m0`, produces exactly `homogBelow_akhcApplication`'s own third
premise — the `∀ m m0, ... → [big-log] ≤ m0 → ...` hypothesis's middle
conjunct — ready for `exact`/application against `hStep`. -/
theorem homogBelow_bigLog_le_m0
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (L : ℕ) (hL1 : 1 ≤ L)
    (H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hH1 : 1 ≤ H) (hD0 : 0 ≤ D)
    (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSge1 : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hKPsiS1 : 1 ≤ KPsiS) (hpPsiS2 : 3 ≤ pPsiS)
    (hgrowthPsiS : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hexistsPsiS : ∀ j : ℕ, m2 ≤ j →
      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
          (Q : Homogenization.TriadicCube d), Q.scale ≤ (j : ℤ) →
          Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                    omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-((1/2 : ℝ) * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    (hD1 : D = 1)
    (hKPsiSeq : KPsiS = Homogenization.IndependentSums.gammaGrowthConst 1)
    (hpPsiSeq : pPsiS = 2 * (d : ℝ))
    (hHeq : H = 4 * homogBelow_Cellip d hd * (1/2 : ℝ)⁻¹ * nu ^ (-(2 : ℝ)))
    (C61 : ℝ) (hC61_1 : 1 ≤ C61)
    (Cmix : ℝ) (hCmix1 : 1 ≤ Cmix)
    (m0 m : ℕ)
    (hM0 :
      32 * C61 * (Cmix + 1) *
        Real.log
          ((C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
                  (6 * ((d : ℝ) + 1) ^ 2) +
              C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
                2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2))))) *
            ((m : ℝ) + (m0 : ℝ) + 1) *
            ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                  4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
              nu⁻¹ ^ 2 * (L : ℝ))) *
        Real.log
          (3 * ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                  4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^
                    2) *
              nu⁻¹ ^ 2 * (L : ℝ)) *
            (2 + 4 * Cmix *
              Real.log
                ((C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
                        (6 * ((d : ℝ) + 1) ^ 2) +
                    C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
                      2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2))))) *
                  ((m : ℝ) + (m0 : ℝ) + 1) *
                  ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                        4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^
                          2) *
                    nu⁻¹ ^ 2 * (L : ℝ))))) ≤
      (m0 : ℝ)) :
    C61 * ((4 * Cmix) + (1 + D) / (1 - (1/2 : ℝ))) * (1 + D) / ((1 - (1/2 : ℝ)) * (1 - (1/2 : ℝ))) *
        Real.log
          ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) /
                (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) +
              C61 / (min 3 pPsiS - 2) *
                Real.exp (C61 * (((4 * Cmix) + D / (1 - (1/2 : ℝ))) * Real.log (2 * nu⁻¹) +
                  (D + Real.log (H + KPsiS)) / (1 - (1/2 : ℝ))))) *
            ((m : ℝ) + (m0 : ℝ) + 1) *
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) *
        Real.log (3 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 *
          (2 + (4 * Cmix) * Real.log
          ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) /
                (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) +
              C61 / (min 3 pPsiS - 2) *
                Real.exp (C61 * (((4 * Cmix) + D / (1 - (1/2 : ℝ))) * Real.log (2 * nu⁻¹) +
                  (D + Real.log (H + KPsiS)) / (1 - (1/2 : ℝ))))) *
            ((m : ℝ) + (m0 : ℝ) + 1) *
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0))) ≤
      (m0 : ℝ) := by
  -- Item (2): the actual Θ₀ is ≥ 1.
  have hTheta1 : (1 : ℝ) ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 :=
    homogBelow_one_le_thetaCutoff_zero hnu hJ4 (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
      hH1 hD0 hPsiSMono hPsiSge1 hKPsiS1 (lt_of_lt_of_le (by norm_num) hpPsiS2) hgrowthPsiS hexistsPsiS
  -- The proved upper bound on Θ₀.
  have hThetaLe : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 ≤
      (2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
          4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
        nu⁻¹ ^ 2 * (L : ℝ) :=
    homogBelow_thetaCutoff_zero_le hnu hnu1 hPrefix hJ2 hJ3 hJ4 L hL1
  -- The `nu ^ (-(2:ℝ)) = nu⁻¹ ^ 2` bridge.
  have hnuRpow2 : nu ^ (-(2 : ℝ)) = nu⁻¹ ^ 2 := by
    have h1 : nu ^ (-(2 : ℝ)) = (nu ^ (2 : ℝ))⁻¹ := Real.rpow_neg hnu.le 2
    have h2 : nu ^ (2 : ℝ) = nu ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h1, h2, inv_pow]
  -- `H + KPsiS = 8 Cellip nu⁻¹² + 2`.
  have hHK : H + KPsiS = 8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2 := by
    rw [hHeq, hKPsiSeq, homogBelow_gammaGrowthConst_one, hnuRpow2]
    ring
  -- `min ((d:ℝ)+1) ((d:ℝ)+1) - d = 1`.
  have hminSelf : min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ) = 1 := by
    rw [min_self]; ring
  -- `min 3 pPsiS - 2 = 1`.
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmin3 : min (3 : ℝ) pPsiS - 2 = 1 := by
    rw [hpPsiSeq, min_eq_left (by linarith only [hd2] : (3 : ℝ) ≤ 2 * (d : ℝ))]
    norm_num
  subst hD1
  rw [hminSelf, hmin3, hHK]
  -- Bring the prefactor and the "Ups1+U2" inner content to the exact numeral-reduced
  -- form `homogBelowM0_threshold_corrected` was proved at.
  have hPREFeq : C61 * ((4 * Cmix) + (1 + (1:ℝ)) / (1 - (1/2 : ℝ))) * (1 + (1:ℝ)) /
      ((1 - (1/2 : ℝ)) * (1 - (1/2 : ℝ))) = 32 * C61 * (Cmix + 1) := by ring
  have hexpArgEq : C61 * (((4 * Cmix) + (1:ℝ) / (1 - (1/2 : ℝ))) * Real.log (2 * nu⁻¹) +
      ((1:ℝ) + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)) / (1 - (1/2 : ℝ))) =
      C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2))) := by ring
  -- Bridge the natural-number power (as elaborated in the goal derived from
  -- [AK, Theorem 6.1]) to the real `rpow` power `M0ThresholdB.lean` is stated with.
  have hexpcast : ((6 * (d + 1) ^ 2 : ℕ) : ℝ) = 6 * ((d : ℝ) + 1) ^ 2 := by push_cast; ring
  have hPowEq :
      (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) =
      (Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3)) ^ (6 * ((d : ℝ) + 1) ^ 2) := by
    rw [← Real.rpow_natCast (Homogenization.IndependentSums.gammaGrowthConst (1/3)) (6 * (d + 1) ^ 2),
      hexpcast]
  have hINNEReq :
      C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) / 1 +
        C61 / 1 * Real.exp (C61 * (((4 * Cmix) + (1:ℝ) / (1 - (1/2 : ℝ))) * Real.log (2 * nu⁻¹) +
          ((1:ℝ) + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)) / (1 - (1/2 : ℝ)))) =
      C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3)) ^ (6 * ((d : ℝ) + 1) ^ 2) +
        C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
          2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)))) := by
    rw [hexpArgEq, hPowEq]; ring
  rw [hPREFeq, hINNEReq]
  set ThetaA : ℝ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 with hThetaAdef
  set ThetaB : ℝ :=
    (2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
        4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
      nu⁻¹ ^ 2 * (L : ℝ) with hThetaBdef
  set Ups12 : ℝ :=
    C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3)) ^ (6 * ((d : ℝ) + 1) ^ 2) +
      C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)))) with
    hUps12def
  set mm0 : ℝ := (m : ℝ) + (m0 : ℝ) + 1 with hmm0def
  have hUps12ge1 : (1 : ℝ) ≤ Ups12 := by
    have hgg1 : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3) :=
      le_trans one_le_two (Homogenization.IndependentSums.two_le_gammaGrowthConst _)
    have hpow1 : (1 : ℝ) ≤
        (Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3)) ^ (6 * ((d : ℝ) + 1) ^ 2) :=
      Real.one_le_rpow hgg1 (by positivity)
    have hUps1ge1 : (1 : ℝ) ≤
        C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3)) ^ (6 * ((d : ℝ) + 1) ^ 2) := by
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1:ℝ)/3)) ^ (6 * ((d : ℝ) + 1) ^ 2) :=
          mul_le_mul hC61_1 hpow1 zero_le_one (by linarith only [hC61_1])
    have hU2nonneg : (0 : ℝ) ≤
        C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
          2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)))) := by
      positivity
    linarith only [hUps1ge1, hU2nonneg]
  have hmm0ge1 : (1 : ℝ) ≤ mm0 := by
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm0nn : (0 : ℝ) ≤ (m0 : ℝ) := Nat.cast_nonneg _
    rw [hmm0def]; linarith only [hmnn, hm0nn]
  have hmono := homogBelowM0_monotone_in_Theta0
    (C61 := C61) (Cmix := Cmix) (Ups12 := Ups12) (mm0 := mm0) (Theta0 := ThetaA)
    (Theta0' := ThetaB) hC61_1 hCmix1 hUps12ge1 hmm0ge1 hTheta1 hThetaLe
  exact le_trans hmono hM0

end SuperdiffusionCLT.Section4.HomogBelow
