/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.LogCompare
public import SuperdiffusionCLT.Section4.LNaught.SstarLowerB
public import SuperdiffusionCLT.Section4.LNaught.Monotone

/-!
Stage 4 (task `sc2`), fourth piece: **collects the four `lNaught`-threshold
facts `homogBelow_akhcApplication` needs** (`hLabsorbApplied`, `hSstarApplied`,
`hLogLeNApplied`, `hLogRatioApplied`, exactly `ThetaLmP3Prime.lean`'s own
input shapes) from the single hypothesis `hThetaLm`'s target itself supplies:
`lNaught C (C*M) alpha cStar nu K ≤ L`.

`lNaught_absorbs`, `lNaught_log_le_n Cmix`, `lNaught_log_ratio` are each
applied at their own `M`-argument set to `C*M` (matching the given hypothesis
literally, no rescaling), then weakened from `C*M` down to `c*M` in the
conclusion using `c ≤ C` and nonnegativity (a *smaller* coefficient makes the
absorption bound, and the `n`-threshold in the other two, only easier to
satisfy). `lNaught_sstar_lower` is applied at `M`-argument `Cmix*M` (matching
`hSstarApplied`'s own amplitude `c*(Cmix*M)*...`), using monotonicity of
`lNaught` in its `M`-argument (`Cmix*M ≤ C*M` since `Cmix ≤ C`) to derive the
needed `L ≥ lNaught C (Cmix*M) ...` from the given `L ≥ lNaught C (C*M) ...`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- `Real.log` of a natural-number cast is always nonnegative: either the
cast is `0` (junk value `log 0 = 0`) or `1` (`log 1 = 0`) or `≥ 2` (positive
log), and no natural cast lies strictly between `0` and `1`. -/
private theorem homogBelow_log_natCast_nonneg (L : ℕ) : 0 ≤ Real.log (L : ℝ) := by
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · simp [hL0]
  · have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
    exact Real.log_nonneg hL1

/-- `M * L^alpha * log(L)^3 ≥ 0` for `M ≥ 0`, any `alpha`, any `L : ℕ`. -/
private theorem homogBelow_absorbAmplitude_nonneg {M alpha : ℝ} (hM : 0 ≤ M) (L : ℕ) :
    0 ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
  have h1 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg L) alpha
  have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
    Real.rpow_nonneg (homogBelow_log_natCast_nonneg L) 3
  have h3 : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha := mul_nonneg hM h1
  exact mul_nonneg h3 h2

/-- **The four threshold facts, collected.** -/
theorem homogBelow_thresholdHyps
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cmix : ℝ) (hCmix1 : 1 ≤ Cmix) :
    ∃ (c : ℝ) (C₀ : ℝ), 0 < c ∧ 1 ≤ C₀ ∧ Cmix ≤ C₀ ∧ c ≤ C₀ ∧
      ∀ C : ℝ, C₀ ≤ C →
      ∀ M alpha cStar nu K : ℝ, 1 ≤ M → 0 ≤ alpha → alpha < 1 →
        0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 → 0 ≤ K →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ L : ℕ, SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
        (c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2) ∧
        (∀ h : ℕ, (L : ℝ) ≤ 2 * (h : ℝ) → h ≤ L →
          c * (Cmix * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ)) ∧
        (∀ n : ℕ, (L : ℝ) - c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
          Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ (n : ℝ)) ∧
        (∀ n : ℕ, (L : ℝ) - c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
          Real.log (nu⁻¹ * (L : ℝ)) ≤ 2 * Real.log (nu⁻¹ * (n : ℝ))) := by
  obtain ⟨C0sstar, hC0sstar1, c, hcpos, hsstarBody⟩ :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower d hd
  obtain ⟨C0abs, hC0abs1, habsBody⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_absorbs
  obtain ⟨C0logn, hC0logn1, hlognBody⟩ :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_log_le_n Cmix hCmix1
  obtain ⟨C0ratio, hC0ratio1, hratioBody⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_log_ratio
  set C₀ : ℝ := max Cmix (max c (max C0sstar (max C0abs (max C0logn C0ratio)))) with hC0def
  have hC0_Cmix : Cmix ≤ C₀ := le_max_left _ _
  have hC0_rest : max c (max C0sstar (max C0abs (max C0logn C0ratio))) ≤ C₀ := le_max_right _ _
  have hC0_c : c ≤ C₀ := le_trans (le_max_left _ _) hC0_rest
  have hC0_sstar : C0sstar ≤ C₀ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC0_rest
  have hC0_abs : C0abs ≤ C₀ :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hC0_rest
  have hC0_logn : C0logn ≤ C₀ :=
    le_trans
      (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
        (le_max_right _ _)) hC0_rest
  have hC0_ratio : C0ratio ≤ C₀ :=
    le_trans
      (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
        (le_max_right _ _)) hC0_rest
  have hC01 : (1 : ℝ) ≤ C₀ := le_trans hCmix1 hC0_Cmix
  refine ⟨c, C₀, hcpos, hC01, hC0_Cmix, hC0_c, ?_⟩
  intro C hC M alpha cStar nu K hM1 halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
    P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hL
  have hCge1 : (1 : ℝ) ≤ C := le_trans hC01 hC
  have hCM_ge1 : (1 : ℝ) ≤ C * M := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C * M := mul_le_mul hCge1 hM1 (by norm_num) (by linarith only [hCge1])
  have hCmix_le_C : Cmix ≤ C := le_trans hC0_Cmix hC
  have hc_le_C : c ≤ C := le_trans hC0_c hC
  have hMnonneg : (0 : ℝ) ≤ M := by linarith only [hM1]
  have hAmpNonneg : 0 ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
    homogBelow_absorbAmplitude_nonneg hMnonneg L
  have hcM_le_CM : c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
      C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have hstep : c * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        C * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hc_le_C hAmpNonneg
    calc c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)
        = c * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
      _ ≤ C * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := hstep
      _ = C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- hLabsorbApplied
    have hAbs := habsBody C (le_trans hC0_abs hC) (C * M) hCM_ge1 alpha halpha0 halpha1 cStar
      hcStar hcStar2 nu hnu hnu1 K hK L hL
    linarith only [hcM_le_CM, hAbs]
  · -- hSstarApplied
    have hCmixM_le_CM : Cmix * M ≤ C * M := mul_le_mul_of_nonneg_right hCmix_le_C hMnonneg
    have hCmixM_ge1 : (1 : ℝ) ≤ Cmix * M := by
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ Cmix * M := mul_le_mul hCmix1 hM1 (by norm_num) (by linarith only [hCmix1])
    have hLCmixM : SuperdiffusionCLT.Frozen.Section4.lNaught C (Cmix * M) alpha cStar nu K ≤
        (L : ℝ) :=
      le_trans
        (SuperdiffusionCLT.Section4.LNaught.lNaught_mono_M
          (by linarith only [hCge1]) (by linarith only [hCmixM_ge1]) hCmixM_le_CM hK hcStar hnu
          halpha1)
        hL
    intro h hLh hhL
    have hS := hsstarBody C (le_trans hC0_sstar hC) (Cmix * M) hCmixM_ge1 alpha halpha0 halpha1
      cStar hcStar hcStar2 nu hnu hnu1 K hK P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hLCmixM h hLh hhL
    have heqpow : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ) =
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [heqpow]
    exact hS
  · -- hLogLeNApplied
    intro n hn
    have hLogLeN := hlognBody C (le_trans hC0_logn hC) (C * M) hCM_ge1 alpha halpha0 halpha1
      cStar hcStar hcStar2 nu hnu hnu1 K hK L hL n (by linarith only [hn, hcM_le_CM])
    exact hLogLeN
  · -- hLogRatioApplied
    intro n hn
    exact hratioBody C (le_trans hC0_ratio hC) (C * M) hCM_ge1 alpha halpha0 halpha1 cStar
      hcStar hcStar2 nu hnu hnu1 K hK L hL n (by linarith only [hn, hcM_le_CM])

end SuperdiffusionCLT.Section4.HomogBelow
