/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmGrowthRate
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmLNaughtGeLinear

/-!
**The composed headroom fact.** Combines
`ThetaLmGrowthRate.lean`'s `homogBelow_logSq_le_rpow_logCube` and
`ThetaLmLNaughtGeLinear.lean`'s `homogBelow_lNaught_ge_linear` (following the
`C₀`-vs-`C_final` resolution described there) into the single fact Step 3's scale positivity
needs: `10m₀ + ⌈Cmix·log L⌉ + 1 ≤ M·L^α·log³L`, where `m₀ := ⌈C₀·log²L⌉₊`
uses `M0ThresholdB`'s *own* minimal threshold `C₀` (fixed first, depending
only on `C₆₁,Cmix,Cellip,d`), **not** the combined outer constant — the
outer constant `C` only needs to be past a threshold depending on `C₀,Cmix`
(chosen here, no circularity: `C₀` is a parameter of this lemma, fixed by
the caller before choosing `C`). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **The Step-3 headroom fact.** For any fixed `C₀ ≥ 1` (`m₀`'s own
coefficient) and `Cmix ≥ 1`, there is a threshold `C₁` such that once the
outer `lNaught`-constant `C` is `≥ C₁` and `L ≥ lNaught C (C·M) α c⋆ ν K`,
`10·⌈C₀·log²L⌉₊ + ⌈Cmix·log L⌉₊ + 1 ≤ M·L^α·log³L`. -/
theorem homogBelow_m0_headroom
    (C0 : ℝ) (hC0 : 1 ≤ C0) (Cmix : ℝ) (hCmix : 1 ≤ Cmix) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ C : ℝ, C1 ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∀ L : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
        10 * (⌈C0 * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + (⌈Cmix * Real.log (L : ℝ)⌉₊ : ℝ) + 1 ≤
          M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 := by
  obtain ⟨Clin, _hClin1, hlin⟩ := homogBelow_lNaught_ge_linear
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2pow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  set Cprime1 : ℝ := 10 * C0 + Cmix + 12 with hCprime1def
  have hCprime1nonneg : (0 : ℝ) ≤ Cprime1 := by rw [hCprime1def]; linarith only [hC0, hCmix]
  set Cthresh : ℝ := 4 * Real.exp Cprime1 / (Real.log 2) ^ (12 : ℝ) with hCthreshdef
  refine ⟨max 1 (max Clin Cthresh), le_max_left _ _, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK L hL
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hC
  have hCClin : Clin ≤ C :=
    le_trans (le_trans (le_max_left Clin Cthresh) (le_max_right 1 _)) hC
  have hCCthresh : Cthresh ≤ C :=
    le_trans (le_trans (le_max_right Clin Cthresh) (le_max_right 1 _)) hC
  have hCMge1 : (1 : ℝ) ≤ C * M := by nlinarith only [hC1, hM]
  have hlinapp :=
    hlin C hCClin (C * M) hCMge1 alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK
  have hLge : (Real.log 2) ^ (12 : ℝ) / 4 * C ≤ (L : ℝ) := le_trans hlinapp hL
  have hLgeExp : Real.exp Cprime1 ≤ (L : ℝ) := by
    have hstep : 4 * Real.exp Cprime1 ≤ (Real.log 2) ^ (12 : ℝ) * C := by
      rw [hCthreshdef, div_le_iff₀ hlog2pow_pos] at hCCthresh
      linarith only [hCCthresh]
    have hstep2 : Real.exp Cprime1 ≤ (Real.log 2) ^ (12 : ℝ) / 4 * C := by
      have heq : (Real.log 2) ^ (12 : ℝ) / 4 * C = (Real.log 2) ^ (12 : ℝ) * C / 4 := by ring
      rw [heq, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      linarith only [hstep]
    linarith only [hstep2, hLge]
  have hmaster := homogBelow_logSq_le_rpow_logCube
    (C1 := Cprime1) hCprime1nonneg hM halpha0 hLgeExp
  have hlogL_ge : Cprime1 ≤ Real.log (L : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos Cprime1) hLgeExp
    rwa [Real.log_exp] at h
  have hlogL_ge1 : (1 : ℝ) ≤ Real.log (L : ℝ) :=
    le_trans (by linarith only [hC0, hCmix] : (1 : ℝ) ≤ Cprime1) hlogL_ge
  have hlogsq_ge_log : Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by nlinarith only [hlogL_ge1]
  have hlogsq_ge1 : (1 : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by nlinarith only [hlogL_ge1]
  have hCmixbound : Cmix * Real.log (L : ℝ) + 12 ≤ (Cmix + 12) * Real.log (L : ℝ) ^ 2 := by
    have h1 : Cmix * Real.log (L : ℝ) ≤ Cmix * Real.log (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq_ge_log (by linarith only [hCmix])
    have h2 : (12 : ℝ) ≤ 12 * Real.log (L : ℝ) ^ 2 := by nlinarith only [hlogsq_ge1]
    nlinarith only [h1, h2]
  have hC0logsq_nonneg : (0 : ℝ) ≤ C0 * Real.log (L : ℝ) ^ 2 :=
    mul_nonneg (by linarith only [hC0]) (sq_nonneg _)
  have hCmixlog_nonneg : (0 : ℝ) ≤ Cmix * Real.log (L : ℝ) :=
    mul_nonneg (by linarith only [hCmix]) (by linarith only [hlogL_ge1])
  have hceil1 : (⌈C0 * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) ≤ C0 * Real.log (L : ℝ) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one hC0logsq_nonneg).le
  have hceil2 : (⌈Cmix * Real.log (L : ℝ)⌉₊ : ℝ) ≤ Cmix * Real.log (L : ℝ) + 1 :=
    (Nat.ceil_lt_add_one hCmixlog_nonneg).le
  calc 10 * (⌈C0 * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + (⌈Cmix * Real.log (L : ℝ)⌉₊ : ℝ) + 1
      ≤ 10 * (C0 * Real.log (L : ℝ) ^ 2 + 1) + (Cmix * Real.log (L : ℝ) + 1) + 1 := by
        linarith only [hceil1, hceil2]
    _ = 10 * C0 * Real.log (L : ℝ) ^ 2 + (Cmix * Real.log (L : ℝ) + 12) := by ring
    _ ≤ 10 * C0 * Real.log (L : ℝ) ^ 2 + (Cmix + 12) * Real.log (L : ℝ) ^ 2 := by
        linarith only [hCmixbound]
    _ = Cprime1 * Real.log (L : ℝ) ^ 2 := by rw [hCprime1def]; ring
    _ ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 := hmaster

end SuperdiffusionCLT.Section4.HomogBelow
