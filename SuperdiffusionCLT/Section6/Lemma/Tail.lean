/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.RootClosure
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section6.Lemma.KBounds
public import SuperdiffusionCLT.Section6.Prereq.GammaMax

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# Tail of the sharp scale inputs

The random minimal scale `X₀ := max X_E K_ρ` of `l.sharp.scale.inputs`, where `X_E` is the scale of
`Frozen.Section4.minimal_scales` at `(ρ/2, δ, 1/9, M)` and `K_ρ` is the scale of
`kBounds_exists`. The explicit threshold is `L̂ = max 1 (c (A + B))`.
-/

namespace SuperdiffusionCLT.Section6

open MeasureTheory

/-- The window `m - ⌈M log m⌉ ≤ n` (integers) implies the natural-number window of
`minimal_scales` at `s = 1/9`, as soon as `1 ≤ C`. -/
theorem l2_window_nat {C M : ℝ} (hC : 1 ≤ C) (hM : 1 ≤ M) {m n : ℕ}
    (h : (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ)) :
    m - ⌈C * M * ((1 / 9 : ℝ))⁻¹ * Real.log (m : ℝ)⌉₊ ≤ n := by
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hM0 : 0 ≤ M := by linarith only [hM]
  have h1 : M * Real.log (m : ℝ) ≤ C * M * ((1 / 9 : ℝ))⁻¹ * Real.log (m : ℝ) := by
    have h9 : ((1 / 9 : ℝ))⁻¹ = 9 := by norm_num
    rw [h9]
    have hCM : M ≤ C * M := le_mul_of_one_le_left hM0 hC
    have : M ≤ C * M * 9 := by linarith only [hCM, hM0]
    exact mul_le_mul_of_nonneg_right this hlog
  have h2 : ⌈M * Real.log (m : ℝ)⌉ ≤ ((⌈C * M * ((1 / 9 : ℝ))⁻¹ * Real.log (m : ℝ)⌉₊ : ℕ) : ℤ) := by
    have hnn : 0 ≤ C * M * ((1 / 9 : ℝ))⁻¹ * Real.log (m : ℝ) := by
      have : (0 : ℝ) ≤ C := by linarith only [hC]
      positivity
    rw [Int.natCast_ceil_eq_ceil hnn]
    exact Int.ceil_le_ceil h1
  omega

/-- **Tail of `l.sharp.scale.inputs`.** `C` is the constant of `minimal_scales`; `δ` is the
homogenization-error parameter of the full-field bullet (the caller takes `δ = c₁ ε`). The
threshold `L̂` is independent of the law. -/
theorem l2_tail (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∀ ρ M delta : ℝ, 0 < ρ → ρ < 1 → C ≤ M → 0 < delta → delta ≤ 1 →
              ∃ Lhat : ℝ, 1 ≤ Lhat ∧
                ∀ (P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                      hPrefix hJ2 hJ3 →
                  ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma ρ)
                      (fun omega => Real.log (X0 omega)) Lhat ∧
                    (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ m n : ℕ,
                        X0 omega ≤ (3 : ℝ) ^ m →
                        Lhat ≤ (m : ℝ) →
                        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
                        n ≤ m →
                        ∀ k : Fin d → ℤ,
                          (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                              Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                            Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) (1 / 9)
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x => nu • (1 : Homogenization.Mat d) +
                                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                                (1 : Homogenization.Mat d)) ≤
                            delta *
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                                  P)⁻¹ *
                              (m : ℝ) ^ (ρ / 2) * Real.log (m : ℝ)) ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ m : ℕ, X0 omega ≤ (3 : ℝ) ^ m →
                        ENNReal.ofReal ((m : ℝ)⁻¹) *
                            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                              (Homogenization.originCube d (m : ℤ)) ∞
                              (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
                          ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
                            SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                              (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
                              (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
                          ENNReal.ofReal ((m : ℝ) ^ ρ) := by
  obtain ⟨C, hC1, hms⟩ := SuperdiffusionCLT.Section4.MinimalScales.minimal_scales_closed d hd
  refine ⟨C, hC1, fun nu hnu hnu1 cStar hcS Knd ρ M delta hρ hρ1 hCM hδ hδ1 => ?_⟩
  obtain ⟨Cρ, hKB⟩ := kBounds_exists d ρ hρ
  have hM1 : 1 ≤ M := le_trans hC1 hCM
  set A : ℝ := max 0 (max
    (SuperdiffusionCLT.Frozen.Section4.lNaught C
      (C * (ρ / 2)⁻¹ * delta ^ (-(2 : ℝ)) * (1 / 9 : ℝ) ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
      (1 - ρ / 2) cStar nu Knd)
    (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * (1 / 9 : ℝ) ^ (-(2 : ℝ)))
      (1 / 2 + ρ / 2) cStar nu Knd)) with hA
  set B : ℝ := max 0 Cρ with hB
  set c : ℝ := (3 * Real.log (2 : ℝ)) ^ ρ⁻¹ with hc
  have hlog2 : (1 : ℝ) < 3 * Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have hc1 : 1 ≤ c := Real.one_le_rpow hlog2.le (inv_nonneg.2 hρ.le)
  have hA0 : 0 ≤ A := le_max_left _ _
  have hB0 : 0 ≤ B := le_max_left _ _
  refine ⟨max 1 (c * (A + B)), le_max_left _ _, fun P hPre hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨Kr, hKm, hK27, hKO, hKae⟩ := hKB P hPre hJ1 hJ2 hJ3 hJ4
  obtain ⟨XE, hXm, hXO, hXae⟩ := hms nu cStar Knd hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5
    (ρ / 2) delta (1 / 9) M (by positivity) (by linarith only [hρ1]) hδ hδ1
    (by norm_num) (by norm_num) hM1
  rw [show 2 * (ρ / 2) = ρ by ring] at hXO
  have hXA := hXO.mono_scale (le_max_right 0 _)
  have hKO' : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (Kr omega)) Cρ :=
    Homogenization.Book.Ch04.IsBigO.gammaSigma_mono_exponent (by linarith only [hρ]) hKO
  have hKB' := hKO'.mono_scale (le_max_right 0 Cρ)
  have hmax := isBigO_gammaSigma_max_two_add hρ hA0 hB0 hXA hKB'
  have hLA : A ≤ c * (A + B) := by
    have h1 : A ≤ A + B := by linarith only [hB0]
    have h2 : 0 ≤ A + B := by linarith only [hA0, hB0]
    have h3 : A + B ≤ c * (A + B) := le_mul_of_one_le_left h2 hc1
    linarith only [h1, h3]
  have hX1 : ∀ omega, 1 ≤ max (XE omega) (Kr omega) := fun omega =>
    le_trans (by norm_num) (le_trans (hK27 omega) (le_max_right _ _))
  refine ⟨fun omega => max (XE omega) (Kr omega), hXm.max hKm, hX1, ?_, ?_, ?_⟩
  · refine Homogenization.IndependentSums.IsBigO.of_abs_le
      (hmax.mono_scale (le_max_right 1 _)) fun omega => ?_
    have h0 : 0 ≤ Real.log (max (XE omega) (Kr omega)) := Real.log_nonneg (hX1 omega)
    have h1 : Real.log (max (XE omega) (Kr omega)) ≤
        max (Real.log (XE omega)) (Real.log (Kr omega)) := by
      rcases max_choice (XE omega) (Kr omega) with h | h
      · rw [h]; exact le_max_left _ _
      · rw [h]; exact le_max_right _ _
    rw [abs_of_nonneg h0, abs_of_nonneg (le_trans h0 h1)]
    exact h1
  · filter_upwards [hXae] with omega h m n hX0 hL hw hnm k himg
    have hXE : XE omega ≤ (3 : ℝ) ^ m := le_trans (le_max_left _ _) hX0
    have hAm : A ≤ (m : ℝ) :=
      le_trans hLA (le_trans (le_max_right 1 _) hL)
    have hmaxm : max
        (SuperdiffusionCLT.Frozen.Section4.lNaught C
          (C * (ρ / 2)⁻¹ * delta ^ (-(2 : ℝ)) * (1 / 9 : ℝ) ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
          (1 - ρ / 2) cStar nu Knd)
        (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * (1 / 9 : ℝ) ^ (-(2 : ℝ)))
          (1 / 2 + ρ / 2) cStar nu Knd) ≤ (m : ℝ) :=
      le_trans (le_max_right 0 _) hAm
    exact (h m n hmaxm hXE (l2_window_nat hC1 hM1 hw) hnm).2 k himg
  · filter_upwards [hKae] with omega h m hm
    exact h m (le_trans (le_max_right _ _) hm)

/-- Satisfiability of the non-law hypotheses of `l2_tail` (`ν = 1`, `c⋆ = 1`, `ρ = 1/2`, `M = C`,
`δ = 1`). -/
example (C : ℝ) (hC : 1 ≤ C) :
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ C ≤ C ∧
      (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ 1 ≤ C :=
  ⟨one_pos, le_rfl, one_pos, by norm_num, by norm_num, le_rfl, one_pos, le_rfl, hC⟩

end SuperdiffusionCLT.Section6
