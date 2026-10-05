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
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open scoped ENNReal

/-!
# The full-field homogenization error on the good event

The `full.good` bullet of `l.sharp.scale.inputs`: on the event `X ≤ 3^m`, with `X` the minimal
scale of `Frozen.Section4.minimal_scales` at `(ρ/2, c₁ε, 1/9, M/(9C))`, the homogenization
error `𝓔_{1/9,∞,2}` of the full centered field on every cube of the window is at most
`ε m^{-(1-ρ)/2} log m`. The route is conjunct 2 of `minimal_scales`, the window comparison and the
absorption of the factor `σ̄_m⁻¹ m^{ρ/2}` by the lower bound `σ̄_m ≥ ½ (2 c⋆ log 3 · m)^{1/2}`,
which is read off the Section 5 sharp bounds (taken as the hypothesis `hS5`).
-/

namespace SuperdiffusionCLT.Section6

/-- Beyond a threshold the Section 5 error `A (log² m + K)` is at most half of `b √m`. -/
theorem l3_sigma_threshold (A K b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      A * (Real.log (m : ℝ) ^ (2 : ℝ) + K) ≤ b / 2 * Real.sqrt (m : ℝ) := by
  have hc : 0 < b / (4 * (A + 1)) := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).def hc
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 4 * A * |K| / b ≤ x ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop _
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (h1.and (h2.and h3))
  obtain ⟨N, hN⟩ := exists_nat_ge T
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨hx1, hx2, hx3⟩ := hT (m : ℝ) (hN.trans (by exact_mod_cast hm))
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hx3
  have hsq : Real.sqrt (m : ℝ) = (m : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsqnn : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hx3]) _), ← hsq] at hx1
  rw [← hsq] at hx2
  have hA1 : A * (b / (4 * (A + 1))) ≤ b / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ b := hb.le
    have h4 : 0 ≤ b * A := mul_nonneg this hA
    linarith only [h4, hb]
  have hK : A * K ≤ b / 4 * Real.sqrt (m : ℝ) := by
    have h5 : A * |K| ≤ b / 4 * Real.sqrt (m : ℝ) := by
      have h6 : 4 * A * |K| ≤ b * Real.sqrt (m : ℝ) := by
        have := (div_le_iff₀ hb).mp hx2
        linarith only [this, mul_comm b (Real.sqrt (m : ℝ))]
      linarith only [h6]
    exact (mul_le_mul_of_nonneg_left (le_abs_self K) hA).trans h5
  have hL : A * Real.log (m : ℝ) ^ (2 : ℝ) ≤ b / 4 * Real.sqrt (m : ℝ) := by
    have h7 := mul_le_mul_of_nonneg_left hx1 hA
    have h8 := mul_le_mul_of_nonneg_right hA1 hsqnn
    linarith only [h7, h8, mul_assoc A (b / (4 * (A + 1))) (Real.sqrt (m : ℝ))]
  linarith only [hK, hL, mul_add A (Real.log (m : ℝ) ^ (2 : ℝ)) K]

/-- The square root of the leading term of the Section 5 bound factors as `b √m`. -/
theorem l3_lead_eq (cStar : ℝ) (hc : 0 < cStar) (m : ℕ) :
    (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) =
      Real.sqrt (2 * cStar * Real.log 3) * Real.sqrt (m : ℝ) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity)]

/-- Lower bound for `σ̄` from the two-sided Section 5 estimate. -/
theorem l3_sigma_lower {σ lead err : ℝ} (h : |σ - lead| ≤ err) (herr : err ≤ lead / 2) :
    lead / 2 ≤ σ := by
  have := (abs_le.mp h).1
  linarith only [this, herr]

/-- The absorption step: the factor `σ̄⁻¹ m^{ρ/2}` against `m^{-(1-ρ)/2}`. -/
theorem l3_absorb {b ε ρ σ m : ℝ} (hb : 0 < b) (hε : 0 ≤ ε) (hm : 1 ≤ m)
    (hσ : b / 2 * Real.sqrt m ≤ σ) :
    (min 1 (b / 2) * ε) * σ⁻¹ * m ^ (ρ / 2) * Real.log m ≤
      ε * m ^ (-((1 - ρ) / 2)) * Real.log m := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hb2 : 0 < b / 2 * Real.sqrt m := by positivity
  have hσinv : σ⁻¹ ≤ (b / 2 * Real.sqrt m)⁻¹ := inv_anti₀ hb2 hσ
  have hmin : min 1 (b / 2) ≤ b / 2 := min_le_right _ _
  have h1 : (min 1 (b / 2) * ε) * σ⁻¹ ≤ ε * (Real.sqrt m)⁻¹ := by
    have hpos : 0 < min 1 (b / 2) := lt_min one_pos (by positivity)
    calc (min 1 (b / 2) * ε) * σ⁻¹ ≤ (b / 2 * ε) * (b / 2 * Real.sqrt m)⁻¹ := by
          apply mul_le_mul _ hσinv (inv_nonneg.mpr (hb2.trans_le hσ).le) (by positivity)
          exact mul_le_mul_of_nonneg_right hmin hε
      _ = ε * (Real.sqrt m)⁻¹ := by field_simp
  have h2 : ε * (Real.sqrt m)⁻¹ * m ^ (ρ / 2) = ε * m ^ (-((1 - ρ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hm0.le, mul_assoc, ← Real.rpow_add hm0]
    congr 2
    ring
  have h3 : 0 ≤ m ^ (ρ / 2) := Real.rpow_nonneg hm0.le _
  calc (min 1 (b / 2) * ε) * σ⁻¹ * m ^ (ρ / 2) * Real.log m
      ≤ ε * (Real.sqrt m)⁻¹ * m ^ (ρ / 2) * Real.log m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h3) hlog
    _ = ε * m ^ (-((1 - ρ) / 2)) * Real.log m := by rw [h2]

/-- **`full.good` of `l.sharp.scale.inputs`.** Hypothesis `hS5`: the statement of
`Frozen.Section5.sigmaBar_sharp_bounds`. Conclusion: the shape of the sharp-scale inputs, with
the single bullet `e.Dir.new.full.good` on the event `X ≤ 3^m`, where `X` is the minimal scale of
`Frozen.Section4.minimal_scales` and `log X = O_{Γ_ρ}(L̂)`. -/
theorem full_good_exists (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hS5 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ M : ℕ,
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                  ∀ m : ℕ, M ≤ m →
                    |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
                        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                      C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
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
                  ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma ρ)
                      (fun omega => Real.log (X omega)) Lhat ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ m n : ℕ,
                        X omega ≤ (3 : ℝ) ^ m →
                        Lhat ≤ (m : ℝ) →
                        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
                        n ≤ m →
                        (∀ k : Fin d → ℤ,
                          (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                              Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                            Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                          -- e.Dir.new.full.good
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) (1 / 9)
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite 2)
                              (fun x => nu • (1 : Homogenization.Mat d) +
                                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                                (1 : Homogenization.Mat d)) ≤
                            ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) := by
  obtain ⟨Cms, hCms1, hMS⟩ := SuperdiffusionCLT.Section4.MinimalScales.minimal_scales_closed d hd
  obtain ⟨C5, hC51, hS5'⟩ := hS5
  refine ⟨9 * Cms, by linarith only [hCms1], ?_⟩
  intro nu hnu0 hnu1 cStar hc K ε ρ M hε0 hε1 hρ0 hρ1 hM
  obtain ⟨N5, hN5⟩ := hS5' nu hnu0 hnu1 cStar hc K
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCpos : 0 < Cms := lt_of_lt_of_le one_pos hCms1
  have hb : 0 < Real.sqrt (2 * cStar * Real.log 3) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨Nabs, hNabs⟩ := l3_sigma_threshold (C5 * cStar⁻¹) K
    (Real.sqrt (2 * cStar * Real.log 3)) (by positivity) hb
  have hdelta0 : 0 < min 1 (Real.sqrt (2 * cStar * Real.log 3) / 2) * ε :=
    mul_pos (lt_min one_pos (by positivity)) hε0
  have hdelta1 : min 1 (Real.sqrt (2 * cStar * Real.log 3) / 2) * ε ≤ 1 :=
    (mul_le_mul (min_le_left _ _) hε1 hε0.le zero_le_one).trans (by norm_num)
  have hMms : 1 ≤ M / (9 * Cms) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hM]
  let L1 : ℝ := SuperdiffusionCLT.Frozen.Section4.lNaught Cms
    (Cms * (ρ / 2)⁻¹ * (min 1 (Real.sqrt (2 * cStar * Real.log 3) / 2) * ε) ^ (-(2 : ℝ)) *
      (1 / 9 : ℝ) ^ (-(4 : ℝ)) * (M / (9 * Cms)) ^ (2 : ℝ)) (1 - ρ / 2) cStar nu K
  let L2 : ℝ := SuperdiffusionCLT.Frozen.Section4.lNaught Cms
    (Cms * (M / (9 * Cms)) * (1 / 9 : ℝ) ^ (-(2 : ℝ))) (1 / 2 + ρ / 2) cStar nu K
  have hLhat : max L1 L2 ≤ max 1 (max (max L1 L2) (max (N5 : ℝ) (Nabs : ℝ))) :=
    (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨max 1 (max (max L1 L2) (max (N5 : ℝ) (Nabs : ℝ))), le_max_left _ _, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X, hXm, hXO, hXae⟩ := hMS nu cStar K hnu0 hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
    (ρ / 2) (min 1 (Real.sqrt (2 * cStar * Real.log 3) / 2) * ε) (1 / 9) (M / (9 * Cms))
    (by linarith only [hρ0]) (by linarith only [hρ1]) hdelta0 hdelta1 (by norm_num)
    (by norm_num) hMms
  refine ⟨X, hXm, ?_, ?_⟩
  · have h2 : 2 * (ρ / 2) = ρ := by ring
    rw [h2] at hXO
    exact hXO.mono_scale hLhat
  · filter_upwards [hXae] with omega hω
    intro m n hX hL hwin hnm k hk
    have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_left _ _) hL
    have hmax : max L1 L2 ≤ (m : ℝ) := le_trans hLhat hL
    have hN5r : (N5 : ℝ) ≤ m :=
      le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hL
    have hNar : (Nabs : ℝ) ≤ m :=
      le_trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hL
    have hN5m : N5 ≤ m := by exact_mod_cast hN5r
    have hNam : Nabs ≤ m := by exact_mod_cast hNar
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    have hMnn : 0 ≤ M * Real.log (m : ℝ) :=
      mul_nonneg (by linarith only [hM, hCpos, hCms1]) hlog
    have hcm : Cms * (M / (9 * Cms)) * ((1 : ℝ) / 9)⁻¹ * Real.log (m : ℝ) =
        M * Real.log (m : ℝ) := by
      field_simp
    have hceil := Int.natCast_ceil_eq_ceil hMnn
    have hwin' : m - ⌈Cms * (M / (9 * Cms)) * ((1 : ℝ) / 9)⁻¹ * Real.log (m : ℝ)⌉₊ ≤ n := by
      rw [hcm]
      omega
    obtain ⟨-, hB⟩ := hω m n hmax hX hwin' hnm
    refine (hB k hk).trans ?_
    have hS := hN5 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m hN5m
    rw [l3_lead_eq cStar hc m] at hS
    have herr := hNabs m hNam
    have hlow := l3_sigma_lower hS (by linarith only [herr])
    exact l3_absorb hb hε0.le hm1 (by linarith only [hlow])

end SuperdiffusionCLT.Section6
