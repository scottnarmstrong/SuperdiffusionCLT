/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Process.Kernel.ResolventTailMoments

/-!
# The layer cake for a pointwise displacement tail

The fourth displacement moment of a measure of mass at most one is bounded by the layer-cake
integral of its tail in the variable rescaled by a length `c`.  Below a threshold `a` the tail is
bounded by one, above it by a profile `psi` with a finite cubic budget.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace SuperdiffusionCLT.Section8

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The fourth moment from a rescaled tail.**  A measure of mass at most one whose rescaled
displacement tail is at most one up to the threshold `a` and at most `psi` beyond it, with
cubic budget `J`, has fourth displacement moment at most `c ^ 4 * (a ^ 4 + 4 * J)`. -/
theorem crudeMom_lintegral_edist_pow_le {nu : Measure X} (hnu : nu Set.univ ≤ 1) (x : X)
    {c : ℝ} (hc : 0 < c) {a J : ℝ} (ha : 0 ≤ a) (hJ : 0 ≤ J) {psi : ℝ → ℝ}
    (hpsi : ∀ s, 0 ≤ psi s)
    (hlevel : ∀ s : ℝ, a < s → nu {z | s < dist z x / c} ≤ ENNReal.ofReal (psi s))
    (hint : ∫⁻ s in Set.Ioi a, ENNReal.ofReal (psi s * s ^ 3) ≤ ENNReal.ofReal J) :
    ∫⁻ z, edist z x ^ (4 : ℝ) ∂nu ≤ ENNReal.ofReal (c ^ 4 * (a ^ 4 + 4 * J)) := by
  have hdistmeas : Measurable fun z : X ↦ dist z x / c :=
    (measurable_dist.comp (measurable_id.prodMk measurable_const)).div_const _
  have hrescale : ∀ z : X, dist z x ^ (4 : ℝ) = c ^ (4 : ℝ) * (dist z x / c) ^ (4 : ℝ) := by
    intro z
    rw [← Real.mul_rpow hc.le (by positivity), mul_div_cancel₀ _ hc.ne']
  have hcake : ∫⁻ z, edist z x ^ (4 : ℝ) ∂nu =
      ENNReal.ofReal (c ^ (4 : ℝ)) *
        (ENNReal.ofReal 4 * ∫⁻ s in Set.Ioi (0 : ℝ),
          nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ ((4 : ℝ) - 1))) := by
    rw [show (∫⁻ z, edist z x ^ (4 : ℝ) ∂nu) =
        ∫⁻ z, ENNReal.ofReal (c ^ (4 : ℝ)) *
          ENNReal.ofReal ((dist z x / c) ^ (4 : ℝ)) ∂nu by
      refine lintegral_congr fun z ↦ ?_
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), hrescale z,
        ENNReal.ofReal_mul (Real.rpow_nonneg hc.le 4)]]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_rpow_eq_lintegral_meas_lt_mul nu
      (Eventually.of_forall fun z ↦ by positivity) hdistmeas.aemeasurable (by norm_num)
  have ha4 : (0 : ℝ) ≤ a ^ 4 / 4 := by positivity
  have hexp3 : ∀ s : ℝ, s ^ ((4 : ℝ) - 1) = s ^ (3 : ℕ) := by
    intro s
    rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hc4 : c ^ (4 : ℝ) = c ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro s hs hs'
    exact absurd hs.2 (not_le.mpr hs')
  have hbound : ∫⁻ s in Set.Ioi (0 : ℝ),
      nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ ((4 : ℝ) - 1)) ≤
      ENNReal.ofReal (a ^ 4 / 4) + ENNReal.ofReal J := by
    simp only [hexp3]
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha, lintegral_union measurableSet_Ioi hdisj]
    refine add_le_add ?_ ?_
    · calc ∫⁻ s in Set.Ioc (0 : ℝ) a,
            nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
          ≤ ∫⁻ s in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (s ^ (3 : ℕ)) := by
            refine setLIntegral_mono' measurableSet_Ioc fun s _ ↦ ?_
            calc nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
                ≤ 1 * ENNReal.ofReal (s ^ (3 : ℕ)) := by
                  gcongr
                  exact (measure_mono (Set.subset_univ _)).trans hnu
              _ = ENNReal.ofReal (s ^ (3 : ℕ)) := one_mul _
        _ = ENNReal.ofReal (a ^ 4 / 4) :=
            SuperdiffusionCLT.Section8.Process.lintegral_Ioc_ofReal_cube ha
    · calc ∫⁻ s in Set.Ioi a, nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
          ≤ ∫⁻ s in Set.Ioi a, ENNReal.ofReal (psi s * s ^ (3 : ℕ)) := by
            refine setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ?_
            have hs0 : 0 < s := lt_of_le_of_lt ha hs
            calc nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ (3 : ℕ))
                ≤ ENNReal.ofReal (psi s) * ENNReal.ofReal (s ^ (3 : ℕ)) := by
                  gcongr
                  exact hlevel s hs
              _ = ENNReal.ofReal (psi s * s ^ (3 : ℕ)) := by
                  rw [← ENNReal.ofReal_mul (hpsi s)]
        _ ≤ ENNReal.ofReal J := hint
  rw [hcake, hc4]
  calc ENNReal.ofReal (c ^ 4) *
        (ENNReal.ofReal 4 * ∫⁻ s in Set.Ioi (0 : ℝ),
          nu {z | s < dist z x / c} * ENNReal.ofReal (s ^ ((4 : ℝ) - 1)))
      ≤ ENNReal.ofReal (c ^ 4) * (ENNReal.ofReal 4 *
          (ENNReal.ofReal (a ^ 4 / 4) + ENNReal.ofReal J)) := by
        gcongr
    _ = ENNReal.ofReal (c ^ 4 * (a ^ 4 + 4 * J)) := by
        rw [← ENNReal.ofReal_add ha4 hJ,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end SuperdiffusionCLT.Section8

end
