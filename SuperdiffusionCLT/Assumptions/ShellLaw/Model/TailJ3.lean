/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesF

/-!
# Sub-Gaussian tail of a weighted row sum of the noise

For iid standard Gaussians `ξ_p` and nonnegative summable weights `b_p` with `∑ b_p ≤ R`, the
series `S = ∑ |ξ_p| b_p` satisfies `P(S > τ) ≤ 2 exp (-τ² / (2 R²))` for every `τ ≥ 0`.

The proof uses Jensen's inequality with the weights `b_p / R`, which turns the exponential moment of
`S` into a convex combination of exponential moments of single coordinates, bounded by
`E exp (a |ξ|) ≤ 2 exp (a² / 2)`.  No independence is needed.

## Main results

* `nv_lintegral_exp_abs_gaussian`
* `nv_exp_sum_le`
* `nv_noiseLaw_tail_tsum`: the tail for the extended-real series
* `nv_noiseLaw_tail_rowSum`: the tail for `nv_rowSum`, uniformly in the cell
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory

noncomputable section

/-- The exponential moment of `|ξ|` for a standard Gaussian. -/
theorem nv_lintegral_exp_abs_gaussian (a : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (a * |y|)) ∂(gaussianReal 0 1)
      ≤ ENNReal.ofReal (2 * Real.exp (a ^ 2 / 2)) := by
  have hI : ∀ s : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (s * y)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (Real.exp (s ^ 2 / 2)) := by
    intro s
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
      (Filter.Eventually.of_forall fun y ↦ (Real.exp_pos _).le)]
    congr 1
    have h := congrFun (mgf_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))) s
    unfold mgf at h
    rw [h]
    norm_num
  have hm : ∀ s : ℝ, Measurable fun y : ℝ ↦ ENNReal.ofReal (Real.exp (s * y)) := fun s ↦
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (a * |y|)) ∂(gaussianReal 0 1)
      ≤ ∫⁻ y, (ENNReal.ofReal (Real.exp (a * y)) + ENNReal.ofReal (Real.exp ((-a) * y)))
          ∂(gaussianReal 0 1) := by
        refine lintegral_mono fun y ↦ ?_
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
          have := (Real.exp_pos ((-a) * y)).le
          linarith only [this]
        · rw [h]
          have := (Real.exp_pos (a * y)).le
          have e : (-a) * y = a * -y := by ring
          rw [e] at *
          linarith only [this]
    _ = ENNReal.ofReal (Real.exp (a ^ 2 / 2)) + ENNReal.ofReal (Real.exp (a ^ 2 / 2)) := by
        rw [lintegral_add_left (hm a), hI a, hI (-a), neg_sq]
    _ = ENNReal.ofReal (2 * Real.exp (a ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-- Finite Jensen with a defect: weights of total mass at most one. -/
theorem nv_jensen_defect {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ y : ι → ℝ)
    (hθ : ∀ i ∈ s, 0 ≤ θ i) (hs : ∑ i ∈ s, θ i ≤ 1) :
    Real.exp (∑ i ∈ s, θ i * y i)
      ≤ ∑ i ∈ s, θ i * Real.exp (y i) + (1 - ∑ i ∈ s, θ i) := by
  have h := convexOn_exp.map_sum_le (t := s.insertNone)
    (w := fun o : Option ι ↦ o.elim (1 - ∑ i ∈ s, θ i) θ) (p := fun o : Option ι ↦ o.elim 0 y)
    (by
      intro o ho
      cases o with
      | none => exact sub_nonneg.2 hs
      | some i => exact hθ i (by simpa using ho))
    (by
      rw [Finset.sum_insertNone]
      simp)
    (fun _ _ ↦ Set.mem_univ _)
  rw [Finset.sum_insertNone, Finset.sum_insertNone] at h
  simpa [smul_eq_mul, Real.exp_zero, add_comm, mul_comm] using h

theorem nv_lintegral_exp_coord (d : ℕ) (k : Fin d → ℤ) (p : NvFrame d) (a : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (Real.exp (a * |ξ (k, p)|)) ∂(nvNoiseLaw d)
      ≤ ENNReal.ofReal (2 * Real.exp (a ^ 2 / 2)) := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : NvIdx d ↦ gaussianReal 0 1) (k, p)
  have hm : Measurable fun y : ℝ ↦ ENNReal.ofReal (Real.exp (a * |y|)) :=
    (Real.measurable_exp.comp (measurable_const.mul continuous_abs.measurable)).ennreal_ofReal
  have := hmp.lintegral_comp (f := fun y : ℝ ↦ ENNReal.ofReal (Real.exp (a * |y|))) hm
  unfold nvNoiseLaw
  rw [this]
  exact nv_lintegral_exp_abs_gaussian a

/-- **Exponential moment of a partial row sum.** -/
theorem nv_exp_sum_le (d : ℕ) {R : ℝ} (hR : 0 < R) (hB : ∑' p, nv_b d p ≤ R)
    (k : Fin d → ℤ) (s : Finset (NvFrame d)) (lam : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * ∑ p ∈ s, |ξ (k, p)| * nv_b d p)) ∂(nvNoiseLaw d)
      ≤ ENNReal.ofReal (2 * Real.exp (lam ^ 2 * R ^ 2 / 2)) := by
  classical
  set θ : NvFrame d → ℝ := fun p ↦ nv_b d p / R with hθ
  have hθ0 : ∀ p ∈ s, 0 ≤ θ p := fun p _ ↦ div_nonneg (nv_b_nonneg d p) hR.le
  have hΘ : ∑ p ∈ s, θ p ≤ 1 := by
    have h1 : ∑ p ∈ s, nv_b d p ≤ R :=
      (Summable.sum_le_tsum s (fun p _ ↦ nv_b_nonneg d p) (nv_b_summable d)).trans hB
    rw [hθ, ← Finset.sum_div, div_le_one hR]
    exact h1
  set Θ : ℝ := ∑ p ∈ s, θ p with hΘdef
  set A : ℝ := 2 * Real.exp ((lam * R) ^ 2 / 2) with hA
  have hA1 : 1 ≤ A := by
    have : 1 ≤ Real.exp ((lam * R) ^ 2 / 2) := Real.one_le_exp (by positivity)
    rw [hA]; linarith only [this]
  have hpt : ∀ ξ : NvNoise d, ENNReal.ofReal (Real.exp (lam * ∑ p ∈ s, |ξ (k, p)| * nv_b d p))
      ≤ ∑ p ∈ s, ENNReal.ofReal (θ p) *
          ENNReal.ofReal (Real.exp (lam * R * |ξ (k, p)|)) + ENNReal.ofReal (1 - Θ) := by
    intro ξ
    have hJ := nv_jensen_defect s θ (fun p ↦ lam * R * |ξ (k, p)|) hθ0 hΘ
    have he : lam * ∑ p ∈ s, |ξ (k, p)| * nv_b d p = ∑ p ∈ s, θ p * (lam * R * |ξ (k, p)|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [hθ]
      field_simp
    rw [he]
    refine (ENNReal.ofReal_le_ofReal hJ).trans ?_
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun p hp ↦ mul_nonneg (hθ0 p hp)
      (Real.exp_pos _).le) (sub_nonneg.2 hΘ), ENNReal.ofReal_sum_of_nonneg fun p hp ↦
      mul_nonneg (hθ0 p hp) (Real.exp_pos _).le]
    refine le_of_eq (congrArg₂ _ (Finset.sum_congr rfl fun p hp ↦ ?_) rfl)
    exact ENNReal.ofReal_mul (hθ0 p hp)
  have hmeas : ∀ p : NvFrame d, Measurable fun ξ : NvNoise d ↦
      ENNReal.ofReal (θ p) * ENNReal.ofReal (Real.exp (lam * R * |ξ (k, p)|)) := fun p ↦
    measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul
        (continuous_abs.measurable.comp (nv_measurable_coord d (k, p))))).ennreal_ofReal
  calc ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * ∑ p ∈ s, |ξ (k, p)| * nv_b d p)) ∂(nvNoiseLaw d)
      ≤ ∫⁻ ξ, (∑ p ∈ s, ENNReal.ofReal (θ p) *
          ENNReal.ofReal (Real.exp (lam * R * |ξ (k, p)|)) + ENNReal.ofReal (1 - Θ))
          ∂(nvNoiseLaw d) := lintegral_mono hpt
    _ = ∑ p ∈ s, ENNReal.ofReal (θ p) *
          ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * R * |ξ (k, p)|)) ∂(nvNoiseLaw d)
          + ENNReal.ofReal (1 - Θ) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const,
          measure_univ, mul_one,
          lintegral_finsetSum _ fun p _ ↦ hmeas p]
        congr 1
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [lintegral_const_mul _ ?_]
        exact (Real.measurable_exp.comp (measurable_const.mul
          (continuous_abs.measurable.comp (nv_measurable_coord d (k, p))))).ennreal_ofReal
    _ ≤ ∑ p ∈ s, ENNReal.ofReal (θ p) * ENNReal.ofReal A + ENNReal.ofReal (1 - Θ) := by
        refine add_le_add (Finset.sum_le_sum fun p _ ↦ ?_) le_rfl
        exact mul_le_mul' le_rfl (nv_lintegral_exp_coord d k p (lam * R))
    _ = ENNReal.ofReal (Θ * A + (1 - Θ)) := by
        rw [ENNReal.ofReal_add (mul_nonneg (Finset.sum_nonneg hθ0) (by linarith only [hA1]))
          (sub_nonneg.2 hΘ), ENNReal.ofReal_mul (Finset.sum_nonneg hθ0),
          ENNReal.ofReal_sum_of_nonneg hθ0, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (2 * Real.exp (lam ^ 2 * R ^ 2 / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (lam * R) ^ 2 / 2 = lam ^ 2 * R ^ 2 / 2 := by ring
        rw [this] at hA
        rw [← hA]
        nlinarith only [mul_nonneg (sub_nonneg.2 hΘ) (sub_nonneg.2 hA1)]

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
