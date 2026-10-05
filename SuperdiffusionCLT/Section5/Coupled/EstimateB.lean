/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.Estimate

/-!
# `lem.coupled.input`: the assembly at a fixed large cube

Given the three analytic inputs (the `L²` bound on `hshell ∇w_D`, the bound on `R_z`, and a lower
bound on the energy `E‖∇w_D‖²`), the average of `E |coupledVec|²` is bounded by
`1 - (energy lower bound) + σ⁻² b² + σ⁻² r² + 2 σ⁻² b r + 2 σ⁻¹ r`.  The measurability of the box
quantities (file `Estimate`) is what lets the `lintegral` of the sum be split.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section3.ResponseFields (vecCubeLpENorm)
open scoped ENNReal

variable {d : ℕ}

theorem coupled4_subcubeAvg_const_le {Kc n : ℕ} (c : ℝ≥0∞) :
    subcubeAvg (d := d) Kc n (fun _ => c) ≤ c := by
  unfold subcubeAvg
  rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hD : (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card = 0
  · simp [hD]
  · rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hD) (ENNReal.natCast_ne_top _),
      one_mul]

theorem coupled4_lintegral_subcubeAvg {Kc n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : TriadicCube d → Ω → ℝ≥0∞)
    (hf : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (f Q)) :
    ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ = subcubeAvg Kc n (fun Q => ∫⁻ ω, f Q ω ∂μ) := by
  unfold subcubeAvg
  by_cases hD : (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card = 0
  · rw [Finset.card_eq_zero.mp hD]; simp
  · have hne : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (by exact_mod_cast hD)
    rw [lintegral_const_mul' _ _ hne, lintegral_finsetSum _ hf]

theorem coupled4_sub_of_add_le {x : ℝ≥0∞} {T gl : ℝ}
    (h : x + ENNReal.ofReal gl ≤ ENNReal.ofReal T) : x ≤ ENNReal.ofReal (T - gl) := by
  by_cases hg : gl ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hg, add_zero] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (by linarith only [hg]))
  · have hg' : 0 ≤ gl := (not_le.mp hg).le
    rw [ENNReal.ofReal_sub _ hg']
    exact ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top h

/-- The AM-GM step for the remainder terms. -/
theorem coupled4_amgm (c t s x y : ℝ) (hc : 0 ≤ c) (ht : 0 < t) (hs : 0 < s) :
    c ^ 2 * y ^ 2 + 2 * c ^ 2 * (x * y) + 2 * c * y ≤
      (c ^ 2 + c ^ 2 / t + c / s) * y ^ 2 + c ^ 2 * t * x ^ 2 + c * s := by
  have h1 : 0 ≤ (t * x - y) ^ 2 / t := by positivity
  have h2 : 0 ≤ (s - y) ^ 2 / s := by positivity
  have e1 : (t * x - y) ^ 2 / t = t * x ^ 2 + y ^ 2 / t - 2 * (x * y) := by
    field_simp
    ring
  have e2 : (s - y) ^ 2 / s = s + y ^ 2 / s - 2 * y := by
    field_simp
    ring
  have h3 : 2 * (x * y) ≤ t * x ^ 2 + y ^ 2 / t := by linarith only [h1, e1]
  have h4 : 2 * y ≤ s + y ^ 2 / s := by linarith only [h2, e2]
  have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
  have h6 := mul_le_mul_of_nonneg_left h4 hc
  have e3 : c ^ 2 * (t * x ^ 2 + y ^ 2 / t) = c ^ 2 * t * x ^ 2 + c ^ 2 / t * y ^ 2 := by ring
  have e4 : c * (s + y ^ 2 / s) = c * s + c / s * y ^ 2 := by ring
  linarith only [h5, h6, e3, e4]

/-- The box average of `|B_z|²` is at most the energy of `hshell ∇w` on the large cube. -/
theorem coupled4_avg_B_le [NeZero d] (m h Kc n : ℕ) (hn : n ≤ Kc) (omega : ShellSeq d)
    {g : Vec d → Vec d} (hg0 : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) g) :
    subcubeAvg Kc n (fun Q => ENNReal.ofReal (vecNormSq (coupledB m h Q omega g))) ≤
      vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x) (g x)) ^ (2 : ℕ) := by
  set F : Vec d → Vec d := fun x => matVecMul (finiteShellIncrement omega (m - h) m x) (g x)
    with hFdef
  have hF0 : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) F :=
    SuperdiffusionCLT.Section3.Terms.memVectorL2_matVecMul_of_continuous
      (originCube d (Kc : ℤ)) (fun i j => coupled3_continuous_entry omega (m - h) m i j) hg0
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hbox : subcubeAvg Kc n (fun Q => ENNReal.ofReal (vecNormSq (coupledB m h Q omega g))) ≤
      subcubeAvg Kc n (fun Q => ∫⁻ x, ENNReal.ofReal (vecNormSq (F x))
        ∂normalizedCubeMeasure Q) := by
    refine coupled_subcubeAvg_mono_on fun Q hQ => ?_
    have hsub := openCubeSet_subset_of_mem_descendantsAtScale hk hQ
    have hFQ : MemVectorL2 (openCubeSet Q) F :=
      hF0.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hint := SuperdiffusionCLT.Section3.ResponseFields.integrable_vecNormSq_normalizedCubeMeasure
      hFQ
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _),
      SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage,
      coupledB_eq_open]
    exact ENNReal.ofReal_le_ofReal (coupled3_jensen hFQ)
  rw [subcubeAvg_lintegral_normalizedCubeMeasure hn (fun x => ENNReal.ofReal (vecNormSq (F x)))]
    at hbox
  have hint := SuperdiffusionCLT.Section3.ResponseFields.integrable_vecNormSq_normalizedCubeMeasure
    hF0
  rw [SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm_two_sq_eq_ofReal hF0,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)]
  exact hbox

end SuperdiffusionCLT.Section5
