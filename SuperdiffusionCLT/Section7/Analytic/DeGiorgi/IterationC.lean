/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.CaccioppoliB
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cube cutoffs with scale-invariant gradient bound

For an axis cube `Q = axisCube z L` and a margin `δ > 0`, a smooth product cutoff `η`, equal to
`1` on the concentric cube of margin `δ`, supported in `Q`, with `|∇η| ≤ c / δ`, where `c`
depends only on the dimension.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem smoothTransition_deriv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv Real.smoothTransition x| ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  by_cases h0 : x < 0
  · have : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h0] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]
    simp
  by_cases h1 : 1 < x
  · have : Real.smoothTransition =ᶠ[nhds x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]
    simp
  · have := hK x ⟨not_lt.1 h0, not_lt.1 h1⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The one-dimensional cutoff profile: zero outside `(a + δ/4, b - δ/4)`, one on
`[a + 3δ/4, b - 3δ/4]`. -/
noncomputable def cubeProfile (a b δ : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a - δ / 4) * (2 / δ)) *
    Real.smoothTransition ((b - δ / 4 - t) * (2 / δ))

theorem cubeProfile_contDiff (a b δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cubeProfile a b δ) := by
  unfold cubeProfile
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (t - a - δ / 4) * (2 / δ) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (b - δ / 4 - t) * (2 / δ) := by fun_prop
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem cubeProfile_nonneg (a b δ t : ℝ) : 0 ≤ cubeProfile a b δ t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cubeProfile_le_one (a b δ t : ℝ) : cubeProfile a b δ t ≤ 1 :=
  (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem cubeProfile_eq_one {a b δ t : ℝ} (hδ : 0 < δ) (h1 : a + δ ≤ t) (h2 : t ≤ b - δ) :
    cubeProfile a b δ t = 1 := by
  unfold cubeProfile
  have e1 : 1 ≤ (t - a - δ / 4) * (2 / δ) := by
    rw [← sub_nonneg]
    have : (t - a - δ / 4) * (2 / δ) - 1 = (2 * (t - a - δ / 4) - δ) / δ := by
      field_simp
    rw [this]
    apply div_nonneg _ hδ.le
    linarith only [h1, hδ]
  have e2 : 1 ≤ (b - δ / 4 - t) * (2 / δ) := by
    rw [← sub_nonneg]
    have : (b - δ / 4 - t) * (2 / δ) - 1 = (2 * (b - δ / 4 - t) - δ) / δ := by
      field_simp
    rw [this]
    apply div_nonneg _ hδ.le
    linarith only [h2, hδ]
  rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2, one_mul]

theorem cubeProfile_eq_zero {a b δ t : ℝ} (hδ : 0 < δ) (h : t ≤ a + δ / 4 ∨ b - δ / 4 ≤ t) :
    cubeProfile a b δ t = 0 := by
  unfold cubeProfile
  rcases h with h | h
  · have : (t - a - δ / 4) * (2 / δ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [h]) (by positivity)
    rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]
  · have : (b - δ / 4 - t) * (2 / δ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [h]) (by positivity)
    rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]

theorem cubeProfile_deriv_bound {K : ℝ} (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K)
    (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ D, HasDerivAt (cubeProfile a b δ) D t ∧ |D| ≤ 4 * K / δ := by
  have hT : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have h1 : HasDerivAt (fun t : ℝ => (t - a - δ / 4) * (2 / δ)) (2 / δ) t := by
    simpa using (((hasDerivAt_id t).sub_const a).sub_const (δ / 4)).mul_const (2 / δ)
  have h2 : HasDerivAt (fun t : ℝ => (b - δ / 4 - t) * (2 / δ)) (-(2 / δ)) t := by
    simpa using (((hasDerivAt_id t).const_sub (b - δ / 4))).mul_const (2 / δ)
  have g1 := (hT ((t - a - δ / 4) * (2 / δ))).hasDerivAt.comp t h1
  have g2 := (hT ((b - δ / 4 - t) * (2 / δ))).hasDerivAt.comp t h2
  refine ⟨_, g1.mul g2, ?_⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hδ2 : 0 ≤ 2 / δ := by positivity
  set u1 := Real.smoothTransition ((t - a - δ / 4) * (2 / δ))
  set u2 := Real.smoothTransition ((b - δ / 4 - t) * (2 / δ))
  have b1 : |deriv Real.smoothTransition ((t - a - δ / 4) * (2 / δ)) * (2 / δ)| ≤ K * (2 / δ) := by
    rw [abs_mul, abs_of_nonneg hδ2]
    exact mul_le_mul_of_nonneg_right (hK _) hδ2
  have b2 : |deriv Real.smoothTransition ((b - δ / 4 - t) * (2 / δ)) * -(2 / δ)| ≤
      K * (2 / δ) := by
    rw [abs_mul, abs_neg, abs_of_nonneg hδ2]
    exact mul_le_mul_of_nonneg_right (hK _) hδ2
  have u1b : |u1| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have u2b : |u2| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  simp only [Function.comp_apply]
  have e : 4 * K / δ = K * (2 / δ) + K * (2 / δ) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    calc _ ≤ |deriv Real.smoothTransition ((t - a - δ / 4) * (2 / δ)) * (2 / δ)| * 1 := by
          exact mul_le_mul_of_nonneg_left u2b (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact b1
  · rw [abs_mul]
    calc _ ≤ 1 * |deriv Real.smoothTransition ((b - δ / 4 - t) * (2 / δ)) * -(2 / δ)| := by
          exact mul_le_mul_of_nonneg_right u1b (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact b2

theorem cubeCutoff_fderiv_apply {K : ℝ} (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K)
    (z : Vec d) (L : ℝ) {δ : ℝ} (hδ : 0 < δ) (x : Vec d) (i : Fin d) :
    |fderiv ℝ (fun y : Vec d => ∏ j, cubeProfile (z j) (z j + L) δ (y j)) x (basisVec i)| ≤
      4 * K / δ := by
  classical
  choose D hD hDb using fun j => cubeProfile_deriv_bound hK (z j) (z j + L) hδ (x j)
  have hF : ∀ j ∈ Finset.univ, HasFDerivAt
      (fun y : Vec d => cubeProfile (z j) (z j + L) δ (y j))
      (D j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x :=
    fun j _ => HasDerivAt.comp_hasFDerivAt (f := fun y : Vec d => y j) x (hD j)
      (hasFDerivAt_apply j x)
  have hP := HasFDerivAt.finsetProd hF
  rw [hP.fderiv]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, basisVec_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, mul_one]
    rw [abs_mul]
    have hp0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, cubeProfile (z j) (z j + L) δ (x j) :=
      Finset.prod_nonneg fun j _ => cubeProfile_nonneg _ _ _ _
    have hp1 : ∏ j ∈ Finset.univ.erase i, cubeProfile (z j) (z j + L) δ (x j) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => cubeProfile_nonneg _ _ _ _)
        (fun j _ => cubeProfile_le_one _ _ _ _)
    rw [abs_of_nonneg hp0]
    calc _ ≤ 1 * |D i| := mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hDb i
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- A smooth cutoff of a cube with margin `δ`: `1` on the concentric cube of margin `δ`,
compactly supported in the cube, and with gradient at most `c / δ`. -/
theorem exists_cube_cutoff (d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (z : Vec d) (L δ : ℝ), 0 < δ → ∃ η : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ axisCube z L ∧
      (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
      (∀ x ∈ axisCube (z + fun _ => δ) (L - 2 * δ), η x = 1) ∧
      ∀ x, eucNorm (cutoffGrad η x) ≤ c / δ := by
  classical
  obtain ⟨K, hK0, hK⟩ := smoothTransition_deriv_bound
  refine ⟨Real.sqrt d * (4 * K), by positivity, fun z L δ hδ => ?_⟩
  set η : Vec d → ℝ := fun y => ∏ j, cubeProfile (z j) (z j + L) δ (y j) with hη
  have hsupp : Function.support η ⊆ Set.pi Set.univ fun j => Set.Icc (z j + δ / 4)
      (z j + L - δ / 4) := by
    intro x hx j _
    by_contra hnot
    apply hx
    have : cubeProfile (z j) (z j + L) δ (x j) = 0 := by
      apply cubeProfile_eq_zero hδ
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with h | h
      · left; linarith only [h]
      · right; linarith only [h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) this
  have hts : tsupport η ⊆ Set.pi Set.univ fun j => Set.Icc (z j + δ / 4) (z j + L - δ / 4) :=
    closure_minimal hsupp (isClosed_set_pi fun _ _ => isClosed_Icc)
  refine ⟨η, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_prod fun j _ =>
      (cubeProfile_contDiff _ _ _).comp (contDiff_apply ℝ ℝ j)
  · exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_tsupport η) hts
  · intro x hx j _
    have := hts hx j (Set.mem_univ j)
    simp only [Set.mem_Icc] at this
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [this.1, this.2, hδ]
  · intro x; exact Finset.prod_nonneg fun j _ => cubeProfile_nonneg _ _ _ _
  · intro x
    exact Finset.prod_le_one₀ (fun j _ => cubeProfile_nonneg _ _ _ _)
      (fun j _ => cubeProfile_le_one _ _ _ _)
  · intro x hx
    refine Finset.prod_eq_one fun j _ => ?_
    have := hx j (Set.mem_univ j)
    simp only [Set.mem_Ioo, Pi.add_apply] at this
    exact cubeProfile_eq_one hδ (by linarith only [this.1]) (by linarith only [this.2])
  · intro x
    unfold eucNorm
    have hb : ∀ i, cutoffGrad η x i ^ 2 ≤ (4 * K / δ) ^ 2 := fun i =>
      sq_le_sq' (abs_le.1 (cubeCutoff_fderiv_apply hK z L hδ x i)).1
        (abs_le.1 (cubeCutoff_fderiv_apply hK z L hδ x i)).2
    have hs : vecNormSq (cutoffGrad η x) ≤ d * (4 * K / δ) ^ 2 := by
      unfold vecNormSq vecDot
      calc ∑ i, cutoffGrad η x i * cutoffGrad η x i ≤ ∑ _i : Fin d, (4 * K / δ) ^ 2 :=
            Finset.sum_le_sum fun i _ => by rw [← sq]; exact hb i
        _ = _ := by simp
    calc Real.sqrt (vecNormSq (cutoffGrad η x)) ≤ Real.sqrt (d * (4 * K / δ) ^ 2) :=
          Real.sqrt_le_sqrt hs
      _ = Real.sqrt d * (4 * K) / δ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by positivity)]
          ring

end SuperdiffusionCLT.Section7
