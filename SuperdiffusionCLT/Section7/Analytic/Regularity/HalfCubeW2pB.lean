/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2p

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Half cube: odd extension of `H¹₀` and the identity against functions vanishing on the face

The odd extension of an `H¹₀` function of the half cube is an `H¹₀` function of the cube
(`hcOddH10`).  A weak identity `∫_D K·∇χ = ∫_D f χ` valid against all `H¹₀(D)` test functions
extends to smooth compactly supported functions of the cube that vanish on the flat face
(`hc_tail_identity`): the test function is cut off in the normal direction, and the commutator
term is controlled by the linear vanishing of the test function on the face.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem hc_zero_of_nonpos {e : Fin d} {m : ℤ} {φ : Vec d → ℝ}
    (hs : tsupport φ ⊆ flatHalfCube e m) {x : Vec d} (hx : x e ≤ 0) :
    φ x = 0 ∧ fderiv ℝ φ x = 0 := by
  have hnot : x ∉ tsupport φ := fun h => by
    have := (hs h).2
    simp only [Set.mem_ofPred_eq] at this
    linarith only [this, hx]
  exact ⟨image_eq_zero_of_notMem_tsupport hnot, fderiv_of_notMem_tsupport ℝ hnot⟩

theorem hc_contDiff_comp_hcFlip {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (e : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (hcFlip e x)) := by
  have : ContDiff ℝ (⊤ : ℕ∞) (hcFlipL e) := (hcFlipL e).contDiff
  have h2 := hφ.comp this
  simpa only [Function.comp_def, hcFlipL_apply] using h2

theorem hc_hasCompactSupport_comp_hcFlip {φ : Vec d → ℝ} (hφ : HasCompactSupport φ) (e : Fin d) :
    HasCompactSupport (fun x => φ (hcFlip e x)) :=
  hφ.comp_homeomorph (hcFlipHomeo e)

/-- The odd reflection of a function supported in the half cube. -/
def hcOddApprox (e : Fin d) (φ : Vec d → ℝ) (x : Vec d) : ℝ := φ x - φ (hcFlip e x)

theorem tsupport_comp_hcFlip_subset (e : Fin d) (φ : Vec d → ℝ) :
    tsupport (fun x => φ (hcFlip e x)) ⊆ hcFlip e ⁻¹' tsupport φ := by
  refine closure_minimal ?_ ((isClosed_tsupport φ).preimage (continuous_hcFlip e))
  intro x hx
  exact subset_tsupport φ hx

theorem tsupport_hcOddApprox_subset {e : Fin d} {m : ℤ} {φ : Vec d → ℝ}
    (hs : tsupport φ ⊆ flatHalfCube e m) :
    tsupport (hcOddApprox e φ) ⊆ openCubeSet (originCube d m) := by
  have h1 : tsupport (fun x => φ (hcFlip e x)) ⊆ openCubeSet (originCube d m) := by
    intro x hx
    have := tsupport_comp_hcFlip_subset e φ hx
    have h2 := (flatHalfCube_subset e m) (hs this)
    exact (hcFlip_mem_openCubeSet_iff e m x).1 h2
  refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
  · exact hs.trans (flatHalfCube_subset e m)
  · simpa [tsupport_neg] using h1

theorem hcOddApprox_eq_hcExt {e : Fin d} {m : ℤ} {φ : Vec d → ℝ}
    (hs : tsupport φ ⊆ flatHalfCube e m) (x : Vec d) :
    hcOddApprox e φ x = hcExt (-1) e φ x := by
  unfold hcOddApprox hcExt
  split_ifs with h
  · have : hcFlip e x e ≤ 0 := by rw [hcFlip_apply_e]; linarith only [h]
    rw [(hc_zero_of_nonpos hs this).1]; ring
  · rw [(hc_zero_of_nonpos hs (not_lt.1 h)).1]; ring

theorem fderiv_hcOddApprox_apply {e : Fin d} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) (x : Vec d) :
    fderiv ℝ (hcOddApprox e φ) x (basisVec j) =
      fderiv ℝ φ x (basisVec j) + hcSgn e j * fderiv ℝ φ (hcFlip e x) (basisVec j) := by
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fun y => φ (hcFlip e y)) :=
    (hc_contDiff_comp_hcFlip hφ e).differentiable (by norm_num)
  unfold hcOddApprox
  rw [fderiv_fun_sub (hd1 x) (hd2 x)]
  simp only [sub_apply, fderiv_comp_hcFlip hd1 e x j]
  ring

theorem fderiv_hcOddApprox_eq_hcExt {e : Fin d} {m : ℤ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : tsupport φ ⊆ flatHalfCube e m) (j : Fin d) (x : Vec d) :
    fderiv ℝ (hcOddApprox e φ) x (basisVec j) =
      hcExt (hcSgn e j) e (fun y => fderiv ℝ φ y (basisVec j)) x := by
  rw [fderiv_hcOddApprox_apply hφ]
  unfold hcExt
  split_ifs with h
  · have : hcFlip e x e ≤ 0 := by rw [hcFlip_apply_e]; linarith only [h]
    rw [(hc_zero_of_nonpos hs this).2]; simp
  · rw [(hc_zero_of_nonpos hs (not_lt.1 h)).2]; simp

theorem memLp_hcExt_volume (e : Fin d) (m : ℤ) {σ : ℝ} (hσ : |σ| = 1) {F : Vec d → ℝ}
    (hF : MemLp F 2 (volume.restrict (flatHalfCube e m))) :
    MemLp (hcExt σ e F) 2 (volume.restrict (openCubeSet (originCube d m))) := by
  rw [memLp_iff, eLpNorm_hcExt_volume e m hσ hF.aestronglyMeasurable (by norm_num) (by norm_num)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
    hF.eLpNorm_lt_top


section HalfCubeOdd

variable {e : Fin d} {m : ℤ}

theorem hc_approx_continuous {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : Continuous φ :=
  hφ.continuous

theorem hc_tendsto_odd (v : H10Function (flatHalfCube e m)) :
    Tendsto (fun n => eLpNorm (fun x => hcOddApprox e (v.approx n) x -
      hcExt (-1) e v.toH1Function.toFun x) 2 (volume.restrict (openCubeSet (originCube d m))))
      atTop (𝓝 0) := by
  have hfun : ∀ n, (fun x => hcOddApprox e (v.approx n) x - hcExt (-1) e v.toH1Function.toFun x) =
      hcExt (-1) e (fun y => v.approx n y - v.toH1Function.toFun y) := by
    intro n
    rw [hcExt_sub]
    funext x
    rw [hcOddApprox_eq_hcExt (v.approx_support_subset n)]
  have hmeas : ∀ n, AEStronglyMeasurable (fun y => v.approx n y - v.toH1Function.toFun y)
      (volume.restrict (flatHalfCube e m)) := fun n =>
    (hc_approx_continuous (v.approx_smooth n)).aestronglyMeasurable.sub
      v.toH1Function.memL2.aestronglyMeasurable
  simp_rw [hfun]
  have : ∀ n, eLpNorm (hcExt (-1) e (fun y => v.approx n y - v.toH1Function.toFun y)) 2
      (volume.restrict (openCubeSet (originCube d m))) =
      2 ^ (1 / (2 : ℝ≥0∞).toReal) * eLpNorm (fun y => v.approx n y - v.toH1Function.toFun y) 2
        (volume.restrict (flatHalfCube e m)) := fun n =>
    eLpNorm_hcExt_volume e m (by simp) (hmeas n) (by norm_num) (by norm_num)
  simp_rw [this]
  have h0 := v.tendsto_approx
  simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (by simp)))

theorem hc_tendsto_odd_grad (v : H10Function (flatHalfCube e m)) (j : Fin d) :
    Tendsto (fun n => eLpNorm (fun x => fderiv ℝ (hcOddApprox e (v.approx n)) x (basisVec j) -
      hcExtVec e v.toH1Function.grad x j) 2 (volume.restrict (openCubeSet (originCube d m))))
      atTop (𝓝 0) := by
  have hfun : ∀ n, (fun x => fderiv ℝ (hcOddApprox e (v.approx n)) x (basisVec j) -
      hcExtVec e v.toH1Function.grad x j) =
      hcExt (hcSgn e j) e (fun y => fderiv ℝ (v.approx n) y (basisVec j) - v.toH1Function.grad y j) := by
    intro n
    rw [hcExt_sub]
    funext x
    rw [fderiv_hcOddApprox_eq_hcExt (v.approx_smooth n) (v.approx_support_subset n)]
    rfl
  have hσ : |hcSgn e j| = 1 := by by_cases h : j = e <;> simp [hcSgn, h]
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun y => fderiv ℝ (v.approx n) y (basisVec j) - v.toH1Function.grad y j)
      (volume.restrict (flatHalfCube e m)) := fun n => by
    refine AEStronglyMeasurable.sub ?_ (v.toH1Function.gradMemL2 j).aestronglyMeasurable
    exact (((v.approx_smooth n).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).aestronglyMeasurable
  simp_rw [hfun]
  have : ∀ n, eLpNorm (hcExt (hcSgn e j) e (fun y => fderiv ℝ (v.approx n) y (basisVec j) -
      v.toH1Function.grad y j)) 2 (volume.restrict (openCubeSet (originCube d m))) =
      2 ^ (1 / (2 : ℝ≥0∞).toReal) * eLpNorm (fun y => fderiv ℝ (v.approx n) y (basisVec j) -
        v.toH1Function.grad y j) 2 (volume.restrict (flatHalfCube e m)) := fun n =>
    eLpNorm_hcExt_volume e m hσ (hmeas n) (by norm_num) (by norm_num)
  simp_rw [this]
  have h0 := v.tendsto_approx_grad j
  simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (by simp)))


theorem hcSgn_abs (e j : Fin d) : |hcSgn e j| = 1 := by by_cases h : j = e <;> simp [hcSgn, h]

theorem hc_oddApprox_memLp {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    MemLp (hcOddApprox e φ) 2 (volume.restrict (openCubeSet (originCube d m))) :=
  flatW2p_memLp_two_of_continuous (hφ.continuous.sub (hc_contDiff_comp_hcFlip hφ e).continuous)
    (hc.sub (hc_hasCompactSupport_comp_hcFlip hc e))

/-- The odd extension of an `H¹₀` function of the half cube to the cube, as an `H¹₀` function. -/
noncomputable def hcOddH10 (v : H10Function (flatHalfCube e m)) :
    H10Function (openCubeSet (originCube d m)) where
  toFun := hcExt (-1) e v.toH1Function.toFun
  grad := hcExtVec e v.toH1Function.grad
  memL2 := memLp_hcExt_volume e m (by simp) v.toH1Function.memL2
  gradMemL2 := fun i => memLp_hcExt_volume e m (hcSgn_abs e i) (v.toH1Function.gradMemL2 i)
  hasWeakGradient := fun j => by
    refine HasWeakPartialDerivOn.of_tendsto_eLpNorm_two
      (u_n := fun n => hcOddApprox e (v.approx n))
      (g_n := fun n x => fderiv ℝ (hcOddApprox e (v.approx n)) x (basisVec j))
      (memLp_hcExt_volume e m (by simp) v.toH1Function.memL2)
      (memLp_hcExt_volume e m (hcSgn_abs e j) (v.toH1Function.gradMemL2 j))
      (fun n => hc_oddApprox_memLp (v.approx_smooth n) (v.approx_hasCompactSupport n))
      (fun n => ?_)
      (fun n => HasWeakPartialDerivOn.of_contDiff (((v.approx_smooth n).sub
        (hc_contDiff_comp_hcFlip (v.approx_smooth n) e)).of_le (by exact_mod_cast le_top)))
      (hc_tendsto_odd v) (hc_tendsto_odd_grad v j)
    have hu := (v.approx_smooth n).sub (hc_contDiff_comp_hcFlip (v.approx_smooth n) e)
    exact flatW2p_memLp_two_of_continuous
      ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (((v.approx_hasCompactSupport n).sub
        (hc_hasCompactSupport_comp_hcFlip (v.approx_hasCompactSupport n) e)).fderiv_apply (𝕜 := ℝ)
        (basisVec j))
  approx := fun n => hcOddApprox e (v.approx n)
  approx_smooth := fun n => (v.approx_smooth n).sub (hc_contDiff_comp_hcFlip (v.approx_smooth n) e)
  approx_hasCompactSupport := fun n =>
    (v.approx_hasCompactSupport n).sub (hc_hasCompactSupport_comp_hcFlip (v.approx_hasCompactSupport n) e)
  approx_support_subset := fun n => tsupport_hcOddApprox_subset (v.approx_support_subset n)
  tendsto_approx := hc_tendsto_odd v
  tendsto_approx_grad := fun j => hc_tendsto_odd_grad v j

end HalfCubeOdd

/-- The smooth cutoff in the normal coordinate: `0` for `x e ≤ δ`, `1` for `x e ≥ 2 δ`. -/
noncomputable def hcCut (e : Fin d) (δ : ℝ) (x : Vec d) : ℝ :=
  Real.smoothTransition (x e / δ - 1)

/-- The normal derivative of the cutoff. -/
noncomputable def hcCutDeriv (e : Fin d) (δ : ℝ) (x : Vec d) : ℝ :=
  deriv Real.smoothTransition (x e / δ - 1) / δ

theorem contDiff_hcCut (e : Fin d) (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (hcCut e δ) := by
  unfold hcCut
  exact Real.smoothTransition.contDiff.comp (((contDiff_apply ℝ ℝ e).div_const δ).sub contDiff_const)

theorem hcCut_nonneg (e : Fin d) (δ : ℝ) (x : Vec d) : 0 ≤ hcCut e δ x :=
  Real.smoothTransition.nonneg _

theorem hcCut_le_one (e : Fin d) (δ : ℝ) (x : Vec d) : hcCut e δ x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem hcCut_of_le {e : Fin d} {δ : ℝ} (hδ : 0 < δ) {x : Vec d} (hx : x e ≤ δ) :
    hcCut e δ x = 0 := by
  unfold hcCut
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [sub_nonpos, div_le_one hδ]; exact hx

theorem hcCut_of_ge {e : Fin d} {δ : ℝ} (hδ : 0 < δ) {x : Vec d} (hx : 2 * δ ≤ x e) :
    hcCut e δ x = 1 := by
  unfold hcCut
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith only [hx]

theorem fderiv_hcCut_apply (e : Fin d) (δ : ℝ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (hcCut e δ) x (basisVec i) = if i = e then hcCutDeriv e δ x else 0 := by
  have h1 : HasFDerivAt (fun y : Vec d => y e / δ - 1)
      ((δ⁻¹ : ℝ) • (ContinuousLinearMap.proj e : Vec d →L[ℝ] ℝ)) x := by
    have h0 : HasFDerivAt (fun y : Vec d => y e) (ContinuousLinearMap.proj e : Vec d →L[ℝ] ℝ) x :=
      hasFDerivAt_apply e x
    have := (h0.const_mul δ⁻¹).sub_const 1
    simpa [div_eq_inv_mul] using this
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (x e / δ - 1))
      (x e / δ - 1) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by norm_num)
      (x e / δ - 1)).hasDerivAt
  have h3 := h2.comp_hasFDerivAt x h1
  have h4 : hcCut e δ = Real.smoothTransition ∘ (fun y : Vec d => y e / δ - 1) := rfl
  rw [h4, h3.fderiv]
  by_cases hi : i = e
  · simp [hi, hcCutDeriv, basisVec, div_eq_inv_mul, mul_comm]
  · simp [hi, basisVec]


theorem hc_deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [this.deriv_eq]; simp

theorem hc_deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
  rw [this.deriv_eq]; simp

theorem hc_exists_bound_deriv_smoothTransition :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · have h1 := hB t ht
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · have : deriv Real.smoothTransition t = 0 := by
      rcases not_and_or.1 ht with h | h
      · exact hc_deriv_smoothTransition_eq_zero_of_lt_zero (not_le.1 h)
      · exact hc_deriv_smoothTransition_eq_zero_of_one_lt (not_le.1 h)
    rw [this]; simp

theorem hcCutDeriv_eq_zero_of_ge {e : Fin d} {δ : ℝ} (hδ : 0 < δ) {x : Vec d} (hx : 2 * δ < x e) :
    hcCutDeriv e δ x = 0 := by
  unfold hcCutDeriv
  rw [hc_deriv_smoothTransition_eq_zero_of_one_lt, zero_div]
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hδ]; linarith only [hx]

theorem abs_mul_hcCutDeriv_le {e : Fin d} {δ B M : ℝ} (hδ : 0 < δ) (hB : ∀ t, |deriv Real.smoothTransition t| ≤ B)
    (hM : 0 ≤ M) {x : Vec d} {ψ : Vec d → ℝ} (hψ : |ψ x| ≤ M * |x e|) (hx : 0 < x e) :
    |ψ x * hcCutDeriv e δ x| ≤ 2 * M * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  by_cases h2 : 2 * δ < x e
  · rw [hcCutDeriv_eq_zero_of_ge hδ h2]; simp; positivity
  · have h2' : x e ≤ 2 * δ := not_lt.1 h2
    rw [abs_mul]
    unfold hcCutDeriv
    rw [abs_div, abs_of_pos hδ]
    have h3 : |ψ x| ≤ M * (2 * δ) := hψ.trans (by rw [abs_of_pos hx]; exact mul_le_mul_of_nonneg_left h2' hM)
    calc |ψ x| * (|deriv Real.smoothTransition (x e / δ - 1)| / δ)
        ≤ (M * (2 * δ)) * (B / δ) := by
          refine mul_le_mul h3 ?_ (by positivity) (by positivity)
          exact div_le_div_of_nonneg_right (hB _) hδ.le
      _ = 2 * M * B := by field_simp


theorem hc_abs_le_of_vanish {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (e : Fin d) (h0 : ∀ x : Vec d, x e = 0 → ψ x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Vec d, |ψ x| ≤ M * |x e| := by
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  set x0 : Vec d := fun i => if i = e then 0 else x i with hx0
  have hψx0 : ψ x0 = 0 := h0 x0 (by simp [hx0])
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ψ) (s := Set.univ)
    (C := max C 0) (fun y _ => (hψ.differentiable (by simp)) y)
    (fun y _ => (hC y).trans (le_max_left _ _)) convex_univ (Set.mem_univ x0) (Set.mem_univ x)
  have hn : ‖x - x0‖ = |x e| := by
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_
      by_cases hi : i = e
      · subst hi; simp [hx0]
      · simp [hx0, hi]
    · have := norm_le_pi_norm (x - x0) e
      simpa [hx0] using this
  rw [hn, hψx0, sub_zero, Real.norm_eq_abs] at hmv
  exact hmv


theorem volume_flatHalfCube_lt_top (e : Fin d) (m : ℤ) : volume (flatHalfCube e m) < ⊤ :=
  (measure_mono (flatHalfCube_subset e m)).trans_lt
    (isBounded_openCubeSet (originCube d m)).measure_lt_top

instance isFiniteMeasure_restrict_flatHalfCube (e : Fin d) (m : ℤ) :
    IsFiniteMeasure (volume.restrict (flatHalfCube e m)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_flatHalfCube_lt_top e m⟩

theorem tsupport_hcCut_mul_subset {e : Fin d} {m : ℤ} {δ : ℝ} (hδ : 0 < δ) {ψ : Vec d → ℝ}
    (hs : tsupport ψ ⊆ openCubeSet (originCube d m)) :
    tsupport (fun x => hcCut e δ x * ψ x) ⊆ flatHalfCube e m := by
  intro x hx
  have h1 : x ∈ tsupport ψ := tsupport_mul_subset_right hx
  have h2 : x ∈ tsupport (hcCut e δ) := tsupport_mul_subset_left hx
  refine ⟨hs h1, ?_⟩
  have : tsupport (hcCut e δ) ⊆ {y : Vec d | δ ≤ y e} := by
    refine closure_minimal (fun y hy => ?_) (isClosed_le continuous_const (continuous_apply e))
    by_contra hlt
    have : y e ≤ δ := le_of_lt (not_le.1 hlt)
    exact hy (hcCut_of_le hδ this)
  have := this h2
  simp only [Set.mem_ofPred_eq] at this ⊢
  linarith only [this, hδ]


/-- The gradient of a smooth function as a vector field. -/
noncomputable def hcGrad (ψ : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ ψ x (basisVec i)

theorem memLp_hcGrad_apply {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (U : Set (Vec d)) (i : Fin d) :
    MemLp (fun x => hcGrad ψ x i) 2 (volume.restrict U) :=
  flatW2p_memLp_two_of_continuous
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply (𝕜 := ℝ) (basisVec i))

theorem hc_vecDot_grad_cut (e : Fin d) (δ : ℝ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (K : Vec d → Vec d) (x : Vec d) :
    vecDot (K x) (hcGrad (fun y => hcCut e δ y * ψ y) x) =
      hcCut e δ x * vecDot (K x) (hcGrad ψ x) + (ψ x * hcCutDeriv e δ x) * K x e := by
  have h1 : DifferentiableAt ℝ (hcCut e δ) x :=
    ((contDiff_hcCut e δ).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
  have hg : ∀ i, hcGrad (fun y => hcCut e δ y * ψ y) x i =
      hcCut e δ x * hcGrad ψ x i + ψ x * (if i = e then hcCutDeriv e δ x else 0) := by
    intro i
    unfold hcGrad
    rw [fderiv_fun_mul h1 h2]
    simp only [add_apply, smul_apply, smul_eq_mul, fderiv_hcCut_apply e δ x i]
  unfold vecDot
  simp_rw [hg, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; unfold hcGrad; ring
  · simp [mul_ite, Finset.sum_ite_eq']
    ring


theorem hc_integrable_vecDot_grad {e : Fin d} {m : ℤ} {K : Vec d → Vec d}
    (hK : ∀ i, MemLp (fun x => K x i) 2 (volume.restrict (flatHalfCube e m))) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => vecDot (K x) (hcGrad ψ x)) (volume.restrict (flatHalfCube e m)) := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ =>
    (hK i).integrable_mul (memLp_hcGrad_apply hψ hc _ i)

theorem hc_cut_identity (e : Fin d) (m : ℤ) {K : Vec d → Vec d} {f : Vec d → ℝ}
    (hK : ∀ i, MemLp (fun x => K x i) 2 (volume.restrict (flatHalfCube e m)))
    (hf : MemLp f 2 (volume.restrict (flatHalfCube e m)))
    (hid : ∀ χ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (K x) (χ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, f x * χ.toH1Function.toFun x)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ openCubeSet (originCube d m)) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in flatHalfCube e m, hcCut e δ x * (vecDot (K x) (hcGrad ψ x) - f x * ψ x)) +
      ∫ x in flatHalfCube e m, (ψ x * hcCutDeriv e δ x) * K x e = 0 := by
  set D := flatHalfCube e m with hD
  set μ := volume.restrict D with hμ
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun x => hcCut e δ x * ψ x) := (contDiff_hcCut e δ).mul hψ
  have hχc : HasCompactSupport (fun x => hcCut e δ x * ψ x) := hc.mul_left
  let X : H10Function D := H10Function.ofContDiff (isOpen_flatHalfCube e m) hχ hχc
    (tsupport_hcCut_mul_subset hδ hs)
  have hX := hid X
  have hXgrad : ∀ x, X.toH1Function.grad x = hcGrad (fun y => hcCut e δ y * ψ y) x := fun x => rfl
  have hXfun : ∀ x, X.toH1Function.toFun x = hcCut e δ x * ψ x := fun x => rfl
  simp only [hXgrad, hXfun, hc_vecDot_grad_cut e δ hψ] at hX
  -- integrability
  have hU1 : Integrable (fun x => vecDot (K x) (hcGrad ψ x)) μ := hc_integrable_vecDot_grad hK hψ hc
  have hψ2 : MemLp ψ 2 μ := flatW2p_memLp_two_of_continuous hψ.continuous hc
  have hU2 : Integrable (fun x => f x * ψ x) μ := hf.integrable_mul hψ2
  have hηm : AEStronglyMeasurable (hcCut e δ) μ := (contDiff_hcCut e δ).continuous.aestronglyMeasurable
  have hηb : ∀ᵐ x ∂μ, ‖hcCut e δ x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcCut_nonneg e δ x)]; exact hcCut_le_one e δ x
  have hI1 : Integrable (fun x => hcCut e δ x * vecDot (K x) (hcGrad ψ x)) μ := hU1.bdd_mul hηm hηb
  have hI2 : Integrable (fun x => hcCut e δ x * (f x * ψ x)) μ := hU2.bdd_mul hηm hηb
  have hLHS : Integrable (fun x => vecDot (K x) (hcGrad (fun y => hcCut e δ y * ψ y) x)) μ :=
    hc_integrable_vecDot_grad hK hχ hχc
  have hT : Integrable (fun x => (ψ x * hcCutDeriv e δ x) * K x e) μ := by
    have := hLHS.sub hI1
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hc_vecDot_grad_cut e δ hψ]
    ring
  rw [integral_add hI1 hT] at hX
  have e2 : (fun x => f x * (hcCut e δ x * ψ x)) = fun x => hcCut e δ x * (f x * ψ x) := by
    funext x; ring
  rw [e2] at hX
  have e3 : (fun x => hcCut e δ x * (vecDot (K x) (hcGrad ψ x) - f x * ψ x)) =
      fun x => hcCut e δ x * vecDot (K x) (hcGrad ψ x) - hcCut e δ x * (f x * ψ x) := by
    funext x; ring
  rw [e3, integral_sub hI1 hI2]
  linarith only [hX]


/-- **The identity extends from `H¹₀` of the half cube to smooth functions vanishing on the flat
face.** -/
theorem hc_tail_identity (e : Fin d) (m : ℤ) {K : Vec d → Vec d} {f : Vec d → ℝ}
    (hK : ∀ i, MemLp (fun x => K x i) 2 (volume.restrict (flatHalfCube e m)))
    (hf : MemLp f 2 (volume.restrict (flatHalfCube e m)))
    (hid : ∀ χ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (K x) (χ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, f x * χ.toH1Function.toFun x)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ openCubeSet (originCube d m)) (h0 : ∀ x : Vec d, x e = 0 → ψ x = 0) :
    ∫ x in flatHalfCube e m, vecDot (K x) (hcGrad ψ x) = ∫ x in flatHalfCube e m, f x * ψ x := by
  set D := flatHalfCube e m with hD
  set μ := volume.restrict D with hμ
  obtain ⟨M, hM0, hM⟩ := hc_abs_le_of_vanish hψ hc e h0
  obtain ⟨B, hB0, hB⟩ := hc_exists_bound_deriv_smoothTransition
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by simp only [hδdef]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ x : Vec d, 0 < x e → ∀ᶠ n in atTop, 2 * δ n < x e := by
    intro x hx
    have := hδlim.const_mul 2
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 (x e) hx
  set W : Vec d → ℝ := fun x => vecDot (K x) (hcGrad ψ x) - f x * ψ x with hW
  have hU1 : Integrable (fun x => vecDot (K x) (hcGrad ψ x)) μ := hc_integrable_vecDot_grad hK hψ hc
  have hψ2 : MemLp ψ 2 μ := flatW2p_memLp_two_of_continuous hψ.continuous hc
  have hU2 : Integrable (fun x => f x * ψ x) μ := hf.integrable_mul hψ2
  have hWint : Integrable W μ := hU1.sub hU2
  have hZ : Integrable (fun x => K x e) μ := (hK e).integrable (by norm_num)
  have hid_n : ∀ n, (∫ x in D, hcCut e (δ n) x * W x) +
      ∫ x in D, (ψ x * hcCutDeriv e (δ n) x) * K x e = 0 := fun n =>
    hc_cut_identity e m hK hf hid hψ hc hs (hδpos n)
  -- first limit
  have hA : Tendsto (fun n => ∫ x in D, hcCut e (δ n) x * W x) atTop (𝓝 (∫ x in D, W x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖W x‖) (fun n => ?_) hWint.norm
      (fun n => ?_) ?_
    · exact ((contDiff_hcCut e (δ n)).continuous.aestronglyMeasurable).mul hWint.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hcCut_nonneg e _ x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcCut_le_one e _ x)
    · filter_upwards [ae_restrict_mem (measurableSet_flatHalfCube e m)] with x hx
      have hx' : 0 < x e := hx.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx'] with n hn
      rw [hcCut_of_ge (hδpos n) hn.le, one_mul]
  -- second limit
  have hT : Tendsto (fun n => ∫ x in D, (ψ x * hcCutDeriv e (δ n) x) * K x e) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => (ψ x * hcCutDeriv e (δ n) x) * K x e) (f := fun _ => (0 : ℝ))
      (fun x => 2 * M * B * ‖K x e‖) (fun n => ?_) (hZ.norm.const_mul _) (fun n => ?_) ?_
    · simpa using this
    · have hc1 : Continuous (fun x : Vec d => ψ x * hcCutDeriv e (δ n) x) := by
        refine hψ.continuous.mul ?_
        unfold hcCutDeriv
        exact (((Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)).comp
          (by fun_prop : Continuous fun x : Vec d => x e / δ n - 1)).div_const _
      exact hc1.aestronglyMeasurable.mul hZ.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_flatHalfCube e m)] with x hx
      have hx' : 0 < x e := hx.2
      rw [norm_mul, Real.norm_eq_abs]
      calc |ψ x * hcCutDeriv e (δ n) x| * ‖K x e‖ ≤ (2 * M * B) * ‖K x e‖ :=
            mul_le_mul_of_nonneg_right (abs_mul_hcCutDeriv_le (hδpos n) hB hM0 (hM x) hx')
              (norm_nonneg _)
        _ = 2 * M * B * ‖K x e‖ := rfl
    · filter_upwards [ae_restrict_mem (measurableSet_flatHalfCube e m)] with x hx
      have hx' : 0 < x e := hx.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx'] with n hn
      rw [hcCutDeriv_eq_zero_of_ge (hδpos n) hn]; simp
  have hlim : Tendsto (fun n => ∫ x in D, hcCut e (δ n) x * W x) atTop (𝓝 0) := by
    have : ∀ n, (∫ x in D, hcCut e (δ n) x * W x) =
        -∫ x in D, (ψ x * hcCutDeriv e (δ n) x) * K x e := fun n => by linarith only [hid_n n]
    simp_rw [this]
    simpa using hT.neg
  have hW0 : ∫ x in D, W x = 0 := tendsto_nhds_unique hA hlim
  rw [hW, integral_sub hU1 hU2] at hW0
  linarith only [hW0]

end SuperdiffusionCLT.Section7
