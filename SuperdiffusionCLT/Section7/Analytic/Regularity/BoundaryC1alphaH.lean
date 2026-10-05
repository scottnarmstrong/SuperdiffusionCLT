/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaG

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# A scale-covariant cutoff with second derivative bounds

`r3c_cutS z₀ λ x = χ₀ ((x - z₀)/λ)` for the fixed unit-scale box cutoff `χ₀`: equal to `1` on the box
of radius `λ/4` around `z₀`, supported in the box of radius `5λ/16`, with `|∇χ| ≤ G₁/λ` and
`|∇²χ| ≤ G₂/λ²` for constants depending only on `d`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The unit-scale cutoff. -/
noncomputable def r3c_cut0 (d : ℕ) : Vec d → ℝ := p12_cut (0 : Vec d) 1 1 1

/-- The cutoff at scale `lam` around `z₀`. -/
noncomputable def r3c_cutS (z₀ : Vec d) (lam : ℝ) (x : Vec d) : ℝ := r3c_cut0 d (lam⁻¹ • (x - z₀))

theorem r3c_hasFDerivAt_scaled {h : Vec d → ℝ} (hh : Differentiable ℝ h) (z₀ : Vec d) (c : ℝ)
    (x : Vec d) :
    HasFDerivAt (fun y => h (c • (y - z₀))) (c • fderiv ℝ h (c • (x - z₀))) x := by
  have h1 : HasFDerivAt (fun y : Vec d => c • (y - z₀)) (c • ContinuousLinearMap.id ℝ (Vec d)) x :=
    ((hasFDerivAt_id x).sub_const z₀).const_smul c
  have h2 := (hh (c • (x - z₀))).hasFDerivAt.comp x h1
  have e1 : (c • fderiv ℝ h (c • (x - z₀))) =
      fderiv ℝ h (c • (x - z₀)) ∘L (c • ContinuousLinearMap.id ℝ (Vec d)) := by
    ext v; simp
  rw [e1]
  exact h2

theorem r3c_fderiv_scaled {h : Vec d → ℝ} (hh : Differentiable ℝ h) (z₀ : Vec d) (c : ℝ)
    (x v : Vec d) :
    fderiv ℝ (fun y => h (c • (y - z₀))) x v = c * fderiv ℝ h (c • (x - z₀)) v := by
  rw [(r3c_hasFDerivAt_scaled hh z₀ c x).fderiv]
  simp

theorem r3c_cut0_contDiff : ContDiff ℝ (⊤ : ℕ∞) (r3c_cut0 d) := p12_cut_contDiff _ _ _ _

theorem r3c_cutS_contDiff (z₀ : Vec d) (lam : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (r3c_cutS z₀ lam) :=
  r3c_cut0_contDiff.comp ((contDiff_id.sub contDiff_const).const_smul lam⁻¹)

theorem r3c_cutS_01 (z₀ : Vec d) (lam : ℝ) (x : Vec d) :
    0 ≤ r3c_cutS z₀ lam x ∧ r3c_cutS z₀ lam x ≤ 1 := p12_cut_01 _ _ _ _ _

theorem r3c_cutS_eq_one (z₀ : Vec d) {lam : ℝ} (hl : 0 < lam) {x : Vec d}
    (hx : ∀ i, |x i - z₀ i| ≤ lam / 4) : r3c_cutS z₀ lam x = 1 := by
  refine p12_cut_eq_one (0 : Vec d) one_pos 1 1 fun i => ?_
  have hr : p12_rad 1 1 1 = 1 / 4 := by unfold p12_rad; norm_num
  rw [hr]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, sub_zero, smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.2 hl)]
  have := hx i
  calc lam⁻¹ * |x i - z₀ i| ≤ lam⁻¹ * (lam / 4) := mul_le_mul_of_nonneg_left this (inv_pos.2 hl).le
    _ = 1 / 4 := by field_simp

theorem r3c_cutS_tsupport (z₀ : Vec d) {lam : ℝ} (hl : 0 < lam) :
    tsupport (r3c_cutS z₀ lam) ⊆ {x | ∀ i, |x i - z₀ i| ≤ 5 * lam / 16} := by
  have hH : tsupport (r3c_cutS z₀ lam) =
      (fun y => lam⁻¹ • (y - z₀)) ⁻¹' tsupport (r3c_cut0 d) := by
    let hm : Vec d ≃ₜ Vec d :=
      (Homeomorph.subRight z₀).trans (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hl.ne'))
    exact tsupport_comp_eq_preimage (r3c_cut0 d) hm
  rw [hH]
  intro x hx i
  have h := p12_cut_tsupport (0 : Vec d) one_pos 1 1 hx
  have hr : p12_rad 1 1 1 = 1 / 4 := by unfold p12_rad; norm_num
  rw [hr, Set.mem_Icc] at h
  have h1 := h.1 i
  have h2 := h.2 i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul] at h1 h2
  have hl' : 0 < lam⁻¹ := inv_pos.2 hl
  have h3 : -(5 / 16 : ℝ) ≤ lam⁻¹ * (x i - z₀ i) := by norm_num at h1 ⊢; linarith only [h1]
  have h4 : lam⁻¹ * (x i - z₀ i) ≤ 5 / 16 := by norm_num at h2 ⊢; linarith only [h2]
  have h5 : x i - z₀ i = lam * (lam⁻¹ * (x i - z₀ i)) := by field_simp
  rw [abs_le]
  constructor
  · rw [h5]; nlinarith only [h3, hl]
  · rw [h5]; nlinarith only [h4, hl]

theorem r3c_cutS_hasCompactSupport (z₀ : Vec d) {lam : ℝ} (hl : 0 < lam) :
    HasCompactSupport (r3c_cutS z₀ lam) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := fun i => z₀ i - 5 * lam / 16)
    (b := fun i => z₀ i + 5 * lam / 16)) (isClosed_tsupport _) fun x hx => ?_
  have := r3c_cutS_tsupport z₀ hl hx
  rw [Set.mem_Icc]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.1 (this i)).1
    show z₀ i - 5 * lam / 16 ≤ x i
    linarith only [this]
  · have := (abs_le.1 (this i)).2
    show x i ≤ z₀ i + 5 * lam / 16
    linarith only [this]


theorem r3c_cut0_hasCompactSupport : HasCompactSupport (r3c_cut0 d) :=
  p12_cut_hasCompactSupport (0 : Vec d) one_pos 1 1

/-- Constants of the first and second derivative bounds of the unit cutoff. -/
theorem r3c_cut0_bounds (d : ℕ) : ∃ G₁ G₂ : ℝ, 0 ≤ G₁ ∧ 0 ≤ G₂ ∧
    (∀ y i, |p12_grad (r3c_cut0 d) y i| ≤ G₁) ∧
    (∀ y j k, |fderiv ℝ (fun z => p12_grad (r3c_cut0 d) z j) y (basisVec k)| ≤ G₂) := by
  have hc := r3c_cut0_hasCompactSupport (d := d)
  have h1 : ∀ i : Fin d, ∃ B : ℝ, ∀ y, |p12_grad (r3c_cut0 d) y i| ≤ B := fun i =>
    r3c_bdd_of_cpt (r3c_contDiff_grad_apply r3c_cut0_contDiff i).continuous
      (by simpa [p12_grad] using hc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have h2 : ∀ jk : Fin d × Fin d, ∃ B : ℝ, ∀ y,
      |fderiv ℝ (fun z => p12_grad (r3c_cut0 d) z jk.1) y (basisVec jk.2)| ≤ B := fun jk => by
    have hs := r3c_contDiff_grad_apply (r3c_cut0_contDiff (d := d)) jk.1
    refine r3c_bdd_of_cpt ?_ ?_
    · simpa using (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    · have hk : HasCompactSupport (fun z => p12_grad (r3c_cut0 d) z jk.1) := by
        simpa [p12_grad] using hc.fderiv_apply (𝕜 := ℝ) (basisVec jk.1)
      simpa using hk.fderiv_apply (𝕜 := ℝ) (basisVec jk.2)
  choose B1 hB1 using h1
  choose B2 hB2 using h2
  refine ⟨∑ i, |B1 i|, ∑ jk, |B2 jk|, Finset.sum_nonneg fun i _ => abs_nonneg _,
    Finset.sum_nonneg fun i _ => abs_nonneg _, fun y i => (hB1 i y).trans ((le_abs_self _).trans ?_),
    fun y j k => (hB2 (j, k) y).trans ((le_abs_self _).trans ?_)⟩
  · exact Finset.single_le_sum (f := fun i => |B1 i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  · exact Finset.single_le_sum (f := fun jk => |B2 jk|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ (j, k))

theorem r3c_grad_cutS (z₀ : Vec d) (lam : ℝ) (x : Vec d) (i : Fin d) :
    p12_grad (r3c_cutS z₀ lam) x i =
      lam⁻¹ * p12_grad (r3c_cut0 d) (lam⁻¹ • (x - z₀)) i := by
  unfold p12_grad r3c_cutS
  exact r3c_fderiv_scaled (r3c_cut0_contDiff.differentiable (by simp)) z₀ lam⁻¹ x (basisVec i)

/-- First and second derivative bounds of the scaled cutoff. -/
theorem r3c_cutS_bounds (d : ℕ) : ∃ G₁ G₂ : ℝ, 0 ≤ G₁ ∧ 0 ≤ G₂ ∧ ∀ (z₀ : Vec d) (lam : ℝ), 0 < lam →
    (∀ x i, |p12_grad (r3c_cutS z₀ lam) x i| ≤ G₁ / lam) ∧
    (∀ x j k, |fderiv ℝ (fun y => p12_grad (r3c_cutS z₀ lam) y j) x (basisVec k)| ≤ G₂ / lam ^ 2) := by
  obtain ⟨G₁, G₂, hG1, hG2, hb1, hb2⟩ := r3c_cut0_bounds d
  refine ⟨G₁, G₂, hG1, hG2, fun z₀ lam hl => ⟨fun x i => ?_, fun x j k => ?_⟩⟩
  · rw [r3c_grad_cutS, abs_mul, abs_of_pos (inv_pos.2 hl), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hb1 _ i) (inv_pos.2 hl).le
  · have hGj : Differentiable ℝ (fun z => p12_grad (r3c_cut0 d) z j) :=
      (r3c_contDiff_grad_apply (r3c_cut0_contDiff (d := d)) j).differentiable (by simp)
    have hfun : (fun y => p12_grad (r3c_cutS z₀ lam) y j) =
        fun y => lam⁻¹ * (fun z => p12_grad (r3c_cut0 d) z j) (lam⁻¹ • (y - z₀)) :=
      funext fun y => r3c_grad_cutS z₀ lam y j
    rw [hfun, ((r3c_hasFDerivAt_scaled hGj z₀ lam⁻¹ x).const_mul lam⁻¹).fderiv]
    simp only [smul_apply, smul_eq_mul]
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hl)]
    calc lam⁻¹ * (lam⁻¹ * |fderiv ℝ (fun z => p12_grad (r3c_cut0 d) z j) (lam⁻¹ • (x - z₀)) (basisVec k)|)
        ≤ lam⁻¹ * (lam⁻¹ * G₂) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb2 _ j k) (inv_pos.2 hl).le)
            (inv_pos.2 hl).le
      _ = G₂ / lam ^ 2 := by field_simp

end SuperdiffusionCLT.Section7
