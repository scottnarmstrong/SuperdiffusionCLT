/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryCasesB
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorOrigin
public import SuperdiffusionCLT.Section7.Analytic.Geometry.CubeFormFlatnessB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Analytic.ElementaryB
public import SuperdiffusionCLT.Section6.Prereq.GammaMax

/-!
# The boundary estimate in the frame of the centre: helpers

Monotonicity of the blocks in their constants, the window `B log m' · δ_{m'} ≤ c`, and the
bridges between the translated dilate `translateSet (-y) (t • U)` and the data of the uniform
`C^{1,1}` class.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The interior estimate is monotone in its constant. -/
theorem lip_bdry_origin_intAt_mono {a : CoeffField d} {nu s C C' : ℝ} {z : Vec d} {n m : ℕ}
    (h : LipIntAt a nu s C z n m) (hs : 0 < s) (hCC : C ≤ C') : LipIntAt a nu s C' z n m := by
  intro f F u hu hF hf
  refine (h f F u hu hF hf).trans ?_
  have h1 : 0 ≤ ((3 : ℝ)⁻¹) ^ m * lipL2 (shiftCube z (m : ℤ))
      (fun x => u.toFun x - ⨍ w in shiftCube z (m : ℤ), u.toFun w) +
      s⁻¹ * (3 : ℝ) ^ m * F := by
    have : 0 ≤ lipL2 (shiftCube z (m : ℤ))
        (fun x => u.toFun x - ⨍ w in shiftCube z (m : ℤ), u.toFun w) := ENNReal.toReal_nonneg
    positivity
  exact mul_le_mul_of_nonneg_right hCC h1

/-- The `L²` block is monotone in the parameter `δ`. -/
theorem LipL2Block.mono_delta {a : CoeffField d} {nu s δ δ' C : ℝ} {A k : ℕ} {V : Set (Vec d)}
    (h : LipL2Block a nu s δ C A k V) (hC : 0 ≤ C) (hδ : δ ≤ δ') :
    LipL2Block a nu s δ' C A k V := by
  intro f g u ub hu hub hg hgb
  refine (h f g u ub hu hub hg hgb).trans ?_
  have e : C * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu ≤ C * δ' * (Real.sqrt s)⁻¹ * Real.sqrt nu := by
    have h0 : 0 ≤ C * (Real.sqrt s)⁻¹ * Real.sqrt nu :=
      mul_nonneg (mul_nonneg hC (inv_nonneg.2 (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_right hδ h0]
  gcongr


/-- **The window is short**: `B log x ≤ c δ_x⁻¹` for large `x`. -/
theorem lip_bdry_origin_win {ε ρ B c : ℝ} (hε : 0 < ε) (hρ : ρ < 1) (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ L : ℝ, 4 ≤ L ∧ ∀ x : ℝ, L ≤ x → B * Real.log x ≤ c * (deltaScale ε ρ x)⁻¹ := by
  set κ : ℝ := (1 - ρ) / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith only [hρ]
  have hc' : 0 < c / (ε * (B + 1)) := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop 2 hκ0).def hc'
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max L0 4, le_max_right _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith only [hx4]
  have hxL : L0 ≤ x := (le_max_left _ _).trans hx
  have hlog1 : 1 ≤ Real.log x := a23_one_le_log hx4
  have hδ : 0 < deltaScale ε ρ x := deltaScale_pos hε (by linarith only [hx4])
  rw [← div_eq_mul_inv, le_div_iff₀ hδ]
  have hsq := hL0 x hxL
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hsq
  rw [Real.rpow_two] at hsq
  unfold deltaScale
  have hk1 : x ^ κ * x ^ (-κ) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hkm : 0 ≤ x ^ (-κ) := by positivity
  have hBl : B * Real.log x ≤ (B + 1) * Real.log x := by nlinarith only [hlog1]
  calc B * Real.log x * (ε * x ^ (-((1 - ρ) / 2)) * Real.log x)
      ≤ ((B + 1) * Real.log x) * (ε * x ^ (-κ) * Real.log x) := by
        rw [← hκ]
        exact mul_le_mul hBl le_rfl (by positivity) (by positivity)
    _ = (ε * (B + 1)) * (Real.log x ^ 2 * x ^ (-κ)) := by ring
    _ ≤ (ε * (B + 1)) * (c / (ε * (B + 1)) * x ^ κ * x ^ (-κ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hsq hkm
    _ = (ε * (B + 1) * (c / (ε * (B + 1)))) * (x ^ κ * x ^ (-κ)) := by ring
    _ = c := by rw [hk1]; field_simp

/-- The translated dilate is the image of the dilate under the translation. -/
theorem lip_bdry_origin_translateSet_eq (y : Vec d) (S : Set (Vec d)) :
    translateSet (-y) S = (fun x => x + -y) '' S := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

/-- The uniform `C^{1,1}` data of the translated dilate. -/
theorem lip_bdry_origin_uniform {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {t : ℝ} (ht : 0 < t) (y : Vec d) :
    IsUniformC11Domain (translateSet (-y) (t • U)) (t * r) M₁ (M₂ / t) (t * D) := by
  rw [lip_bdry_origin_translateSet_eq]
  exact (h.smul ht).translate (-y)

/-- The rescaled image form and the rescaled translate. -/
theorem lip_bdry_origin_image_eq (y : Vec d) (V : Set (Vec d)) (c : ℝ) :
    (fun x => c • (x - y)) '' V = c • translateSet (-y) V := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w - y, ?_, rfl⟩
    rw [mem_translateSet_iff_sub_mem]
    simpa using hw
  · rintro ⟨w, hw, rfl⟩
    rw [mem_translateSet_iff_sub_mem] at hw
    refine ⟨w + y, ?_, ?_⟩
    · simpa using hw
    · simp

/-- Membership of the centre in the translated dilate. -/
theorem lip_bdry_origin_zero_mem {y : Vec d} {S : Set (Vec d)} (h : y ∈ S) :
    (0 : Vec d) ∈ translateSet (-y) S := by
  rw [mem_translateSet_iff_sub_mem]
  simpa using h

/-- Logarithm of a maximum of two numbers `≥ 1`. -/
theorem lip_bdry_origin_log_max {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    Real.log (max X Y) = max (Real.log X) (Real.log Y) := by
  rcases le_total X Y with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log (by linarith only [hX]) h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log (by linarith only [hY]) h)]


/-- The maximum of three tails, in the logarithmic form of the scale `X₀`. -/
theorem lip_bdry_origin_bigO_max3 {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
      {A B C : ℝ} {X Y Z : Ω → ℝ}, 0 ≤ A → 0 ≤ B → 0 ≤ C → (∀ ω, 1 ≤ X ω) → (∀ ω, 1 ≤ Y ω) →
      (∀ ω, 1 ≤ Z ω) →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (X ω)) A →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (Y ω)) B →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (Z ω)) C →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (max (max (X ω) (Y ω)) (Z ω))) (Cg * (Cg * (A + B) + C)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := Section6.exists_isBigO_gammaSigma_max_two_add hρ
  refine ⟨Cg, hCg0, ?_⟩
  intro Ω _ μ _ A B C X Y Z hA hB hC hX hY hZ hXO hYO hZO
  have h1 := hCg hA hB hXO hYO
  have h2 := hCg (by positivity) hC h1 hZO
  have e : (fun ω => max (max (Real.log (X ω)) (Real.log (Y ω))) (Real.log (Z ω))) =
      fun ω => Real.log (max (max (X ω) (Y ω)) (Z ω)) := by
    funext ω
    have hXY : 1 ≤ max (X ω) (Y ω) := le_trans (hX ω) (le_max_left _ _)
    rw [lip_bdry_origin_log_max hXY (hZ ω), lip_bdry_origin_log_max (hX ω) (hY ω)]
  rw [← e]
  exact h2

/-- Translation preserves openness. -/
theorem lip_bdry_origin_isOpen_translate {S : Set (Vec d)} (hS : IsOpen S) (z : Vec d) :
    IsOpen (translateSet z S) := by
  rw [← preimage_subRight_eq_translateSet]
  exact hS.preimage (by fun_prop)

/-- Balls about `0` and about `y`, seen through the translation by `-y`. -/
theorem lip_bdry_origin_mem_ball_iff (y x : Vec d) (ρ : ℝ) :
    x ∈ Metric.ball (0 : Vec d) ρ ↔ x - (-y) ∈ Metric.ball y ρ := by
  rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_eq_norm]
  have : x - -y - y = x := by abel
  rw [this]

end SuperdiffusionCLT.Section7
