/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox

/-!
# Norms on origin cubes

Triangle inequality, scale monotonicity, the best-constant property of the mean, and the
algebra of the flatness `cubeFlat`.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem e0b_isProb (n : ℕ) :
    IsProbabilityMeasure (normalizedCubeMeasure (originCube d (n : ℤ))) :=
  ⟨normalizedCubeMeasure_apply_univ _⟩

theorem e0b_sq {μ : Measure (Vec d)} [IsProbabilityMeasure μ] {f : Vec d → ℝ}
    (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h1 : ∫ x, ‖f x‖ ^ (ENNReal.toReal 2) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    congr 1
    ext x
    simp [Real.norm_eq_abs]
  rw [h1, ENNReal.toReal_ofReal (by positivity)]
  have h2 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have h3 : (ENNReal.toReal 2)⁻¹ = (1 / 2 : ℝ) := by simp
  rw [h3, ← Real.sqrt_eq_rpow, Real.sq_sqrt h2]

theorem e0b_expand {μ : Measure (Vec d)} [IsProbabilityMeasure μ] {f : Vec d → ℝ}
    (hf : MemLp f 2 μ) (c : ℝ) :
    ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - 2 * c * ∫ x, f x ∂μ + c ^ 2 := by
  have h1 : Integrable f μ := hf.integrable one_le_two
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have h3 : Integrable (fun x => 2 * c * f x) μ := h1.const_mul _
  have : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 := by
    ext x; ring
  rw [this, integral_add (f := fun x => f x ^ 2 - 2 * c * f x) (g := fun _ => c ^ 2)
    (h2.sub h3) (integrable_const _), integral_sub h2 h3, integral_const_mul]
  simp

theorem e0b_var {μ : Measure (Vec d)} [IsProbabilityMeasure μ] {f : Vec d → ℝ}
    (hf : MemLp f 2 μ) (c : ℝ) :
    (eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ).toReal ≤
      (eLpNorm (fun x => f x - c) 2 μ).toReal := by
  have hm : MemLp (fun x => f x - ∫ y, f y ∂μ) 2 μ := hf.sub (memLp_const _)
  have hc : MemLp (fun x => f x - c) 2 μ := hf.sub (memLp_const _)
  refine le_of_sq_le_sq ?_ ENNReal.toReal_nonneg
  rw [e0b_sq hm, e0b_sq hc, e0b_expand hf, e0b_expand hf]
  nlinarith only [sq_nonneg ((∫ x, f x ∂μ) - c)]

theorem e0b_memLp_step {k : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ)))) :
    MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) ∧
    eLpNorm f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ))) := by
  have hk : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
  have hsub := HarmonicApprox.originCube_pred_cubeSet_subset (d := d) ((k + 1 : ℕ) : ℤ)
  have hrat := HarmonicApprox.cubeVolume_originCube_ratio (d := d) ((k + 1 : ℕ) : ℤ)
  rw [hk] at hsub hrat
  have hle := HarmonicApprox.eLpNorm_normalizedCubeMeasure_le hsub f hf.aestronglyMeasurable
  rw [hrat] at hle
  have hlt : eLpNorm f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) < ⊤ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hf.eLpNorm_lt_top)
  exact ⟨hlt, hle⟩

theorem e0b_cubeFlat_eq (n : ℕ) (f : Vec d → ℝ) :
    cubeFlat n f = ((3 : ℝ)⁻¹) ^ n *
      (eLpNorm (fun x => f x - ∫ y, f y ∂(normalizedCubeMeasure (originCube d (n : ℤ)))) 2
        (normalizedCubeMeasure (originCube d (n : ℤ)))).toReal := by
  unfold cubeFlat cubeL2 cubeLpNorm
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]

theorem cubeL2_nonneg (n : ℕ) (f : Vec d → ℝ) : 0 ≤ cubeL2 n f :=
  ENNReal.toReal_nonneg

theorem cubeFlat_nonneg (n : ℕ) (f : Vec d → ℝ) : 0 ≤ cubeFlat n f :=
  mul_nonneg (by positivity) (cubeL2_nonneg _ _)

theorem cubeL2_congr_ae {n : ℕ} {f g : Vec d → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure (originCube d (n : ℤ))] g) : cubeL2 n f = cubeL2 n g := by
  unfold cubeL2 cubeLpNorm
  rw [eLpNorm_congr_ae h]

theorem cubeFlat_congr_ae {n : ℕ} {f g : Vec d → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure (originCube d (n : ℤ))] g) : cubeFlat n f = cubeFlat n g := by
  rw [e0b_cubeFlat_eq, e0b_cubeFlat_eq, integral_congr_ae h]
  congr 2
  refine eLpNorm_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

theorem cubeFlat_add_const {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (c : ℝ) :
    cubeFlat n (fun x => f x + c) = cubeFlat n f := by
  have := e0b_isProb (d := d) n
  rw [e0b_cubeFlat_eq, e0b_cubeFlat_eq]
  have hi : Integrable f (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hf.integrable one_le_two
  rw [integral_add hi (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  congr 3
  ext x; ring

theorem cubeL2_add_le {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeL2 n (fun x => f x + g x) ≤ cubeL2 n f + cubeL2 n g := by
  unfold cubeL2 cubeLpNorm
  have h := eLpNorm_add_le (μ := normalizedCubeMeasure (originCube d (n : ℤ))) (f := f) (g := g)
    (p := 2) one_le_two
  have hfin : eLpNorm f 2 (normalizedCubeMeasure (originCube d (n : ℤ))) +
      eLpNorm g 2 (normalizedCubeMeasure (originCube d (n : ℤ))) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.ne, hg.ne⟩
  rw [← ENNReal.toReal_add hf.ne hg.ne]
  exact ENNReal.toReal_mono hfin h

theorem e0b_step {k : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ)))) :
    cubeL2 k f ^ 2 ≤ (3 : ℝ) ^ d * cubeL2 (k + 1) f ^ 2 := by
  obtain ⟨_, hle⟩ := e0b_memLp_step hf
  unfold cubeL2 cubeLpNorm
  have hfin : ENNReal.ofReal ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
      eLpNorm f 2 (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ))) ≠ ⊤ :=
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hf).ne
  have h := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)] at h
  have h0 : 0 ≤ (eLpNorm f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))).toReal :=
    ENNReal.toReal_nonneg
  have h2 := pow_le_pow_left₀ h0 h 2
  have h3 : (((3 : ℝ) ^ d) ^ (1 / 2 : ℝ)) ^ 2 = (3 : ℝ) ^ d := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  rwa [mul_pow, h3] at h2

theorem cubeL2_mono_scale [NeZero d] {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeL2 l f ^ 2 * (3 : ℝ) ^ (d * l) ≤ cubeL2 k f ^ 2 * (3 : ℝ) ^ (d * k) := by
  induction k, hlk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    have hk := (e0b_memLp_step hf).1
    have h1 := ih hk
    have h2 := e0b_step hf
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (d * k) := by positivity
    have h4 : (3 : ℝ) ^ (d * (k + 1)) = (3 : ℝ) ^ d * (3 : ℝ) ^ (d * k) := by
      rw [mul_add, mul_one, pow_add, mul_comm]
    rw [h4]
    calc cubeL2 l f ^ 2 * (3 : ℝ) ^ (d * l) ≤ cubeL2 k f ^ 2 * (3 : ℝ) ^ (d * k) := h1
      _ ≤ ((3 : ℝ) ^ d * cubeL2 (k + 1) f ^ 2) * (3 : ℝ) ^ (d * k) :=
          mul_le_mul_of_nonneg_right h2 h3.le
      _ = _ := by ring

theorem cubeFlat_le_of_sub_const [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (c : ℝ) :
    cubeFlat n f ≤ ((3 : ℝ)⁻¹) ^ n * cubeL2 n (fun x => f x - c) := by
  have := e0b_isProb (d := d) n
  rw [e0b_cubeFlat_eq]
  exact mul_le_mul_of_nonneg_left (e0b_var hf c) (by positivity)

theorem cubeL2_const_mul (n : ℕ) (c : ℝ) (f : Vec d → ℝ) :
    cubeL2 n (fun x => c * f x) = |c| * cubeL2 n f := by
  unfold cubeL2 cubeLpNorm
  have : (fun x => c * f x) = c • f := rfl
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

theorem cubeFlat_const_mul [NeZero d] (n : ℕ) (c : ℝ) (f : Vec d → ℝ) :
    cubeFlat n (fun x => c * f x) = |c| * cubeFlat n f := by
  have h : cubeAverage (originCube d (n : ℤ)) (fun x => c * f x) =
      c * cubeAverage (originCube d (n : ℤ)) f := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure,
      integral_const_mul]
  unfold cubeFlat
  rw [h]
  have : (fun x => c * f x - c * cubeAverage (originCube d (n : ℤ)) f) =
      fun x => c * (f x - cubeAverage (originCube d (n : ℤ)) f) := by
    ext x; ring
  rw [this, cubeL2_const_mul]
  ring

theorem cubeFlat_add_le [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeFlat n (fun x => f x + g x) ≤ cubeFlat n f + cubeFlat n g := by
  have := e0b_isProb (d := d) n
  have h : cubeAverage (originCube d (n : ℤ)) (fun x => f x + g x) =
      cubeAverage (originCube d (n : ℤ)) f + cubeAverage (originCube d (n : ℤ)) g := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      integral_add (hf.integrable one_le_two) (hg.integrable one_le_two)]
  unfold cubeFlat
  rw [h, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have : (fun x => f x + g x - (cubeAverage (originCube d (n : ℤ)) f +
      cubeAverage (originCube d (n : ℤ)) g)) =
      fun x => (f x - cubeAverage (originCube d (n : ℤ)) f) +
        (g x - cubeAverage (originCube d (n : ℤ)) g) := by
    ext x; ring
  rw [this]
  exact cubeL2_add_le (hf.sub (memLp_const _)) (hg.sub (memLp_const _))

theorem e0b_flat_sq (n : ℕ) (f : Vec d → ℝ) (c : ℝ) :
    (((3 : ℝ)⁻¹) ^ n * cubeL2 n (fun x => f x - c)) ^ 2 * (3 : ℝ) ^ ((d + 2) * n) =
      cubeL2 n (fun x => f x - c) ^ 2 * (3 : ℝ) ^ (d * n) := by
  have h : (3 : ℝ) ^ ((d + 2) * n) = (3 : ℝ) ^ (d * n) * ((3 : ℝ) ^ n) ^ 2 := by
    rw [add_mul, pow_add]; ring
  have h2 : ((3 : ℝ)⁻¹) ^ n * (3 : ℝ) ^ n = 1 := by
    rw [← mul_pow]; simp
  calc _ = cubeL2 n (fun x => f x - c) ^ 2 * (3 : ℝ) ^ (d * n) *
        (((3 : ℝ)⁻¹) ^ n * (3 : ℝ) ^ n) ^ 2 := by rw [h]; ring
    _ = _ := by rw [h2]; ring

theorem cubeFlat_mono_scale [NeZero d] {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeFlat l f ^ 2 * (3 : ℝ) ^ ((d + 2) * l) ≤ cubeFlat k f ^ 2 * (3 : ℝ) ^ ((d + 2) * k) := by
  have hl : MemLp f 2 (normalizedCubeMeasure (originCube d (l : ℤ))) := by
    induction k, hlk using Nat.le_induction with
    | base => exact hf
    | succ k _ ih => exact ih (e0b_memLp_step hf).1
  set c := cubeAverage (originCube d (k : ℤ)) f
  have h1 := cubeFlat_le_of_sub_const hl c
  have h2 := pow_le_pow_left₀ (cubeFlat_nonneg l f) h1 2
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ ((d + 2) * l))
  rw [e0b_flat_sq] at h3
  have h4 := cubeL2_mono_scale hlk (f := fun x => f x - c) (hf.sub (memLp_const _))
  have h5 : cubeFlat k f ^ 2 * (3 : ℝ) ^ ((d + 2) * k) =
      cubeL2 k (fun x => f x - c) ^ 2 * (3 : ℝ) ^ (d * k) := e0b_flat_sq k f c
  rw [h5]
  exact h3.trans h4

/-- Witness: both `f = 0` and `f = 1` have zero flatness. -/
example [NeZero d] (n : ℕ) : cubeFlat n (fun _ : Vec d => (0 : ℝ)) = 0 ∧
    cubeFlat n (fun _ : Vec d => (1 : ℝ)) = 0 := by
  have := e0b_isProb (d := d) n
  have h : ∀ c : ℝ, cubeFlat n (fun _ : Vec d => c) = 0 := by
    intro c
    rw [e0b_cubeFlat_eq]
    simp
  exact ⟨h 0, h 1⟩

/-- Witness for the scale inequality with `f = 1`. -/
example [NeZero d] {l k : ℕ} (hlk : l ≤ k) :
    cubeFlat l (fun _ : Vec d => (1 : ℝ)) ^ 2 * (3 : ℝ) ^ ((d + 2) * l) ≤
      cubeFlat k (fun _ : Vec d => (1 : ℝ)) ^ 2 * (3 : ℝ) ^ ((d + 2) * k) :=
  have := e0b_isProb (d := d) k
  cubeFlat_mono_scale hlk (memLp_const _)

end SuperdiffusionCLT.Section6
