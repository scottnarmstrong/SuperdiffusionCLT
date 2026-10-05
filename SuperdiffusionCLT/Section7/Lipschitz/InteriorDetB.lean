/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Lipschitz.Iteration
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorStep
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.HarmonicAffineC
public import SuperdiffusionCLT.Section6.Engine.WindowFlat
public import SuperdiffusionCLT.Section6.Engine.Chain
public import SuperdiffusionCLT.Section6.Engine.ZeroSlopeB

/-!
# Helpers for the interior large-scale Lipschitz estimate

Slope comparison, restriction and oscillation bounds for the flatness relative to a slope, and the
restriction of a weak solution to a smaller origin cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

theorem lip_int_det_vecDot_sub (p q x : Vec d) :
    vecDot (p - q) x = vecDot p x - vecDot q x := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

theorem lip_int_det_memLp [NeZero d] {m k : ℕ} (hk : k ≤ m)
    (u : H1Function (Section6.engCube d m)) :
    MemLp u.toFun 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
  Section6.eb3_memLp_le hk (memL2On_openCubeSet_normalizedCubeMeasure u.memL2)

theorem lip_int_det_memLp_sub [NeZero d] {k : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) (p : Vec d) :
    MemLp (fun x => f x - vecDot p x) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
  hf.sub (Section6.e0c_memLp k (Section6.e0c_continuous_vecDot p))

/-- The slope comparison at one scale. -/
theorem lip_int_det_slope [NeZero d] {j : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (j : ℤ)))) (p q : Vec d) :
    Section6.engNorm p ≤ Section6.engNorm q +
      2 * Real.sqrt 3 * (Section6.cubeFlat j (fun x => f x - vecDot p x) +
        Section6.cubeFlat j (fun x => f x - vecDot q x)) := by
  have h1 := Section6.eb6a_norm_le_add' p q
  have h2 := Section6.cubeFlat_vecDot (d := d) j (p - q)
  have h3 : (fun x => vecDot (p - q) x) = fun x =>
      (f x - vecDot q x) + (-1 : ℝ) * (f x - vecDot p x) := by
    funext x; rw [lip_int_det_vecDot_sub]; ring
  have hq := lip_int_det_memLp_sub hf q
  have hp := lip_int_det_memLp_sub hf p
  have h4 := Section6.cubeFlat_add_le hq (hp.const_mul (-1 : ℝ))
  have h5 := Section6.cubeFlat_const_mul (d := d) j (-1 : ℝ) (fun x => f x - vecDot p x)
  rw [abs_neg, abs_one, one_mul] at h5
  rw [← h3] at h4
  rw [h5, h2] at h4
  have h6 : (0 : ℝ) < 2 * Real.sqrt 3 := by positivity
  have h7 : Section6.engNorm (p - q) ≤
      2 * Real.sqrt 3 * (Section6.cubeFlat j (fun x => f x - vecDot q x) +
        Section6.cubeFlat j (fun x => f x - vecDot p x)) := by
    rw [div_le_iff₀ h6] at h4
    linarith only [h4]
  linarith only [h1, h7]

/-- The restriction bound for the flatness relative to a slope. -/
theorem lip_int_det_restr [NeZero d] {j : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d ((j + 1 : ℕ) : ℤ)))) (p : Vec d) :
    Section6.cubeFlat j (fun x => f x - vecDot p x) ≤
      (3 : ℝ) ^ (d + 2) * Section6.cubeFlat (j + 1) (fun x => f x - vecDot p x) := by
  have h := Section6.cubeFlat_mono_scale (Nat.le_succ j) (lip_int_det_memLp_sub hf p)
  refine Section6.eb3_sq_to_lin (Section6.cubeFlat_nonneg _ _) (Section6.cubeFlat_nonneg _ _)
    (P := (3 : ℝ) ^ ((d + 2) * j)) (Q := (3 : ℝ) ^ (d + 2)) (by positivity)
    (one_le_pow₀ (by norm_num)) ?_
  have e : (3 : ℝ) ^ ((d + 2) * j) * (3 : ℝ) ^ (d + 2) = (3 : ℝ) ^ ((d + 2) * (j + 1)) := by
    rw [← pow_add, mul_add, mul_one]
  rw [e]
  exact h

/-- The oscillation is bounded by the flatness relative to a slope plus the slope. -/
theorem lip_int_det_osc [NeZero d] {j : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (j : ℤ)))) (p : Vec d) :
    Section6.cubeFlat j f ≤ Section6.cubeFlat j (fun x => f x - vecDot p x) +
      (2 * Real.sqrt 3)⁻¹ * Section6.engNorm p := by
  have h1 := Section6.cubeFlat_add_le (lip_int_det_memLp_sub hf p)
    (Section6.e0c_memLp j (Section6.e0c_continuous_vecDot p))
  have h2 := Section6.cubeFlat_vecDot (d := d) j p
  have h3 : (fun x => (f x - vecDot p x) + vecDot p x) = f := by funext x; ring
  rw [h3, h2] at h1
  rw [div_eq_inv_mul] at h1
  exact h1

/-- Restriction of a solution on `□_m` to `□_k`. -/
theorem lip_int_det_restrict {a : CoeffField d} {m k : ℕ} (hk : k ≤ m)
    {u : H1Function (Section6.engCube d m)} {f : Vec d → ℝ} {F : ℝ}
    (hu : IsWeakSolutionOn a (Section6.engCube d m) u f (fun _ => 0))
    (hfF : ∀ᵐ x ∂volume.restrict (Section6.engCube d m), |f x| ≤ F) :
    IsWeakSolutionOn a (Section6.engCube d k)
      (u.restrict (isOpen_openCubeSet _) (Section6.eb5a_engCube_mono hk)) f (fun _ => 0) ∧
      (∀ᵐ x ∂volume.restrict (Section6.engCube d k), |f x| ≤ F) :=
  ⟨IsWeakSolutionOn.restrict' hu (isOpen_openCubeSet _) (Section6.eb5a_engCube_mono hk),
    ae_restrict_of_ae_restrict_of_subset (Section6.eb5a_engCube_mono hk) hfF⟩

theorem lip_int_det_geom (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    ∑ k ∈ S, (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := by
  have h1 : ∑ k ∈ S, (3 : ℝ) ^ k ≤ ∑ k ∈ Finset.range m, (3 : ℝ) ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
  have h2 : ∑ k ∈ Finset.range m, (3 : ℝ) ^ k = ((3 : ℝ) ^ m - 1) / 2 := by
    rw [geom_sum_eq (by norm_num)]; norm_num
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  rw [h2] at h1
  linarith only [h1, h3]

theorem lip_int_det_reindex (δ : ℕ → ℝ) (n m k₀ : ℕ) (hk₀ : 1 ≤ k₀) (hδ : ∀ k, n ≤ k → k ≤ m → 0 ≤ δ k) :
    ∑ k ∈ Finset.Icc (n + k₀) (m - 1), δ (k + 1) ≤ ∑ k ∈ Finset.Icc n m, δ k := by
  rw [← Finset.sum_image (f := δ) (s := Finset.Icc (n + k₀) (m - 1)) (g := fun k => k + 1)
    (fun x _ y _ h => by simpa using h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => ?_)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · rw [Finset.mem_Icc] at hx
    exact hδ x hx.1 hx.2

end SuperdiffusionCLT.Section7
