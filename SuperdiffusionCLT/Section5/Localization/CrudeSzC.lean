/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzB

/-!
# The averaging step of the crude bound

For a field `g ∈ L²(cu_K)`, the subcube average of the fourth powers of the `L̲²` norms is at most
the fourth power of the `L̲⁸` norm on `cu_K` (`subcubeAvg_L2_pow_four_le`); together with
elementary `ℝ≥0∞` inequalities of Young type this reduces the average over `z` of the per-cube
bound to the `L̲⁸` norms on `cu_K`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

theorem lintegral_enorm_pow_four_eq {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    vecCubeLpENorm Q 4 g ^ (4 : ℕ) =
      ∫⁻ x, ‖hilbertifyVecField g x‖ₑ ^ (4 : ℕ) ∂normalizedCubeMeasure Q := by
  have hm := SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
    hg
  have h1 := avgRootENorm_eq_cubeLpENorm Q (p := 4) (by norm_num) hm
  have h2 := avgPowENorm_eq_rootENorm_rpow Q (p := 4) (by norm_num) (hilbertifyVecField g)
  have h4 : ENNReal.ofReal 4 = 4 := by norm_num
  rw [h4] at h1
  rw [vecCubeLpENorm, ← h1]
  have h3 : avgRootENorm Q 4 (hilbertifyVecField g) ^ (4 : ℕ) =
      avgRootENorm Q 4 (hilbertifyVecField g) ^ (4 : ℝ) := by
    rw [← ENNReal.rpow_natCast]; norm_num
  rw [h3, ← h2]
  unfold avgPowENorm
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_natCast]; norm_num

theorem sq_vecCubeLpENorm_two_sq_le {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    (vecCubeLpENorm Q 2 g ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      ∫⁻ x, ‖hilbertifyVecField g x‖ₑ ^ (4 : ℕ) ∂normalizedCubeMeasure Q := by
  rw [← lintegral_enorm_pow_four_eq hg, ← pow_mul]
  exact pow_le_pow_left' (vecCubeLpENorm_mono_exponent Q (by norm_num) g) 4

/-- The subcube average of the fourth powers of the `L̲²` norms is below the fourth power of the
`L̲⁸` norm on `cu_K`. -/
theorem subcubeAvg_L2_pow_four_le {Kc n : ℕ} (hn : n ≤ Kc) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) g) :
    subcubeAvg Kc n (fun Q => (vecCubeLpENorm Q 2 g ^ (2 : ℕ)) ^ (2 : ℕ)) ≤
      vecCubeLpENorm (originCube d (Kc : ℤ)) 8 g ^ (4 : ℕ) := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hstep : subcubeAvg Kc n (fun Q => (vecCubeLpENorm Q 2 g ^ (2 : ℕ)) ^ (2 : ℕ)) ≤
      subcubeAvg Kc n (fun Q => ∫⁻ x, ‖hilbertifyVecField g x‖ₑ ^ (4 : ℕ)
        ∂normalizedCubeMeasure Q) := by
    unfold subcubeAvg
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun Q hQ => ?_)
    exact sq_vecCubeLpENorm_two_sq_le (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono
      (openCubeSet_subset_of_mem_descendantsAtScale hk hQ) hg)
  refine hstep.trans ?_
  rw [subcubeAvg_lintegral_normalizedCubeMeasure hn, ← lintegral_enorm_pow_four_eq hg]
  exact pow_le_pow_left' (vecCubeLpENorm_mono_exponent _ (by norm_num) g) 4


theorem ennreal_two_mul_le (x y : ℝ≥0∞) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  by_cases hx : x = ⊤
  · simp [hx]
  by_cases hy : y = ⊤
  · simp [hy]
  lift x to NNReal using hx
  lift y to NNReal using hy
  have : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith only [sq_nonneg ((x : ℝ) - y)]
  exact_mod_cast this

/-- Young's inequality with the scale `c`, `c * ci = 1`. -/
theorem ennreal_young {c ci : ℝ≥0∞} (hc : c * ci = 1) (x y : ℝ≥0∞) :
    2 * (x * y) ≤ c * x ^ 2 + ci * y ^ 2 := by
  have h := ennreal_two_mul_le (c * x) y
  calc 2 * (x * y) = ci * (2 * (c * x) * y) := by
        calc 2 * (x * y) = (c * ci) * (2 * (x * y)) := by rw [hc, one_mul]
          _ = ci * (2 * (c * x) * y) := by ring
    _ ≤ ci * ((c * x) ^ 2 + y ^ 2) := mul_le_mul' le_rfl h
    _ = c * x ^ 2 + ci * y ^ 2 := by
        calc ci * ((c * x) ^ 2 + y ^ 2) = (c * ci) * (c * x ^ 2) + ci * y ^ 2 := by ring
          _ = c * x ^ 2 + ci * y ^ 2 := by rw [hc, one_mul]

/-- The per-cube Young step. -/
theorem young_cube {c ci : ℝ≥0∞} (hc : c * ci = 1) (r a b : ℝ≥0∞) :
    2 * (r * (2 + a + b)) ≤ 2 + (2 + 2 * c) * r ^ 2 + ci * (a ^ 2 + b ^ 2) := by
  have h1 := ennreal_two_mul_le 1 r
  have h2 := ennreal_young hc r a
  have h3 := ennreal_young hc r b
  calc 2 * (r * (2 + a + b)) = 2 * (2 * 1 * r) + 2 * (r * a) + 2 * (r * b) := by ring
    _ ≤ 2 * (1 ^ 2 + r ^ 2) + (c * r ^ 2 + ci * a ^ 2) + (c * r ^ 2 + ci * b ^ 2) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl h1) h2) h3
    _ = 2 + (2 + 2 * c) * r ^ 2 + ci * (a ^ 2 + b ^ 2) := by ring

theorem subcubeAvg_const {Kc n : ℕ} (hn : n ≤ Kc) (c : ℝ≥0∞) :
    subcubeAvg (d := d) Kc n (fun _ => c) = c := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hne : (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card ≠ 0 :=
    (Finset.card_pos.2 (descendantsAtScale_nonempty _ hk)).ne'
  unfold subcubeAvg
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hne) (ENNReal.natCast_ne_top _), one_mul]

/-- The averaged Young step. -/
theorem subcubeAvg_young {Kc n : ℕ} (hn : n ≤ Kc) {c ci : ℝ≥0∞} (hc : c * ci = 1)
    (r a b : TriadicCube d → ℝ≥0∞) :
    2 * subcubeAvg Kc n (fun Q => r Q * (2 + a Q + b Q)) ≤
      2 + (2 + 2 * c) * subcubeAvg Kc n (fun Q => r Q ^ 2) +
        ci * (subcubeAvg Kc n (fun Q => a Q ^ 2) + subcubeAvg Kc n (fun Q => b Q ^ 2)) := by
  have h := subcubeAvg_mono (Kc := Kc) (n := n)
    (f := fun Q => 2 * (r Q * (2 + a Q + b Q)))
    (g := fun Q => (2 + (2 + 2 * c) * r Q ^ 2) + ci * (a Q ^ 2 + b Q ^ 2))
    (fun Q => young_cube hc (r Q) (a Q) (b Q))
  rw [subcubeAvg_const_mul] at h
  have e1 : subcubeAvg (d := d) Kc n (fun Q => 2 + (2 + 2 * c) * r Q ^ 2) =
      2 + (2 + 2 * c) * subcubeAvg Kc n (fun Q => r Q ^ 2) := by
    rw [subcubeAvg_add (fun _ => (2 : ℝ≥0∞)) (fun Q => (2 + 2 * c) * r Q ^ 2),
      subcubeAvg_const hn, subcubeAvg_const_mul (2 + 2 * c) (fun Q => r Q ^ 2)]
  have e2 : subcubeAvg (d := d) Kc n (fun Q => ci * (a Q ^ 2 + b Q ^ 2)) =
      ci * (subcubeAvg Kc n (fun Q => a Q ^ 2) + subcubeAvg Kc n (fun Q => b Q ^ 2)) := by
    rw [subcubeAvg_const_mul ci (fun Q => a Q ^ 2 + b Q ^ 2),
      subcubeAvg_add (fun Q => a Q ^ 2) (fun Q => b Q ^ 2)]
  rw [subcubeAvg_add, e1, e2] at h
  exact h

end SuperdiffusionCLT.Section5
