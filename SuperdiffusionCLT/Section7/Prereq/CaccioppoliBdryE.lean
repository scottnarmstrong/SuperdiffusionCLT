/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2Assembly
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryD

/-!
# A Sobolev inequality on a small subset for zero-trace functions

For `v ∈ H¹₀(D)` and a measurable `B ⊆ D`,
`‖v‖_{L²(B)} ≤ C (|B| |D|)^{1/(2d)} Σ_i ‖∂_i v‖_{L²(D)}`: Hölder from `L²(B)` to `L^q(B)` with
`q = 2d/(d-1)`, the Sobolev inequality for `H¹₀(D)` with `p = 2d/(d+1)`, and Hölder from
`L^p(D)` to `L²(D)`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The Sobolev constant at the exponent `p = 2d/(d+1)`. -/
noncomputable def ca2_CS (d : ℕ) : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) (ENNReal.ofReal (2 * d / (d + 1))).toNNReal

theorem ca2_sob_layer (hd : 2 ≤ d) {D B : Set (Vec d)} (hDb : Bornology.IsBounded D) (hBD : B ⊆ D)
    (v : H10Function D) :
    eLpNorm v.toH1Function.toFun 2 (volume.restrict B) ≤
      (ca2_CS d : ℝ≥0∞) * (volume B) ^ (1 / (2 * (d : ℝ))) * (volume D) ^ (1 / (2 * (d : ℝ))) *
        ∑ i : Fin d, eLpNorm (fun x => v.toH1Function.grad x i) 2 (volume.restrict D) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : (1 : ℝ) < 2 * d / (d + 1) := by rw [lt_div_iff₀ (by positivity)]; linarith only [hd2]
  have hp2 : 2 * (d : ℝ) / (d + 1) ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith only [hd2]
  have hq2 : (2 : ℝ) ≤ 2 * d / (d - 1) := by
    rw [le_div_iff₀ (by linarith only [hd2])]; linarith only [hd2]
  have hq1 : (1 : ℝ) < 2 * d / (d - 1) := by linarith only [hq2]
  let P : FiniteLpExponent := ⟨ENNReal.ofReal (2 * d / (d + 1)), by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hp1])).2 hp1,
    ENNReal.ofReal_lt_top⟩
  let Q : FiniteLpExponent := ⟨ENNReal.ofReal (2 * d / (d - 1)), by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hq1])).2 hq1,
    ENNReal.ofReal_lt_top⟩
  have hPr : P.exponent.toReal = 2 * d / (d + 1) := ENNReal.toReal_ofReal (by linarith only [hp1])
  have hQr : Q.exponent.toReal = 2 * d / (d - 1) := ENNReal.toReal_ofReal (by linarith only [hq1])
  have hP2 : P.exponent ≤ 2 := by
    show ENNReal.ofReal (2 * d / (d + 1)) ≤ 2
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp2
  have hPd : P.exponent.toReal < d := by
    rw [hPr, div_lt_iff₀ (by positivity)]; nlinarith only [hd2]
  have hPQ : Q.exponent.toReal⁻¹ = P.exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    rw [hPr, hQr]
    have h1 : (d : ℝ) - 1 ≠ 0 := by linarith only [hd2]
    field_simp
    ring
  have hS := l2d_sobolev_H10 (by omega : 0 < d) P Q hP2 hPd hPQ hDb v
  have hCg : (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) P.exponent.toNNReal :
      ℝ≥0∞) = (ca2_CS d : ℝ≥0∞) := rfl
  rw [hCg] at hS
  set μD : Measure (Vec d) := volume.restrict D with hμD
  have hDfin : μD Set.univ < ⊤ := by
    rw [hμD, Measure.restrict_apply_univ]; exact hDb.measure_lt_top
  have hvm : AEStronglyMeasurable v.toH1Function.toFun μD := v.toH1Function.memL2.aestronglyMeasurable
  -- Hölder on `B` from `L²` to `L^q`
  have h2q : (2 : ℝ≥0∞) ≤ Q.exponent := by
    show (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * d / (d - 1))
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hq2
  have hH1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B) h2q
    (f := v.toH1Function.toFun) (hvm.mono_measure (Measure.restrict_mono hBD le_rfl))
  have e1 : (1 : ℝ) / (2 : ℝ≥0∞).toReal - 1 / Q.exponent.toReal = 1 / (2 * (d : ℝ)) := by
    rw [hQr]
    have h1 : (d : ℝ) - 1 ≠ 0 := by linarith only [hd2]
    norm_num
    field_simp
    ring
  rw [e1, Measure.restrict_apply_univ] at hH1
  have hH2 : eLpNorm v.toH1Function.toFun Q.exponent (volume.restrict B) ≤
      eLpNorm v.toH1Function.toFun Q.exponent μD :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hBD le_rfl)
  -- Hölder on `D` from `L^p` to `L²`
  have hH3 : ∀ i, eLpNorm (fun x => v.toH1Function.grad x i) P.exponent μD ≤
      eLpNorm (fun x => v.toH1Function.grad x i) 2 μD * (volume D) ^ (1 / (2 * (d : ℝ))) := by
    intro i
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μD) hP2
      (f := fun x => v.toH1Function.grad x i) (v.toH1Function.gradMemL2 i).aestronglyMeasurable
    have e2 : (1 : ℝ) / P.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / (2 * (d : ℝ)) := by
      rw [hPr]
      norm_num
      field_simp
      ring
    rw [e2, hμD, Measure.restrict_apply_univ] at this
    exact this
  calc eLpNorm v.toH1Function.toFun 2 (volume.restrict B)
      ≤ eLpNorm v.toH1Function.toFun Q.exponent (volume.restrict B) * (volume B) ^ (1 / (2 * (d : ℝ))) := hH1
    _ ≤ eLpNorm v.toH1Function.toFun Q.exponent μD * (volume B) ^ (1 / (2 * (d : ℝ))) :=
        by gcongr
    _ ≤ ((ca2_CS d : ℝ≥0∞) * ∑ i : Fin d, eLpNorm (fun x => v.toH1Function.grad x i) P.exponent μD) *
          (volume B) ^ (1 / (2 * (d : ℝ))) := by gcongr
    _ ≤ ((ca2_CS d : ℝ≥0∞) * ∑ i : Fin d, (eLpNorm (fun x => v.toH1Function.grad x i) 2 μD *
          (volume D) ^ (1 / (2 * (d : ℝ))))) * (volume B) ^ (1 / (2 * (d : ℝ))) := by
        gcongr with i _
        exact hH3 i
    _ = _ := by
        rw [← Finset.sum_mul]
        ring

end SuperdiffusionCLT.Section7
