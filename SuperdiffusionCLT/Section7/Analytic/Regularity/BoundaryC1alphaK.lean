/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaJ
public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Norm bookkeeping for the translated half cube
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3c_cubeVolume_originCube (m : ℤ) : cubeVolume (originCube d m) = ((3 : ℝ) ^ m) ^ d := by
  simp [cubeVolume, cubeScaleFactor_originCube]

/-- Translation to the half cube of scale `m - 1`: membership and norm bound by the normalized
`L^q` norm on the cube of scale `m`. -/
theorem r3c_flatHalf_translate_norm (e : Fin d) (m : ℤ) (z : Vec d) {q : ℝ≥0∞} (hq1 : 1 ≤ q)
    (hqt : q ≠ ⊤) {F : Vec d → ℝ} (hF : MemLp F q (normalizedCubeMeasure (originCube d m)))
    (hVD : {x : Vec d | x + z ∈ flatHalfCube e (m - 1)} ⊆ openCubeSet (originCube d m)) :
    MemLp (fun x => F (x - z)) q (flatHalfMeasure e (m - 1)) ∧
      flatHalfNorm e (m - 1) q (fun x => F (x - z)) ≤
        (3 : ℝ) ^ d * (eLpNorm F q (normalizedCubeMeasure (originCube d m))).toReal := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  set V : Set (Vec d) := {x : Vec d | x + z ∈ flatHalfCube e (m - 1)} with hV
  have hVo : IsOpen V := (isOpen_flatHalfCube e (m - 1)).preimage (continuous_id.add continuous_const)
  have hmp := measurePreserving_subRight_restrict_translateSet (d := d) z V
  rw [hV, r3c_translateSet_halfCube] at hmp
  have hFD : MemLp F q (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_restrict_of_normalized _ hF
  have hFV : MemLp F q (volume.restrict V) := hFD.mono_measure (Measure.restrict_mono hVD le_rfl)
  have hcomp : MemLp (fun x => F (x - z)) q (volume.restrict (flatHalfCube e (m - 1))) :=
    hFV.comp_measurePreserving hmp
  have hV' : (0 : ℝ) < cubeVolume (originCube d (m - 1)) := cubeVolume_pos _
  have hV0 : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  have h1 : ENNReal.ofReal (cubeVolume (originCube d (m - 1)))⁻¹ ≠ 0 := by simpa using hV'
  refine ⟨?_, ?_⟩
  · rw [flatHalfMeasure_eq]
    exact hcomp.smul_measure ENNReal.ofReal_ne_top
  · unfold flatHalfNorm
    have e1 : eLpNorm (fun x => F (x - z)) q (flatHalfMeasure e (m - 1)) =
        (ENNReal.ofReal (cubeVolume (originCube d (m - 1)))⁻¹) ^ (1 / q).toReal •
          eLpNorm F q (volume.restrict V) := by
      rw [flatHalfMeasure_eq, eLpNorm_smul_measure_of_ne_zero_of_ne_top hq0 hqt]
      congr 1
      exact eLpNorm_comp_measurePreserving hFV.aestronglyMeasurable hmp
    have e2 : eLpNorm F q (volume.restrict (openCubeSet (originCube d m))) =
        (ENNReal.ofReal (cubeVolume (originCube d m))) ^ (1 / q).toReal •
          eLpNorm F q (normalizedCubeMeasure (originCube d m)) := by
      have : volume.restrict (openCubeSet (originCube d m)) =
          (ENNReal.ofReal (cubeVolume (originCube d m))⁻¹)⁻¹ • normalizedCubeMeasure (originCube d m) := by
        rw [normalizedCubeMeasure_eq_smul, smul_smul, ENNReal.inv_mul_cancel
          (by simpa using hV0) ENNReal.ofReal_ne_top, one_smul]
      rw [this, eLpNorm_smul_measure_of_ne_zero_of_ne_top hq0 hqt,
        ENNReal.ofReal_inv_of_pos hV0, inv_inv]
    have e3 : eLpNorm F q (volume.restrict V) ≤ eLpNorm F q (volume.restrict (openCubeSet (originCube d m))) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hVD le_rfl)
    have hfin : eLpNorm F q (normalizedCubeMeasure (originCube d m)) ≠ ⊤ := hF.eLpNorm_ne_top
    have e4 : eLpNorm (fun x => F (x - z)) q (flatHalfMeasure e (m - 1)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ d) * eLpNorm F q (normalizedCubeMeasure (originCube d m)) := by
      rw [e1]
      rw [smul_eq_mul]
      refine (mul_le_mul_right e3 _).trans ?_
      rw [e2, smul_eq_mul, ← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      refine mul_le_mul_left ?_ _
      have hr : ENNReal.ofReal (cubeVolume (originCube d (m - 1)))⁻¹ *
          ENNReal.ofReal (cubeVolume (originCube d m)) = ENNReal.ofReal ((3 : ℝ) ^ d) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hV'.le), r3c_cubeVolume_originCube,
          r3c_cubeVolume_originCube, zpow_sub_one₀ (by norm_num)]
        congr 1
        have : ((3 : ℝ) ^ m) ≠ 0 := by positivity
        field_simp
        rw [div_pow]
        field_simp
      rw [hr]
      have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((3 : ℝ) ^ d) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
      have h4 : (1 / q).toReal ≤ 1 := by
        have : 1 / q ≤ 1 := by rw [one_div]; exact ENNReal.inv_le_one.2 hq1
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
      calc ENNReal.ofReal ((3 : ℝ) ^ d) ^ (1 / q).toReal ≤ ENNReal.ofReal ((3 : ℝ) ^ d) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le h3 h4
        _ = _ := by simp
    have hne : ENNReal.ofReal ((3 : ℝ) ^ d) * eLpNorm F q (normalizedCubeMeasure (originCube d m)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have := ENNReal.toReal_mono hne e4
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

end SuperdiffusionCLT.Section7
