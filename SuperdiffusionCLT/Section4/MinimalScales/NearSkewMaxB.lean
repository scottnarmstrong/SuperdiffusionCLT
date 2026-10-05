/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearSkewMax
public import SuperdiffusionCLT.Section2.Estimates.Stream.SpatialAverageTail
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergy
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeLevelDecay
public import SuperdiffusionCLT.Section2.Norms.MultiscalePoincare

/-!
# The shell decomposition of the coarse average of the infrared cutoff

The coarse average of `streamCutoff ω q` over the origin cube is the sum of the
spatial averages of the shells `r ≤ q`. For each entry the shells `r ≤ m` form a
geometrically decaying `Γ₂` family (a single variable `Z`, uniform in `q`), and the
shells `r ∈ (m, q]` are independent, mean zero, `O_{Γ₂}(c)`; the latter are handled
by `srootNS_walk_tail_max`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.IndependentSums Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-- The coarse average of the cutoff is the sum of the shell spatial averages. -/
theorem srootNS_avg_eq_sum (m q : ℕ) (omega : ShellSeq d) :
    volumeAverageMat (cubeSet (originCube d (m : ℤ)))
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega q) =
      ∑ k ∈ Finset.range (q + 1), ShellField.shellSpatialAverage (m : ℤ) 0 (omega k) := by
  have hcs : volumeAverageMat (cubeSet (originCube d (m : ℤ)))
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega q) =
      volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega q) := by
    funext i j
    exact (SuperdiffusionCLT.Section2.Annealed.volumeAverage_openCubeSet_eq_cubeSet
      (originCube d (m : ℤ)) _).symm
  rw [hcs, SuperdiffusionCLT.Section2.Carriers.volumeAverageMat_streamCutoff_eq_sum
    (SuperdiffusionCLT.Section2.Carriers.isBounded_openCubeSet_originCube (m : ℤ))
    omega q]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hshell : volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
      (fun y : Vec d => SuperdiffusionCLT.Section2.Cutoff.shellReg omega k y) =
        volumeAverageMat (openCubeSet (originCube d (m : ℤ))) (omega k) := rfl
  rw [hshell,
    ShellField.shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet (m : ℤ) 0
      (omega k), translateSet_zero]

/-- The operator norm is at most the sum of the absolute values of the entries. -/
theorem srootNS_matrixOperatorNorm_le_sum (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ q : Fin d × Fin d, |A q.1 q.2| := by
  have hsum : ∑ q : Fin d × Fin d, |A q.1 q.2| =
      ∑ i : Fin d, ∑ l : Fin d, |A i l| :=
    Fintype.sum_prod_type fun q : Fin d × Fin d ↦ |A q.1 q.2|
  rw [hsum]
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    (matrixFrobeniusNorm_le_sum_abs_entries A)

/-- The geometric sum `∑_{r ≤ m} (3/4)^{m-r} ≤ 4`. -/
theorem srootNS_geom_sum_le (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1), (3 / 4 : ℝ) ^ (m - r) ≤ 4 := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero]
    have h : ∑ r ∈ Finset.range (n + 1), (3 / 4 : ℝ) ^ (n + 1 - r) =
        (3 / 4 : ℝ) * ∑ r ∈ Finset.range (n + 1), (3 / 4 : ℝ) ^ (n - r) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      rw [show n + 1 - r = (n - r) + 1 by omega, pow_succ]
      ring
    rw [h]
    linarith only [ih]

/-- Each geometric weight `3^{-(d/2) j}` is at most `(3/4)^j` once `1 ≤ d`. -/
theorem srootNS_rpow_le_geom (hd : 1 ≤ d) (j : ℕ) :
    (3 : ℝ) ^ (-((d : ℝ) / 2) * (j : ℝ)) ≤ (3 / 4 : ℝ) ^ j := by
  have hbase : (3 : ℝ) ^ (-((d : ℝ) / 2)) ≤ 3 / 4 := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : (3 : ℝ) ^ (-((d : ℝ) / 2)) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hd'])
    have h2 : (3 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 3)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]
      congr 1
      ring
    have h3 : (4 / 3 : ℝ) ≤ Real.sqrt 3 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have h4 : (Real.sqrt 3)⁻¹ ≤ 3 / 4 := by
      rw [inv_le_comm₀ (by linarith only [h3]) (by norm_num)]
      linarith only [h3]
    linarith only [h1, h2, h4]
  have hpow : (3 : ℝ) ^ (-((d : ℝ) / 2) * (j : ℝ)) = ((3 : ℝ) ^ (-((d : ℝ) / 2))) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [hpow]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hbase j

end

end SuperdiffusionCLT.Section4.MinimalScales
