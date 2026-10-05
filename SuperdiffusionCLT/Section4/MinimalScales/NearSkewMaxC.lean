/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearSkewMaxB

/-!
# The entrywise head and tail of the coarse average, and the pointwise bound

Entry by entry, the shells `r ≤ m` contribute the variable
`Z = ∑_{r ≤ m} |entry_r|`, which is `O_{Γ₂}` of a dimensional constant (geometric
decay of the single-shell tail), and the shells `r ∈ (m, q]` contribute the running
sums handled by `srootNS_walk_tail_max`. Summing the `d²` entries gives a pointwise
bound for the operator norm of the coarse average, uniformly in `q ≤ m + h`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.IndependentSums Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Estimates.Stream
  (spatialAverageColorConst spatialAverageColorConst_nonneg)

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}

theorem srootNS_entry_measurable (m r : ℕ) (i l : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l) :=
  SuperdiffusionCLT.Section2.Estimates.Stream.measurable_translatedShellCubeAverage_entry_coordinate
    r 0 (originCube d (m : ℤ)) i l

theorem srootNS_entry_indep (hJ2 : ShellLawJ2 d P) (m : ℕ) (i l : Fin d) :
    iIndepFun (fun (r : ℕ) (omega : ShellSeq d) =>
      ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l) P.toMeasure := by
  have hF : Measurable (fun F : ShellField d =>
      ShellField.shellSpatialAverage (m : ℤ) 0 F i l) := by
    have hrow : Measurable (fun A : Mat d ↦ A i) := measurable_pi_apply i
    have hcol : Measurable (fun v : Fin d → ℝ ↦ v l) := measurable_pi_apply l
    exact hcol.comp (hrow.comp (ShellField.measurable_shellSpatialAverage (m : ℤ) 0))
  exact hJ2.independent.comp
    (fun _ (F : ShellField d) => ShellField.shellSpatialAverage (m : ℤ) 0 F i l)
    (fun _ => hF)

theorem srootNS_entry_mean (hJ4 : ShellLawJ4 d P) (m r : ℕ) (i l : Fin d) :
    ∫ omega, ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l ∂P.toMeasure = 0 :=
  SuperdiffusionCLT.Section3.Setup.integral_eq_zero_of_negateSequence_neg hJ4
    (X := fun omega : ShellSeq d => ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l)
    (srootNS_entry_measurable m r i l).aestronglyMeasurable
    (fun omega => by
      simp only [ShellField.negateSequence_apply, ShellField.shellSpatialAverage_negate,
        Matrix.neg_apply])

/-- Splitting a prefix sum at the scale `m`. -/
theorem srootNS_split_abs_sum (f : ℕ → ℝ) (m q : ℕ) :
    |∑ k ∈ Finset.range (q + 1), f k| ≤
      ∑ k ∈ Finset.range (m + 1), |f k| + |∑ k ∈ Finset.Ioc m q, f k| := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (q + 1)) (fun k => k ≤ m) f]
  have hset : (Finset.range (q + 1)).filter (fun k => ¬ k ≤ m) = Finset.Ioc m q := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [hset]
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => abs_nonneg (f k))
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  omega

/-- The head of one entry: the shells `r ≤ m`. -/
theorem srootNS_entry_head (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (i l : Fin d) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => ∑ r ∈ Finset.range (m + 1),
        |ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l|)
      (gammaTriangleConst 2 * (4 * (1 + spatialAverageColorConst d))) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hcol : 0 ≤ spatialAverageColorConst d :=
    spatialAverageColorConst_nonneg d
  have hcpos : (0 : ℝ) < 1 + spatialAverageColorConst d := by linarith only [hcol]
  have hterm : ∀ r ∈ Finset.range (m + 1),
      (1 + spatialAverageColorConst d) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((m : ℤ) - (r : ℤ)) 0 : ℤ) : ℝ)) ≤
      (1 + spatialAverageColorConst d) * (3 / 4 : ℝ) ^ (m - r) := by
    intro r hr
    have hmax : ((max ((m : ℤ) - (r : ℤ)) 0 : ℤ) : ℝ) = ((m - r : ℕ) : ℝ) := by
      have hr' : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      have : max ((m : ℤ) - (r : ℤ)) 0 = ((m - r : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    rw [hmax]
    exact mul_le_mul_of_nonneg_left (srootNS_rpow_le_geom hd0 (m - r)) hcpos.le
  have hne : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
  have htri := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.range (m + 1))
    (X := fun r (omega : ShellSeq d) =>
      |ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l|)
    (a := fun r => (1 + spatialAverageColorConst d) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((m : ℤ) - (r : ℤ)) 0 : ℤ) : ℝ)))
    (σ := 2) (by norm_num) hne
    (fun r _ => mul_pos hcpos (Real.rpow_pos_of_pos (by norm_num) _))
    (fun r _ => by
      have h := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_shellSpatialAverage_entry
        hPrefix hJ1 hJ3 hJ4 r (m : ℤ) 0 i l
      exact h.of_abs_le (fun omega => by rw [abs_abs]))
    (fun r _ => (srootNS_entry_measurable m r i l).abs)
  refine htri.mono_scale ?_
  have hsum : ∑ r ∈ Finset.range (m + 1), (1 + spatialAverageColorConst d) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((m : ℤ) - (r : ℤ)) 0 : ℤ) : ℝ)) ≤
      4 * (1 + spatialAverageColorConst d) := by
    calc _ ≤ ∑ r ∈ Finset.range (m + 1), (1 + spatialAverageColorConst d) *
          (3 / 4 : ℝ) ^ (m - r) := Finset.sum_le_sum hterm
      _ = (1 + spatialAverageColorConst d) *
          ∑ r ∈ Finset.range (m + 1), (3 / 4 : ℝ) ^ (m - r) := by rw [Finset.mul_sum]
      _ ≤ (1 + spatialAverageColorConst d) * 4 :=
          mul_le_mul_of_nonneg_left (srootNS_geom_sum_le m) hcpos.le
      _ = 4 * (1 + spatialAverageColorConst d) := by ring
  exact mul_le_mul_of_nonneg_left hsum IndependentSums.gammaTriangleConst_pos.le

/-- The tail of one entry: the maximal bound for the shells `r ∈ (m, m + h]`. -/
theorem srootNS_entry_tail (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m h : ℕ) (hh : 1 ≤ h) (i l : Fin d) :
    0 ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 ∧
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        (Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
          (1 + spatialAverageColorConst d)) ∧
      ∀ ω, ∀ q, q ≤ m + h →
        |∑ r ∈ Finset.Ioc m q, ShellField.shellSpatialAverage (m : ℤ) 0 (ω r) i l| ≤
          Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
            (1 + spatialAverageColorConst d) *
            Real.log (2 * (h : ℝ)) ^ ((2 : ℝ)⁻¹) + Y ω := by
  have hcol : 0 ≤ spatialAverageColorConst d :=
    spatialAverageColorConst_nonneg d
  have hcpos : (0 : ℝ) < 1 + spatialAverageColorConst d := by linarith only [hcol]
  refine srootNS_walk_tail_max (μ := P.toMeasure)
    (X := fun r (omega : ShellSeq d) =>
      ShellField.shellSpatialAverage (m : ℤ) 0 (omega r) i l)
    hcpos (srootNS_entry_indep hJ2 m i l) (fun r => srootNS_entry_measurable m r i l) m h hh
    ?_ (fun r => srootNS_entry_mean hJ4 m r i l)
  intro r hmr _
  have h := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_shellSpatialAverage_entry
    hPrefix hJ1 hJ3 hJ4 r (m : ℤ) 0 i l
  have hmax : ((max ((m : ℤ) - (r : ℤ)) 0 : ℤ) : ℝ) = 0 := by
    have : max ((m : ℤ) - (r : ℤ)) 0 = 0 := by omega
    rw [this]
    norm_num
  rw [hmax, mul_zero, Real.rpow_zero, mul_one] at h
  exact h

end

end SuperdiffusionCLT.Section4.MinimalScales
