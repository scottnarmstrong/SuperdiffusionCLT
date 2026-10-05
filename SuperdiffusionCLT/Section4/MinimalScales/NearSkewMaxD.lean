/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearSkewMaxC

/-!
# The pointwise decomposition of the coarse average over the window

Summing the `d²` entries of `srootNS_entry_head` and `srootNS_entry_tail` gives two
variables `Hs`, `Ys`, both `O_{Γ₂}`, with a pointwise bound on the operator norm of
the coarse average of the cutoff at every `q ≤ m + h`.
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

theorem srootNS_core (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m h : ℕ) (hh : 1 ≤ h) :
    0 ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 ∧
    ∃ Hs Ys : ShellSeq d → ℝ, Measurable Hs ∧ Measurable Ys ∧
      (∀ ω, 0 ≤ Hs ω) ∧ (∀ ω, 0 ≤ Ys ω) ∧
      IsBigO P.toMeasure (gammaSigma 2) Hs
        (gammaTriangleConst 2 * (((d * d : ℕ) : ℝ) *
          (gammaTriangleConst 2 * (4 * (1 + spatialAverageColorConst d))))) ∧
      IsBigO P.toMeasure (gammaSigma 2) Ys
        (gammaTriangleConst 2 * (((d * d : ℕ) : ℝ) *
          (Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
            (1 + spatialAverageColorConst d) + 1))) ∧
      ∀ ω, ∀ q, q ≤ m + h →
        matrixOperatorNorm (volumeAverageMat (cubeSet (originCube d (m : ℤ)))
            (SuperdiffusionCLT.Frozen.Section2.streamCutoff ω q)) ≤
          Hs ω + Ys ω + ((d * d : ℕ) : ℝ) *
            (Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
              (1 + spatialAverageColorConst d) *
              Real.log (2 * (h : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd0⟩, ⟨0, hd0⟩), Finset.mem_univ _⟩
  have hentry := fun e : Fin d × Fin d =>
    srootNS_entry_tail hPrefix hJ1 hJ2 hJ3 hJ4 m h hh e.1 e.2
  have hC0 : 0 ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    (hentry (⟨0, hd0⟩, ⟨0, hd0⟩)).1
  refine ⟨hC0, ?_⟩
  choose Ye hYm hYnn hYO hYb using fun e => (hentry e).2
  have hcol : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  have hKc : 0 ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
      (1 + spatialAverageColorConst d) := by
    have : 0 ≤ 1 + spatialAverageColorConst d := by linarith only [hcol]
    positivity
  refine ⟨fun ω => ∑ e : Fin d × Fin d, ∑ r ∈ Finset.range (m + 1),
      |ShellField.shellSpatialAverage (m : ℤ) 0 (ω r) e.1 e.2|,
    fun ω => ∑ e : Fin d × Fin d, Ye e ω, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun e _ => Finset.measurable_sum _ fun r _ =>
      (srootNS_entry_measurable m r e.1 e.2).abs
  · exact Finset.measurable_sum _ fun e _ => hYm e
  · intro ω
    exact Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun r _ => abs_nonneg _
  · intro ω
    exact Finset.sum_nonneg fun e _ => hYnn e ω
  · have htri := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
      (X := fun (e : Fin d × Fin d) (ω : ShellSeq d) => ∑ r ∈ Finset.range (m + 1),
        |ShellField.shellSpatialAverage (m : ℤ) 0 (ω r) e.1 e.2|)
      (a := fun _ => gammaTriangleConst 2 * (4 * (1 + spatialAverageColorConst d)))
      (σ := 2) (by norm_num) hne
      (fun _ _ => mul_pos IndependentSums.gammaTriangleConst_pos
        (by linarith only [hcol]))
      (fun e _ => srootNS_entry_head hPrefix hJ1 hJ3 hJ4 m e.1 e.2)
      (fun e _ => Finset.measurable_sum _ fun r _ =>
        (srootNS_entry_measurable m r e.1 e.2).abs)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul] at htri
    exact htri
  · have htri := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
      (X := fun (e : Fin d × Fin d) (ω : ShellSeq d) => Ye e ω)
      (a := fun _ => Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
        (1 + spatialAverageColorConst d) + 1)
      (σ := 2) (by norm_num) hne
      (fun _ _ => by linarith only [hKc])
      (fun e _ => (hYO e).mono_scale (by linarith only []))
      (fun e _ => hYm e)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul] at htri
    exact htri
  · intro ω q hq
    rw [srootNS_avg_eq_sum]
    refine (srootNS_matrixOperatorNorm_le_sum _).trans ?_
    have hstep : ∀ e : Fin d × Fin d,
        |(∑ k ∈ Finset.range (q + 1),
            ShellField.shellSpatialAverage (m : ℤ) 0 (ω k)) e.1 e.2| ≤
          ∑ r ∈ Finset.range (m + 1),
              |ShellField.shellSpatialAverage (m : ℤ) 0 (ω r) e.1 e.2| +
            (Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) *
              (1 + spatialAverageColorConst d) *
              Real.log (2 * (h : ℝ)) ^ ((2 : ℝ)⁻¹) + Ye e ω) := by
      intro e
      have hmat : (∑ k ∈ Finset.range (q + 1),
          ShellField.shellSpatialAverage (m : ℤ) 0 (ω k)) e.1 e.2 =
          ∑ k ∈ Finset.range (q + 1),
            ShellField.shellSpatialAverage (m : ℤ) 0 (ω k) e.1 e.2 := by
        simp only [Matrix.sum_apply]
      rw [hmat]
      exact (srootNS_split_abs_sum
        (fun k => ShellField.shellSpatialAverage (m : ℤ) 0 (ω k) e.1 e.2) m q).trans
        (add_le_add le_rfl (hYb e ω q hq))
    refine (Finset.sum_le_sum fun e _ => hstep e).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul]
    ring

end

end SuperdiffusionCLT.Section4.MinimalScales
