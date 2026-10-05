/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldRegularityB
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeH
public import SuperdiffusionCLT.Section8.Root.DtExpH

/-!
# The pointwise growth clause with constants uniform in the law

The pointwise growth clause gives, with `σ = 1`, constants `C` and `B` that do not depend on
the law, and a scale `K` with `log K = O_{Γ_2}(B)`.  Combined with the fourth moment bound for
times at least one, this bounds the fourth moment of the process uniformly, on the event that `K`
is at most `√t`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise ENNReal NNReal

variable {d : ℕ}

/-- **Uniform growth.**  There are constants `C, B` such that for every law satisfying the shell
assumptions there is a measurable `K ≥ 27` with `log K = O_{Γ_2}(B)` and, almost surely,
`‖k(x)‖² ≤ C (log (K² + |x|²))^4` for the recentred stream. -/
theorem dtExp_growth :
    ∃ C B : ℝ, ∀ (P : ProbabilityMeasure (ShellSeq d)) (_hPrefix : ShellLawPrefix d P)
      (_hJ1 : ShellLawJ1Restriction d P) (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P)
      (_hJ4 : ShellLawJ4 d P),
      ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧ (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 * 1))
          (fun omega => Real.log (Kfun omega)) B ∧
        ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
          matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
            C * Real.log (Kfun omega ^ 2 + vecNormSq x) ^ ((2 : ℝ) * (1 + 1)) := by
  obtain ⟨C₂, h⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, h'⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨C, h''⟩ := h' 2 (by norm_num)
  refine ⟨C, C₀ * (C₁ * (1 / 2 : ℝ)⁻¹ * Real.sqrt ((1 : ℝ)⁻¹ *
    Real.log (Real.exp 1 + C₂ * (1 / 2 : ℝ)⁻¹ * (1 : ℝ)⁻¹))) ^ (1 : ℝ)⁻¹,
    fun P hPrefix hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨-, -, h3⟩ := h'' P hPrefix hJ1 hJ2 hJ3 hJ4
  obtain ⟨Kfun, hKm, hK27, hKb, hae⟩ := h3 (1 / 2) (by norm_num) (by norm_num) 1 one_pos
  refine ⟨Kfun, hKm, hK27, hKb, ?_⟩
  filter_upwards [hae, ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega h1 hg x
  have h2 := (h1 hg).2 x
  rw [fieldReg_centered_sub_origin_eq omega hg x] at h2
  exact h2

end SuperdiffusionCLT.Section8
