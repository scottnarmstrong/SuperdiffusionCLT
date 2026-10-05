/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldRegularity
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi
public import SuperdiffusionCLT.Section6.Root.CenteredRecenteredBridge
public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.DiracJ1Restriction

/-!
# The centred field and the recentred field differ by a constant skew matrix

Almost surely (under `ShellLawJ3`), `centeredStreamField omega □₀ - fullStreamRecentered omega`
is the constant skew matrix `centeredStreamField omega □₀ 0`.  Consequences: the two
coefficient fields have the same `divForm` on `C²` functions, and the pointwise growth
clause of the stream-increment scale estimates holds verbatim for `fullStreamRecentered`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

theorem fieldReg_ae_centered_sub_recentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∃ K : Mat d, matTranspose K = -K ∧
      ∀ x : Vec d,
        centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
          fullStreamRecentered omega x = K := by
  filter_upwards [ae_centered_eq_recentered_add_skew hJ3 0] with omega h
  obtain ⟨K, hK, hx⟩ := h 0
  refine ⟨K, hK, fun x => ?_⟩
  have h1 := hx x
  simp only [fullCoefficientRecentered, zero_smul, zero_add, Nat.cast_zero] at h1
  rw [h1]
  abel

/-- Under the summability guard, the centred field of the unit cube minus its value at the
origin is the recentred stream, at every point. -/
theorem fieldReg_centered_sub_origin_eq (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) (x : Vec d) :
    centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) 0 =
      fullStreamRecentered omega x := by
  have h := SuperdiffusionCLT.Section2.Estimates.Stream.centeredStreamField_sub_eq_tsum
    omega hguard 0 x 0
  simp only [Nat.cast_zero] at h
  rw [h]
  rfl

/-- **The V6 pointwise growth clause for the recentred field.**  Under the five shell laws,
with a constant depending only on the dimension, for every `σ > 0` there is a measurable
`Kfun ≥ 27` with `log Kfun = O_{Γ_{2σ}}(B)` such that almost surely, for every `x`,
`|k(x) - k(0)|² ≤ C (log (Kfun² + |x|²))^{2(1+σ)}`, where `k - k(0)` is `fullStreamRecentered`. -/
theorem fieldReg_ae_pointwise_growth {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    ∃ C : ℝ, ∀ sigma : ℝ, 0 < sigma → ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧
      (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
      (∃ B : ℝ, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 * sigma))
        (fun omega => Real.log (Kfun omega)) B) ∧
      ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
        matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
          C * Real.log (Kfun omega ^ 2 + vecNormSq x) ^ (2 * (1 + sigma)) := by
  obtain ⟨C₂, h⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, h'⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨C, h''⟩ := h' 2 (by norm_num)
  obtain ⟨-, -, h3⟩ := h'' P hPrefix hJ1 hJ2 hJ3 hJ4
  refine ⟨C, fun sigma hsigma => ?_⟩
  obtain ⟨Kfun, hKm, hK27, hKb, hae⟩ := h3 (1 / 2) (by norm_num) (by norm_num) sigma hsigma
  refine ⟨Kfun, hKm, hK27, ⟨_, hKb⟩, ?_⟩
  filter_upwards [hae, ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega h1 hg x
  have h2 := (h1 hg).2 x
  rw [fieldReg_centered_sub_origin_eq omega hg x] at h2
  exact h2

/-! ## Satisfiability witnesses -/

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ K : Mat d, matTranspose K = -K ∧ ∀ x : Vec d,
        centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
          fullStreamRecentered omega x = K :=
  fieldReg_ae_centered_sub_recentered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ sigma : ℝ, 0 < sigma → ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧
      (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
      (∃ B : ℝ, IndependentSums.IsBigO
        (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure
        (IndependentSums.gammaSigma (2 * sigma)) (fun omega => Real.log (Kfun omega)) B) ∧
      ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
        ∀ x : Vec d, matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
          C * Real.log (Kfun omega ^ 2 + vecNormSq x) ^ (2 * (1 + sigma)) :=
  fieldReg_ae_pointwise_growth
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ1Restriction_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw

end

end SuperdiffusionCLT.Section8
