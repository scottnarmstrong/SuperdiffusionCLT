/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Analytic
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section3.Terms.ResponseHessianMeasurableB
public import SuperdiffusionCLT.Frozen.Section3.WBasicRegbounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds

/-!
# The non-localization residue of `l.RHS.term2`

## Summary

This module proves the finiteness inputs that the printed display `e.RHS.term2.R.bounds`
needs from the stream increment: the annealed fourth moment of the canonical increment
density `x ↦ ‖(k_{L'} − k_ℓ)(x)‖_op` on a cube is finite, by the moment display
`e.kmn.bounds`.  The response factor enters through `Frozen.Section3.w_basic_regbounds`
(`e.nablaw.Lt`) and is not treated here.

## Main results

* `lintegral_ofReal_ne_top_of_isBigOWith_gammaSigma`: an annealed integral with a
  one-sided `Γ_σ` tail is finite.
* `annealed_four_finite_of_isBigOWith`: the same for the annealed fourth moment.
* `continuous_finiteShellIncrement`: the finite shell increment is continuous in `x`.
* `aemeasurable_cubeLpENorm_four_matrixOperatorNorm_increment`: sample-measurability
  of the cube `L̲⁴` norm of the canonical increment density.
* `increment_annealed_four_finite`: finiteness of the annealed fourth moment of that
  norm.

## References

* The paper: `l.RHS.term2`, `e.RHS.term2.R.bounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Finiteness from a `Γ_σ` tail -/

/-- **Finiteness of an annealed integral from a one-sided `Γ_σ` tail.**  If a
nonnegative random variable `Y` satisfies `Y ≤ O_{Γ_σ}(K)` with `0 < σ` and
`0 < K`, then `∫⁻ ofReal ∘ Y` is finite: the `Γ_σ` growth display
(`hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma`) gives `Integrable Y` at the
first moment, and a Bochner-integrable nonnegative function has finite
`lintegral`.  This is the finiteness companion of
`annealed_four_root_le_of_isBigOWith`, which returns only the bound. -/
theorem lintegral_ofReal_ne_top_of_isBigOWith_gammaSigma {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu] {sigma K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) {Y : Omega → ℝ}
    (hYnn : ∀ omega : Omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y K) :
    (∫⁻ omega : Omega, ENNReal.ofReal (Y omega) ∂mu) ≠ ⊤ := by
  have hgrowth := IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    (μ := mu) (Y := Y) (K := K) (σ := sigma) hsigma hK hYnn hYm hY
  have hstep := (IndependentSums.hasGammaMomentGrowthWith_iff_of_nonneg
    (μ := mu) (σ := sigma) (M := IndependentSums.gammaMomentConst sigma * K)
    (Y := Y) hYnn).1 hgrowth (le_rfl : (1 : ℝ) ≤ 1)
  obtain ⟨hint, -⟩ := hstep
  have hYint : Integrable Y mu := by
    simpa only [Real.rpow_one] using hint
  rw [← ofReal_integral_eq_lintegral_ofReal hYint (Filter.Eventually.of_forall hYnn)]
  exact ENNReal.ofReal_ne_top

/-- **Finiteness of the annealed fourth moment from a `Γ_σ` tail.**  The same
hypotheses as `annealed_four_root_le_of_isBigOWith`, returning the finiteness
half of the conclusion (`NE_Lp` at `p = 4`). -/
theorem annealed_four_finite_of_isBigOWith {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {sigma K : ℝ} (hsigma : 0 < sigma)
    (hK : 0 < K) {Y : Omega → ℝ} (hYnn : ∀ omega : Omega, 0 ≤ Y omega)
    (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y K)
    {F : Omega → ℝ≥0∞} (hF : ∀ omega : Omega, F omega ^ (4 : ℕ) ≤ ENNReal.ofReal (Y omega)) :
    (∫⁻ omega : Omega, F omega ^ (4 : ℕ) ∂mu) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (lintegral_ofReal_ne_top_of_isBigOWith_gammaSigma hsigma hK hYnn hYm hY)
    (lintegral_mono hF)

/-! ## The canonical stream-increment density

The density `KN = ‖k_{L'} − k_ℓ‖` of the printed product rule is instantiated at
`matrixOperatorNorm (finiteShellIncrement omega n m ·)`.  The two typing clauses
the display asks of it — sample-measurability of its cube `L̲⁴` norm, and
finiteness of its annealed fourth moment — are theorems here, from the
stream-increment moment display. -/

/-- The canonical increment is continuous in the spatial variable: it is the
finite sum of the continuous shell value maps. -/
theorem continuous_finiteShellIncrement (omega : ShellSeq d) (n m : ℕ) :
    Continuous fun x : Vec d => finiteShellIncrement omega n m x := by
  have hsum : Continuous fun x : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) x :=
    continuous_finsetSum _ fun k _ => (omega k).1.1.continuous
  refine hsum.congr fun x => ?_
  rw [finiteShellIncrement_apply]
  rfl

/-- The scalar-density norm of the pointwise magnitude of a field equals the
norm of the field: the pointwise magnitude of `x ↦ ‖g x‖` is `‖g x‖` again, so
the two cube norms coincide. -/
private theorem cubeLpENorm_norm_field_eq (Q : TriadicCube d) (q : ℝ≥0∞)
    {E : Type*} [NormedAddCommGroup E] (g : Vec d → E)
    (hg : AEStronglyMeasurable g (normalizedCubeMeasure Q)) :
    cubeLpENorm Q q (fun x => ‖g x‖) = cubeLpENorm Q q g :=
  le_antisymm (cubeLpENorm_mono_enorm (f := fun x => ‖g x‖) hg.norm fun x => by simp)
    (cubeLpENorm_mono_enorm (g := fun x => ‖g x‖) hg fun x => by simp)

/-- **Sample-measurability of the cube `L̲⁴` norm of the canonical increment
density.**  The normalized cube `L̲⁴` norm is the fourth root of the normalized
volume average of the fourth power of the pointwise operator norm
(`cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm`), which is a measurable
function of the sample by the joint measurability of the increment
(`measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement` read through
`measurable_volumeAverage_of_measurable_uncurry`). -/
theorem aemeasurable_cubeLpENorm_four_matrixOperatorNorm_increment
    (P : ProbabilityMeasure (ShellSeq d)) (n m : ℕ) (Q : TriadicCube d) :
    AEMeasurable (fun omega : ShellSeq d => cubeLpENorm Q 4
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x)))
      P.toMeasure := by
  have hbase : AEMeasurable (fun omega : ShellSeq d => volumeAverage (cubeSet Q)
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x) ^ (4 : ℝ)))
      P.toMeasure :=
    aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement P n m
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ)) Q
  have hroot : AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal
      ((volumeAverage (cubeSet Q) (fun x : Vec d =>
        matrixOperatorNorm (finiteShellIncrement omega n m x) ^ (4 : ℝ))) ^ (((4 : ℝ))⁻¹)))
      P.toMeasure :=
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ ((4 : ℝ))⁻¹)).measurable.comp_aemeasurable
      hbase).ennreal_ofReal
  refine hroot.congr (Filter.Eventually.of_forall fun omega => ?_)
  show ENNReal.ofReal ((volumeAverage (cubeSet Q) (fun x : Vec d =>
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ (4 : ℝ))) ^ (((4 : ℝ))⁻¹)) =
    cubeLpENorm Q 4 (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x))
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) by norm_num]
  simp only [← norm_eq_matrixOperatorNorm]
  rw [cubeLpENorm_norm_field_eq Q (ENNReal.ofReal ((4 : ℝ)))
    (fun x : Vec d => finiteShellIncrement omega n m x)
    (continuous_finiteShellIncrement omega n m).aestronglyMeasurable]
  exact (cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm Q (by norm_num : (1 : ℝ) ≤ 4)
    (fun x : Vec d => finiteShellIncrement omega n m x)
    (continuous_finiteShellIncrement omega n m)).symm

/-- **Finiteness of the annealed fourth moment of the canonical increment
density.**  The stream-increment moment display `e.kmn.bounds`
(`isBigOWith_gammaSigma_finiteShellIncrementPthMoment` at `p = 4`,
`Γ_{1/2}`-indexed) bounds the normalized volume average of the fourth power by a
`Γ_{1/2}` tail; `annealed_four_finite_of_isBigOWith` converts that tail into
finiteness.  This is the `hKNfin` clause for the canonical `KN`. -/
theorem increment_annealed_four_finite (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {n m : ℕ} (hnm : n < m) (Q : TriadicCube d) :
    (∫⁻ omega : ShellSeq d,
      cubeLpENorm Q 4 (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x)) ^
        (4 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
  have hnp1 : (1 : ℕ) ≤ m - n := by omega
  have hu1 : (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by exact_mod_cast hnp1
  have hsqrtp : 0 < Real.sqrt (((m - n : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hu1)
  have hprov := isBigOWith_gammaSigma_finiteShellIncrementPthMoment
    (P := P) hPrefix hJ2 hJ3 hJ4 (p := (4 : ℝ)) (by norm_num) hnm Q
  rw [show ((2 : ℝ) / 4) = ((1 : ℝ) / 2) from by norm_num] at hprov
  refine annealed_four_finite_of_isBigOWith (mu := P.toMeasure) (sigma := ((1 : ℝ) / 2))
    (K := Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (streamLinftyConst d * Real.sqrt (((m - n : ℕ) : ℝ))) ^ (4 : ℝ)))
    (by norm_num) (mul_pos (Real.exp_pos 1) (mul_pos
      (IndependentSums.gammaMomentConst_pos (by norm_num))
      (Real.rpow_pos_of_pos (mul_pos (streamLinftyConst_pos hPrefix) hsqrtp) 4)))
    (Y := fun omega : ShellSeq d => volumeAverage (cubeSet Q) (fun x : Vec d =>
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ (4 : ℝ)))
    (fun omega => SuperdiffusionCLT.Section2.Norms.volumeAverage_cubeSet_nonneg Q
      (fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 4))
    (aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement P n m
      (by norm_num) Q)
    hprov fun omega =>
    cubeLpENorm_four_le_ofReal_volumeAverage Q
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x))
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x))
      (fun x => matrixOperatorNorm_nonneg _)
      (continuous_matrixOperatorNorm_finiteShellIncrement omega n m).aestronglyMeasurable
      (fun x => le_rfl) (fun x => matrixOperatorNorm_nonneg _)
      (continuous_matrixOperatorNorm_finiteShellIncrement omega n m)

end

end SuperdiffusionCLT.Section3.Terms
