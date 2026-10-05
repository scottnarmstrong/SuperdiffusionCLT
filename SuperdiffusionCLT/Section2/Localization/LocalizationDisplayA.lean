/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1Inputs
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1MomentsB

/-!
# The two printed per-cube displays `hpoint` and `hDd`

The localization average estimate fixes the carriers of the first summand `T_1` to
the objects `localizationDz` and `localizationB` and keeps two printed
per-cube displays as hypotheses:

* `hpoint`,
  `|G_{-h_z}P · (G_{h_z}ᵗ bfA_L(z+cu_n) G_{h_z} - bfA_ℓ(z+cu_n)) G_{-h_z}P| ≤ D_z · B_z`,
  with `B_z = |bfA_ℓ^{1/2}(z+cu_n) G_{-h_z}P|²`;
* `hDd`, `D_z ≤ O_{Γ_1}(Cd ν⁻²3^{-(ℓ-n)})` for each fixed `z`.

This module states both at these carriers and reduces each to the shortest
remaining input.

## `hpoint`

The printed proof obtains `hpoint` from the operator-norm
form of Lemma `l.localization.A` at `a = a_ℓ` and perturbation field
`k_L - k_ℓ - h_z`, by the Cauchy--Schwarz/quadratic-form step
`|X · (M - A) X| ≤ D |A^{1/2} X|²`.  The engine
`coarseBlockMatrix_localization_scalar_two_sided` (`BlockPerturbation`) returns
that input in the *two-sided Loewner form*

`(-D) • A_ℓ ≤ M - A_ℓ ≤ D • A_ℓ`

with `D = ν⁻¹M + ν⁻²M²`; the two-sided form is weaker than the operator-norm
form and is exactly what the quadratic-form step needs (`abs_le` after one
application at `X = G_{-h_z}P`).  `localizationT1CubeError_abs_le_Dz_mul_localizationB`
discharges that step: its only inputs are the two Loewner clauses at the
carriers `localizationCoarseAt nu l R`, `localizationCoarseAt nu L R`, the gauge
`localizationGaugeAverage l L R` and the constant `localizationDz`.

## `hDd`

The printed chain turns the per-cube second-moment display
`D_z² ≤ O_{Γ_{1/2}}(Cν⁻⁴3^{-2(ℓ-n)})` into `D_z ≤ O_{Γ_1}(Cν⁻²3^{-(ℓ-n)})` by
the power rule `e.powerofGammasigma`; the lemma
`isBigO_gammaSigma_sqrt_of_sq` (`LocalizationAverageT1`) is that step at `σ = 1`, so the
surviving input of `hDd` is the printed second-moment display itself.  On the degenerate branch
`L ≤ ℓ` the perturbation vanishes (`localizationD_eq_zero_of_not_lt`), so
`D_z ≡ 0` and `hDd` holds with no input at all
(`localizationDz_isBigO_of_not_lt`).

Both reductions are stated at the exact carriers consumed by
the localization average estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## `hpoint` -/

/-- **The printed per-cube inequality `hpoint`**, reduced to the
two-sided Loewner sandwich of Lemma `l.localization.A` at these carriers.

The left-hand side is `localizationT1CubeError nu l L R Pvec omega`, the
quadratic form `G_{-h_z}P · (G_{h_z}ᵗ bfA_L G_{h_z} - bfA_ℓ) G_{-h_z}P`; the
right-hand side is `localizationDz nu l L R omega * localizationB nu l L R Pvec omega`,
the printed `D_z · |bfA_ℓ^{1/2} G_{-h_z}P|²`.

The two hypotheses are the two Loewner clauses with `M := G_{h_z}ᵗ bfA_L G_{h_z}`
and `A := bfA_ℓ`, both at the constant `D_z = localizationDz`.  They are the
conclusion of `coarseBlockMatrix_localization_scalar_two_sided` at
`a = a_ℓ`, `b = bfA`-field with `b = a + (k_L - k_ℓ - h_z)`, and are strictly
weaker than the operator-norm form.  The Cauchy--Schwarz step
is discharged, so no other input remains. -/
theorem localizationT1CubeError_abs_le_Dz_mul_localizationB {nu : ℝ} (l L : ℕ)
    (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d)
    (hlo : BlockMatLoewnerLE
      ((-(localizationDz nu l L R omega)) • localizationCoarseAt nu l R omega)
      (ofFullBlockMat
        (toFullBlockMat
            (blockMatMul (blockMatTranspose (blockG (localizationGaugeAverage l L R omega)))
              (blockMatMul (localizationCoarseAt nu L R omega)
                (blockG (localizationGaugeAverage l L R omega)))) -
          toFullBlockMat (localizationCoarseAt nu l R omega))))
    (hhi : BlockMatLoewnerLE
      (ofFullBlockMat
        (toFullBlockMat
            (blockMatMul (blockMatTranspose (blockG (localizationGaugeAverage l L R omega)))
              (blockMatMul (localizationCoarseAt nu L R omega)
                (blockG (localizationGaugeAverage l L R omega)))) -
          toFullBlockMat (localizationCoarseAt nu l R omega)))
      ((localizationDz nu l L R omega) • localizationCoarseAt nu l R omega)) :
    |localizationT1CubeError nu l L R Pvec omega| ≤
      localizationDz nu l L R omega * localizationB nu l L R Pvec omega := by
  have h1 := hlo (localizationGaugeVector l L R Pvec omega)
  have h2 := hhi (localizationGaugeVector l L R Pvec omega)
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right] at h1 h2
  unfold localizationT1CubeError localizationB
  rw [abs_le]
  exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-! ## `hDd` -/

/-- The weak-Orlicz tail of the identically zero function at any positive
amplitude: `{|0| > A t}` is empty because `A t > 0`, and the tail function is
`≥ 1` on `[1, ∞)`, so the bound holds vacuously. -/
private theorem isBigOWith_gammaSigma_zero {σ A : ℝ} {μ : MeasureTheory.Measure (ShellSeq d)}
    (hA : 0 < A) :
    IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma σ)
      (fun _ : ShellSeq d => (0 : ℝ)) A := by
  intro t ht
  have hAt : 0 < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hemp : IndependentSums.upperTailEvent (fun _ : ShellSeq d => (0 : ℝ)) (A * t) = ∅ := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hAt.le
  rw [hemp, MeasureTheory.measureReal_empty]
  exact inv_nonneg.mpr (le_trans zero_le_one
    (IndependentSums.one_le_gammaSigma (le_trans zero_le_one ht)))

/-- **The degenerate branch of `hDd`, with no input at all.**  When `L ≤ ℓ` the
perturbation `k_L − k_ℓ − h_z` vanishes identically
(`localizationD_eq_zero_of_not_lt`), so `D_z ≡ 0`; the printed tail bound then
holds at every positive amplitude because the tail event of the zero function is
empty.  The second-moment display is therefore not needed on this branch. -/
theorem localizationDz_isBigO_of_not_lt {Cd nu : ℝ} (hCd : 0 < Cd) (hnu : 0 < nu)
    (l L n : ℕ) (R : TriadicCube d) (P : ProbabilityMeasure (ShellSeq d))
    (hLl : ¬ l < L) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (localizationDz nu l L R) (localizationAverageT1CubeAmplitude Cd nu l n) := by
  have hA : 0 < localizationAverageT1CubeAmplitude Cd nu l n :=
    localizationAverageT1CubeAmplitude_pos hCd hnu l n
  have hzero : localizationDz nu l L R = fun _ : ShellSeq d => (0 : ℝ) := by
    funext omega
    exact localizationD_eq_zero_of_not_lt hLl R omega
  have hbase := isBigOWith_gammaSigma_zero (σ := 1)
    (A := localizationAverageT1CubeAmplitude Cd nu l n) (μ := P.toMeasure) hA
  rw [hzero]
  simpa only [IndependentSums.IsBigO, abs_zero] using hbase

end SuperdiffusionCLT.Section2.Localization
