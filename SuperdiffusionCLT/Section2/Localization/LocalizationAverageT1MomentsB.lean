/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1Moments
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageAssembly

/-!
# `T1`'s two moment averages, composed back into the summand

`localizationAverageT1_secondMoment_of_cube_bounds` and
`localizationAverageT1_fourthMoment_of_factor_bounds` prove the two printed moment averages
(the second-moment average and the fourth-moment average) from their printed *per-cube*
inputs, but as standalone theorems.  `localizationAverage_T1_of_grid` still carries those two
averages as the hypotheses `hD2bound` and `hB2bound`.  This module composes the two
derivations back into the summand: the
theorems below have exactly the hypotheses of `localizationAverage_T1_of_grid`
with `hD2bound` and `hB2bound` removed, replaced by the printed per-cube
`Γ` bounds they were derived from.

## The printed per-cube inputs

* `Dd i = O_{Γ_1}(Cd ν⁻²3^{-(ℓ-n)})` for each cube `i`
  (`e.nabla.kmn.Linfty` at the deterministic comparison `e.localization.average.Dz`);
* `Ysq i = O_{Γ_{1/2}}(KY)` (`Y_z²`, from
  `e.Enaught.vs.A.and.Ahom`), conditionally on `F_>` in the conditional form;
* `R i = O_{Γ_{1/2}}(CR ν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)`
  (`R_z = |bfE_ℓ^{1/2}G_{-h_z}P|⁴`, from `e.jk.spatialavg`, `p.concentration`,
  `e.Enaught.mixing`), conditionally on `F_>` in the conditional form;
* the pointwise domination `Bd i² ≤ Ysq i · R i`.

No index and no amplitude is altered: the conclusions are the printed
`Γ_{1/2}` / `ν⁻⁴` / `3^{-2(ℓ-n)}` and `Γ_{1/4}` / `ν⁻²` / `((1∨ℓ)²+(L-ℓ)²)|P|⁴`
averages, fed through the printed Cauchy--Schwarz combine.

## Why the two per-cube constants must be reconciled

The two moment averages carry
the explicit triangle and multiplication constants:

* `avsum_i Dd_i² = O_{Γ_{1/2}}(gammaTriangleConst (1/2) · Cd² ν⁻⁴3^{-2(ℓ-n)})`;
* `avsum_i Bd_i² = O_{Γ_{1/4}}(gammaTriangleConst (1/4) · orliczProductConst (1/2) (1/2) ·
  (KY·CR) ν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)`.

But `localizationAverage_T1_of_grid` feeds *one* common constant `C` into both
amplitudes.  The two derived constants are therefore reconciled by the enlarged
constant `localizationAverageT1CubeBoundConst Cd KY CR`, the maximum of the two,
which is the constant enlargement the printed proof performs
("after enlarging the constant `C(d)` if necessary").  When the three per-cube
constants are the printed ones (`Cd = KY = CR = C`) this maximum is
`C² · max (gammaTriangleConst (1/2)) (gammaTriangleConst (1/4) · orliczProductConst (1/2) (1/2))`,
so the envelope carries the printed amplitude at an enlarged constant,
exactly as `localizationAverageEnvelopeT1` does.

## What this module does not reach

The per-cube bounds are still named hypotheses: their carriers (the
envelope `bfE_ℓ`, `Y_z`, `R_z`) are not constructed here.  This module removes
the two *average* hypotheses of the `T1` pipeline and leaves only the printed
per-cube ones.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## Monotonicity of the two amplitudes in their constant -/

/-- **The second-moment amplitude is monotone in its constant.**  This is the
`mono_scale` bookkeeping that lifts the derived average amplitude
`gammaTriangleConst (1/2) * Cd²` to the common enlarged constant fed into
`localizationAverage_T1_of_grid`. -/
theorem localizationAverageT1SecondAmplitude_mono_const {K K' nu : ℝ} (h : K ≤ K')
    (hnu : 0 ≤ nu) (l n : ℕ) :
    localizationAverageT1SecondAmplitude K nu l n ≤
      localizationAverageT1SecondAmplitude K' nu l n := by
  unfold localizationAverageT1SecondAmplitude
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hnu _))
    (Real.rpow_nonneg (by norm_num) _)

/-- **The fourth-moment amplitude is monotone in its constant.** -/
theorem localizationAverageT1FourthAmplitude_mono_const {K K' nu : ℝ} (h : K ≤ K')
    (hnu : 0 ≤ nu) (l L : ℕ) (Pvec : BlockVec d) :
    localizationAverageT1FourthAmplitude K nu l L Pvec ≤
      localizationAverageT1FourthAmplitude K' nu l L Pvec := by
  unfold localizationAverageT1FourthAmplitude
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hnu _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (sq_nonneg _)

/-! ## The reconciled constant -/

/-- The common constant reconciling the two derived moment-average amplitudes.
It is the maximum of `gammaTriangleConst (1/2) * Cd²` (the constant the
second-moment derivation produces from the per-cube constant `Cd`) and
`gammaTriangleConst (1/4) * orliczProductConst (1/2) (1/2) * (KY*CR)` (the
constant the fourth-moment derivation produces from the per-cube constants `KY`
and `CR`), since `localizationAverage_T1_of_grid` feeds a single `C` into both
amplitudes.  The enlargement is the one the printed proof performs. -/
noncomputable def localizationAverageT1CubeBoundConst (Cd KY CR : ℝ) : ℝ :=
  max (IndependentSums.gammaTriangleConst ((1 : ℝ) / 2) * Cd ^ 2)
    (IndependentSums.gammaTriangleConst ((1 : ℝ) / 4) *
      SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
      (KY * CR))

/-- The reconciled constant is positive as soon as `Cd > 0`. -/
theorem localizationAverageT1CubeBoundConst_pos {Cd KY CR : ℝ} (hCd : 0 < Cd) :
    0 < localizationAverageT1CubeBoundConst Cd KY CR :=
  lt_of_lt_of_le (mul_pos IndependentSums.gammaTriangleConst_pos (pow_pos hCd 2))
    (le_max_left _ _)

/-! ## The unconditional composition -/

/-- **The first printed summand from the printed per-cube inputs.**  This is
`localizationAverage_T1_of_grid` with the two moment-average hypotheses
`hD2bound` and `hB2bound` removed: they are supplied by
`localizationAverageT1_secondMoment_of_cube_bounds` and
`localizationAverageT1_fourthMoment_of_factor_bounds`
from the printed per-cube bounds together with the pointwise domination.
The two derived constants are reconciled by the enlarged
constant `localizationAverageT1CubeBoundConst Cd KY CR`, and the
pointwise Cauchy--Schwarz, the two nonnegativities and the `L = ℓ` vanishing are
discharged by `localizationAverage_T1_of_grid` itself. -/
theorem localizationAverage_T1_of_cubeBounds {Cd nu : ℝ} (hCd : 0 < Cd) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (l L n : ℕ) (Pvec : BlockVec d)
    {ι : Type*} (grid : Finset ι) (hne : grid.Nonempty)
    (Dd Bd : ι → ShellSeq d → ℝ) (T1 D2 B2 : ShellSeq d → ℝ)
    (hT1 : ∀ omega, T1 omega = (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Dd i omega * Bd i omega)
    (hD2def : ∀ omega, D2 omega = (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Dd i omega ^ 2)
    (hB2def : ∀ omega, B2 omega = (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Bd i omega ^ 2)
    (hDdnn : ∀ i ∈ grid, ∀ omega, 0 ≤ Dd i omega)
    (hBdnn : ∀ i ∈ grid, ∀ omega, 0 ≤ Bd i omega)
    (hDdzero : ¬ l < L → ∀ i ∈ grid, ∀ omega, Dd i omega = 0)
    (hDdmeas : ∀ i ∈ grid, Measurable (Dd i))
    (hBdmeas : ∀ i ∈ grid, Measurable (Bd i))
    (hDd : ∀ i ∈ grid, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (Dd i) (localizationAverageT1CubeAmplitude Cd nu l n))
    (Ysq R : ι → ShellSeq d → ℝ) {KY CR : ℝ} (hKY : 0 < KY) (hCR : 0 < CR)
    (hYnn : ∀ i ∈ grid, ∀ omega, 0 ≤ Ysq i omega)
    (hRnn : ∀ i ∈ grid, ∀ omega, 0 ≤ R i omega)
    (hdom : ∀ i ∈ grid, ∀ omega, Bd i omega ^ 2 ≤ Ysq i omega * R i omega)
    (hBdzero : blockVecDot Pvec Pvec = 0 → ∀ i ∈ grid, ∀ omega, Bd i omega = 0)
    (hY : ∀ i ∈ grid, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (Ysq i) KY)
    (hR : ∀ i ∈ grid, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (R i) (localizationAverageT1FourthAmplitude CR nu l L Pvec)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1
        (localizationAverageT1Const * localizationAverageT1CubeBoundConst Cd KY CR)
        nu l L n Pvec) := by
  have hD2raw : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (fun omega => (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Dd i omega ^ 2)
      (localizationAverageT1SecondAmplitude
        (IndependentSums.gammaTriangleConst ((1 : ℝ) / 2) * Cd ^ 2) nu l n) :=
    localizationAverageT1_secondMoment_of_cube_bounds hCd hnu P l L n grid hne Dd
      hDdnn hDdmeas hDdzero hDd
  have hD2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) D2
      (localizationAverageT1SecondAmplitude
        (localizationAverageT1CubeBoundConst Cd KY CR) nu l n) := by
    rw [show D2 = (fun omega => (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Dd i omega ^ 2)
      from funext hD2def]
    exact hD2raw.mono_scale
      (localizationAverageT1SecondAmplitude_mono_const (le_max_left _ _) hnu.le l n)
  have hB2raw : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 4))
      (fun omega => (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Bd i omega ^ 2)
      (localizationAverageT1FourthAmplitude
        (IndependentSums.gammaTriangleConst ((1 : ℝ) / 4) *
          SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
          (KY * CR)) nu l L Pvec) :=
    localizationAverageT1_fourthMoment_of_factor_bounds hnu P l L Pvec hKY hCR grid hne
      Ysq R Bd hYnn hRnn hBdmeas hdom hBdzero hY hR
  have hB2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 4)) B2
      (localizationAverageT1FourthAmplitude
        (localizationAverageT1CubeBoundConst Cd KY CR) nu l L Pvec) := by
    rw [show B2 = (fun omega => (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Bd i omega ^ 2)
      from funext hB2def]
    exact hB2raw.mono_scale
      (localizationAverageT1FourthAmplitude_mono_const (le_max_right _ _) hnu.le l L Pvec)
  exact localizationAverage_T1_of_grid (localizationAverageT1CubeBoundConst_pos hCd) hnu P
    l L n Pvec grid hne Dd Bd T1 D2 B2 hT1 hD2def hB2def hDdnn hBdnn hDdzero hD2 hB2

/-! ## The printed lattice specialisation -/

/-- **The first printed summand on the printed lattice, from the printed per-cube
inputs.**  `localizationAverage_T1_of_cubeBounds` specialised to the actual
printed lattice `3^nℤ^d ∩ cu_m` (`localizationAverageGrid d m n`), with the grid
nonemptiness discharged.  The two moment-average hypotheses are replaced by the printed
per-cube `Γ` bounds. -/
theorem localizationAverage_T1_of_descendantGrid_cubeBounds {Cd nu : ℝ} (hCd : 0 < Cd)
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (l L m n : ℕ) (Pvec : BlockVec d)
    (Dd Bd : TriadicCube d → ShellSeq d → ℝ) (T1 D2 B2 : ShellSeq d → ℝ)
    (hT1 : ∀ omega, T1 omega = ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
      ∑ i ∈ localizationAverageGrid d m n, Dd i omega * Bd i omega)
    (hD2def : ∀ omega, D2 omega = ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
      ∑ i ∈ localizationAverageGrid d m n, Dd i omega ^ 2)
    (hB2def : ∀ omega, B2 omega = ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
      ∑ i ∈ localizationAverageGrid d m n, Bd i omega ^ 2)
    (hDdnn : ∀ i ∈ localizationAverageGrid d m n, ∀ omega, 0 ≤ Dd i omega)
    (hBdnn : ∀ i ∈ localizationAverageGrid d m n, ∀ omega, 0 ≤ Bd i omega)
    (hDdzero : ¬ l < L → ∀ i ∈ localizationAverageGrid d m n, ∀ omega, Dd i omega = 0)
    (hDdmeas : ∀ i ∈ localizationAverageGrid d m n, Measurable (Dd i))
    (hBdmeas : ∀ i ∈ localizationAverageGrid d m n, Measurable (Bd i))
    (hDd : ∀ i ∈ localizationAverageGrid d m n, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 1) (Dd i) (localizationAverageT1CubeAmplitude Cd nu l n))
    (Ysq R : TriadicCube d → ShellSeq d → ℝ) {KY CR : ℝ} (hKY : 0 < KY) (hCR : 0 < CR)
    (hYnn : ∀ i ∈ localizationAverageGrid d m n, ∀ omega, 0 ≤ Ysq i omega)
    (hRnn : ∀ i ∈ localizationAverageGrid d m n, ∀ omega, 0 ≤ R i omega)
    (hdom : ∀ i ∈ localizationAverageGrid d m n, ∀ omega,
      Bd i omega ^ 2 ≤ Ysq i omega * R i omega)
    (hBdzero : blockVecDot Pvec Pvec = 0 →
      ∀ i ∈ localizationAverageGrid d m n, ∀ omega, Bd i omega = 0)
    (hY : ∀ i ∈ localizationAverageGrid d m n, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma ((1 : ℝ) / 2)) (Ysq i) KY)
    (hR : ∀ i ∈ localizationAverageGrid d m n, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma ((1 : ℝ) / 2)) (R i)
      (localizationAverageT1FourthAmplitude CR nu l L Pvec)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1
        (localizationAverageT1Const * localizationAverageT1CubeBoundConst Cd KY CR)
        nu l L n Pvec) :=
  localizationAverage_T1_of_cubeBounds hCd hnu P l L n Pvec (localizationAverageGrid d m n)
    (localizationAverageGrid_nonempty m n) Dd Bd T1 D2 B2 hT1 hD2def hB2def hDdnn hBdnn
    hDdzero hDdmeas hBdmeas hDd Ysq R hKY hCR hYnn hRnn hdom hBdzero hY hR

end SuperdiffusionCLT.Section2.Localization
