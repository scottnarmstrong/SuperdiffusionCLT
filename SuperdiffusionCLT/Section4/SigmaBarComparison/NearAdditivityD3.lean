/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityD2
public import SuperdiffusionCLT.Section2.Localization.LocalizationAveragePrintedClose

/-!
# Near-additivity, the moment bound

The localization error at the single cube `cu_n` is controlled by the per-cube
estimates that feed `localization_average` (`localizationDisplayKConst`,
`localizationDisplayGConst`, `localizationY`), composed on the one-cube grid
`descendantsAtDepth cu_n 0 = {cu_n}`: `D_z B_z = O_{Γ_{1/3}}(C ν⁻³ L 3^{-(ell-n)})`.
Its first moment then bounds the left side of `hNearAdd`
(`sbNear_integral_identity`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The one-cube `T1` carrier is the product `D_z B_z` at `cu_n`. -/
theorem sbNear_T1Carrier_self (nu : ℝ) (ell L n : ℕ) (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationT1Carrier nu ell L n n Pvec omega =
      localizationDz nu ell L (originCube d (n : ℤ)) omega *
        localizationB nu ell L (originCube d (n : ℤ)) Pvec omega := by
  simp [localizationT1Carrier]

/-- **`D_z B_z` at the single cube `cu_n`**: the per-cube inputs of
`localization_average`, composed on the one-cube grid. -/
theorem sbNear_T1_isBigO {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n l L : ℕ) (hnl : n ≤ l) (v : BlockVec d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3))
      (localizationT1Carrier nu l L n n v)
      (localizationAverageEnvelopeT1 (localizationAveragePrintedT1Const d) nu l L n v) := by
  have hCd : 0 < localizationDisplayKConst d + localizationDisplayKConst d ^ 2 :=
    add_pos_of_pos_of_nonneg localizationDisplayKConst_pos (sq_nonneg _)
  unfold localizationAveragePrintedT1Const
  refine localizationAverage_T1_of_descendantGrid_cubeBounds
    (KY := SuperdiffusionCLT.Probability.orliczProductConst 1 1)
    (CR := localizationDisplayGConst d) hCd hnu P l L n n v
    (localizationDz nu l L) (fun R => localizationB nu l L R v)
    (localizationT1Carrier nu l L n n v)
    (fun omega => ((localizationAverageGrid d n n).card : ℝ)⁻¹ *
      ∑ R ∈ localizationAverageGrid d n n, localizationDz nu l L R omega ^ 2)
    (fun omega => ((localizationAverageGrid d n n).card : ℝ)⁻¹ *
      ∑ R ∈ localizationAverageGrid d n n, localizationB nu l L R v omega ^ 2)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_
    (fun R => localizationY nu l R ^ 2) (fun R => localizationR nu l L R v)
    (SuperdiffusionCLT.Probability.orliczProductConst_pos 1 1)
    localizationDisplayGConst_pos ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun R _ omega => localizationD_nonneg hnu l L R omega
  · exact localizationB_nonneg_on_grid hnu l L n n v
  · exact fun h R _ omega => localizationD_eq_zero_of_not_lt h R omega
  · exact localizationDz_measurable_on_grid (nu := nu) l L n n
  · exact localizationB_measurable_on_grid hnu l L n n v
  · exact localizationDisplayK_hDd_grid hPrefix hJ3 hnu hnu1 hnl le_rfl L
  · exact fun _ _ _ => sq_nonneg _
  · exact fun _ _ _ => sq_nonneg _
  · exact fun R _ omega =>
      localizationB_sq_le_localizationY_sq_mul_localizationR hnu l L R v omega
  · exact fun h _ _ omega => localizationB_eq_zero_of_dot_eq_zero h omega
  · exact localizationY_sq_isBigO_on_grid_of_lawBinders_four P hnu hPrefix hJ2 hJ3 hJ4 l n n
  · exact localizationDisplayG_R_on_grid P hPrefix hJ2 hJ3 hJ4 hnu hnu1 l L n n hnl v

theorem sbNear_printedT1Const_pos : 0 < localizationAveragePrintedT1Const d :=
  mul_pos localizationAverageT1Const_pos (localizationAverageT1CubeBoundConst_pos
    (add_pos_of_pos_of_nonneg localizationDisplayKConst_pos (sq_nonneg _)))

theorem sbNear_blockVecDot_e0_self : blockVecDot (sbNear_e0 (d := d)) (sbNear_e0 (d := d)) = 1 := by
  simp [sbNear_e0, blockVecDot, vecDot, Pi.single_apply]

/-- The amplitude at `P = (e_0, 0)`, for `ell < L`. -/
theorem sbNear_envelope_eq {nu : ℝ} {ell L : ℕ} (hellL : ell < L) (n : ℕ) :
    localizationAverageEnvelopeT1 (localizationAveragePrintedT1Const d) nu ell L n
        (sbNear_e0 (d := d)) =
      localizationAveragePrintedT1Const d * nu ^ (-(3 : ℝ)) *
        ((L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ))) := by
  rw [localizationAverageEnvelopeT1, sbNear_blockVecDot_e0_self]
  simp only [hellL, ↓reduceIte, mul_one]

/-- **The first-moment bound on the near-additivity defect**:
`|σ̄_L(cu_n) - σ̄_ell(cu_n) - E[quad] - E[cross]| ≤ C ν⁻³ L 3^{-(ell-n)}`, for every
`n ≤ ell < L`, under the standing shell laws only. -/
theorem sbNear_abs_le_moment {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {ell L n : ℕ} (hellL : ell < L)
    (hnl : n ≤ ell) :
    |sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n -
        (∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure) -
        (∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure)| ≤
      IndependentSums.gammaMomentConst ((1 : ℝ) / 3) *
        (localizationAveragePrintedT1Const d * nu ^ (-(3 : ℝ)) *
          ((L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)))) := by
  set K := localizationAveragePrintedT1Const d * nu ^ (-(3 : ℝ)) *
    ((L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ))) with hKdef
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (Nat.zero_le ell).trans_lt hellL
  have hK : 0 < K := mul_pos (mul_pos sbNear_printedT1Const_pos (Real.rpow_pos_of_pos hnu _))
    (mul_pos hLpos (Real.rpow_pos_of_pos (by norm_num) _))
  have hBig := sbNear_T1_isBigO hnu hnu1 P hPrefix hJ2 hJ3 hJ4 n ell L hnl (sbNear_e0 (d := d))
  rw [sbNear_envelope_eq hellL n] at hBig
  have hmeas : Measurable (localizationT1Carrier nu ell L n n (sbNear_e0 (d := d))) :=
    localizationT1Carrier_measurable hnu ell L n n _
  have hmom := IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := P.toMeasure) (p := 1) (by norm_num) hK le_rfl hmeas.aemeasurable hBig
  have hint : Integrable (fun omega =>
      |localizationT1Carrier nu ell L n n (sbNear_e0 (d := d)) omega|) P.toMeasure := by
    have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma (μ := P.toMeasure)
      (p := 1) (by norm_num) hK le_rfl (fun omega => abs_nonneg _)
      (continuous_abs.measurable.comp hmeas).aemeasurable hBig
    simpa only [Real.rpow_one] using h
  simp only [Real.rpow_one, Real.one_rpow, mul_one] at hmom
  rw [sbNear_integral_identity hnu hPrefix hJ2 hJ3 hJ4 hellL n]
  refine (abs_integral_le_integral_abs).trans ((integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint
    (Filter.Eventually.of_forall fun omega => ?_)).trans hmom)
  dsimp only
  rw [sbNear_T1Carrier_self]
  exact (sbNear_localizationML hnu hellL.le n _ omega).trans (le_abs_self _)

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
