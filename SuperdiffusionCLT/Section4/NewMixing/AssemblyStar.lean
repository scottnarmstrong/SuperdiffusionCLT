/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.Reductions
public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerStepsB
public import SuperdiffusionCLT.Section2.Localization.CoarseCentering
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# The reference cutoff comparison for the annealed lower block

The annealed lower block `shom_{ell,*}^{-1}(cu_n)` is the expectation of the diagonal entry of
`s_*^{-1}(cu_n; a_ell)`. By the cutoff localization, that entry at two cutoffs
`a ≤ b` is comparable up to a random factor `1 ± X` with `X = O_{Γ_1}(C nu^{-2} 3^{-(a-n)})`, and
the entry is at most `nu⁻¹`, so the two annealed blocks differ by at most
`C nu^{-3} 3^{-(a-n)}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

theorem newMixAsm_starCompare (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cst : ℝ, 0 < Cst ∧
      ∀ {nu : ℝ} (_hnu : 0 < nu), nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ1Restriction d P →
          ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ {n a b : ℕ}, n ≤ a → a ≤ b →
            |sigmaBarStarInvSeq nu b P n - sigmaBarStarInvSeq nu a P n| ≤
              Cst * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ (-((a - n : ℕ) : ℝ)) := by
  obtain ⟨C0, hLoc⟩ := SuperdiffusionCLT.Section2.Localization.cutoff_localization_unconditional d hd
  refine ⟨Homogenization.IndependentSums.gammaMomentConst 1 * (|C0| + 1), ?_, ?_⟩
  · have h1 : 0 < Homogenization.IndependentSums.gammaMomentConst 1 :=
      Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num)
    have h2 : 0 < |C0| + 1 := by positivity
    exact mul_pos h1 h2
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 n a b hna hab
  set Q := Homogenization.originCube d (n : ℤ) with hQdef
  have hsub : ((Homogenization.Book.Ch02.cubeDomain Q : Homogenization.Book.Ch02.Domain d) :
      Set (Homogenization.Vec d)) ⊆ Homogenization.openCubeSet Q := by
    rw [Homogenization.Book.Ch02.cubeDomain_coe]
  obtain ⟨X, hXm, hXbig, hXpoint⟩ :=
    (hLoc nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 a n b hna hab
      (Homogenization.Book.Ch02.cubeDomain Q) hsub).1
  -- the entry
  set S : ℕ → ShellSeq d → ℝ := fun c omega =>
    Homogenization.sigmaStarInvCoarse (Homogenization.openCubeSet Q)
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega c).toCoeffField 0 0
    with hSdef
  have hSint : ∀ c : ℕ, sigmaBarStarInvSeq nu c P n = ∫ omega, S c omega ∂P.toMeasure := by
    intro c
    rw [sigmaBarStarInvSeq, sigmaBarStarInvScalar,
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu c P Q 0 0]
    rfl
  have hSbound : ∀ c omega, |S c omega| ≤ nu⁻¹ := fun c omega =>
    SuperdiffusionCLT.Section2.Annealed.abs_entry_sigmaStarInvCoarse_openCubeSet_le hnu omega c Q 0 0
  have hSmeas : ∀ c, Measurable (S c) := fun c =>
    SuperdiffusionCLT.Section2.Annealed.measurable_entry_sigmaStarInvCoarse_openCubeSet hnu c Q 0 0
  have hSintegrable : ∀ c, Integrable (S c) P.toMeasure := fun c =>
    Integrable.of_bound (hSmeas c).aestronglyMeasurable nu⁻¹
      (Filter.Eventually.of_forall fun omega => by
        rw [Real.norm_eq_abs]; exact hSbound c omega)
  -- pointwise comparison
  have hpt : ∀ omega, |S b omega - S a omega| ≤ nu⁻¹ * |X omega| := by
    intro omega
    have hlo := SuperdiffusionCLT.Section2.Annealed.diag_le_of_matLoewnerLE
      (hXpoint omega).2.2.1 (0 : Fin d)
    have hhi := SuperdiffusionCLT.Section2.Annealed.diag_le_of_matLoewnerLE
      (hXpoint omega).2.2.2 (0 : Fin d)
    rw [Homogenization.Book.Ch02.cubeDomain_coe] at hlo hhi
    simp only [Matrix.smul_apply, smul_eq_mul] at hlo hhi
    have hXS : X omega * S a omega ≤ nu⁻¹ * |X omega| := by
      calc X omega * S a omega ≤ |X omega * S a omega| := le_abs_self _
        _ = |X omega| * |S a omega| := abs_mul _ _
        _ ≤ |X omega| * nu⁻¹ := mul_le_mul_of_nonneg_left (hSbound a omega) (abs_nonneg _)
        _ = nu⁻¹ * |X omega| := mul_comm _ _
    rw [abs_le]
    constructor
    · have h1 : S a omega - S b omega ≤ X omega * S a omega := by
        have : (1 - X omega) * S a omega ≤ S b omega := hlo
        linarith only [this]
      linarith only [h1, hXS]
    · have h1 : S b omega - S a omega ≤ X omega * S a omega := by
        have : S b omega ≤ (1 + X omega) * S a omega := hhi
        linarith only [this]
      linarith only [h1, hXS]
  -- the moment of `X`
  set Kamp : ℝ := (|C0| + 1) * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((a - n : ℕ) : ℝ)) with hKampdef
  have hKpos : 0 < Kamp := by
    rw [hKampdef]
    have : 0 < |C0| + 1 := by positivity
    positivity
  have hXbigK : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) X Kamp := by
    refine hXbig.mono_scale ?_
    rw [hKampdef]
    have h1 : C0 ≤ |C0| + 1 := by linarith only [le_abs_self C0]
    have h2 : 0 ≤ nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((a - n : ℕ) : ℝ)) := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    linarith only [h3]
  have hmom := Homogenization.IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := P.toMeasure) (p := 1) (by norm_num) hKpos le_rfl hXm.aemeasurable hXbigK
  simp only [Real.rpow_one, inv_one, mul_one] at hmom
  have hXint : Integrable (fun omega => |X omega|) P.toMeasure := by
    have h := Homogenization.IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (μ := P.toMeasure) (p := 1) (by norm_num) hKpos le_rfl (fun omega => abs_nonneg _)
      (continuous_abs.measurable.comp hXm).aemeasurable hXbigK
    simpa only [Real.rpow_one] using h
  rw [hSint b, hSint a, ← integral_sub (hSintegrable b) (hSintegrable a)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hint2 : ∫ omega, |S b omega - S a omega| ∂P.toMeasure ≤
      ∫ omega, nu⁻¹ * |X omega| ∂P.toMeasure :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (hXint.const_mul _) (Filter.Eventually.of_forall hpt)
  refine hint2.trans ?_
  rw [integral_const_mul]
  have hnuinv : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have h5 := mul_le_mul_of_nonneg_left hmom hnuinv
  refine h5.trans (le_of_eq ?_)
  rw [hKampdef]
  have hnu3 : nu⁻¹ * nu ^ (-(2 : ℝ)) = nu ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hnu]
    norm_num
  calc nu⁻¹ * (Homogenization.IndependentSums.gammaMomentConst 1 *
        ((|C0| + 1) * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((a - n : ℕ) : ℝ))))
      = Homogenization.IndependentSums.gammaMomentConst 1 * (|C0| + 1) *
          (nu⁻¹ * nu ^ (-(2 : ℝ))) * (3 : ℝ) ^ (-((a - n : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hnu3]

end
end SuperdiffusionCLT.Section4.NewMixing
