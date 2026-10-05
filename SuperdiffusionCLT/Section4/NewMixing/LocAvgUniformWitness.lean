/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.LocAvgUniformGridBf
public import SuperdiffusionCLT.Probability.OrliczTriangleSmallIndex
public import SuperdiffusionCLT.Frozen.Section2.LocalizationAverage

/-!
# `locAvg_uniform`: a `Pvec`-uniform witness for `localization_average`

`SuperdiffusionCLT.Frozen.Section2.localization_average`
reads `∀ Pvec, ∃ X, ...`: the error witness `X` is chosen *after* the test
vector `Pvec`, so a consumer that needs the same witness at every `Pvec`
simultaneously (e.g. at a random `h0`, or maximized over a unit vector `e`)
cannot literally instantiate it.

This file proves `locAvg_uniform`: `∃ X0` (an explicit `Pvec`-independent,
`Γ_{1/3}`-Orlicz-controlled witness) such that the anchor's inequality holds
for **every** `Pvec` with `X := ⟪Pvec, Pvec⟫ * X0`. The construction is pure
linear algebra plus a finite triangle inequality: the inner
expression is, for each fixed `omega`, a bilinear form in `Pvec` via a
`Pvec`-independent (grid-averaged) matrix (`LocAvgUniformGridBf.lean`); by
`locAvgU_biform_bound` (`LocAvgUniformBiform.lean`) that bilinear form's
diagonal is controlled *uniformly in `Pvec`* by testing `localization_average` at only the
`(2d)²` vectors `blockBasis α + blockBasis β`, and the resulting finitely many
witnesses are combined into one via the `Γ_{1/3}`-triangle inequality
(`isBigO_gammaSigma_finset_sum_of_le_one`, `OrliczTriangleSmallIndex.lean`).
`localization_average` is used only through its statement.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open MeasureTheory

noncomputable section

/-- **The `Pvec`-uniform localization-average witness.** Same statement as
`localization_average`, except the error witness `X0` is chosen
*before* `Pvec`, and the bound becomes `⟪Pvec, Pvec⟫ * X0 omega`. -/
theorem locAvg_uniform (d : ℕ) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m n l L : ℕ, n ≤ l → l ≤ m → l ≤ L →
            ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X0 ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X0
                  (C * nu ^ (-(3 : ℝ)) *
                    ((if l < L then (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) else 0) +
                      max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
                        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))))) ∧
              ∀ (Pvec : Homogenization.BlockVec d)
                (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                |((Homogenization.descendantsAtDepth
                        (Homogenization.originCube d (m : ℤ))
                        (m - n)).card : ℝ)⁻¹ *
                    ∑ R ∈ Homogenization.descendantsAtDepth
                        (Homogenization.originCube d (m : ℤ)) (m - n),
                      Homogenization.blockVecDot Pvec
                        (Homogenization.blockMatVecMul
                          (Homogenization.ofFullBlockMat
                            (Homogenization.toFullBlockMat
                                (Homogenization.coarseBlockMatrix
                                  (Homogenization.cubeSet R)
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField) -
                              Homogenization.toFullBlockMat
                                (Homogenization.Book.Ch02.blockMatMul
                                  (Homogenization.Book.Ch02.blockMatTranspose
                                    (Homogenization.Book.Ch02.blockG
                                      (-Homogenization.volumeAverageMat
                                        (Homogenization.cubeSet R)
                                        (fun y =>
                                          SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                            omega l L y))))
                                  (Homogenization.Book.Ch02.blockMatMul
                                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                      nu l P
                                      (Homogenization.cubeSet
                                        (Homogenization.originCube d (n : ℤ))))
                                    (Homogenization.Book.Ch02.blockG
                                      (-Homogenization.volumeAverageMat
                                        (Homogenization.cubeSet R)
                                        (fun y =>
                                          SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                            omega l L y)))))))
                          Pvec)| ≤
                  Homogenization.blockVecDot Pvec Pvec * X0 omega := by
  obtain ⟨C, hC⟩ := SuperdiffusionCLT.Frozen.Section2.localization_average d
  set Cuse : ℝ := max C 0 + 1 with hCusedef
  have hCusepos : (0 : ℝ) < Cuse := by
    rw [hCusedef]; have := le_max_right C 0; linarith only [this]
  have hCleCuse : C ≤ Cuse := by
    rw [hCusedef]; have := le_max_left C 0; linarith only [this]
  refine ⟨((4 : ℝ) * d + 1) *
      (4 * (2 / ((1 : ℝ) / 3)) ^ ((12 : ℝ) / ((1 : ℝ) / 3))) *
      (4 * (d : ℝ) ^ 2) * (4 * Cuse), ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n l L hnl hlm hlL
  set Kappa : ℝ := (if l < L then (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) else 0) +
      max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))) with hKappadef
  have hKappapos : (0 : ℝ) < Kappa := by
    rw [hKappadef]
    have h1 : (0 : ℝ) ≤ if l < L then (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) else 0 := by
      split_ifs with h <;> positivity
    have h2 : (0 : ℝ) < max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))) := by positivity
    linarith only [h1, h2]
  have hspec := hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n l L hnl hlm hlL
  choose Xw hXwmeas hXwBigO hXwbound using hspec
  set Aunif : ℝ := 4 * Cuse * nu ^ (-(3 : ℝ)) * Kappa with hAunifdef
  have hAunifpos : (0 : ℝ) < Aunif := by
    rw [hAunifdef]
    have hnupow : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
    positivity
  -- The standard basis vectors are orthonormal.
  have hself : ∀ α : BlockCoord d, blockVecDot (blockBasis α) (blockBasis α) = 1 := by
    intro α
    cases α with
    | inl i => simp [blockBasis, blockVecDot, vecDot_single_left, vecDot_zero_left]
    | inr i => simp [blockBasis, blockVecDot, vecDot_single_left, vecDot_zero_left]
  have hortho : ∀ α β : BlockCoord d, α ≠ β → blockVecDot (blockBasis α) (blockBasis β) = 0 := by
    intro α β hne
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            have hij : i ≠ j := fun h => hne (by rw [h])
            simp [blockBasis, blockVecDot, vecDot_single_left, vecDot_zero_left, Ne.symm hij]
        | inr j => simp [blockBasis, blockVecDot, vecDot_zero_left, vecDot_zero_right]
    | inr i =>
        cases β with
        | inl j => simp [blockBasis, blockVecDot, vecDot_zero_left, vecDot_zero_right]
        | inr j =>
            have hij : i ≠ j := fun h => hne (by rw [h])
            simp [blockBasis, blockVecDot, vecDot_single_left, vecDot_zero_left, Ne.symm hij]
  -- Step 1: upgrade every witness to the common amplitude `Aunif`.
  have hupgrade : ∀ p : BlockCoord d × BlockCoord d,
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3))
        (Xw (blockBasis p.1 + blockBasis p.2)) Aunif := by
    intro p
    refine (hXwBigO (blockBasis p.1 + blockBasis p.2)).mono_scale ?_
    have hdotle : Homogenization.blockVecDot (blockBasis p.1 + blockBasis p.2)
        (blockBasis p.1 + blockBasis p.2) ≤ 4 := by
      rcases eq_or_ne p.1 p.2 with heq | hne
      · rw [heq]
        have h2 : blockBasis p.2 + blockBasis p.2 = (2 : ℝ) • blockBasis p.2 :=
          (two_smul ℝ _).symm
        rw [h2, blockVecDot_smul_left, blockVecDot_smul_right, hself p.2]
        norm_num
      · rw [blockVecDot_add_left, blockVecDot_add_right, blockVecDot_add_right,
          hself p.1, hself p.2, hortho p.1 p.2 hne,
          blockVecDot_comm (blockBasis p.2) (blockBasis p.1), hortho p.1 p.2 hne]
        norm_num
    have hnupownn : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg hnu.le _
    have hKappann : (0 : ℝ) ≤ Kappa := hKappapos.le
    calc C * nu ^ (-(3 : ℝ)) * Homogenization.blockVecDot (blockBasis p.1 + blockBasis p.2)
          (blockBasis p.1 + blockBasis p.2) * Kappa
        ≤ Cuse * nu ^ (-(3 : ℝ)) * 4 * Kappa := by
          have hstep1 : C * nu ^ (-(3 : ℝ)) ≤ Cuse * nu ^ (-(3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCleCuse hnupownn
          have hstep2 : C * nu ^ (-(3 : ℝ)) *
              Homogenization.blockVecDot (blockBasis p.1 + blockBasis p.2)
                (blockBasis p.1 + blockBasis p.2) ≤ Cuse * nu ^ (-(3 : ℝ)) * 4 := by
            calc C * nu ^ (-(3 : ℝ)) *
                Homogenization.blockVecDot (blockBasis p.1 + blockBasis p.2)
                  (blockBasis p.1 + blockBasis p.2)
                ≤ Cuse * nu ^ (-(3 : ℝ)) *
                    Homogenization.blockVecDot (blockBasis p.1 + blockBasis p.2)
                      (blockBasis p.1 + blockBasis p.2) :=
                  mul_le_mul_of_nonneg_right hstep1 (blockVecDot_nonneg _)
              _ ≤ Cuse * nu ^ (-(3 : ℝ)) * 4 :=
                  mul_le_mul_of_nonneg_left hdotle (by positivity)
          exact mul_le_mul_of_nonneg_right hstep2 hKappann
      _ = Aunif := by rw [hAunifdef]; ring
  have hdne : NeZero d := ⟨by have := hPrefix.dimension; omega⟩
  have hUnivNe : (Finset.univ : Finset (BlockCoord d × BlockCoord d)).Nonempty :=
    Finset.univ_nonempty
  -- Step 2: combine the finitely many upgraded witnesses via the triangle inequality.
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_le_one
    (mu := P.toMeasure) (s := (Finset.univ : Finset (BlockCoord d × BlockCoord d)))
    (X := fun p => Xw (blockBasis p.1 + blockBasis p.2)) (a := fun _ => Aunif)
    (sigma := (1 : ℝ) / 3) (by norm_num) (by norm_num) hUnivNe
    (fun p _ => hAunifpos) (fun p _ => hupgrade p)
    (fun p _ => hXwmeas (blockBasis p.1 + blockBasis p.2))
  set X0raw : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ :=
    fun omega => ∑ p : BlockCoord d × BlockCoord d, Xw (blockBasis p.1 + blockBasis p.2) omega
    with hX0rawdef
  set X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ :=
    fun omega => ((4 : ℝ) * d + 1) * X0raw omega with hX0def
  have hX0raw_meas : Measurable X0raw := by
    rw [hX0rawdef]
    exact Finset.measurable_sum _ (fun p _ => hXwmeas (blockBasis p.1 + blockBasis p.2))
  have hX0_meas : Measurable X0 := by
    rw [hX0def]; exact hX0raw_meas.const_mul _
  have hX0raw_bigO : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X0raw
      ((4 * (2 / ((1 : ℝ) / 3)) ^ ((12 : ℝ) / ((1 : ℝ) / 3))) *
        ∑ _p : BlockCoord d × BlockCoord d, Aunif) := hsum
  have hX0_bigO : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X0
      (((4 : ℝ) * d + 1) *
        ((4 * (2 / ((1 : ℝ) / 3)) ^ ((12 : ℝ) / ((1 : ℝ) / 3))) *
          ∑ _p : BlockCoord d × BlockCoord d, Aunif)) := by
    rw [hX0def]
    exact hX0raw_bigO.const_mul (by positivity)
  -- The `Finset.univ`-cardinality of `BlockCoord d × BlockCoord d` is exactly `4d²`.
  have hcard2 : (Finset.univ : Finset (BlockCoord d × BlockCoord d)).card = 4 * (d : ℕ) ^ 2 := by
    have h1 : (Finset.univ : Finset (BlockCoord d × BlockCoord d)).card =
        Fintype.card (BlockCoord d) * Fintype.card (BlockCoord d) := by
      rw [Finset.card_univ, Fintype.card_prod]
    rw [h1, locAvgU_card_blockCoord d]
    ring
  have hsumconst : (∑ _p : BlockCoord d × BlockCoord d, Aunif) = 4 * (d : ℝ) ^ 2 * Aunif := by
    rw [Finset.sum_const, hcard2, nsmul_eq_mul]
    push_cast
    ring
  refine ⟨X0, hX0_meas, ?_, ?_⟩
  · refine hX0_bigO.mono_scale (le_of_eq ?_)
    rw [hsumconst, hAunifdef]
    ring
  · intro Pvec omega
    -- Instantiate the finite-basis polarization bound at this `omega`'s
    -- `Pvec`-independent grid matrix.
    have hbound := locAvgU_biform_bound
      (Bf := locAvgU_gridBf
        (Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - n))
        (fun R => Homogenization.ofFullBlockMat
          (Homogenization.toFullBlockMat
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) -
            Homogenization.toFullBlockMat
              (Homogenization.Book.Ch02.blockMatMul
                (Homogenization.Book.Ch02.blockMatTranspose
                  (Homogenization.Book.Ch02.blockG
                    (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y =>
                          SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y))))
                (Homogenization.Book.Ch02.blockMatMul
                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu l P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                  (Homogenization.Book.Ch02.blockG
                    (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y =>
                          SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y))))))))
      (locAvgU_gridBf_add_left _ _) (locAvgU_gridBf_add_right _ _)
      (locAvgU_gridBf_smul_left _ _) (locAvgU_gridBf_smul_right _ _)
      (wit := fun p => Xw (blockBasis p.1 + blockBasis p.2) omega)
      (fun p => (abs_nonneg _).trans (hXwbound (blockBasis p.1 + blockBasis p.2) omega))
      (fun α β => hXwbound (blockBasis α + blockBasis β) omega)
      Pvec
    have heqX0 : ((4 : ℝ) * d + 1) *
        ∑ p : BlockCoord d × BlockCoord d, Xw (blockBasis p.1 + blockBasis p.2) omega = X0 omega := by
      rw [hX0def, hX0rawdef]
    rw [heqX0] at hbound
    exact hbound

end

end SuperdiffusionCLT.Section4.NewMixing
