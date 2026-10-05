/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.Term1Localization
public import SuperdiffusionCLT.Section4.Mixing.Term2ScaleComparison
public import SuperdiffusionCLT.Frozen.Section2.LocalizationAverage
public import SuperdiffusionCLT.Section4.Ellipticity.EllipticityBelowCutoff

/-!
# `p.mixing.P.three.prime#term1-bound`, polarized reduction

This combines `l.localization.average` (`Frozen/Section2/LocalizationAverage.lean`), applied
at the three test vectors `p + q`, `p`, `q`, with `mixTerms_polarization_avg`
and `mixTerms_isSymmetricBlockMat_coarseBlockMatrix` /
`mixTerms_isSymmetricBlockMat_gaugeConjugate_blockDiag` (both
`Term1Localization.lean`) to bound twice the cross-term average by the sum of
the three per-vector witnesses.

This is the algebraic core of the "testing with `P`, taking the supremum over a finite net" step.
The remaining printed step reduces this `|v|²`-scaled bound to the `Aell`-normalized
`O_{Γ1/3}(m^{-5000})` bound via `e.Enaught.vs.Ahom.L.crude` together with the margins of
`e.good.gaps`, "`K(d)` chosen sufficiently large". The crude ellipticity conversion it needs is
`mixTerms_crudeEllipticity` below. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions

variable {d : ℕ}

/-- The localization-term matrix at a descendant cube `R`, an auxiliary scale
`ell`, and a gauge point `omega`: `bfA_L(R) - G_{-h_R}^t Aell(cu_n) G_{-h_R}`,
exactly the matrix bounded (pointwise, at a single test vector) by
`l.localization.average`. -/
noncomputable def mixTerms_localizationTermMatrix (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ell L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (n : ℤ) (R : Homogenization.TriadicCube d) : BlockMat d :=
  ofFullBlockMat
    (toFullBlockMat
        (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) -
      toFullBlockMat
        (blockMatMul
          (blockMatTranspose
            (blockG
              (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                  (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega ell L y)))))
          (blockMatMul (annealedBlockMatrix nu ell P (Homogenization.cubeSet (Homogenization.originCube d n)))
            (blockG
              (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                  (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega ell L y)))))))

/-- The localization-term matrix is symmetric, for every descendant cube `R`
and gauge point `omega`, given `ShellLawJ4` (which makes `Aell(cu_n)` block
diagonal with scalar blocks, `mixTerms_annealedBlockDiag`). -/
theorem mixTerms_isSymmetricBlockMat_localizationTermMatrix [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ell L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : Homogenization.TriadicCube d) :
    IsSymmetricBlockMat (mixTerms_localizationTermMatrix nu omega ell L P n R) := by
  refine isSymmetricBlockMat_ofFullBlockMat_sub
    (mixTerms_isSymmetricBlockMat_coarseBlockMatrix (Homogenization.cubeSet R)
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) ?_
  rw [mixTerms_annealedBlockDiag hnu ell hJ4 n]
  exact mixTerms_isSymmetricBlockMat_gaugeConjugate_blockDiag _ _ _

/-- **`p.mixing.P.three.prime#term1-bound`, polarized reduction.** See the
file docstring. -/
theorem mixTerms_term1PolarizedBound (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
            ∀ m n ell L : ℕ, n ≤ ell → ell ≤ m → ell ≤ L →
              ∀ p q : Homogenization.BlockVec d,
                ∃ X1 X2 X3 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X1 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X1
                        (C * nu ^ (-(3 : ℝ)) * Homogenization.blockVecDot (p + q) (p + q) *
                          ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
                            max 1 (ell : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
                              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))))) ∧
                    Measurable X2 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                        (C * nu ^ (-(3 : ℝ)) * Homogenization.blockVecDot p p *
                          ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
                            max 1 (ell : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
                              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))))) ∧
                    Measurable X3 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X3
                        (C * nu ^ (-(3 : ℝ)) * Homogenization.blockVecDot q q *
                          ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
                            max 1 (ell : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
                              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))))) ∧
                      ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                        2 *
                            (((Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ))
                                    (m - n)).card : ℝ)⁻¹ *
                              ∑ R ∈ Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ))
                                  (m - n),
                                Homogenization.blockVecDot p
                                  (Homogenization.blockMatVecMul
                                    (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
                          X1 omega + X2 omega + X3 omega := by
  obtain ⟨C, hC⟩ := SuperdiffusionCLT.Frozen.Section2.localization_average d
  refine ⟨C, fun nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL p q => ?_⟩
  obtain ⟨X1, hX1meas, hX1O, hX1bd⟩ :=
    hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL (p + q)
  obtain ⟨X2, hX2meas, hX2O, hX2bd⟩ :=
    hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL p
  obtain ⟨X3, hX3meas, hX3O, hX3bd⟩ :=
    hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL q
  refine ⟨X1, X2, X3, hX1meas, hX1O, hX2meas, hX2O, hX3meas, hX3O, fun omega => ?_⟩
  set s := Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - n) with hs
  have hSymm : ∀ R ∈ s, IsSymmetricBlockMat (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) :=
    fun R _ => mixTerms_isSymmetricBlockMat_localizationTermMatrix hnu omega ell L hJ4 (n : ℤ) R
  have hpol := mixTerms_polarization_avg s (fun R => mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R)
    hSymm p q
  have hb1 := hX1bd omega
  have hb2 := hX2bd omega
  have hb3 := hX3bd omega
  have h1 :
      (s.card : ℝ)⁻¹ * ∑ R ∈ s,
          blockVecDot (p + q) (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R)
            (p + q)) ≤
        X1 omega :=
    le_trans (le_abs_self _) hb1
  have h2 :
      -((s.card : ℝ)⁻¹ * ∑ R ∈ s,
          blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) p)) ≤
        X2 omega := by
    have hneg := le_abs_self
      (-((s.card : ℝ)⁻¹ * ∑ R ∈ s,
        blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) p)))
    rw [abs_neg] at hneg
    exact le_trans hneg hb2
  have h3 :
      -((s.card : ℝ)⁻¹ * ∑ R ∈ s,
          blockVecDot q (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
        X3 omega := by
    have hneg := le_abs_self
      (-((s.card : ℝ)⁻¹ * ∑ R ∈ s,
        blockVecDot q (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)))
    rw [abs_neg] at hneg
    exact le_trans hneg hb3
  rw [hpol]
  linarith only [h1, h2, h3]

/-! ## The crude ellipticity conversion `e.Enaught.vs.Ahom.L.crude`

This is the first half of the reduction left open above, using
`SuperdiffusionCLT.Section4.Ellipticity.ellipBelow_crude_comparison`
(`Section4/Ellipticity/EllipticityBelowCutoff.lean`): the Euclidean quadratic
form `blockVecDot v v` is bounded by a constant multiple of the `Aell`
quadratic form, with an explicit `nu`- and `ell`-polynomial constant, no
threshold needed for this half. -/

open SuperdiffusionCLT.Section4.Ellipticity in
/-- The envelope's two diagonal scalars are each at least `nu`, since `0 <
nu ≤ 1 ≤ cutoffEnvelopeConst d` and both scalars have `nu`- and
`nu⁻¹`-monomial summands dominating `nu`. -/
private theorem mixTerms_nu_le_envelopeUpperScalar {nu : ℝ} (hnu : 0 < nu) (d m : ℕ) :
    nu ≤ envelopeUpperScalar d nu m := by
  have hC : 0 ≤ cutoffEnvelopeConst d := (cutoffEnvelopeConst_pos d).le
  have hinv : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hmax : (0 : ℝ) ≤ max 1 (m : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hterm : 0 ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (m : ℝ) := by
    have h1 : 0 ≤ 2 * cutoffEnvelopeConst d := mul_nonneg (by norm_num) hC
    have h2 : 0 ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ := mul_nonneg h1 hinv
    exact mul_nonneg h2 hmax
  unfold envelopeUpperScalar
  linarith only [hterm]

open SuperdiffusionCLT.Section4.Ellipticity in
private theorem mixTerms_nu_le_envelopeLowerScalar {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (d : ℕ) : nu ≤ envelopeLowerScalar d nu := by
  have hCge1 : (1 : ℝ) ≤ cutoffEnvelopeConst d := one_le_cutoffEnvelopeConst d
  have hnuinv : 1 ≤ nu⁻¹ := by
    simpa only [inv_one] using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hnu).2 hnu1
  unfold envelopeLowerScalar
  nlinarith only [hCge1, hnuinv, hnu1]

open SuperdiffusionCLT.Section4.Ellipticity in
/-- **`nu` lower-bounds the envelope quadratic form.** `envelopeBlockMat d nu
m` has both diagonal scalars at least `nu`, so its quadratic form dominates
`nu` times the Euclidean quadratic form. -/
theorem mixTerms_nu_blockVecDot_le_envelopeBlockMat {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (d m : ℕ) (v : BlockVec d) :
    nu * blockVecDot v v ≤ blockVecDot v (blockMatVecMul (envelopeBlockMat d nu m) v) := by
  obtain ⟨p, q⟩ := v
  rw [envelopeBlockMat, blockVecDot_blockDiag_smul_one]
  have hp := vecNormSq_nonneg p
  have hq := vecNormSq_nonneg q
  have hU := mixTerms_nu_le_envelopeUpperScalar hnu d m
  have hD := mixTerms_nu_le_envelopeLowerScalar hnu hnu1 d
  have hUmul : nu * vecNormSq p ≤ envelopeUpperScalar d nu m * vecNormSq p :=
    mul_le_mul_of_nonneg_right hU hp
  have hDmul : nu * vecNormSq q ≤ envelopeLowerScalar d nu * vecNormSq q :=
    mul_le_mul_of_nonneg_right hD hq
  show nu * (vecDot p p + vecDot q q) ≤ _
  have hpp : vecDot p p = vecNormSq p := rfl
  have hqq : vecDot q q = vecNormSq q := rfl
  rw [hpp, hqq]
  nlinarith only [hUmul, hDmul]

open SuperdiffusionCLT.Section4.Ellipticity in
/-- **The crude ellipticity comparison, `e.Enaught.vs.Ahom.L.crude`.** For
`ell ≥ 1`, the Euclidean quadratic form on `BlockVec d` is bounded by
`ellipBelow_crudeConst d * nu^{-3} * ell` times the `Aell(cu_n)` quadratic
form. Combines `mixTerms_nu_blockVecDot_le_envelopeBlockMat` with
`ellipBelow_crude_comparison`. -/
theorem mixTerms_crudeEllipticity (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (ell n : ℕ) (hell : 1 ≤ ell) (v : BlockVec d) :
    blockVecDot v v ≤
      ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ) *
        blockVecDot v
          (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v) := by
  have hlow := mixTerms_nu_blockVecDot_le_envelopeBlockMat hnu hnu1 d ell v
  have hcrude := ellipBelow_crude_comparison d hnu hnu1 P hPrefix hJ2 hJ3 hJ4 ell n hell v
  have hup : blockVecDot v (blockMatVecMul (envelopeBlockMat d nu ell) v) ≤
      ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (ell : ℝ) *
        blockVecDot v
          (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v) := by
    have hRHS : blockMatVecMul ((ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (ell : ℝ)) •
        annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v =
        (ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (ell : ℝ)) •
          blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v :=
      blockMatVecMul_blockSMul _ _ _
    rw [hRHS, blockVecDot_smul_right] at hcrude
    linarith only [hcrude]
  have hchain :
      nu * blockVecDot v v ≤
        ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (ell : ℝ) *
          blockVecDot v
            (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v) :=
    le_trans hlow hup
  have hnu3 : ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ) * nu =
      ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (ell : ℝ) := by
    rw [Real.rpow_neg hnu.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hgoal_mul :
      blockVecDot v v * nu ≤
        ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ) *
          blockVecDot v
            (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v) *
          nu := by
    rw [mul_assoc (ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ)), mul_comm
      (blockVecDot v
        (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) v)),
      ← mul_assoc, hnu3, mul_comm (blockVecDot v v)]
    exact hchain
  exact le_of_mul_le_mul_right hgoal_mul hnu

end SuperdiffusionCLT.Section4.Mixing
