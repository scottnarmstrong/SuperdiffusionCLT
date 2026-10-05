/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGapsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsE

/-!
# The `L^2(P)` second moment of the descendant average of the quadratic tail carrier

This is the input of the Hoelder step of Step 3 in the proof of `l.RHS.term3`.  The Hoelder
step `weightedBlockAverage_integral_le` (`Section3/Terms/RHSTerm3SourceGaps.lean`) consumes
the `L^2(P)` condition `hQuadZc` of `holder_terms_bridge`
(`Section3/Terms/RHSTerm3SourceGapsB.lean`): the descendant average of the carrier
`quad_z = translatedStreamQuadForm nu S.ell S.LPrime e omega z` over the depth-`(k - n)`
descendants of the coarse block `zc` is square integrable.  This module proves it.

## The route

* The crude quenched ellipticity bound `s_{L',*}^{-1}(z + cu_n) <= nu^{-1} Id`
  (`matLoewnerLE_sigmaStarInvCoarse_cutoffCube` of
  `Section3/Setup/CrudeBounds.lean`) tested at the coarse average of the stream
  increment gives the pointwise bound `q_z <= nu^{-1} * s_z`.
* The `Γ₁` envelope of `s_z` on every scale-`n` cube is
  `isBigO_gammaSigma_translatedStreamNormSq_originCube`
  (`Section3/Terms/RHSTerm3InputsE.lean`) transported to the translate by
  `isBigO_gammaSigma_translatedStreamNormSq`; its second moment is
  `hasGammaMomentGrowthWith_of_isBigO_gammaSigma` at the exponent `2`, i.e. the
  fourth-moment envelope of the carrier at `p = 4` read at `q = 2`.
* Monotonicity of the integral closes `quad_z in L^2(P)`, and the finite
  average of square-integrable functions is square integrable
  (`memLp_finsetSum`), which is `hQuadZc`.

The consumer is `holder_terms_bridge` (binder `hQuadZc`) in
`SuperdiffusionCLT/Section3/Terms/RHSTerm3SourceGapsB.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The crude ellipticity bound on the tested quadratic form -/

/-- **`q_{s_{L,*}^{-1}}(v) <= nu^{-1}|v|^2`**, the crude quenched ellipticity
bound `e.CG.bounds.1` on a translated cube, tested at the coarse average of the
stream increment.  This is the carrier `q_z` of the averaged quadratic tail,
bounded by the carrier `s_z`; the proof is the one of
`translatedStreamQuadFormLower_le_nuInv_mul`
(`Section3/Terms/RHSTerm3SourceGaps.lean`) at the matrix `s_{L,*}^{-1}`. -/
theorem translatedStreamQuadForm_le_nuInv_mul [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamQuadForm nu l L e omega z ≤
      nu⁻¹ * translatedStreamNormSq l L e omega z := by
  have hL := matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega L z
    (streamIncrementCubeVec l L e omega z)
  have hrw : Homogenization.sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toFun =
      Homogenization.sigmaStarInvCoarse (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField := by
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    rfl
  rw [hrw] at hL
  have hsm : vecDot (streamIncrementCubeVec l L e omega z)
      (matVecMul (nu⁻¹ • (1 : Mat d)) (streamIncrementCubeVec l L e omega z)) =
      nu⁻¹ * translatedStreamNormSq l L e omega z := by
    rw [smul_matVecMul, vecDot_smul_right]
    refine congrArg (fun t : ℝ => nu⁻¹ * t) ?_
    show vecDot (streamIncrementCubeVec l L e omega z)
        (matVecMul (1 : Mat d) (streamIncrementCubeVec l L e omega z)) =
      vecDot (streamIncrementCubeVec l L e omega z)
        (streamIncrementCubeVec l L e omega z)
    refine congrArg (fun u : Vec d =>
      vecDot (streamIncrementCubeVec l L e omega z) u) ?_
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [hsm] at hL
  show vecDot (streamIncrementCubeVec l L e omega z)
      (matVecMul (Homogenization.sigmaStarInvCoarse (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField)
        (streamIncrementCubeVec l L e omega z)) ≤
    nu⁻¹ * translatedStreamNormSq l L e omega z
  linarith only [hL]

/-! ## The `L^2(P)` second moment of the carrier on a scale-`n` cube -/

/-- **The carrier `q_z` is in `L^2(P)` on every scale-`n` cube**, for a unit
direction `e` and scales `n <= ell < L`.  The proof is the pointwise bound
`q_z <= nu^{-1} * s_z` together with the second moment of the
`Γ₁` envelope of `s_z`: the fourth-moment envelope of the carrier
(`isBigO_gammaSigma_translatedStreamNormSq_originCube`, transported to the
translate) read at the exponent `2` by
`hasGammaMomentGrowthWith_of_isBigO_gammaSigma`. -/
theorem memLp_two_translatedStreamQuadForm [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nn l L : ℕ} (hnl : nn ≤ l) (hlL : l < L)
    {e : Vec d} (he : vecNormSq e = 1)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) :
    MemLp (fun omega : ShellSeq d => translatedStreamQuadForm nu l L e omega z) 2
      P.toMeasure := by
  have hcent : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => translatedStreamNormSq l L e omega (originCube d (nn : ℤ)))
      (streamTailConst d * ((L - l : ℕ) : ℝ)) :=
    isBigO_gammaSigma_translatedStreamNormSq_originCube hPrefix hJ2 hJ3 hJ4 hnl hlL he
  have hbig : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => translatedStreamNormSq l L e omega z)
      (streamTailConst d * ((L - l : ℕ) : ℝ)) := by
    refine isBigO_gammaSigma_translatedStreamNormSq hPrefix hJ2 l L e ?_
    rw [hz]
    exact hcent
  have hK : (0 : ℝ) < streamTailConst d * ((L - l : ℕ) : ℝ) := by
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
    have hgap : (0 : ℝ) < ((L - l : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hlL
    exact mul_pos (streamTailConst_pos hd) hgap
  have hgrowth := hasGammaMomentGrowthWith_of_isBigO_gammaSigma (μ := P.toMeasure)
    (show (0 : ℝ) < 1 by norm_num) hK
    (measurable_translatedStreamNormSq l L e z).aemeasurable hbig
  obtain ⟨hint, -⟩ := hgrowth (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
  have hint' : Integrable (fun omega : ShellSeq d =>
      translatedStreamNormSq l L e omega z ^ (2 : ℕ)) P.toMeasure := by
    refine hint.congr (Filter.Eventually.of_forall fun omega => ?_)
    show |translatedStreamNormSq l L e omega z| ^ ((2 : ℕ) : ℝ) =
      translatedStreamNormSq l L e omega z ^ (2 : ℕ)
    rw [Real.rpow_natCast, abs_of_nonneg (translatedStreamNormSq_nonneg l L e omega z)]
  refine (memLp_two_iff_integrable_sq
    (measurable_translatedStreamQuadForm hnu l L e z).aestronglyMeasurable).2 ?_
  refine Integrable.mono' (hint'.const_mul (nu⁻¹ ^ (2 : ℕ)))
    ((measurable_translatedStreamQuadForm hnu l L e z).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (translatedStreamQuadForm_nonneg hnu l L e omega z) 2)]
  have hbound := pow_le_pow_left₀ (translatedStreamQuadForm_nonneg hnu l L e omega z)
    (translatedStreamQuadForm_le_nuInv_mul hnu l L e omega z) 2
  rwa [mul_pow] at hbound

/-! ## The descendant average -/

/-- **The `L^2(P)` side condition `hQuadZc` of `holder_terms_bridge`**
(`Section3/Terms/RHSTerm3SourceGapsB.lean`): the descendant average of the quadratic tail
carrier over the depth-`(k - n)` descendants of the coarse block `zc` of scale
`k = coarseBlockScale d S` is in `L^2(P)`.

The measurability half is `measurable_translatedStreamQuadForm`; the
second moment is the triangle inequality for the finite average
(`memLp_finsetSum`), the per-term second moment being
`memLp_two_translatedStreamQuadForm` at the scale `S.n` of every descendant
(`scale_eq_sub_of_mem_descendantsAtDepth` together with
`coarse_block_scale_choice`). -/
theorem memLp_two_descendantAverage_translatedStreamQuadForm [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    {zc : TriadicCube d} (hzc : zc.scale = ((coarseBlockScale d S : ℕ) : ℤ)) :
    MemLp (fun omega : ShellSeq d =>
      (((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
          translatedStreamQuadForm nu S.ell S.LPrime e omega z) 2 P.toMeasure := by
  have hkn : S.n ≤ coarseBlockScale d S :=
    le_trans hSorder.n_lt_ell.le
      (coarse_block_scale_choice d S hSorder.ell_lt_ellPrime.le).1
  have hlL : S.ell < S.LPrime :=
    lt_trans (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m) hSorder.m_lt_LPrime
  have hzsn : ∀ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
      z.scale = ((S.n : ℕ) : ℤ) := by
    intro z hz
    have h1 := scale_eq_sub_of_mem_descendantsAtDepth hz
    rw [hzc, Nat.cast_sub hkn, sub_sub_cancel] at h1
    exact h1
  have hA : ∀ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
      MemLp (fun omega : ShellSeq d =>
        translatedStreamQuadForm nu S.ell S.LPrime e omega z) 2 P.toMeasure := by
    intro z hz
    exact memLp_two_translatedStreamQuadForm (nn := S.n) (l := S.ell) (L := S.LPrime)
      (z := z) hnu hPrefix hJ2 hJ3 hJ4 hSorder.n_lt_ell.le hlL he (hzsn z hz)
  have hB : MemLp (fun omega : ShellSeq d =>
      ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
        translatedStreamQuadForm nu S.ell S.LPrime e omega z) 2 P.toMeasure :=
    memLp_finsetSum (descendantsAtDepth zc (coarseBlockScale d S - S.n))
      (fun z hz => hA z hz)
  exact hB.const_mul _

end

end SuperdiffusionCLT.Section3.Terms