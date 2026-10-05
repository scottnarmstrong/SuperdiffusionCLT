/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst

/-!
# The inputs of the Hölder step at the translated carriers

The inputs of the Hölder step in the proof of `e.RHS.term3` (Step 3).  This module supplies
the carriers that the free binders of the Hölder step have to take, and discharges the
inputs that are reachable.

## The carriers

The Hölder step already fixes three of them:

* `bLnorm = translatedBlockNorm nu S.LPrime` (`TranslatedBlocks`),
* `quadLPrime = translatedStreamQuadForm nu S.ell S.LPrime e`
  (`RHSTerm3Inputs`), through
  `quadMoment = E[|avsum_z translatedStreamQuadForm|^2]^{1/2}`,
* the block deviation, through
  `devMoment = coarseBlockDevMoment nu S.ell S.n P (descendantsAtDepth zc _)`
  (`RHSTerm3InputsD`).

The two missing ones are the `sigma_{ell,*}^{-1}` carrier and the
replacement error of the printed argument; they are `translatedStreamQuadFormLower` and
`translatedStreamQuadFormGap` below.

Every quadratic carrier is the printed matrix quadratic form **tested at the
unit direction `e`** of `e.Sec3.p.q.def`.  That is the reading already fixed by
`translatedStreamQuadForm` and by `averaged_quadratic_tail_translated`
(`RHSTerm3Inputs`).

## What is proved here

* `translatedStreamQuadFormLower_le_add_gap`: the triangle hypothesis of the carrier swap,
  from the bilinearity of the tested quadratic form.
* `matrixOperatorNorm_le_sum_diag_of_posSemidef`: for a positive-semidefinite
  matrix the Euclidean operator norm is at most the trace.  This is the fact
  the paper uses silently ("`b_ell(z+cu_n)` is symmetric
  positive and `shom_ell(cu_n)` is a scalar", the `e.homs.defs.U` edge of
  `e.bL.to.bhomell.pre0zz`).
* `weightedBlockAverage_one`, `ofReal_weightedBlockAverage_one_le`,
  `holder_term_one`: the first-term hypothesis, i.e. the Jensen step
  `avsum_{z'} |(nabla w)_{z'+cu_k}|^2 <= ||nabla w||^2_{L2(cu_m)}` that the
  source performs silently, together with the passage to
  the expectation.

## Main results

* `translatedStreamQuadFormLower`, `translatedStreamQuadFormGap`.
* `translatedStreamQuadFormLower_le_add_gap`.
* `holder_term_one`.
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
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The two missing quadratic carriers -/

/-- **`(k_l - k_L)_{z+cu_n}^t s_{l,*}^{-1}(z+cu_n) (k_l - k_L)_{z+cu_n}`**, the
quadratic term of `e.bL.to.bhomell.pre0zz` *before* the carrier swap: the quadratic
form of the coarse matrix
`s_{l,*}^{-1}(z + cu_n)` at the tested stream increment
`streamIncrementCubeVec l L e omega z`.  Its companion after the swap is
`translatedStreamQuadForm`, whose carrier is `s_{L,*}^{-1}(z+cu_n)`. -/
def translatedStreamQuadFormLower (nu : ℝ) (l L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  vecDot (streamIncrementCubeVec l L e omega z)
    (matVecMul (sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega l).toCoeffField)
      (streamIncrementCubeVec l L e omega z))

/-- **`|(k_l - k_L)_{z+cu_n}^t (s_{l,*}^{-1} - s_{L,*}^{-1})(z+cu_n)
(k_l - k_L)_{z+cu_n}|`**, the replacement error of
`l.RHS.term3#sigma-star-carrier-swap`, at the tested stream increment. -/
def translatedStreamQuadFormGap (nu : ℝ) (l L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  |vecDot (streamIncrementCubeVec l L e omega z)
    (matVecMul
      (sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega l).toCoeffField -
        sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega L).toCoeffField)
      (streamIncrementCubeVec l L e omega z))|

/-- **The triangle hypothesis of the carrier swap** at these carriers: the tested quadratic form
of `s_{l,*}^{-1}(z+cu_n)` is at most the tested quadratic form of
`s_{L,*}^{-1}(z+cu_n)` plus the replacement error.  This is the linearity of
the quadratic form in the matrix followed by `a ≤ b + |a - b|`; it is the step
the source performs in the words "we may replace `s_{ell,*}^{-1}` by
`s_{L',*}^{-1}` in the quadratic term". -/
theorem translatedStreamQuadFormLower_le_add_gap (nu : ℝ) (l L : ℕ) (e : Vec d)
    (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamQuadFormLower nu l L e omega z ≤
      translatedStreamQuadForm nu l L e omega z +
        translatedStreamQuadFormGap nu l L e omega z := by
  set v : Vec d := streamIncrementCubeVec l L e omega z with hv
  set A : Mat d :=
    sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega l).toCoeffField with hA
  set B : Mat d :=
    sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega L).toCoeffField with hB
  have hsplit : vecDot v (matVecMul (A - B) v) =
      vecDot v (matVecMul A v) - vecDot v (matVecMul B v) := by
    rw [sub_matVecMul, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]
  have habs : vecDot v (matVecMul A v) - vecDot v (matVecMul B v) ≤
      |vecDot v (matVecMul (A - B) v)| := by
    rw [hsplit]
    exact le_abs_self _
  show vecDot v (matVecMul A v) ≤ vecDot v (matVecMul B v) +
    |vecDot v (matVecMul (A - B) v)|
  linarith only [habs]

/-! ## The coordinate decomposition of the operator norm -/

private theorem vecDot_smul_one_self (a : ℝ) (x : Vec d) :
    vecDot x (matVecMul (a • (1 : Mat d)) x) = a * vecNormSq x := by
  rw [smul_matVecMul, vecDot_smul_right]
  refine congrArg (fun t : ℝ => a * t) ?_
  show vecDot x (matVecMul (1 : Mat d) x) = vecDot x x
  refine congrArg (fun v : Vec d => vecDot x v) ?_
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem posSemidef_smul_one {a : ℝ} (ha : 0 ≤ a) :
    Matrix.PosSemidef (a • (1 : Mat d)) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · show Matrix.conjTranspose (a • (1 : Mat d)) = a • (1 : Mat d)
    simp
  · intro x
    have heq : star x ⬝ᵥ Matrix.mulVec (a • (1 : Mat d)) x =
        vecDot x (matVecMul (a • (1 : Mat d)) x) := by
      simp only [Homogenization.vecDot, Homogenization.matVecMul, dotProduct,
        Matrix.mulVec, star_trivial]
    rw [heq, vecDot_smul_one_self]
    exact mul_nonneg ha (vecNormSq_nonneg x)

/-- **The Euclidean operator norm of a positive-semidefinite matrix is at most
its trace.**  This is the fact the paper uses silently where `|b_ell(z+cu_n)|` is
replaced by the sum of its diagonal entries in the coordinate frame
`(e_i)_{i=1}^d`; it is the `e.homs.defs.U` edge of `e.bL.to.bhomell.pre0zz`
("`b_ell(z+cu_n)` is symmetric positive").

The proof is the one the statement suggests: writing `B` for the
positive-semidefinite square root, `x . (M x) = |B x|^2` is at most the squared
Frobenius norm of `B` times `|x|^2`, and that squared Frobenius norm is the
trace of `B^t B = M`. -/
theorem matrixOperatorNorm_le_sum_diag_of_posSemidef [NeZero d] {M : Mat d}
    (hM : M.PosSemidef) : matrixOperatorNorm M ≤ ∑ i : Fin d, M i i := by
  classical
  set B : Mat d := CFC.sqrt M with hBdef
  have hBsymm : B.IsSymm := posSemidef_sqrt_isSymm M
  have hBB : B * B = M := posSemidef_sqrt_mul_self hM
  have htr : matrixFrobeniusNormSq B = ∑ i : Fin d, M i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hMi : M i i = ∑ j : Fin d, B i j * B j i := by
      rw [← hBB]
      exact Matrix.mul_apply
    rw [hMi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hBsymm.apply i j, sq]
  have htr0 : (0 : ℝ) ≤ ∑ i : Fin d, M i i :=
    Finset.sum_nonneg fun i _ => hM.diag_nonneg (i := i)
  have hLoew : MatLoewnerLE M ((∑ i : Fin d, M i i) • (1 : Mat d)) := by
    intro x
    have hquad : vecDot x (matVecMul M x) = vecNormSq (matVecMul B x) :=
      (vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul hM x).symm
    have hfrob : vecNormSq (matVecMul B x) ≤ matrixFrobeniusNormSq B * vecNormSq x :=
      vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq B x
    have hrhs : vecDot x (matVecMul ((∑ i : Fin d, M i i) • (1 : Mat d)) x) =
        (∑ i : Fin d, M i i) * vecNormSq x := vecDot_smul_one_self _ x
    rw [hrhs, hquad, ← htr]
    linarith only [hfrob]
  have hnorm := matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hM
    (posSemidef_smul_one htr0) hLoew
  rwa [matrixOperatorNorm_smul_one_eq_of_nonneg htr0] at hnorm

/-! ## `e.bL.to.bhomell.pre0zz` at the carrier `translatedBlockNorm` -/

/-! ## `hTerm1`: the Jensen step -/

/-- At the constant weight `1` the weighted coarse-block average
is the plain lattice average of `|(nabla w)_{z'+cu_k}|^2`: the inner
average over the descendants of `z'` is an average of ones. -/
theorem weightedBlockAverage_one (n k m : ℕ) (g : Vec d → Vec d) :
    weightedBlockAverage d n k m g (fun _ => (1 : ℝ)) =
      ((largeCubeSubcubes d k m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k m,
          vecNormSq (volumeAverageVec (openCubeSet z') g) := by
  classical
  simp only [weightedBlockAverage]
  refine congrArg (fun t : ℝ => ((largeCubeSubcubes d k m).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl fun z' _ => ?_
  have hcard : (0 : ℝ) < (((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty z' (k - n))
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ (ne_of_gt hcard), mul_one]

/-- **The Jensen step of the proof of `e.RHS.term3`, Step 3**:

`avsum_{z' in 3^k Z^d cap cu_m} |(nabla w)_{z'+cu_k}|^2 <=
  ||nabla w||^2_{L2(cu_m)}`,

which the source performs silently when it passes from the weighted average to
`E[||nabla w||^2_{L2(cu_m)}]`.  It is Jensen on each sub-cube
(`ofReal_vecNormSq_volumeAverageVec_le`) followed by the exact tiling identity
`cubeLpENorm_two_sq_eq_inv_card_mul_sum` for the squared normalized norm. -/
theorem ofReal_weightedBlockAverage_one_le (n : ℕ) {k m : ℕ} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) g) :
    ENNReal.ofReal (weightedBlockAverage d n k m g (fun _ => (1 : ℝ))) ≤
      vecCubeLpENorm (originCube d (m : ℤ)) 2 g ^ (2 : ℕ) := by
  classical
  rw [weightedBlockAverage_one]
  have hnn : ∀ z' ∈ largeCubeSubcubes d k m,
      (0 : ℝ) ≤ vecNormSq (volumeAverageVec (openCubeSet z') g) :=
    fun _ _ => vecNormSq_nonneg _
  have hcard : (0 : ℝ) ≤ ((largeCubeSubcubes d k m).card : ℝ)⁻¹ := by positivity
  rw [ENNReal.ofReal_mul hcard, ENNReal.ofReal_sum_of_nonneg hnn]
  have hstep : ∀ z' ∈ largeCubeSubcubes d k m,
      ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet z') g)) ≤
        vecCubeLpENorm z' 2 g ^ (2 : ℕ) :=
    fun _ hz' => ofReal_vecNormSq_volumeAverageVec_le (memVectorL2_subcube hz' hg)
  refine le_trans (mul_le_mul_right (Finset.sum_le_sum hstep) _) ?_
  rw [show vecCubeLpENorm (originCube d (m : ℤ)) 2 g ^ (2 : ℕ) =
      (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 2 (hilbertifyVecField g)) ^ (2 : ℕ)
      from rfl,
    cubeLpENorm_two_sq_eq_inv_card_mul_sum (m - k) (hilbertifyVecField g)]
  exact le_rfl

/-- **The first-term hypothesis of the Hölder step** at these carriers:

`E[avsum_{z'} |(nabla w)_{z'+cu_k}|^2] <= E[||nabla w||^2_{L2(cu_m)}]`.

`hfin` is the finiteness of the second moment on the right, which the Bochner
integral on the left needs in order to be compared with a `toReal`; it is
supplied by the first conjunct of `l.w.basic.regbounds` (`e.nablaw.Lt`) and is
discharged where this lemma is used.  No integrability of the
left-hand integrand is required: when it fails the Bochner integral is `0`, and
the right-hand side is nonnegative. -/
theorem holder_term_one {m : ℕ} (n k : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ))))
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤) :
    ∫ omega : ShellSeq d,
        weightedBlockAverage d n k m ((w omega).toH1Function.grad) (fun _ => (1 : ℝ))
        ∂P.toMeasure ≤ gradResponseMoment (m := m) 2 2 P w := by
  classical
  have hnn : ∀ omega : ShellSeq d,
      (0 : ℝ) ≤ weightedBlockAverage d n k m ((w omega).toH1Function.grad)
        (fun _ => (1 : ℝ)) := by
    intro omega
    rw [weightedBlockAverage_one]
    have h1 : (0 : ℝ) ≤ ((largeCubeSubcubes d k m).card : ℝ)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ ∑ z' ∈ largeCubeSubcubes d k m,
        vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) :=
      Finset.sum_nonneg fun _ _ => vecNormSq_nonneg _
    exact mul_nonneg h1 h2
  by_cases hint : Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d n k m ((w omega).toH1Function.grad) (fun _ => (1 : ℝ)))
      P.toMeasure
  · have heq := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (f := fun omega : ShellSeq d =>
        weightedBlockAverage d n k m ((w omega).toH1Function.grad) (fun _ => (1 : ℝ)))
      (μ := P.toMeasure) (Filter.Eventually.of_forall hnn) hint.aestronglyMeasurable
    have hmono : (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (weightedBlockAverage d n k m ((w omega).toH1Function.grad)
          (fun _ => (1 : ℝ))) ∂P.toMeasure) ≤
        ∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
          ∂P.toMeasure :=
      lintegral_mono fun omega =>
        ofReal_weightedBlockAverage_one_le n (w omega).toH1Function.grad_memVectorL2
    rw [heq]
    exact ENNReal.toReal_mono hfin hmono
  · rw [MeasureTheory.integral_undef hint]
    exact gradResponseMoment_nonneg 2 2 P w

end

end SuperdiffusionCLT.Section3.Terms
