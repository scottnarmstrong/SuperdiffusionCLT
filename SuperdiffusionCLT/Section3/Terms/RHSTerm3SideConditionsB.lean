/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SignedBlockDev
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsC
public import SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs
public import SuperdiffusionCLT.Section3.Terms.TranslatedQuadFormMoment

/-!
# The `L^2(P)` weighted-block-average side conditions of the response

The second obligation cluster of the final Term 3 statement: the binders `hIntB`,
`hInt2`, `hInt3`, `hIntSwap`, `hbHalfInt` -- the integrability in the sample of
the `∇w`-weighted double lattice average with the four weight observables
`translatedBlockNorm`, `translatedStreamQuadForm`,
`translatedBlockDevSumSigned`, `translatedStreamQuadFormGap`, and the
integrability of the half-weight carrier `translatedBlockHalfWeight`.

What `RHSTerm3SideConditions.lean` does for `hsq` and the flux side conditions
is continued here: the `hsq` binder, once available as a hypothesis, pairs
against every one of the weight observables, because each weight is square
integrable in the sample through its `Γ₁` envelope

* `translatedBlockNorm` -- by
  `isBigO_gammaSigma_translatedBlockNorm_envelope`
  (`Section3/Terms/TranslatedBlocks.lean`) at amplitude `bfE_L`;
* `translatedStreamQuadForm` -- by
  `memLp_two_translatedStreamQuadForm`
  (`Section3/Terms/TranslatedQuadFormMoment.lean`);
* `translatedBlockDevSumSigned` -- the coordinate sum of the `Γ₁`-enveloped
  centred blocks (`isBigO_gammaSigma_blockDeviation_of_shellLaws`,
  `Section3/Terms/BlockConcentrationInputs.lean`);
* `translatedStreamQuadFormGap` -- through the two crude ellipticity bounds
  `translatedStreamQuadFormLower_le_nuInv_mul` and
  `translatedStreamQuadForm_le_nuInv_mul` at the `Γ₁` envelope of the
  stream increment, `|gap| <= 2 nu^{-1} |stream increment|^2`;
* `translatedBlockHalfWeight` -- the operator-norm bridge
  `translatedBlockHalfWeight_le` (`Section3/Terms/TranslatedBlocks.lean`),
  measurability coming from the identity
  `|b^{1/2} v|^2 = v . (b v)` of `Section2/Localization/PsdSqrtQuadratic.lean`
  together with the canonical-response measurability of the cube average of
  `∇w` (`Section3/Setup/ResponseMeasurability.lean`).

## What is proved here

* `sideCondition_hIntB` -- the weighted block average with the weight
  `translatedBlockNorm nu S.LPrime omega` is integrable.
* `sideCondition_hInt2` -- the weighted block average with the weight
  `translatedStreamQuadForm nu S.ell S.LPrime e omega` is integrable.
* `sideCondition_hInt3` -- the weighted block average with the weight
  `translatedBlockDevSumSigned nu S.ell S.n P omega` is integrable.
* `sideCondition_hIntSwap` -- the weighted block average with the weight
  `translatedStreamQuadFormGap nu S.ell S.LPrime e omega` is integrable.
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

/-! ## Helpers -/

/-- The squared norm of the unit coordinate vector is one. -/
private theorem vecNormSq_pi_single_one {d : ℕ} [NeZero d] (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply]

/-- A `Gamma_sigma` observable with positive amplitude is square integrable. -/
private theorem memLp_two_of_isBigO_gammaSigma {P : ProbabilityMeasure (ShellSeq d)}
    {X : ShellSeq d → ℝ} {K sigma : ℝ} (hsigma : 0 < sigma) (hK : 0 < K)
    (hXm : Measurable X) (hX : IsBigO P.toMeasure (gammaSigma sigma) X K) :
    MemLp X 2 P.toMeasure := by
  have hgrowth := hasGammaMomentGrowthWith_of_isBigO_gammaSigma (μ := P.toMeasure)
    hsigma hK hXm.aemeasurable hX
  obtain ⟨hint, -⟩ := hgrowth (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
  have hint' : Integrable (fun omega : ShellSeq d => X omega ^ (2 : ℕ)) P.toMeasure := by
    refine hint.congr (Filter.Eventually.of_forall fun omega => ?_)
    show |X omega| ^ ((2 : ℕ) : ℝ) = X omega ^ (2 : ℕ)
    rw [Real.rpow_natCast, sq_abs]
  exact (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 hint'

/-- A measurable real observable dominated by `c` times a nonnegative square
integrable one is square integrable. -/
private theorem memLp_two_of_abs_le {P : ProbabilityMeasure (ShellSeq d)}
    {f g : ShellSeq d → ℝ} {c : ℝ} (hf : Measurable f) (hg : MemLp g 2 P.toMeasure)
    (h : ∀ omega : ShellSeq d, |f omega| ≤ c * g omega) :
    MemLp f 2 P.toMeasure := by
  have hgi : Integrable (fun omega : ShellSeq d => g omega ^ (2 : ℕ)) P.toMeasure :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hcgi : Integrable (fun omega : ShellSeq d => (c * g omega) ^ (2 : ℕ))
      P.toMeasure := by
    have hkey : (fun omega : ShellSeq d => (c * g omega) ^ (2 : ℕ)) =
        fun omega : ShellSeq d => c ^ (2 : ℕ) * (g omega ^ (2 : ℕ)) := by
      funext omega
      rw [mul_pow]
    rw [hkey]
    exact hgi.const_mul _
  refine (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 ?_
  refine Integrable.mono' hcgi (hf.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  show |f omega ^ (2 : ℕ)| ≤ (c * g omega) ^ (2 : ℕ)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (h omega) 2

/-- Every descendant of a member of the sub-cube family has the advertised
scale. -/
private theorem scale_of_descendantsAtDepth {k m nn : ℕ} (hkm : k ≤ m) (hkn : nn ≤ k)
    {z' : TriadicCube d} (hz' : z' ∈ largeCubeSubcubes d k m)
    {z : TriadicCube d} (hz : z ∈ descendantsAtDepth z' (k - nn)) :
    z.scale = (nn : ℤ) := by
  have h := scale_eq_sub_of_mem_descendantsAtDepth hz
  rw [scale_of_mem_largeCubeSubcubes hkm hz'] at h
  rw [h, Nat.cast_sub hkn]
  ring

/-- The scales of a scale selection: the coarse block scale sits between
`S.n` and `S.m`. -/
private theorem coarseBlockScale_bounds (S : ScaleSelection) (hSorder : ScalesOrdering S) :
    S.n ≤ coarseBlockScale d S ∧ coarseBlockScale d S ≤ S.m := by
  obtain ⟨hlk, hkl, -, -⟩ := coarse_block_scale_choice d S hSorder.ell_lt_ellPrime.le
  exact ⟨le_trans hSorder.n_lt_ell.le hlk,
    le_trans hkl (le_of_lt hSorder.ellPrime_lt_m)⟩

/-! ## The `hIntB` obligation -/

/-- **The `hIntB` side condition**: the `∇w`-weighted double lattice average
with the weight `translatedBlockNorm nu S.LPrime omega` is integrable.  The
squared cube means of `∇w` are square integrable (`hsq`), and the descendant
average of the coarse block norm is square integrable through its
`Γ₁` envelope `isBigO_gammaSigma_translatedBlockNorm_envelope`; the
product of two square integrable observables is integrable. -/
theorem sideCondition_hIntB [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedBlockNorm nu S.LPrime omega)) P.toMeasure := by
  classical
  have hAvg : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedBlockNorm nu S.LPrime omega z) 2 P.toMeasure := by
    intro z' hz'
    refine (memLp_finsetSum (descendantsAtDepth z' (coarseBlockScale d S - S.n))
      (f := fun z omega => translatedBlockNorm nu S.LPrime omega z)
      (fun z hz => ?_)).const_mul _
    exact memLp_two_of_isBigO_gammaSigma (show (0 : ℝ) < 1 by norm_num)
      (envelopeUpperScalar_pos hnu d S.LPrime)
      (measurable_translatedBlockNorm hnu S.LPrime z)
      (isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4
        S.LPrime z)
  have hint : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
          ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedBlockNorm nu S.LPrime omega z)) P.toMeasure :=
    fun z' hz' => ((hsq z' hz').integrable_mul (hAvg z' hz')).congr
      (Filter.Eventually.of_forall fun omega =>
        Pi.mul_apply (fun omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)))
          (fun omega => (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedBlockNorm nu S.LPrime omega z) omega)
  have hfun : ∀ omega : ShellSeq d,
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedBlockNorm nu S.LPrime omega) =
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedBlockNorm nu S.LPrime omega z) := by
    intro omega
    rw [weightedBlockAverage]
  have hsum : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedBlockNorm nu S.LPrime omega z)) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum
      (largeCubeSubcubes d (coarseBlockScale d S) S.m)
      (f := fun z' omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) *
        ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedBlockNorm nu S.LPrime omega z))
      (fun z' hz' => hint z' hz')).const_mul _
  exact hsum.congr (Filter.Eventually.of_forall fun omega => (hfun omega).symm)

/-! ## The `hInt2` obligation -/

/-- **The `hInt2` side condition**: the `∇w`-weighted double lattice average
with the weight `translatedStreamQuadForm nu S.ell S.LPrime e omega` is
integrable.  The descendant average of the quadratic tail carrier is square
integrable by `memLp_two_descendantAverage_translatedStreamQuadForm`
(`Section3/Terms/TranslatedQuadFormMoment.lean`). -/
theorem sideCondition_hInt2 [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedStreamQuadForm nu S.ell S.LPrime e omega)) P.toMeasure := by
  classical
  have hkm : coarseBlockScale d S ≤ S.m := (coarseBlockScale_bounds S hSorder).2
  have hAvg : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedStreamQuadForm nu S.ell S.LPrime e omega z) 2 P.toMeasure :=
    fun z' hz' => memLp_two_descendantAverage_translatedStreamQuadForm hnu hPrefix hJ2
      hJ3 hJ4 S hSorder he (scale_of_mem_largeCubeSubcubes hkm hz')
  have hint : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
          ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedStreamQuadForm nu S.ell S.LPrime e omega z)) P.toMeasure :=
    fun z' hz' => ((hsq z' hz').integrable_mul (hAvg z' hz')).congr
      (Filter.Eventually.of_forall fun omega =>
        Pi.mul_apply (fun omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)))
          (fun omega => (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedStreamQuadForm nu S.ell S.LPrime e omega z) omega)
  have hfun : ∀ omega : ShellSeq d,
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedStreamQuadForm nu S.ell S.LPrime e omega) =
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedStreamQuadForm nu S.ell S.LPrime e omega z) := by
    intro omega
    rw [weightedBlockAverage]
  have hsum : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedStreamQuadForm nu S.ell S.LPrime e omega z)) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum
      (largeCubeSubcubes d (coarseBlockScale d S) S.m)
      (f := fun z' omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) *
        ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedStreamQuadForm nu S.ell S.LPrime e omega z))
      (fun z' hz' => hint z' hz')).const_mul _
  exact hsum.congr (Filter.Eventually.of_forall fun omega => (hfun omega).symm)

/-! ## The `hInt3` obligation -/

/-- **The `hInt3` side condition**: the `∇w`-weighted double lattice average
with the weight `translatedBlockDevSumSigned nu S.ell S.n P omega` is
integrable.  Each coordinate centred block carries the `Γ₁` envelope
`isBigO_gammaSigma_blockDeviation_of_shellLaws`
(`Section3/Terms/BlockConcentrationInputs.lean`), so the signed coordinate sum
and then its descendant average are square integrable. -/
theorem sideCondition_hInt3 [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedBlockDevSumSigned nu S.ell S.n P omega)) P.toMeasure := by
  classical
  have hbounds := coarseBlockScale_bounds (d := d) S hSorder
  have hkm : coarseBlockScale d S ≤ S.m := hbounds.2
  have hkn : S.n ≤ coarseBlockScale d S := hbounds.1
  have hAvg : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedBlockDevSumSigned nu S.ell S.n P omega z) 2 P.toMeasure := by
    intro z' hz'
    have hcore : ∀ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
        MemLp (fun omega : ShellSeq d =>
          translatedBlockDevSumSigned nu S.ell S.n P omega z) 2 P.toMeasure := by
      intro z hz
      have hzs : z.scale = ((S.n : ℕ) : ℤ) := scale_of_descendantsAtDepth hkm hkn hz' hz
      show MemLp (fun omega : ShellSeq d =>
        ∑ i : Fin d, blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z) 2
        P.toMeasure
      exact memLp_finsetSum (Finset.univ : Finset (Fin d))
        (f := fun i omega => blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z)
        (fun i _ => memLp_two_of_isBigO_gammaSigma (show (0 : ℝ) < 1 by norm_num)
          (add_pos (envelopeUpperScalar_pos hnu d S.ell)
            (sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n))
          (measurable_blockDeviation hnu S.ell S.n (Pi.single i (1 : ℝ)) z)
          (isBigO_gammaSigma_blockDeviation_of_shellLaws hnu hPrefix hJ2 hJ3 hJ4 S.ell
            S.n (vecNormSq_pi_single_one i) hzs))
    exact (memLp_finsetSum (descendantsAtDepth z' (coarseBlockScale d S - S.n))
      (f := fun z omega => translatedBlockDevSumSigned nu S.ell S.n P omega z)
      (fun z hz => hcore z hz)).const_mul _
  have hint : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
          ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedBlockDevSumSigned nu S.ell S.n P omega z)) P.toMeasure :=
    fun z' hz' => ((hsq z' hz').integrable_mul (hAvg z' hz')).congr
      (Filter.Eventually.of_forall fun omega =>
        Pi.mul_apply (fun omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)))
          (fun omega => (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedBlockDevSumSigned nu S.ell S.n P omega z) omega)
  have hfun : ∀ omega : ShellSeq d,
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedBlockDevSumSigned nu S.ell S.n P omega) =
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedBlockDevSumSigned nu S.ell S.n P omega z) := by
    intro omega
    rw [weightedBlockAverage]
  have hsum : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedBlockDevSumSigned nu S.ell S.n P omega z)) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum
      (largeCubeSubcubes d (coarseBlockScale d S) S.m)
      (f := fun z' omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) *
        ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedBlockDevSumSigned nu S.ell S.n P omega z))
      (fun z' hz' => hint z' hz')).const_mul _
  exact hsum.congr (Filter.Eventually.of_forall fun omega => (hfun omega).symm)

/-! ## The `hIntSwap` obligation -/

/-- **The `hIntSwap` side condition**: the `∇w`-weighted double lattice average
with the weight `translatedStreamQuadFormGap nu S.ell S.LPrime e omega` is
integrable.  The gap is the absolute difference of the lower quadratic form and
the carrier (`translatedStreamQuadFormGap_eq_abs_sub`), both dominated by
`nu^{-1}` times the stream increment squared, so the gap is dominated by twice
that amplitude, whose `Γ₁` envelope
`isBigO_gammaSigma_translatedStreamNormSq_originCube`
(`Section3/Terms/RHSTerm3InputsE.lean`) gives the second moment. -/
theorem sideCondition_hIntSwap [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedStreamQuadFormGap nu S.ell S.LPrime e omega)) P.toMeasure := by
  classical
  have hbounds := coarseBlockScale_bounds (d := d) S hSorder
  have hkm : coarseBlockScale d S ≤ S.m := hbounds.2
  have hkn : S.n ≤ coarseBlockScale d S := hbounds.1
  have hAvg : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedStreamQuadFormGap nu S.ell S.LPrime e omega z) 2 P.toMeasure := by
    intro z' hz'
    refine (memLp_finsetSum (descendantsAtDepth z' (coarseBlockScale d S - S.n))
      (f := fun z omega => translatedStreamQuadFormGap nu S.ell S.LPrime e omega z)
      (fun z hz => ?_)).const_mul _
    have hzs : z.scale = ((S.n : ℕ) : ℤ) := scale_of_descendantsAtDepth hkm hkn hz' hz
    have hcent : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d =>
          translatedStreamNormSq S.ell S.LPrime e omega (originCube d ((S.n : ℕ) : ℤ)))
        (streamTailConst d * ((S.LPrime - S.ell : ℕ) : ℝ)) :=
      isBigO_gammaSigma_translatedStreamNormSq_originCube hPrefix hJ2 hJ3 hJ4
        hSorder.n_lt_ell.le (lt_trans (lt_trans hSorder.ell_lt_ellPrime
          hSorder.ellPrime_lt_m) hSorder.m_lt_LPrime) he
    have hbig : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => translatedStreamNormSq S.ell S.LPrime e omega z)
        (streamTailConst d * ((S.LPrime - S.ell : ℕ) : ℝ)) := by
      refine isBigO_gammaSigma_translatedStreamNormSq hPrefix hJ2 S.ell S.LPrime e ?_
      rw [hzs]
      exact hcent
    have hK : (0 : ℝ) < streamTailConst d * ((S.LPrime - S.ell : ℕ) : ℝ) := by
      have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
      have hgap : (0 : ℝ) < ((S.LPrime - S.ell : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt
          (lt_trans (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m)
            hSorder.m_lt_LPrime)
      exact mul_pos (streamTailConst_pos hd) hgap
    have hstreamSq : MemLp (fun omega : ShellSeq d =>
        translatedStreamNormSq S.ell S.LPrime e omega z) 2 P.toMeasure :=
      memLp_two_of_isBigO_gammaSigma (show (0 : ℝ) < 1 by norm_num) hK
        (measurable_translatedStreamNormSq S.ell S.LPrime e z) hbig
    refine memLp_two_of_abs_le (c := 2 * nu⁻¹)
      (measurable_translatedStreamQuadFormGap hnu S.ell S.LPrime e z) hstreamSq ?_
    intro omega
    show |translatedStreamQuadFormGap nu S.ell S.LPrime e omega z| ≤
      2 * nu⁻¹ * translatedStreamNormSq S.ell S.LPrime e omega z
    rw [translatedStreamQuadFormGap_eq_abs_sub, abs_abs]
    have h1 := translatedStreamQuadFormLower_le_nuInv_mul hnu S.ell S.LPrime e omega z
    have h2 := translatedStreamQuadForm_le_nuInv_mul hnu S.ell S.LPrime e omega z
    have h3 := translatedStreamQuadFormLower_nonneg hnu S.ell S.LPrime e omega z
    have h4 := translatedStreamQuadForm_nonneg hnu S.ell S.LPrime e omega z
    have hX : (0 : ℝ) ≤ nu⁻¹ * translatedStreamNormSq S.ell S.LPrime e omega z :=
      mul_nonneg (inv_nonneg.2 hnu.le) (translatedStreamNormSq_nonneg S.ell S.LPrime e omega z)
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [h2, h3, h4, hX]
    · linarith only [h1, h3, h4, hX]
  have hint : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
          ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedStreamQuadFormGap nu S.ell S.LPrime e omega z)) P.toMeasure :=
    fun z' hz' => ((hsq z' hz').integrable_mul (hAvg z' hz')).congr
      (Filter.Eventually.of_forall fun omega =>
        Pi.mul_apply (fun omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)))
          (fun omega => (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
              translatedStreamQuadFormGap nu S.ell S.LPrime e omega z) omega)
  have hfun : ∀ omega : ShellSeq d,
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedStreamQuadFormGap nu S.ell S.LPrime e omega) =
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedStreamQuadFormGap nu S.ell S.LPrime e omega z) := by
    intro omega
    rw [weightedBlockAverage]
  have hsum : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                translatedStreamQuadFormGap nu S.ell S.LPrime e omega z)) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum
      (largeCubeSubcubes d (coarseBlockScale d S) S.m)
      (f := fun z' omega => vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) *
        ((((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
            translatedStreamQuadFormGap nu S.ell S.LPrime e omega z))
      (fun z' hz' => hint z' hz')).const_mul _
  exact hsum.congr (Filter.Eventually.of_forall fun omega => (hfun omega).symm)

end

end SuperdiffusionCLT.Section3.Terms