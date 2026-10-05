/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsE
public import SuperdiffusionCLT.Section3.Terms.GluedFieldAverages
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1

/-!
# The Step 2 displays of `l.RHS.term1`

`RHSTerm1InputsE` closes the first display of Step 1 down to the
localization line; this file supplies the ingredients for the first display of Step 2
(`hL2`), which `RHSTerm1InputsH.l2_second_moment_bridge'` assembles.

## Main results

* `volumeAverageVec_cubeMaximizerFlux`: the cube average of the **flux**
  `a_L ∇u_{k,z}` of the cube maximizer, the flux companion of
  `GluedField.volumeAverageVec_cubeMaximizerGradient`.  It is
  `e.solution.avg.grad.flux.identity` in the pure-flux slot, and it makes the
  matched-level `q̃` of `e.Sec3.p.q.def` a coarse-matrix quantity.
* `vecCubeLpENorm_matVecMul_le`: the multiplier bound
  `‖a F‖_{L̲^q(Q)} ≤ ‖a‖_{L^∞(Q)} ‖F‖_{L̲^q(Q)}` in the cube carriers, the
  `L^∞` factor read through a real pointwise envelope so that no measurability
  side condition on `F` is needed.
* `second_moment_coeffLinftySupBound_le`: the annealed **second** `L^∞` moment
  of `a_L` on `cu_m`, of size `(1+L)(1+m)`.

## What stays explicit, and why

* `hLocalized`, the localization line.  It is the conclusion of
  `Frozen.Section2.cutoff_localization` (clause
  `e.localization.minimizers`) transported to the translates `z' + cu_n` and
  averaged by `avsum`.  `TranslatedBlocks` proves the
  covariance mechanism `isBigO_gammaSigma_of_translationCovariant` and
  `integral_of_translationCovariant`; both need the pointwise covariance
  `F ω Q = F (translateSequence (triadicCubeShift Q) ω) (cu_{Q.scale})` of the
  quantity transported.  For `F ω Q = ‖∇u_{n,Q}(ω)‖²_{L̲²(Q)}` it is not
  available: a.e. uniqueness of the maximizer gradient **is** proved
  (`Book.Ch02.responseGradientUniquenessTheory`,
  `sameGradientAE_of_isResponseMaximizer`), so that norm is a genuine function
  of `(U, a, p, q)`; what is missing is the transport of
  `Book.Ch02.IsResponseMaximizer` along a translation of the domain.
  The `H^1` transport `H1Function.translate` is available, but the induced map
  on `Solution U a` and the equivariance of the maximizing property are not.
* `hJensen`.  It needs `q̃ − q = E[(a_ℓ(∇ũ_n − ∇u_n))_{cu_ℓ}]`, the splitting
  of the Bochner integral defining `GluedField.qVector`, whose integrand's
  integrability in the sample is the explicit `hq` of
  `GluedField.qVector_apply`.  `volumeAverageVec_cubeMaximizerFlux` reaches it
  for the **matched** level `q̃` (coefficient level `ℓ` = maximizer level `ℓ`);
  for `q` the maximizer is at level `L'`, and the mismatched flux average
  `(a_ℓ ∇u_n)_{cu_ℓ}` is a coarse-matrix quantity of neither level.
* `hConc`, the sublattice concentration of the proof of `l.RHS.term1`.  Its
  probabilistic inputs are proved (`RHSTerm3StepsD.block_concentration` with
  `BlockConcentrationInputs`/`CoarseBlockLocalityB`), but the first line of the
  printed display — the decomposition of `‖·‖_{Ĥ̲^{-1}(cu_m)}` into the triadic
  sum `∑_{k ≤ m} 3^{2k} avsum_z |(·)_{z+cu_k}|²` — has no counterpart in
  `vecHatNegENorm` (in `Section3/ResponseFields/Norms`), whose upper
  bounds are all single-scale.

## References

The paper: the proof of `l.RHS.term1`, and `e.v.ky.energy`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cube average of the flux of the cube maximizer -/

/-- **`e.solution.avg.grad.flux.identity` in the pure-flux slot**: the cube
average of the flux `a_L ∇u_{k,z}` of the cube maximizer is
`F − (kcg_L(z))^t s_{L,*}^{-1}(z) F`, a function of the Chapter 2 coarse
matrices alone.

This is the flux companion of
`GluedField.volumeAverageVec_cubeMaximizerGradient`, and it is what makes the
matched-level `q̃` of `e.Sec3.p.q.def` a coarse-matrix observable: the
right-hand side is `F + (coarseBlockMatrix)_{upperRight} F`, whose entrywise
integrability in the sample is proved
(`Section2.Annealed.integrable_coarseBlockMatrix_upperRight_apply`). -/
theorem volumeAverageVec_cubeMaximizerFlux {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    volumeAverageVec (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (cubeMaximizerGradient hnu omega L F z x)) =
      F - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField))
        (matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField) F) :=
  averageFlux_setupMaximizer (Book.Ch02.cubeDomain z)
    (cubeCutoffCoeffOn hnu omega L z) F

/-! ## The multiplier bound in the cube carriers -/

/-- The Hilbert reading of `A u` is strongly measurable when `A` is a continuous
matrix field and the Hilbert reading of `u` is strongly measurable. -/
theorem aestronglyMeasurable_hilbertifyVecField_matVecMul {μ : Measure (Vec d)}
    {A : Vec d → Mat d} {u : Vec d → Vec d} (hA : Continuous A)
    (hu : AEStronglyMeasurable (hilbertifyVecField u) μ) :
    AEStronglyMeasurable (hilbertifyVecField (fun x => matVecMul (A x) (u x))) μ := by
  have hu' : AEStronglyMeasurable u μ := by
    have h := (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable hu
    exact h
  have hpm : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    exact inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  have hpair : AEStronglyMeasurable (fun x => (A x, u x)) μ :=
    hA.aestronglyMeasurable.prodMk hu'
  have hcont : Continuous (fun p : Mat d × Vec d => matVecMul p.1 p.2) := by
    change Continuous fun p : Mat d × Vec d => fun i => ∑ j, p.1 i j * p.2 j
    exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      (((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
        ((continuous_apply j).comp continuous_snd))
  exact (((HilbertVec.ofVecL d).continuous).comp hcont).comp_aestronglyMeasurable hpair

/-- **`‖a F‖_{L̲^q(Q)} ≤ ‖a‖_{L^∞(Q)} ‖F‖_{L̲^q(Q)}`.**  The `L^∞` factor is
read through a real pointwise envelope `c` of the Euclidean operator norm of
`a`, so that no measurability side condition on `F` is needed. -/
theorem vecCubeLpENorm_matVecMul_le {Q : TriadicCube d} (q : ℝ≥0∞)
    (A : Vec d → Mat d) (V : Vec d → Vec d) {c : ℝ} (hc : 0 ≤ c)
    (hAV : MeasureTheory.AEStronglyMeasurable
      (hilbertifyVecField (fun x => matVecMul (A x) (V x))) (normalizedCubeMeasure Q))
    (hA : ∀ᵐ x ∂normalizedCubeMeasure Q, matrixOperatorNorm (A x) ≤ c) :
    vecCubeLpENorm Q q (fun x => matVecMul (A x) (V x)) ≤
      ENNReal.ofReal c * vecCubeLpENorm Q q V := by
  have hae : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ‖hilbertifyVecField (fun x => matVecMul (A x) (V x)) x‖ₑ ≤
        (c.toNNReal : ℝ≥0∞) * ‖hilbertifyVecField V x‖ₑ := by
    refine hA.mono fun x hx => ?_
    have hpt : vecNorm (matVecMul (A x) (V x)) ≤ c * vecNorm (V x) := by
      refine le_trans (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
        (A x) (V x)) ?_
      exact mul_le_mul_of_nonneg_right hx (vecNorm_nonneg _)
    have h1 : ‖hilbertifyVecField (fun x => matVecMul (A x) (V x)) x‖ₑ =
        ENNReal.ofReal (vecNorm (matVecMul (A x) (V x))) := by
      rw [← ofReal_norm, norm_hilbertifyVecField_apply]
    have h2 : ‖hilbertifyVecField V x‖ₑ = ENNReal.ofReal (vecNorm (V x)) := by
      rw [← ofReal_norm, norm_hilbertifyVecField_apply]
    have hcoe : ((c.toNNReal : ℝ≥0∞)) = ENNReal.ofReal c := rfl
    rw [h1, h2, hcoe, ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal hpt
  have hmain := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (μ := normalizedCubeMeasure Q) hAV hae q
  simp only [vecCubeLpENorm, Section2.Norms.cubeLpENorm, ENNReal.smul_def, smul_eq_mul] at hmain ⊢
  exact hmain

/-- The pointwise envelope of the cutoff coefficient is an a.e. bound on the
normalized cube measure. -/
theorem ae_matrixOperatorNorm_coefficientCutoff_le {nu : ℝ} (hnu : 0 ≤ nu)
    (omega : ShellSeq d) (L r : ℕ) :
    ∀ᵐ x ∂normalizedCubeMeasure (originCube d (r : ℤ)),
      matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
        coeffLinftySupBound nu L r omega := by
  have hmem : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (r : ℤ)),
      x ∈ cubeSet (originCube d (r : ℤ)) :=
    MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet _)) _
  exact hmem.mono fun x hx =>
    matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu hnu omega hx

/-! ## The annealed second `L^∞` moment of the cutoff coefficient -/

/-- The constant of the annealed second `L^∞` moment: the square of the linear
amplitude constant of `RHSTerm1InputsC.lean` times the printed moment factor
`1 + γ(2)` of `l.moments.gamma.psi` at `k = 2`. -/
def coeffCubeLinftySecondMomentConst (d : ℕ) : ℝ :=
  coeffCubeLinftyAmplitudeConst d ^ (2 : ℕ) * (1 + Real.Gamma 2)

theorem one_le_coeffCubeLinftySecondMomentConst
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) :
    1 ≤ coeffCubeLinftySecondMomentConst d := by
  have hK : (1 : ℝ) ≤ coeffCubeLinftyAmplitudeConst d :=
    one_le_coeffCubeLinftyAmplitudeConst hPrefix
  have hKsq : (1 : ℝ) ≤ coeffCubeLinftyAmplitudeConst d ^ (2 : ℕ) :=
    one_le_pow₀ hK
  have hG : (0 : ℝ) < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
  rw [coeffCubeLinftySecondMomentConst]
  nlinarith only [hKsq, hG]

/-- **The annealed second `L^∞` moment of the cutoff coefficient**, in the real
envelope carrier of the coefficient `L^∞` moment estimates:

`E[(‖a_L‖-envelope on cu_m)²] ≤ C(d) (1 + L)(1 + m)`, for `0 ≤ ν ≤ 1`, `L ≤ m`.

The companion of `RHSTerm1InputsC.sqrt_fourth_moment_coeffCubeLinftyENorm_le`
at `k = 2`; the same `Γ₂` tail
`isBigO_gammaSigma_coeffLinftySupBound` through the printed moment bound
of `l.moments.gamma.psi`. -/
theorem second_moment_coeffLinftySupBound_le
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) {L m : ℕ} (hLm : L ≤ m) :
    (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu L m omega)) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (coeffCubeLinftySecondMomentConst d *
        ((1 + (L : ℝ)) * (1 + (m : ℝ)))) := by
  set Z : ShellSeq d → ℝ := coeffLinftySupBound nu L m with hZ
  set A : ℝ := coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m with hAdef
  have hgamma : (0 : ℝ) < gammaTriangleConst 2 := IndependentSums.gammaTriangleConst_pos
  have hc1 : (1 : ℝ) ≤ shellValueLargeCubeConst d :=
    one_le_shellValueLargeCubeConst d
  have hC : (0 : ℝ) < largeCubeLinftyConst d := largeCubeLinftyConst_pos hPrefix
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hApos : 0 < A := by
    have hsq1 : (0 : ℝ) < Real.sqrt (1 + (m : ℝ)) :=
      Real.sqrt_pos.2 (by linarith only [hm0])
    have hsq2 : (0 : ℝ) ≤ Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [hAdef, coeffLinftyGammaTwoAmplitude, streamCutoffLinftyGammaTwoAmplitude]
    have hinner : (0 : ℝ) < shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
        largeCubeLinftyConst d * (Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ)) := by
      have h1 : (0 : ℝ) < shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) :=
        mul_pos (by linarith only [hc1]) hsq1
      have h2 : (0 : ℝ) ≤ largeCubeLinftyConst d *
          (Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ)) := mul_nonneg hC.le hsq2
      linarith only [h1, h2]
    have := mul_pos hgamma hinner
    linarith only [this, hnu]
  have hZmeas : Measurable Z := measurable_coeffLinftySupBound nu L m
  have hbigO : IsBigO P.toMeasure (gammaSigma 2) Z A :=
    isBigO_gammaSigma_coeffLinftySupBound hPrefix hJ2 hJ3 hJ4 hnu hLm
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((2 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hApos hZmeas.aemeasurable hbigO 2
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hApos hZmeas.aemeasurable hbigO 2
  have hptr : ∀ omega : ShellSeq d,
      (ENNReal.ofReal (Z omega)) ^ (2 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
    intro omega
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (ENNReal.ofReal (Z omega)) ^ (2 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (2 : ℕ) := pow_le_pow_left' habs 2
      _ = ENNReal.ofReal (|Z omega| ^ (2 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by rw [Real.rpow_natCast]
  have hGamma : Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) = Real.Gamma 2 := by norm_num
  have hlint : (∫⁻ omega : ShellSeq d,
      (ENNReal.ofReal (Z omega)) ^ (2 : ℕ) ∂P.toMeasure) ≤
      ENNReal.ofReal (A ^ (((2 : ℕ) : ℝ)) *
        (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1))) := by
    calc (∫⁻ omega : ShellSeq d, (ENNReal.ofReal (Z omega)) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) ∂P.toMeasure :=
          lintegral_mono hptr
      _ = ENNReal.ofReal (∫ omega : ShellSeq d,
            |Z omega| ^ (((2 : ℕ) : ℝ)) ∂P.toMeasure) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (A ^ (((2 : ℕ) : ℝ)) *
            (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1))) := ENNReal.ofReal_le_ofReal hmom
  refine le_trans hlint (ENNReal.ofReal_le_ofReal ?_)
  have hAle : A ≤ coeffCubeLinftyAmplitudeConst d *
      (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ))) :=
    coeffLinftyGammaTwoAmplitude_le hPrefix hnu1 L m
  have hsq : A ^ (2 : ℕ) ≤ (coeffCubeLinftyAmplitudeConst d *
      (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hApos.le hAle 2
  have hsqL : Real.sqrt (1 + (L : ℝ)) ^ (2 : ℕ) = 1 + (L : ℝ) :=
    Real.sq_sqrt (by linarith only [hL0])
  have hsqm : Real.sqrt (1 + (m : ℝ)) ^ (2 : ℕ) = 1 + (m : ℝ) :=
    Real.sq_sqrt (by linarith only [hm0])
  have hexp : (coeffCubeLinftyAmplitudeConst d *
        (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)))) ^ (2 : ℕ) *
      (1 + Real.Gamma 2) =
      coeffCubeLinftySecondMomentConst d * ((1 + (L : ℝ)) * (1 + (m : ℝ))) := by
    rw [coeffCubeLinftySecondMomentConst, mul_pow, mul_pow, hsqL, hsqm]
    ring
  have hG : (0 : ℝ) < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
  have hrw : A ^ (((2 : ℕ) : ℝ)) = A ^ (2 : ℕ) := by rw [Real.rpow_natCast]
  rw [hGamma, hrw, ← hexp]
  exact mul_le_mul_of_nonneg_right hsq (by linarith only [hG])

/-! ## `hL2`: the first display of Step 2 -/

/-- The constant of the `hL2` display: the annealed second `L^∞` moment
constant, the factor `2` of the printed energy identity, the factor `4` of the
`ℝ≥0∞` triangle inequality and the two factors `2` of `1 + ℓ ≤ 2ℓ`,
`1 + m ≤ 2m`. -/
def hminusL2Const (d : ℕ) : ℝ :=
  max 1 (64 * coeffCubeLinftySecondMomentConst d)

theorem one_le_hminusL2Const (d : ℕ) : 1 ≤ hminusL2Const d :=
  le_max_left _ _

/-! ## `l.RHS.term1` from the anchors -/

end

end SuperdiffusionCLT.Section3.Terms
