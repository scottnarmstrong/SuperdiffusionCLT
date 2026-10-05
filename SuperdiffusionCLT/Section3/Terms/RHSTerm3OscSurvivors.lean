/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscSeminormClose
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF

/-!
# The remaining leaves of `_hOscBound` at the seminorm carrier

`term3_oscBound_seminorm` (`RHSTerm3OscSeminormClose.lean`) proves the display
`_hOscBound` of the term-3 statement verbatim at `CB = max 1 (oscBoundConstBase 1 C C3)`,
a function of `d` and `hd` alone, fixed before `S` is quantified; `_hCS` and
`_hPoincare` are both discharged there, the first unconditionally and the second at
the constant `1`.  Beyond the ambient telescope (`hd`, `nu`, `hnu`, `hnu1`, the five
shell laws, `S`, `hSorder`, `hWindowVsOffset`, `e`, `he`, `w`, `hw`) exactly four
binders remain:

* `_hFlux`: `∫_ω seminormFluxNeg ω R ^ (3/2) ≤ C3 · 3^(3n/2) · (L'·ν⁻¹)^(3/4) ·
  (∫_ω oscEnergy ω R)^(3/4)`, the flux chain of `e.RHS.term3.B`;
* `_hEnergy`: `card⁻¹ ∑_R ∫_ω oscEnergy ω R ≤ δ + η`, the energy display of
  `e.RHS.term3.B`;
* `_hMemOsc`: `MemLp (ω ↦ centredSeminormAt (oscHessianWitness hd hSorder w hw ω) R)
  (ofReal 3)`, a sample-side membership;
* `_hMemFlux`: `MemLp (ω ↦ seminormFluxNeg ν hnu S P e ω R) (ofReal (3/2))`, a
  sample-side membership.

The last two are the sample-side memberships of the Hölder step.  Only two
things about them are *leaves*: the power moment, and the a.e. strong
measurability.  This module removes the moment of the flux leaf outright.

## Main results

* `seminormFluxNeg_envelope` and `lintegral_seminormFluxNeg_rpow_ne_top`: the
  `3/2`-moment of `seminormFluxNeg` is finite, from the telescope's
  scale-`m`/scale-`n` glued-field energy `vecCubeLpENorm_gluedGradientField_diff_subcube_B`
  against the measurable envelope `coeffLinftySupBound`, whose square is
  `P`-integrable (`integrable_coeffLinftySupBound_sq_at_B`).  No flux chain, no
  energy bound and no measurability hypothesis is used.
* `memLp_seminormFluxNeg_of_aestronglyMeasurable`: consequently `_hMemFlux` —
  and with it the `_hIntFlux` of `term3_oscBound_seminorm_measurable` — costs
  **one** hypothesis instead of two, namely the a.e. strong measurability of
  `ω ↦ seminormFluxNeg ν hnu S P e ω R` alone.

## What is not derived from the telescope, and why

`_hAEMFlux`.  Measurability of `ω ↦ seminormFluxNeg ν hnu S P e ω R` is not
derivable from the telescope.  The norm is the value of the class functional
`centredSeminormNegNorm R` on the sample-dependent `L²(R)` class of the flux
field, so its measurability would follow from the measurability of that class;
but the sample measurability of the `L²` class of the glued gradient field — the
input of every class-measurability route — is not available at the glued-field
carriers, because the cube maximizer is not known to be stable under coefficient
perturbation.  The flux norm's class statement is strictly harder than that one,
since it must additionally be read on a scale-`n` sub-cube.  So this leaf is not a
moment statement that an estimate can close: it is a class-selection statement,
and it is carried as a hypothesis.

`_hMemOsc`.  Its moment half is already a theorem
(`integrable_seminormThird_of_envelope`, `RHSTerm3OscSeminormClose.lean`), and its
measurability half is *not* derivable from the telescope.  The integrand is
`centredSeminormAt (oscHessianWitness hd hSorder w hw ω) R`, the `L²` norm of the
Hessian matrix field of the chosen weak-Hessian **witness**.  The telescope
supplies the response only through `IsDirichletResponse`
(`Section3/Setup/Scales.lean`), which is a pure `Prop`: the weak formulation
`∫ ∇w·∇φ = -∫ F·∇φ` for zero-trace `φ`.  It pins no Hessian, no `H²` regularity
and no selection; `oscHessianWitness` is
`Classical.choice (exists_hasWeakHessianOn_of_isDirichletResponse …)`, and the
weak-Hessian operator is not made measurable by the `1`-Lipschitz Dirichlet
solution operator.  Unlike the centered-gradient carrier — whose measurability
holds (`Section3/Terms/CenteredGradientMeasurable.lean`)
because the gradient is a `L²` class pinned by the weak formulation — the Hessian
seminorm has no such `L²`-class reading available from the telescope.  The leaf is
therefore stated as the measurability statement alone.

`_hFlux` and `_hEnergy` are the printed estimates of `e.RHS.term3.B`, not leaves,
and are untouched.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The flux leaf -/

/-- The coefficient bound of `matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound`
holds `normalizedCubeMeasure R`-a.e., because the scale-`n` sub-cube `R` of
`cu_m` sits inside `cubeSet cu_m`, where the bound is pointwise. -/
theorem ae_matrixOperatorNorm_coefficientCutoff_le_subcube {nu : ℝ} (hnu : 0 ≤ nu)
    (omega : ShellSeq d) {L m : ℕ} {n : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m) :
    ∀ᵐ x ∂normalizedCubeMeasure R,
      Book.Ch02.matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
        coeffLinftySupBound nu L m omega := by
  have hmem : ∀ᵐ x ∂normalizedCubeMeasure R, x ∈ openCubeSet R := by
    rw [ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)) _
  exact hmem.mono fun x hx =>
    matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu hnu omega
      (openCubeSet_subset_cubeSet (originCube d (m : ℤ))
        (openCubeSet_subset_of_mem_descendantsAtDepth (Q := originCube d (m : ℤ)) hR hx))

/-- **The `L²(R)` norm of the glued flux field, against the coefficient
envelope.**  The multiplier bound `vecCubeLpENorm_matVecMul_le` at the sub-cube
`R`, with the a.e. coefficient bound above and the energy identity
`vecCubeLpENorm_gluedGradientField_diff_subcube_B` of the two glued fields. -/
theorem toReal_vecCubeLpENorm_fluxField_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (hnm : S.n ≤ S.m) {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (omega : ShellSeq d) :
    (ResponseFields.vecCubeLpENorm R 2 (fluxFieldCarrier nu S omega
        (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega)
        (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega))).toReal ≤
      coeffLinftySupBound nu S.LPrime S.m omega *
        ((Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
          (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)))) := by
  classical
  set V : Vec d → Vec d := fun x =>
    gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega x -
      gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x with hV
  have hcnn : 0 ≤ coeffLinftySupBound nu S.LPrime S.m omega :=
    coeffLinftySupBound_nonneg nu hnu.le S.LPrime S.m omega
  have hmemV : MemVectorL2 (openCubeSet R) V :=
    (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
        (fluxSlot nu S.LPrime P S.n e) omega R).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega R)
  have hVmem : MemLp (hilbertifyVecField V) 2 (normalizedCubeMeasure R) :=
    memLp_hilbertifyVecField_of_memVectorL2 hmemV
  have hVfin : ResponseFields.vecCubeLpENorm R 2 V ≠ ⊤ := hVmem.eLpNorm_lt_top.ne
  have hmul := vecCubeLpENorm_matVecMul_le (Q := R) 2
    (fun x : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField x) V
    hcnn
    (aestronglyMeasurable_hilbertifyVecField_matVecMul
      (continuous_coefficientCutoff_apply nu omega S.LPrime) hVmem.aestronglyMeasurable)
    (ae_matrixOperatorNorm_coefficientCutoff_le_subcube hnu.le omega (L := S.LPrime) hR)
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hmul
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcnn] at hbound
  have henergy := vecCubeLpENorm_gluedGradientField_diff_subcube_B hnu omega
    (L := S.LPrime) (n := S.n) (m := S.m) hnm (F := fluxSlot nu S.LPrime P S.n e) hR
  have hflux : fluxFieldCarrier nu S omega
      (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega)
      (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega) =
      fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x) (V x) := rfl
  have henergy' : (ResponseFields.vecCubeLpENorm R 2 V).toReal ≤
      (Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
        (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e))) := by
    rw [hV]
    exact henergy
  rw [hflux]
  exact le_trans hbound (mul_le_mul_of_nonneg_left henergy' hcnn)

/-- **The seminorm flux norm against the coefficient envelope.**  The finiteness
bound `centredSeminormNegNorm_le_hessScaled` together with the `L²(R)` bound
above.  The constant splits as a `d`-and-`R` factor and a scale-energy factor,
both deterministic. -/
theorem seminormFluxNeg_envelope {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (hnm : S.n ≤ S.m) {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (omega : ShellSeq d) :
    seminormFluxNeg nu hnu S P e omega R ≤
      ((cubeScaleFactor R * (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
          ((Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
            (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e))))) *
        coeffLinftySupBound nu S.LPrime S.m omega := by
  classical
  set F : Vec d → Vec d := fluxFieldCarrier nu S omega
    (oscGluedGradM nu hnu S P e omega) (oscGluedGradN nu hnu S P e omega) with hF
  have hFmem : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R) := by
    rw [hF]
    simpa only [oscGluedGradM, oscGluedGradN] using
      (memLp_seminormFluxField (d := d) hnu S P e omega R)
  have hCd0 : 0 ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hcf : (0 : ℝ) < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale
  have hK0 : 0 ≤ cubeScaleFactor R * (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    mul_nonneg hcf.le hCd0
  have hFfin : ResponseFields.vecCubeLpENorm R 2 F ≠ ⊤ := hFmem.eLpNorm_lt_top.ne
  have hscale := centredSeminormNegNorm_le_hessScaled (Q := R) hFmem
  have htoReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hFfin ENNReal.ofReal_ne_top) hscale
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at htoReal
  have henv : (ResponseFields.vecCubeLpENorm R 2 F).toReal ≤
      coeffLinftySupBound nu S.LPrime S.m omega *
        ((Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
          (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)))) := by
    rw [hF]
    exact toReal_vecCubeLpENorm_fluxField_le hnu S P e hnm hR omega
  calc seminormFluxNeg nu hnu S P e omega R
      = (centredSeminormNegNorm R F).toReal := rfl
    _ ≤ (ResponseFields.vecCubeLpENorm R 2 F).toReal *
          (cubeScaleFactor R * (originCubeMeanZeroH1CoerciveEstimate d 0).constant) := htoReal
    _ ≤ coeffLinftySupBound nu S.LPrime S.m omega *
          ((Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
            (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)))) *
          (cubeScaleFactor R * (originCubeMeanZeroH1CoerciveEstimate d 0).constant) :=
        mul_le_mul_of_nonneg_right henv hK0
    _ = ((cubeScaleFactor R * (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
          ((Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
            (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e))))) *
          coeffLinftySupBound nu S.LPrime S.m omega := by ring

/-- The third-half power is dominated by `1 + x²` on the nonnegative half-line. -/
private theorem rpow_three_halves_le_one_add_sq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 2) ≤ 1 + x ^ (2 : ℕ) := by
  rcases le_or_gt x 1 with h | h
  · have h1 : x ^ ((3 : ℝ) / 2) ≤ 1 := by
      have hstep := Real.rpow_le_rpow hx h (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
      simpa using hstep
    have h2 : (0 : ℝ) ≤ x ^ (2 : ℕ) := pow_nonneg hx 2
    linarith only [h1, h2]
  · have h1 : x ^ ((3 : ℝ) / 2) ≤ x ^ (2 : ℕ) := by
      have hstep := Real.rpow_le_rpow_of_exponent_le (le_of_lt h)
        (by norm_num : (3 : ℝ) / 2 ≤ 2)
      rw [← Real.rpow_two]
      exact hstep
    linarith only [h1, (zero_le_one : (0 : ℝ) ≤ 1)]

/-- **The `3/2`-moment of the seminorm flux norm is finite**, per scale-`n`
sub-cube, from the telescope's shell laws alone: the pointwise envelope
`seminormFluxNeg_envelope`, the third-half power conversion
`rpow_three_halves_le_one_add_sq`, and the `P`-integrability of the square of
`coeffLinftySupBound` (`integrable_coeffLinftySupBound_sq_at_B`). -/
theorem lintegral_seminormFluxNeg_rpow_ne_top {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2))
        ∂P.toMeasure) ≠ ⊤ := by
  classical
  have hn_lt_m : S.n < S.m :=
    lt_trans hSorder.n_lt_ell (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m)
  have hnm : S.n ≤ S.m := hn_lt_m.le
  have hmpos : 0 < S.m := lt_of_le_of_lt (Nat.zero_le S.n) hn_lt_m
  have hLpos : 0 < S.LPrime := lt_trans hmpos hSorder.m_lt_LPrime
  set M : ShellSeq d → ℝ := fun omega => coeffLinftySupBound nu S.LPrime S.m omega with hM
  set K : ℝ := (cubeScaleFactor R * (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
    ((Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
      (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)))) with hK
  have hMnn : ∀ omega : ShellSeq d, 0 ≤ M omega := fun omega =>
    coeffLinftySupBound_nonneg nu hnu.le S.LPrime S.m omega
  have hCd0 : 0 ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hcf : (0 : ℝ) < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale
  have hinner0 : 0 ≤ (Real.sqrt (((largeCubeSubcubes d S.n S.m).card : ℝ)) + 1) *
      (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e))) :=
    mul_nonneg (by positivity) (mul_nonneg (inv_nonneg.2 hnu.le) (Real.sqrt_nonneg _))
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg hcf.le hCd0) hinner0
  have henv : ∀ omega : ShellSeq d, seminormFluxNeg nu hnu S P e omega R ≤ K * M omega := by
    intro omega
    have h := seminormFluxNeg_envelope hnu S P e hnm hR omega
    rw [hM, hK]
    exact h
  have hint : Integrable (fun omega : ShellSeq d => 1 + M omega ^ (2 : ℕ)) P.toMeasure :=
    (integrable_const (1 : ℝ)).add
      (integrable_coeffLinftySupBound_sq_at_B hPrefix hJ2 hJ3 hJ4 hnu.le hLpos hmpos)
  have hfin : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (1 + M omega ^ (2 : ℕ))
      ∂P.toMeasure) ≠ ⊤ := by
    have h := hint.hasFiniteIntegral
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun omega => by positivity)] at h
    exact h.ne
  have hpoint : ∀ omega : ShellSeq d,
      ENNReal.ofReal (seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)) ≤
        ENNReal.ofReal (K ^ ((3 : ℝ) / 2)) *
          ENNReal.ofReal (1 + M omega ^ (2 : ℕ)) := by
    intro omega
    have h1 : seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
        K ^ ((3 : ℝ) / 2) * (1 + M omega ^ (2 : ℕ)) := by
      calc seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)
          ≤ (K * M omega) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow (seminormFluxNeg_nonneg nu hnu S P e omega R) (henv omega)
              (by norm_num)
        _ = K ^ ((3 : ℝ) / 2) * M omega ^ ((3 : ℝ) / 2) :=
            Real.mul_rpow hK0 (hMnn omega)
        _ ≤ K ^ ((3 : ℝ) / 2) * (1 + M omega ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left (rpow_three_halves_le_one_add_sq (hMnn omega))
              (Real.rpow_nonneg hK0 _)
    refine le_trans (ENNReal.ofReal_le_ofReal h1) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hK0 _)]
  have hle : (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2))
        ∂P.toMeasure) ≤
      ENNReal.ofReal (K ^ ((3 : ℝ) / 2)) *
        ∫⁻ omega : ShellSeq d, ENNReal.ofReal (1 + M omega ^ (2 : ℕ)) ∂P.toMeasure :=
    calc (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2))
          ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d, ENNReal.ofReal (K ^ ((3 : ℝ) / 2)) *
            ENNReal.ofReal (1 + M omega ^ (2 : ℕ)) ∂P.toMeasure :=
          lintegral_mono hpoint
      _ = ENNReal.ofReal (K ^ ((3 : ℝ) / 2)) *
            ∫⁻ omega : ShellSeq d, ENNReal.ofReal (1 + M omega ^ (2 : ℕ)) ∂P.toMeasure :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact ne_of_lt (lt_of_le_of_lt hle
    (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)))

/-- **The `3/2`-power of the seminorm flux norm is integrable, given only its
a.e. strong measurability.**  This is `_hIntFlux` of
`term3_oscBound_seminorm_measurable` with the moment half discharged by the
telescope. -/
theorem integrable_seminormFluxNeg_rpow_of_aestronglyMeasurable {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (hmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R) P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)) P.toMeasure := by
  refine ⟨(Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)).comp_aestronglyMeasurable
    hmeas, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  have hpoint : ∀ omega : ShellSeq d,
      ‖seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)‖ₑ =
        ENNReal.ofReal (seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)) :=
    fun omega => Real.enorm_eq_ofReal (Real.rpow_nonneg
      (seminormFluxNeg_nonneg nu hnu S P e omega R) _)
  rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact lt_top_iff_ne_top.2 (lintegral_seminormFluxNeg_rpow_ne_top hnu P hPrefix hJ2 hJ3 hJ4
    S hSorder e hR)

/-- **`_hMemFlux` costs measurability alone.**  The `L^{3/2}(P)` membership of
the seminorm flux norm follows from its a.e. strong measurability and the
telescope's `3/2`-moment finiteness; the second input of `_hMemFlux` is
discharged in this module and is no longer a hypothesis. -/
theorem memLp_seminormFluxNeg_of_aestronglyMeasurable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (hmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R) P.toMeasure) :
    MemLp (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R)
      (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure :=
  memLp_ofReal_of_integrable_rpow (q := (3 : ℝ) / 2) (by norm_num)
    (fun omega => seminormFluxNeg_nonneg nu hnu S P e omega R) hmeas
    (integrable_seminormFluxNeg_rpow_of_aestronglyMeasurable hnu P hPrefix hJ2 hJ3 hJ4
      S hSorder e hR hmeas)

/-! ## The oscillation leaf: the carrier does not depend on the witness

The obstruction to `_hAEMOsc` is a *selection*, not an estimate.  Two weak
Hessians of the same `H¹` function agree a.e. on the open cube
(`hess_ae_eq`), so the seminorm
`‖∇²v‖_{\underline L²(R)}` — and with it the whole carrier `centredSeminormAt` —
takes the same value on either witness.  Hence the sample-side statement
`_hAEMOsc` is *independent of which weak-Hessian family is chosen*: it is
exactly the measurability of the seminorm field `ω ↦ ‖∇²v(ω)‖_{L̲²(R)}` of the
response, i.e. the graph measurability of the weak-Hessian operator, which is not
derivable from the telescope.  In particular no estimate on the telescope can
produce it: the only content of the leaf is that a measurable selection of weak
Hessians exists. -/

/-! ## The display with the flux leaf removed -/

end

end SuperdiffusionCLT.Section3.Terms
