/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Probability.StationaryProjection

/-!
# Comparing the cube responses with the stationary potential field

Step 1 of the proof of `l.abstract.response.fields` compares the energies of
the two cube responses of a stationary flux with the second moment of the
stationary potential field at the origin. This file supplies the three
ingredients of that step.

## The three ingredients

* **Harmonic orthogonality.** If `u ∈ H¹(cu_M)` satisfies the
  same interior identity as the Dirichlet response, then testing the Dirichlet
  equation with the Dirichlet response itself and the interior identity with the
  same function gives `⨍ ∇w_D·∇w_D = ⨍ ∇u·∇w_D`, and Cauchy-Schwarz turns that
  into `‖∇w_D‖_{L̲²(cu_M)} ≤ ‖∇u‖_{L̲²(cu_M)}`. No stationarity is used.
* **The Neumann variational inequality.** The Neumann response
  minimizes `u ↦ ⨍(½|∇u|² + F·∇u)` over `H¹(cu_M)`; the minimum value is
  `-½‖∇w_N‖²_{L̲²(cu_M)}` because the equation tested with the response itself
  gives `⨍|∇w_N|² = -⨍F·∇w_N`. The proof below is the completed square, and it
  needs no admissibility hypothesis beyond `u ∈ H¹(cu_M)`.
* **Stationarity** (the undisplayed passage `E‖∇ŵ‖²_{L̲²(cu_M)} = E|∇ŵ(0)|²`).
  For a square-integrable origin value `G` the cube average of the sample field
  `x ↦ G (x +ᵥ ω)` has the same expectation as `|G|²`, by Tonelli and the
  invariance of `μ` under the action.

The orthogonality of the stationary potential and solenoidal subspaces
is the fourth ingredient and is one line from the stationary projection
construction (`stationaryPotentialProjection`).

## What is *not* here: the realization

`l.abstract.response.fields` reads `∇ŵ_F` as a field on `ℝ^d`. On the abstract
carrier of `SuperdiffusionCLT.Frozen.Section3.responseFields_stationary`
the potential field is only its origin value `gradHatW : Ω → Vec d`, an `L²`
equivalence class, and the
sample field `x ↦ gradHatW (x +ᵥ ω)` is not known to be the weak gradient of an
`H¹` function on the cube, nor even to be jointly measurable: the standing
instance is `MeasurableConstVAdd (Vec d) Ω`, which makes each single translation
measurable and says nothing about the pair `(x, ω) ↦ x +ᵥ ω`. The flux `F` is
primitive data with the cocycle identity `F (x +ᵥ ω) y = F ω (y + x)`, so
`F ω x = (fun ω => F ω 0) (x +ᵥ ω)`, but no such identification is available for
`gradHatW`, whose defining property is an `L²`-level projection identity.

Both energy comparisons therefore carry the realization as an explicit
hypothesis: a family `u : Ω → H1Function (openCubeSet cu_M)` whose gradient is,
for `μ`-almost every `ω`, the sample field `x ↦ gradHatW (x +ᵥ ω)` on the cube,
and which satisfies the same interior identity as the responses. Together with
the joint measurability of the two sample fields this is the only input the
statement of `l.abstract.response.fields` still needs; nothing else in
`e.energy.comparison.N.D` is left open.

## Main results

* `vecCubeLpENorm_two_sq`: `‖F‖²_{L̲²(Q)}` as a lower integral of `|F|²`.
* `lintegral_lintegral_vadd`, `integral_integral_vadd`: the stationarity
  identity for a lower integral and for a Bochner integral.
* `lintegral_vecCubeLpENorm_sq_vadd`: `E‖G(·+ᵥω)‖²_{L̲²(Q)} = E|G|²`.
* `vecCubeLpENorm_grad_dirichlet_le`: the pathwise Dirichlet minimality.
* `setIntegral_neumann_variational`: the pathwise Neumann variational
  inequality.
* `inner_neg_stationaryPotentialProjection_eq`: the potential/solenoidal
  orthogonality in the form `⟪-Π F, F⟫ = -‖Π F‖²`.
* `lintegral_vecCubeLpENorm_grad_dirichlet_le`,
  `lintegral_enorm_sq_le_lintegral_vecCubeLpENorm_grad_neumann`: the two conclusions of
  `e.energy.comparison.N.D`, each from the realization hypothesis.
* `responseFields_stationary_of_realization`: both conclusions together, in the
  shape of the statement `responseFields_stationary`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Probability.Stationary
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The squared normalized cube norm -/

/-- The square of an `L²` norm is the lower integral of the squared norm. -/
theorem eLpNorm_two_sq {α : Type*} {E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (ν : Measure α) (f : α → E) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ (2 : ℕ) = ∫⁻ a, ‖f a‖ₑ ^ (2 : ℕ) ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- The square of `‖F‖_{L̲²(Q)}` is the normalized cube integral of `|F|²`. -/
theorem vecCubeLpENorm_two_sq (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 F ^ (2 : ℕ) =
      ∫⁻ x, ‖HilbertVec.ofVec (F x)‖ₑ ^ (2 : ℕ) ∂normalizedCubeMeasure Q :=
  eLpNorm_two_sq _ _ hF

/-- The squared Euclidean magnitude is the squared norm of the Hilbert
reading. -/
theorem enorm_ofVec_sq (x : Vec d) :
    ‖HilbertVec.ofVec x‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq x) := by
  have hnorm : ‖HilbertVec.ofVec x‖ ^ (2 : ℕ) = vecNormSq x := by
    rw [HilbertVec.norm_sq_eq_sum_sq]
    simp [vecNormSq, vecDot, sq]
  rw [← hnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- A vector field that is `L²` on the open cube is square integrable for the
normalized cube measure. -/
theorem integrable_vecNormSq_normalizedCubeMeasure {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    Integrable (fun x => vecNormSq (F x)) (normalizedCubeMeasure Q) := by
  have hmem : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure
      ENNReal.ofReal_ne_top
  refine (hmem.norm.integrable_sq).congr (Filter.Eventually.of_forall fun x => ?_)
  simpa [vecNormSq, vecDot, sq, hilbertifyVecField] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec (F x))

/-- The normalized cube integral is the open-cube integral divided by the cube
volume. -/
theorem integral_normalizedCubeMeasure_eq (Q : TriadicCube d) (f : Vec d → ℝ) :
    ∫ x, f x ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.2 (cubeVolume_pos Q))), smul_eq_mul]

/-- The squared normalized cube norm as an `ENNReal.ofReal`. -/
theorem vecCubeLpENorm_two_sq_eq_ofReal {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    vecCubeLpENorm Q 2 F ^ (2 : ℕ) =
      ENNReal.ofReal (∫ x, vecNormSq (F x) ∂normalizedCubeMeasure Q) := by
  have hmeas : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField hF).aestronglyMeasurable.smul_measure _
  rw [vecCubeLpENorm_two_sq Q F hmeas,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_vecNormSq_normalizedCubeMeasure hF)
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg (F x))]
  exact lintegral_congr fun x => enorm_ofVec_sq (F x)

/-- The normalized cube norm is the `L²` norm of the open cube, rescaled by the
cube volume. -/
theorem vecCubeLpENorm_two_eq_smul (Q : TriadicCube d) (F : Vec d → Vec d) :
    vecCubeLpENorm Q 2 F =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (2 : ℝ)⁻¹ *
        eLpNorm (hilbertifyVecField F) 2 (volumeMeasureOn (openCubeSet Q)) := by
  rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm,
    normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne']
  norm_num

/-- Monotonicity of `‖·‖_{L̲²(Q)}` under the `L²` norm of the open cube. -/
theorem vecCubeLpENorm_two_mono {Q : TriadicCube d} {F G : Vec d → Vec d}
    (h : eLpNorm (hilbertifyVecField F) 2 (volumeMeasureOn (openCubeSet Q)) ≤
      eLpNorm (hilbertifyVecField G) 2 (volumeMeasureOn (openCubeSet Q))) :
    vecCubeLpENorm Q 2 F ≤ vecCubeLpENorm Q 2 G := by
  rw [vecCubeLpENorm_two_eq_smul, vecCubeLpENorm_two_eq_smul]
  gcongr

/-! ## Stationarity: the cube average of a sample field -/

section Stationary

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **Stationarity for a lower integral.** Averaging the sample field
`x ↦ g (x +ᵥ ω)` over a probability measure on `ℝ^d` and then over `μ` returns
the expectation of `g`: Tonelli exchanges the two integrals, and each fixed
translation preserves `μ`. The joint measurability is a hypothesis because
`MeasurableConstVAdd` supplies only the fixed-translation half. -/
theorem lintegral_lintegral_vadd (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {g : Ω → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hjoint : AEMeasurable (fun p : Ω × Vec d => g (p.2 +ᵥ p.1)) (μ.prod ν)) :
    ∫⁻ ω, ∫⁻ x, g (x +ᵥ ω) ∂ν ∂μ = ∫⁻ ω, g ω ∂μ := by
  rw [lintegral_lintegral_swap hjoint]
  have hinner : ∀ x : Vec d, ∫⁻ ω, g (x +ᵥ ω) ∂μ = ∫⁻ ω, g ω ∂μ := by
    intro x
    have hmp := measurePreserving_const_vadd (μ := μ) (d := d) x
    calc ∫⁻ ω, g (x +ᵥ ω) ∂μ
        = ∫⁻ ω, g ω ∂(Measure.map (fun ω : Ω => x +ᵥ ω) μ) :=
          (lintegral_map' (by rw [hmp.map_eq]; exact hg)
            (measurable_const_vadd x).aemeasurable).symm
      _ = ∫⁻ ω, g ω ∂μ := by rw [hmp.map_eq]
  simp only [hinner]
  rw [lintegral_const, measure_univ, mul_one]

/-- The sample field of an integrable origin value is integrable on the
product. -/
theorem integrable_vadd_prod (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {h : Ω → ℝ} (hint : Integrable h μ)
    (hjoint : AEStronglyMeasurable (fun p : Ω × Vec d => h (p.2 +ᵥ p.1)) (μ.prod ν)) :
    Integrable (fun p : Ω × Vec d => h (p.2 +ᵥ p.1)) (μ.prod ν) := by
  refine ⟨hjoint, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hjoint.enorm,
    lintegral_lintegral_vadd ν hint.aestronglyMeasurable.enorm hjoint.enorm]
  exact hint.hasFiniteIntegral

/-- **Stationarity for a Bochner integral**, the form used by the cross term
`⨍_{cu_M} ∇ŵ·F` of the paper. -/
theorem integral_integral_vadd (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {h : Ω → ℝ} (hint : Integrable h μ)
    (hjoint : AEStronglyMeasurable (fun p : Ω × Vec d => h (p.2 +ᵥ p.1)) (μ.prod ν)) :
    ∫ ω, ∫ x, h (x +ᵥ ω) ∂ν ∂μ = ∫ ω, h ω ∂μ := by
  rw [integral_integral_swap (integrable_vadd_prod ν hint hjoint)]
  have hinner : ∀ x : Vec d, ∫ ω, h (x +ᵥ ω) ∂μ = ∫ ω, h ω ∂μ := by
    intro x
    have hmp := measurePreserving_const_vadd (μ := μ) (d := d) x
    calc ∫ ω, h (x +ᵥ ω) ∂μ
        = ∫ ω, h ω ∂(Measure.map (fun ω : Ω => x +ᵥ ω) μ) :=
          (integral_map (measurable_const_vadd x).aemeasurable
            (by rw [hmp.map_eq]; exact hint.aestronglyMeasurable)).symm
      _ = ∫ ω, h ω ∂μ := by rw [hmp.map_eq]
  simp only [hinner]
  rw [integral_const, probReal_univ, one_smul]

/-- **The stationarity identity of Step 1**: the expected normalized cube energy
of the sample field of `G` is the second moment of `G` at the origin. -/
theorem lintegral_vecCubeLpENorm_sq_vadd (Q : TriadicCube d) {G : Ω → Vec d}
    (hG : AEStronglyMeasurable (fun ω => HilbertVec.ofVec (G ω)) μ)
    (hjoint : AEStronglyMeasurable
      (fun p : Ω × Vec d => HilbertVec.ofVec (G (p.2 +ᵥ p.1)))
      (μ.prod (normalizedCubeMeasure Q))) :
    ∫⁻ ω, vecCubeLpENorm Q 2 (fun x => G (x +ᵥ ω)) ^ (2 : ℕ) ∂μ =
      ∫⁻ ω, ‖HilbertVec.ofVec (G ω)‖ₑ ^ (2 : ℕ) ∂μ := by
  have hprob : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hsec : ∀ᵐ ω ∂μ, AEStronglyMeasurable
      (hilbertifyVecField (fun x => G (x +ᵥ ω))) (normalizedCubeMeasure Q) :=
    hjoint.prodMk_left
  rw [lintegral_congr_ae (by
    filter_upwards [hsec] with ω hω
    exact congrArg (· ^ (2 : ℕ)) rfl |>.trans (vecCubeLpENorm_two_sq Q _ hω))]
  exact lintegral_lintegral_vadd (normalizedCubeMeasure Q) (hG.enorm.pow_const 2)
    (hjoint.enorm.pow_const 2)

end Stationary

/-! ## The pathwise energy comparisons -/

section Pathwise

/-- Cauchy-Schwarz on the open cube: a field whose self-pairing equals its
pairing with a second field has the smaller `L²` norm. -/
theorem eLpNorm_le_of_setIntegral_vecDot_self {Q : TriadicCube d}
    {a b : Vec d → Vec d} (ha : MemVectorL2 (openCubeSet Q) a)
    (hb : MemVectorL2 (openCubeSet Q) b)
    (h : ∫ x in openCubeSet Q, vecDot (a x) (a x) =
      ∫ x in openCubeSet Q, vecDot (b x) (a x)) :
    eLpNorm (hilbertifyVecField a) 2 (volumeMeasureOn (openCubeSet Q)) ≤
      eLpNorm (hilbertifyVecField b) 2 (volumeMeasureOn (openCubeSet Q)) := by
  set A := toHilbertVectorL2OfVecField ha with hA
  set B := toHilbertVectorL2OfVecField hb with hB
  have hAA : inner ℝ A A = ∫ x in openCubeSet Q, vecDot (a x) (a x) :=
    inner_toHilbertVectorL2OfVecField_eq_integral ha ha
  have hBA : inner ℝ B A = ∫ x in openCubeSet Q, vecDot (b x) (a x) :=
    inner_toHilbertVectorL2OfVecField_eq_integral hb ha
  have hnorm : ‖A‖ ≤ ‖B‖ := by
    have hsq : ‖A‖ * ‖A‖ ≤ ‖B‖ * ‖A‖ := by
      calc ‖A‖ * ‖A‖ = inner ℝ A A := (real_inner_self_eq_norm_mul_norm A).symm
        _ = inner ℝ B A := by rw [hAA, hBA, h]
        _ ≤ ‖B‖ * ‖A‖ := real_inner_le_norm B A
    rcases eq_or_lt_of_le (norm_nonneg A) with hzero | hpos
    · rw [← hzero]
      exact norm_nonneg B
    · exact le_of_mul_le_mul_right (by linarith only [hsq]) hpos
  have hAnorm : ‖A‖ =
      (eLpNorm (hilbertifyVecField a) 2 (volumeMeasureOn (openCubeSet Q))).toReal :=
    Lp.norm_toLp _ (memHilbertVectorL2_hilbertifyVecField ha)
  have hBnorm : ‖B‖ =
      (eLpNorm (hilbertifyVecField b) 2 (volumeMeasureOn (openCubeSet Q))).toReal :=
    Lp.norm_toLp _ (memHilbertVectorL2_hilbertifyVecField hb)
  rw [hAnorm, hBnorm] at hnorm
  exact (ENNReal.toReal_le_toReal
    (memHilbertVectorL2_hilbertifyVecField ha).eLpNorm_ne_top
    (memHilbertVectorL2_hilbertifyVecField hb).eLpNorm_ne_top).1 hnorm

/-- **The Dirichlet half of the harmonic orthogonality argument**.
If `u ∈ H¹(cu_M)` satisfies the interior identity of the
Dirichlet problem, then the Dirichlet response has the smaller normalized
energy. Testing the Dirichlet equation with `w_D` and the interior identity with
the same `w_D` gives `⨍|∇w_D|² = ⨍∇u·∇w_D`, and Cauchy-Schwarz finishes; this
is the print's `∫(∇û − ∇w_D)·∇w_D = 0` followed by its Cauchy-Schwarz step. -/
theorem vecCubeLpENorm_grad_dirichlet_le {Q : TriadicCube d} {F : Vec d → Vec d}
    {wD : H10Function (openCubeSet Q)} {u : H1Function (openCubeSet Q)}
    (hD : IsCubeDirichletResponse Q F wD)
    (hu : ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (u.grad x) (φ.toH1Function.grad x) =
        -∫ x in openCubeSet Q, vecDot (F x) (φ.toH1Function.grad x)) :
    vecCubeLpENorm Q 2 wD.toH1Function.grad ≤ vecCubeLpENorm Q 2 u.grad := by
  refine vecCubeLpENorm_two_mono
    (eLpNorm_le_of_setIntegral_vecDot_self wD.toH1Function.grad_memVectorL2
      u.grad_memVectorL2 ?_)
  rw [hD wD, ← hu wD]

/-- **The Neumann variational inequality**, in the plain
integral form `−∫|∇w_N|² ≤ ∫|∇u|² + 2∫F·∇u`. It is the completed square
`0 ≤ ∫|∇u − ∇w_N|²` after the Neumann equation, tested with the mean-zero
normalization of `u`, has replaced `∫∇w_N·∇u` by `−∫F·∇u`. -/
theorem setIntegral_neumann_variational {Q : TriadicCube d} {F : Vec d → Vec d}
    {wN : H1MeanZeroFunction (openCubeSet Q)} (hN : IsCubeNeumannResponse Q F wN)
    (u : H1Function (openCubeSet Q)) :
    -∫ x in openCubeSet Q, vecNormSq (wN.toH1Function.grad x) ≤
      (∫ x in openCubeSet Q, vecNormSq (u.grad x)) +
        2 * ∫ x in openCubeSet Q, vecDot (F x) (u.grad x) := by
  have hgrad : (H1Function.toMeanZero u).toH1Function.grad = u.grad := by
    funext x
    exact H1Function.grad_subAverage u x
  have hNu := hN (H1Function.toMeanZero u)
  rw [hgrad] at hNu
  have hUU : IntegrableOn (fun x => vecDot (u.grad x) (u.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 u.grad_memVectorL2
  have hNN : IntegrableOn
      (fun x => vecDot (wN.toH1Function.grad x) (wN.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 wN.toH1Function.grad_memVectorL2
      wN.toH1Function.grad_memVectorL2
  have hNU : IntegrableOn
      (fun x => vecDot (wN.toH1Function.grad x) (u.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 wN.toH1Function.grad_memVectorL2
      u.grad_memVectorL2
  have hpt : ∀ x : Vec d,
      vecNormSq (u.grad x - wN.toH1Function.grad x) =
        vecDot (u.grad x) (u.grad x) -
          2 * vecDot (wN.toH1Function.grad x) (u.grad x) +
          vecDot (wN.toH1Function.grad x) (wN.toH1Function.grad x) := by
    intro x
    simp only [vecNormSq, vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmix : IntegrableOn
      (fun x => vecDot (u.grad x) (u.grad x) -
        2 * vecDot (wN.toH1Function.grad x) (u.grad x)) (openCubeSet Q) :=
    hUU.sub (hNU.const_mul 2)
  have hnonneg : (0 : ℝ) ≤
      ∫ x in openCubeSet Q, vecNormSq (u.grad x - wN.toH1Function.grad x) :=
    setIntegral_nonneg (measurableSet_openCubeSet Q)
      (fun x _ => vecNormSq_nonneg _)
  rw [setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => hpt x),
    integral_add hmix hNN, integral_sub hUU (hNU.const_mul 2),
    integral_const_mul, hNu] at hnonneg
  simp only [vecNormSq]
  linarith only [hnonneg]

end Pathwise

/-! ## Orthogonality of the stationary potential and solenoidal parts -/

section Orthogonality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The potential/solenoidal orthogonality**: the potential
part of a stationary field is orthogonal to the solenoidal remainder. -/
theorem inner_stationaryPotentialProjection_sub_eq_zero (F : VectorL2 d μ) :
    inner ℝ (stationaryPotentialProjection (μ := μ) F)
        (F - stationaryPotentialProjection (μ := μ) F) = 0 :=
  (Submodule.mem_orthogonal _ _).1
    (sub_stationaryPotentialProjection_mem_orthogonal F) _
    (stationaryPotentialProjection_mem F)

/-- The form of the orthogonality used by the Neumann half:
`E[(∇ŵ·F)(0)] = -E[|∇ŵ(0)|²]` for `∇ŵ = -Π F`. -/
theorem inner_neg_stationaryPotentialProjection_eq (F : VectorL2 d μ) :
    inner ℝ (-stationaryPotentialProjection (μ := μ) F) F =
      -‖(-stationaryPotentialProjection (μ := μ) F : VectorL2 d μ)‖ ^ 2 := by
  have hsplit : F = (F - stationaryPotentialProjection (μ := μ) F) +
      stationaryPotentialProjection (μ := μ) F := by
    rw [sub_add_cancel]
  rw [norm_neg, ← real_inner_self_eq_norm_sq, inner_neg_left]
  congr 1
  nth_rewrite 2 [hsplit]
  rw [inner_add_right, inner_stationaryPotentialProjection_sub_eq_zero, zero_add]

end Orthogonality

/-! ## The two halves of `e.energy.comparison.N.D` -/

section Comparison

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The first inequality of `e.energy.comparison.N.D`**, from
the realization `u` of the stationary potential field on the cube. Pathwise the
Dirichlet response has the smaller energy, by
`vecCubeLpENorm_grad_dirichlet_le`; taking expectations and using
`lintegral_vecCubeLpENorm_sq_vadd` replaces the cube energy of the sample field
by the second moment at the origin. -/
theorem lintegral_vecCubeLpENorm_grad_dirichlet_le (Q : TriadicCube d)
    (F : Ω → Vec d → Vec d) (gradHatW : Ω → Vec d)
    (wD : Ω → H10Function (openCubeSet Q)) (u : Ω → H1Function (openCubeSet Q))
    (hG : AEStronglyMeasurable (fun ω => HilbertVec.ofVec (gradHatW ω)) μ)
    (hjoint : AEStronglyMeasurable
      (fun p : Ω × Vec d => HilbertVec.ofVec (gradHatW (p.2 +ᵥ p.1)))
      (μ.prod (normalizedCubeMeasure Q)))
    (hgrad : ∀ᵐ ω ∂μ, (u ω).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => gradHatW (x +ᵥ ω))
    (hueq : ∀ᵐ ω ∂μ, ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot ((u ω).grad x) (φ.toH1Function.grad x) =
        -∫ x in openCubeSet Q, vecDot (F ω x) (φ.toH1Function.grad x))
    (hD : ∀ ω, IsCubeDirichletResponse Q (F ω) (wD ω)) :
    ∫⁻ ω, vecCubeLpENorm Q 2 (wD ω).toH1Function.grad ^ (2 : ℕ) ∂μ ≤
      ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ := by
  calc ∫⁻ ω, vecCubeLpENorm Q 2 (wD ω).toH1Function.grad ^ (2 : ℕ) ∂μ
      ≤ ∫⁻ ω, vecCubeLpENorm Q 2 (fun x => gradHatW (x +ᵥ ω)) ^ (2 : ℕ) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgrad, hueq] with ω hg1 hg2
        have hpath := vecCubeLpENorm_grad_dirichlet_le (hD ω) hg2
        rw [← vecCubeLpENorm_congr_openCubeSet_ae hg1]
        gcongr
    _ = ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ :=
        lintegral_vecCubeLpENorm_sq_vadd Q hG hjoint

/-- A nonnegative function with a finite lower integral of its `ENNReal`
reading is integrable. -/
private theorem integrable_of_ofReal_lintegral_ne_top {α : Type*}
    [MeasurableSpace α] {ν : Measure α} {f : α → ℝ} (hnn : ∀ a, 0 ≤ f a)
    (hmeas : AEMeasurable (fun a => ENNReal.ofReal (f a)) ν)
    (htop : ∫⁻ a, ENNReal.ofReal (f a) ∂ν ≠ ⊤) :
    Integrable f ν := by
  have hrw : ∀ a, (ENNReal.ofReal (f a)).toReal = f a := fun a =>
    ENNReal.toReal_ofReal (hnn a)
  refine ⟨(hmeas.ennreal_toReal.congr
    (Filter.Eventually.of_forall hrw)).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have henorm : ∀ a, ‖f a‖ₑ = ENNReal.ofReal (f a) := fun a =>
    Real.enorm_eq_ofReal (hnn a)
  simp only [henorm]
  exact lt_top_iff_ne_top.2 htop

/-- **The second inequality of `e.energy.comparison.N.D`**,
from the realization `u` of the stationary potential field on the cube. The
pathwise variational inequality of `setIntegral_neumann_variational` is
integrated over `Ω`; the quadratic term is handled by
`lintegral_vecCubeLpENorm_sq_vadd` and the cross term by
`integral_integral_vadd` followed by the potential/solenoidal orthogonality. -/
theorem lintegral_enorm_sq_le_lintegral_vecCubeLpENorm_grad_neumann
    (Q : TriadicCube d) (F : Ω → Vec d → Vec d) (gradHatW : Ω → Vec d)
    (wN : Ω → H1MeanZeroFunction (openCubeSet Q))
    (u : Ω → H1Function (openCubeSet Q))
    (hwN : AEStronglyMeasurable
      (fun ω => vecCubeLpENorm Q 2 (wN ω).toH1Function.grad) μ)
    (hcocycle : ∀ (ω : Ω) (x y : Vec d), F (x +ᵥ ω) y = F ω (y + x))
    (hF : MemLp (fun ω => HilbertVec.ofVec (F ω 0)) 2 μ)
    (hG : MemLp (fun ω => HilbertVec.ofVec (gradHatW ω)) 2 μ)
    (hproj : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := μ)
        (hF.toLp (fun ω => HilbertVec.ofVec (F ω 0))))
    (hjointG : AEStronglyMeasurable
      (fun p : Ω × Vec d => HilbertVec.ofVec (gradHatW (p.2 +ᵥ p.1)))
      (μ.prod (normalizedCubeMeasure Q)))
    (hjointF : AEStronglyMeasurable
      (fun p : Ω × Vec d => HilbertVec.ofVec (F (p.2 +ᵥ p.1) 0))
      (μ.prod (normalizedCubeMeasure Q)))
    (hgrad : ∀ᵐ ω ∂μ, (u ω).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => gradHatW (x +ᵥ ω))
    (hN : ∀ ω, IsCubeNeumannResponse Q (F ω) (wN ω)) :
    ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ ≤
      ∫⁻ ω, vecCubeLpENorm Q 2 (wN ω).toH1Function.grad ^ (2 : ℕ) ∂μ := by
  have hprob : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hLval : ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ =
      ENNReal.ofReal
        (‖hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))‖ ^ (2 : ℕ)) := by
    rw [← eLpNorm_two_sq _ _ hG.aestronglyMeasurable, Lp.norm_toLp _ hG,
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hG.eLpNorm_ne_top]
  -- the quadratic term of the realization
  have hb_ofReal : ∀ᵐ ω ∂μ, ENNReal.ofReal
      (∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q) =
        vecCubeLpENorm Q 2 (fun x => gradHatW (x +ᵥ ω)) ^ (2 : ℕ) := by
    filter_upwards [hgrad] with ω hg
    rw [← vecCubeLpENorm_two_sq_eq_ofReal (u ω).grad_memVectorL2,
      vecCubeLpENorm_congr_openCubeSet_ae hg]
  have hb_nonneg : ∀ ω,
      0 ≤ ∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q :=
    fun _ => integral_nonneg fun _ => vecNormSq_nonneg _
  have hb_lint : ∫⁻ ω, ENNReal.ofReal
        (∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q) ∂μ =
      ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ := by
    rw [lintegral_congr_ae hb_ofReal]
    exact lintegral_vecCubeLpENorm_sq_vadd Q hG.aestronglyMeasurable
      hjointG
  have hb_meas : AEMeasurable (fun ω => ENNReal.ofReal
      (∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q)) μ := by
    refine AEMeasurable.congr ?_ (Filter.EventuallyEq.symm hb_ofReal)
    have hsec : ∀ᵐ ω ∂μ, AEStronglyMeasurable
        (hilbertifyVecField (fun x => gradHatW (x +ᵥ ω))) (normalizedCubeMeasure Q) :=
      hjointG.prodMk_left
    refine AEMeasurable.congr ((hjointG.enorm.pow_const 2).lintegral_prod_right') ?_
    filter_upwards [hsec] with ω hω
    exact (vecCubeLpENorm_two_sq Q _ hω).symm
  have hb_int : Integrable
      (fun ω => ∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q) μ :=
    integrable_of_ofReal_lintegral_ne_top hb_nonneg hb_meas
      (by rw [hb_lint, hLval]; exact ENNReal.ofReal_ne_top)
  have hb_val : ∫ ω, (∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q) ∂μ =
      ‖hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))‖ ^ (2 : ℕ) := by
    refine (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hb_nonneg)
      (by positivity)).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hb_int
      (Filter.Eventually.of_forall hb_nonneg), hb_lint, hLval]
  -- the cross term of the realization
  have hHint : Integrable (fun ω => vecDot (F ω 0) (gradHatW ω)) μ := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (hF.toLp (fun ω => HilbertVec.ofVec (F ω 0)))
      (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)))).congr ?_
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with ω h1 h2
    simp only [h1, h2, HilbertVec.inner_def, HilbertVec.toVec_ofVec]
  have hjointH : AEStronglyMeasurable (fun p : Ω × Vec d =>
      vecDot (F (p.2 +ᵥ p.1) 0) (gradHatW (p.2 +ᵥ p.1)))
      (μ.prod (normalizedCubeMeasure Q)) := by
    refine (hjointF.inner (𝕜 := ℝ) hjointG).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [HilbertVec.inner_def, HilbertVec.toVec_ofVec]
  have hc_eq : ∀ᵐ ω ∂μ,
      ∫ x, vecDot (F ω x) ((u ω).grad x) ∂normalizedCubeMeasure Q =
        ∫ x, vecDot (F (x +ᵥ ω) 0) (gradHatW (x +ᵥ ω))
          ∂normalizedCubeMeasure Q := by
    filter_upwards [hgrad] with ω hg
    refine integral_congr_ae ?_
    have hae : (u ω).grad =ᵐ[normalizedCubeMeasure Q]
        fun x => gradHatW (x +ᵥ ω) := by
      rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
      exact Measure.ae_smul_measure hg _
    filter_upwards [hae] with x hx
    rw [hx, hcocycle ω x 0, zero_add]
  have hc_int : Integrable
      (fun ω => ∫ x, vecDot (F ω x) ((u ω).grad x)
        ∂normalizedCubeMeasure Q) μ := by
    exact ((integrable_vadd_prod (normalizedCubeMeasure Q) hHint
      hjointH).integral_prod_left).congr (Filter.EventuallyEq.symm hc_eq)
  have hc_val : ∫ ω, (∫ x, vecDot (F ω x) ((u ω).grad x)
        ∂normalizedCubeMeasure Q) ∂μ =
      -‖hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))‖ ^ (2 : ℕ) := by
    rw [integral_congr_ae hc_eq,
      integral_integral_vadd (normalizedCubeMeasure Q) hHint hjointH]
    have hinner : inner ℝ (hF.toLp (fun ω => HilbertVec.ofVec (F ω 0)))
        (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))) =
        ∫ ω, vecDot (F ω 0) (gradHatW ω) ∂μ := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with ω h1 h2
      simp only [h1, h2, HilbertVec.inner_def, HilbertVec.toVec_ofVec]
    rw [← hinner, real_inner_comm, hproj,
      inner_neg_stationaryPotentialProjection_eq]
  -- the Neumann energy
  by_cases hA : ∫⁻ ω, vecCubeLpENorm Q 2 (wN ω).toH1Function.grad ^ (2 : ℕ) ∂μ = ⊤
  · rw [hA]
    exact le_top
  · have ha_ofReal : ∀ ω, ENNReal.ofReal
        (∫ x, vecNormSq ((wN ω).toH1Function.grad x)
          ∂normalizedCubeMeasure Q) =
        vecCubeLpENorm Q 2 (wN ω).toH1Function.grad ^ (2 : ℕ) := fun ω =>
      (vecCubeLpENorm_two_sq_eq_ofReal (wN ω).toH1Function.grad_memVectorL2).symm
    have ha_nonneg : ∀ ω, 0 ≤ ∫ x, vecNormSq ((wN ω).toH1Function.grad x)
        ∂normalizedCubeMeasure Q :=
      fun _ => integral_nonneg fun _ => vecNormSq_nonneg _
    have ha_int : Integrable (fun ω => ∫ x,
        vecNormSq ((wN ω).toH1Function.grad x)
          ∂normalizedCubeMeasure Q) μ := by
      refine integrable_of_ofReal_lintegral_ne_top ha_nonneg ?_ ?_
      · simp only [ha_ofReal]
        exact hwN.aemeasurable.pow_const 2
      · simp only [ha_ofReal]
        exact hA
    have hpath : ∀ ω,
        -(∫ x, vecNormSq ((wN ω).toH1Function.grad x)
            ∂normalizedCubeMeasure Q) ≤
          (∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q) +
            2 * ∫ x, vecDot (F ω x) ((u ω).grad x)
              ∂normalizedCubeMeasure Q := by
      intro ω
      have hpos : (0 : ℝ) ≤ (cubeVolume Q)⁻¹ :=
        le_of_lt (inv_pos.2 (cubeVolume_pos Q))
      have key := mul_le_mul_of_nonneg_left
        (setIntegral_neumann_variational (hN ω) (u ω)) hpos
      rw [integral_normalizedCubeMeasure_eq Q
          (fun x => vecNormSq ((wN ω).toH1Function.grad x)),
        integral_normalizedCubeMeasure_eq Q (fun x => vecNormSq ((u ω).grad x)),
        integral_normalizedCubeMeasure_eq Q
          (fun x => vecDot (F ω x) ((u ω).grad x))]
      linarith only [key]
    have hmono : ∫ ω, -(∫ x, vecNormSq ((wN ω).toH1Function.grad x)
          ∂normalizedCubeMeasure Q) ∂μ ≤
        ∫ ω, ((∫ x, vecNormSq ((u ω).grad x) ∂normalizedCubeMeasure Q) +
          2 * ∫ x, vecDot (F ω x) ((u ω).grad x)
            ∂normalizedCubeMeasure Q) ∂μ :=
      integral_mono ha_int.neg (hb_int.add (hc_int.const_mul 2)) hpath
    rw [integral_neg, integral_add hb_int (hc_int.const_mul 2),
      integral_const_mul, hb_val, hc_val] at hmono
    have hle : ‖hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))‖ ^ (2 : ℕ) ≤
        ∫ ω, (∫ x, vecNormSq ((wN ω).toH1Function.grad x)
          ∂normalizedCubeMeasure Q) ∂μ := by
      linarith only [hmono]
    calc ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ
        = ENNReal.ofReal
            (‖hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))‖ ^ (2 : ℕ)) :=
          hLval
      _ ≤ ENNReal.ofReal (∫ ω, (∫ x,
            vecNormSq ((wN ω).toH1Function.grad x)
              ∂normalizedCubeMeasure Q) ∂μ) := ENNReal.ofReal_le_ofReal hle
      _ = ∫⁻ ω, vecCubeLpENorm Q 2 (wN ω).toH1Function.grad ^ (2 : ℕ) ∂μ := by
          rw [ofReal_integral_eq_lintegral_ofReal ha_int
            (Filter.Eventually.of_forall ha_nonneg)]
          exact lintegral_congr fun ω => ha_ofReal ω

/-- **Both inequalities of `e.energy.comparison.N.D`** on the
origin cube `cu_M`, in the shape of the statement `responseFields_stationary`
and with its binders, except that the
realization of `∇ŵ_F` as a field on the cube is carried explicitly by `u`
together with `hgrad`, `hueq`, `hjointF` and `hjointG`. The standing `2 ≤ d`
of that statement is omitted here because no conclusion below uses it. -/
theorem responseFields_stationary_of_realization (M : ℕ)
    (F : Ω → Vec d → Vec d) (gradHatW : Ω → Vec d)
    (wD : Ω → H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : Ω → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (u : Ω → H1Function (openCubeSet (originCube d (M : ℤ))))
    (hwN : AEStronglyMeasurable
      (fun ω => vecCubeLpENorm (originCube d (M : ℤ)) 2
        (wN ω).toH1Function.grad) μ)
    (hcocycle : ∀ (ω : Ω) (x y : Vec d), F (x +ᵥ ω) y = F ω (y + x))
    (hF : MemLp (fun ω => HilbertVec.ofVec (F ω 0)) 2 μ)
    (hG : MemLp (fun ω => HilbertVec.ofVec (gradHatW ω)) 2 μ)
    (hproj : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := μ)
        (hF.toLp (fun ω => HilbertVec.ofVec (F ω 0))))
    (hjointG : AEStronglyMeasurable
      (fun p : Ω × Vec d => HilbertVec.ofVec (gradHatW (p.2 +ᵥ p.1)))
      (μ.prod (normalizedCubeMeasure (originCube d (M : ℤ)))))
    (hjointF : AEStronglyMeasurable
      (fun p : Ω × Vec d => HilbertVec.ofVec (F (p.2 +ᵥ p.1) 0))
      (μ.prod (normalizedCubeMeasure (originCube d (M : ℤ)))))
    (hgrad : ∀ᵐ ω ∂μ,
      (u ω).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
        fun x => gradHatW (x +ᵥ ω))
    (hueq : ∀ᵐ ω ∂μ, ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
      ∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot ((u ω).grad x) (φ.toH1Function.grad x) =
        -∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot (F ω x) (φ.toH1Function.grad x))
    (hD : ∀ ω, IsCubeDirichletResponse (originCube d (M : ℤ)) (F ω) (wD ω))
    (hN : ∀ ω, IsCubeNeumannResponse (originCube d (M : ℤ)) (F ω) (wN ω)) :
    (∫⁻ ω, vecCubeLpENorm (originCube d (M : ℤ)) 2
        (wD ω).toH1Function.grad ^ (2 : ℕ) ∂μ ≤
      ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ) ∧
      (∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ ≤
        ∫⁻ ω, vecCubeLpENorm (originCube d (M : ℤ)) 2
          (wN ω).toH1Function.grad ^ (2 : ℕ) ∂μ) :=
  ⟨lintegral_vecCubeLpENorm_grad_dirichlet_le (originCube d (M : ℤ)) F gradHatW
      wD u hG.aestronglyMeasurable hjointG hgrad hueq hD,
    lintegral_enorm_sq_le_lintegral_vecCubeLpENorm_grad_neumann
      (originCube d (M : ℤ)) F gradHatW wN u hwN hcocycle hF hG hproj hjointG
      hjointF hgrad hN⟩

end Comparison

end

end ResponseFields
end Section3
end SuperdiffusionCLT
