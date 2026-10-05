/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Probability.StationaryProjection
public import SuperdiffusionCLT.Section3.ResponseFields.StationaryComparison

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

/-- **Lemma `l.abstract.response.fields`, the stationary half**: the hypotheses of the
lemma together with the energy comparison `e.energy.comparison.N.D`.

Let `F` be an `ℝ^d`-stationary random vector field with `E[|F(0)|²] < ∞`, let
`∇ŵ_F` be its stationary potential field, and for `M ∈ ℕ` let `w_D ∈ H¹₀(cu_M)`
and the zero-average `w_N ∈ H¹(cu_M)` solve the two response problems
`e.abstract.response.equations`. Then
`E[‖∇w_D‖²_{L̲²(cu_M)}] ≤ E[|∇ŵ_F(0)|²] ≤ E[‖∇w_N‖²_{L̲²(cu_M)}]`.

The deterministic estimates of the lemma, which the paper introduces as the ones "which do not
use stationarity", are the companion statement `responseFields_apriori_orderOne`; this statement
consequently carries no constant `C(d)`, because the constant is introduced in the other half.
The gap identity `e.energy.quadratic.N.D` is not included among the conjuncts and is the proved
`SuperdiffusionCLT.Section3.ResponseFields.volumeAverage_energy_gap`.

Readings: the sample fields are primitive `Ω → Vec d → Vec d` data with the
cocycle identity of stationarity; `2 ≤ d` is standing;
`E|∇ŵ(0)|² < ∞` is a typing assumption; the function spaces are on the
open cube while the normalized norms and averages are on the half-open cube,
the two being interchangeable by
`SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet`.

The carrier `Ω` is universe-polymorphic. The two `AEStronglyMeasurable`
hypotheses are typing data of the same class as `hG`: without them the two outer
`∫⁻` are Mathlib's *lower* integrals of possibly non-measurable integrands, so
the second inequality would assert strictly more than the paper does.

The realization of the stationary potential gradient on the cube is primitive data, as the sample
fields of `F` are: an `H¹` function `u ω` on the open cube whose weak
gradient is the sample field `x ↦ ∇ŵ(x + ω)` and which solves the same interior
identity as the Dirichlet response, together with the joint measurability of the
two sample fields on the product of the law and the normalized cube measure
(typing binders; the instances give only fixed-translation
measurability). -/
theorem SuperdiffusionCLT.Frozen.Section3.responseFields_stationary.{u}
    (d : ℕ) (hd : 2 ≤ d) :
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
      [VAddInvariantMeasure (Vec d) Ω μ]
      (F : Ω → Vec d → Vec d) (gradHatW : Ω → Vec d)
      (M : ℕ)
      (wD : Ω → H10Function (openCubeSet (originCube d (M : ℤ))))
      (wN : Ω → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
      (_hwD : AEStronglyMeasurable
        (fun ω => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wD ω).toH1Function.grad) μ)
      (_hwN : AEStronglyMeasurable
        (fun ω => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wN ω).toH1Function.grad) μ)
      (u : Ω → H1Function (openCubeSet (originCube d (M : ℤ))))
      (_hjointG : AEStronglyMeasurable
        (fun p : Ω × Vec d => HilbertVec.ofVec (gradHatW (p.2 +ᵥ p.1)))
        (μ.prod (normalizedCubeMeasure (originCube d (M : ℤ)))))
      (_hjointF : AEStronglyMeasurable
        (fun p : Ω × Vec d => HilbertVec.ofVec (F (p.2 +ᵥ p.1) 0))
        (μ.prod (normalizedCubeMeasure (originCube d (M : ℤ)))))
      (_hgrad : ∀ᵐ ω ∂μ,
        (u ω).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
          fun x => gradHatW (x +ᵥ ω))
      (_hueq : ∀ᵐ ω ∂μ, ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
        ∫ x in openCubeSet (originCube d (M : ℤ)),
            vecDot ((u ω).grad x) (φ.toH1Function.grad x) =
          -∫ x in openCubeSet (originCube d (M : ℤ)),
            vecDot (F ω x) (φ.toH1Function.grad x)),
      (∀ (ω : Ω) (x y : Vec d), F (x +ᵥ ω) y = F ω (y + x)) →
      ∀ hF : MemLp (fun ω => HilbertVec.ofVec (F ω 0)) 2 μ,
      ∀ hG : MemLp (fun ω => HilbertVec.ofVec (gradHatW ω)) 2 μ,
      (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) =
        -SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection
            (μ := μ) (hF.toLp (fun ω => HilbertVec.ofVec (F ω 0)))) →
      (∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
        (originCube d (M : ℤ)) (F ω) (wD ω)) →
      (∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
        (originCube d (M : ℤ)) (F ω) (wN ω)) →
      (∫⁻ ω, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
              (originCube d (M : ℤ)) 2 (wD ω).toH1Function.grad) ^ (2 : ℕ) ∂μ ≤
          ∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ) ∧
        (∫⁻ ω, ‖HilbertVec.ofVec (gradHatW ω)‖ₑ ^ (2 : ℕ) ∂μ ≤
          ∫⁻ ω, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
            (originCube d (M : ℤ)) 2 (wN ω).toH1Function.grad) ^ (2 : ℕ) ∂μ)
    := by
  have _hd := hd
  intro Ω _ μ _ _ _ _ F gradHatW M wD wN _hwD hwN u hjointG hjointF hgrad hueq
    hcocycle hF hG hproj hD hN
  exact SuperdiffusionCLT.Section3.ResponseFields.responseFields_stationary_of_realization
    M F gradHatW wD wN u hwN hcocycle hF hG hproj hjointG hjointF hgrad hueq hD hN
